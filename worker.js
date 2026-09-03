import { createEncoder } from "./libopus/index.js";

const VENDOR_SONY = 0x054C;
const PRODUCT_SONY_DUALSENSE = 0x0CE6;
const INPUT_REPORT_ID = 0x31;
const STATE_REPORT_ID = 0x32;
const AUDIO_REPORT_ID = 0x39;
const CHANNELS = 2;
const FRAMES_PER_OPUS_PACKET = 480;
const SAMPLES_PER_OPUS_PACKET = FRAMES_PER_OPUS_PACKET * CHANNELS;
const FULL_REPORT_LENGTH = 547;
const STATE_REPORT_LENGTH = 142;

const audioReportBuffer = new Uint8Array(FULL_REPORT_LENGTH);
const stateReportBuffer = new Uint8Array(STATE_REPORT_LENGTH);
const resampleOutputBuffer = new Float32Array(SAMPLES_PER_OPUS_PACKET * 2);

let encoder = null;
let audioPort = null;
let hidDevice = null;
let inputState = null;

let stateReportReady = false;
let packetCounter = 0;
let sequenceCounter = 0;
let controls = {
  playerLight1: 0,
  playerLight2: 0,
  playerLight3: 0,
  playerLight4: 0,
  playerLight5: 0,
  playerLightFade: 1,  // player lights instantly change
};

let heartbeatInterval = 100;
let stateReportInterval = 0;
let lastStateReportTimestamp = null;
let lastAudioReportTimestamp = null;
let metrics = {
  inputsReceived: 0,
  audioReportsSent: 0,
  stateReportsSent: 0,
  pluggedUsbPower: false,
  pluggedHeadphones: false,
  batteryPercent: 100,
  batteryText: '100%',
  deltas: [],
  energy: [],
};

function getNextSequenceByte() {
  const seqByte = (sequenceCounter << 4) & 0xFF;
  sequenceCounter = (sequenceCounter + 1) & 0x0F;
  return seqByte;
}

// --- Sony DualSense CRC32 Implementation ---
const CRC32_TABLE = new Uint32Array(256);
for (let i = 0; i < 256; i++) {
  let c = i;
  for (let bit = 0; bit < 8; bit++) {
    c = (c & 1) ? (0xEDB88320 ^ (c >>> 1)) : (c >>> 1);
  }
  CRC32_TABLE[i] = c >>> 0;
}

function sonyCrc32(data) {
  let crc = ~0xEADA2D49 >>> 0;
  for (let i = 0; i < data.length; i++) {
    crc = (crc >>> 8) ^ CRC32_TABLE[(crc ^ data[i]) & 0xFF];
  }
  return (~crc) >>> 0;
}

function fillSonyCrc(report) {
  const crc = sonyCrc32(report.subarray(0, report.length - 4));
  const view = new DataView(report.buffer, report.byteOffset, report.byteLength);
  view.setUint32(report.length - 4, crc, true);
  return crc;
}

function resampleStereoLinear(input, inputFrames, output, outputFrames) {
  const step = inputFrames / outputFrames;
  for (let outputFrame = 0; outputFrame < outputFrames; outputFrame++) {
    const sourcePosition = outputFrame * step;
    const sourceFrame = Math.floor(sourcePosition);
    const fraction = sourcePosition - sourceFrame;
    const nextFrame = Math.min(sourceFrame + 1, inputFrames - 1);

    const sourceOffset = sourceFrame * 2;
    const nextOffset = nextFrame * 2;
    const outputOffset = outputFrame * 2;

    output[outputOffset] = input[sourceOffset] + (input[nextOffset] - input[sourceOffset]) * fraction;
    output[outputOffset + 1] = input[sourceOffset + 1] + (input[nextOffset + 1] - input[sourceOffset + 1]) * fraction;
  }
}

// --- HD Haptics Block Generation ---
function fillHapticBlocks(report, pcmFrame) {
  if (!controls.isHapticsEnabled || !pcmFrame) {
    report[10] = 0xD0;
    report[11] = 64;
    report.fill(0, 12, 74);
    report[74] = 0xD0;
    report[75] = 64;
    report.fill(0, 76, 138);
    return;
  }

  const totalInputFrames = pcmFrame.length / 2;
  const windowSize = SAMPLES_PER_OPUS_PACKET / 62;

  function populateBlock(blockHeaderOffset, dataHeaderOffset, startIndex) {
    report[blockHeaderOffset] = 0xD2;
    report[blockHeaderOffset + 1] = 64;

    let energy = 0;
    for (let i = 0; i < 31; i++) {
      const pairIndex = startIndex + i;
      const windowStart = Math.floor(pairIndex * windowSize);
      const windowEnd = Math.min(Math.floor((pairIndex + 1) * windowSize), totalInputFrames);

      let peakLeft = 0;
      let peakRight = 0;

      for (let f = windowStart; f < windowEnd; f++) {
        const lVal = pcmFrame[f * 2];
        const rVal = pcmFrame[f * 2 + 1];

        if (Math.abs(lVal) > Math.abs(peakLeft)) peakLeft = lVal;
        if (Math.abs(rVal) > Math.abs(peakRight)) peakRight = rVal;
      }

      const scale = 8 * (controls.currentHaptics / 100);
      peakLeft *= scale;
      peakRight *= scale;

      if (Math.abs(peakLeft) < 0.005) peakLeft = 0;
      if (Math.abs(peakRight) < 0.005) peakRight = 0;
      if (Math.abs(peakLeft) > 1.0) peakLeft = 1.0;
      if (Math.abs(peakRight) > 1.0) peakRight = 1.0;

      energy += peakLeft * peakLeft + peakRight * peakRight;
      report[dataHeaderOffset + i * 2] = Math.round(peakLeft * 127.0) & 0xFF;
      report[dataHeaderOffset + i * 2 + 1] = Math.round(peakRight * 127.0) & 0xFF;
    }
    return energy;
  }

  return populateBlock(10, 12, 0) + populateBlock(74, 76, 31);
}

function buildAudioReport(encodedA, encodedB, pcmFrame) {
  const report = audioReportBuffer;

  report[0] = AUDIO_REPORT_ID;
  report[1] = getNextSequenceByte();
  report[2] = 0x91;
  report[3] = 0x06;
  report[4] = 0x7E;

  report[5] = 64;
  report[6] = 64;
  report[7] = 64;
  report[8] = 64;

  packetCounter = (packetCounter + 2) & 0xFF;
  report[9] = packetCounter;

  const frameEnergy = fillHapticBlocks(report, pcmFrame);
  metrics.energy.push(frameEnergy);

  const audioPacketType = (controls.currentTarget === 'headset') ? 0x16 : 0x13;
  report[140] = audioPacketType | 0xC0;
  report[141] = encodedA.length;

  report.set(encodedA, 142);
  report.set(encodedB, 342);

  fillSonyCrc(report);
  return report;
}

function buildStateReport() {
  const report = stateReportBuffer;

  const energy = metrics.energy[metrics.energy.length - 1];
  let intensity = Math.min(1.0, energy / 10)
  intensity = Math.sqrt(intensity * intensity);
  const cold = {r: 30, g: 0, b: 30};
  const hot = {r: 30, g: 255, b: 30};
  let color = {
    r: Math.sqrt(0.5 * (hot.r * hot.r * intensity + cold.r * cold.r * (1 - intensity))),
    g: Math.sqrt(0.5 * (hot.g * hot.g * intensity + cold.g * cold.g * (1 - intensity))),
    b: Math.sqrt(0.5 * (hot.b * hot.b * intensity + cold.b * cold.b * (1 - intensity))),
  };

  let playerLight1 = 0;
  let playerLight2 = 0;
  let playerLight3 = 0;
  let playerLight4 = 0;
  let playerLight5 = 0;
  const playerLightFade = 0;
  let muteLight = 0;
  if (intensity > 0.9) {
    playerLight1 = 1;
    playerLight2 = 0;
    playerLight3 = 0;
    playerLight4 = 0;
    playerLight5 = 1;
  } else if (intensity > 0.7) {
    playerLight1 = 0;
    playerLight2 = 1;
    playerLight3 = 0;
    playerLight4 = 1;
    playerLight5 = 0;
  } else if (intensity > 0.3) {
    playerLight1 = 0;
    playerLight2 = 0;
    playerLight3 = 1;
    playerLight4 = 0;
    playerLight5 = 0;
  }
  if (intensity > 0.95) {
    muteLight = 1;
  }

  report[0] = 0x32;
  report[1] = getNextSequenceByte();
  report[2] = 0x90;
  report[3] = 0x3F;

  const state = 4;
  report[state + 0] = 0xF0;  // ~EnableRumbleEmulation
                             // ~UseRumbleNotHaptics
                             // ~AllowRightTriggerFFB
                             // ~AllowLeftTriggerFFB
                             // AllowHeadphoneVolume
                             // AllowSpeakerVolume
                             // AllowMicVolume
                             // AllowAudioControl
  report[state + 1] = 0xB7;  // AllowMuteLight
                             // AllowAudioMute
                             // AllowLedColor
                             // ~ResetLights
                             // AllowPlayerIndicators
                             // AllowHapticLowPassFilter
                             // ~AllowMotorPowerLevel
                             // AllowAudioControl2
  report[state + 4] = controls.currentVolume & 0x7F;  // VolumeHeadphones
  report[state + 5] = controls.currentVolume & 0x7F;  // VolumeSpeaker
  report[state + 6] = 0x00;  // VolumeMic
  report[state + 7] = (controls.currentTarget === 'headset') ? 0x20 : 0x00;  // OutputPathSelect
  report[state + 8] = (muteLight) ? 0x01 : 0x00;  // MuteLightMode
  report[state + 37] = 0x01;  // SpeakerCompPreGain
                              // ~BeamformingEnable
  report[state + 38] = 0x03;  // AllowLightBrightnessChange
                              // AllowColorLightFadeAnimation
                              // ~EnableImprovedRumbleEmulation
                              // ~UseRumbleNotHaptics2
  report[state + 39] = 0x01;  // HapticLowPassFilter
  report[state + 41] = 0x02;  // LightFadeAnimation
  report[state + 42] = 0x00;  // LightBrightness
  report[state + 43] = (playerLight1 << 0) || (playerLight2 << 1) || (playerLight3 << 2) || (playerLight4 << 3) || (playerLight5 << 4) || (playerLightFade << 5);
  report[state + 44] = Math.round(color.r) & 0xFF;
  report[state + 45] = Math.round(color.g) & 0xFF;
  report[state + 46] = Math.round(color.b) & 0xFF;

  fillSonyCrc(report);
  stateReportReady = true;
  lastStateReportTimestamp = Date.now();
}

function onInputReport(event) {
  const {reportId, data} = event;
  if (reportId === INPUT_REPORT_ID) {
    ++metrics.inputsReceived;
    const byte0 = data.getUint8(0);
    const hasHid = (byte0 >> 0) & 0x01;
    const hasMic = (byte0 >> 1) & 0x01;
    const seqNo = (byte0 >> 4) & 0x0F;
    const leftStickX = data.getUint8(1);
    const leftStickY = data.getUint8(2);
    const rightStickX = data.getUint8(3);
    const rightStickY = data.getUint8(4);
    const triggerLeft = data.getUint8(5);
    const triggerRight = data.getUint8(6);

    const byte8 = data.getUint8(8);
    const dpad = (byte8 >> 0) & 0x0F;
    const buttonSquare = (byte8 >> 4) & 0x01;
    const buttonCross = (byte8 >> 5) & 0x01;
    const buttonCircle = (byte8 >> 6) & 0x01;
    const buttonTriangle = (byte8 >> 7) & 0x01;

    const byte9 = data.getUint8(9);
    const buttonL1 = (byte9 >> 0) & 0x01;
    const buttonR1 = (byte9 >> 1) & 0x01;
    const buttonL2 = (byte9 >> 2) & 0x01;
    const buttonR2 = (byte9 >> 3) & 0x01;
    const buttonCreate = (byte9 >> 4) & 0x01;
    const buttonOptions = (byte9 >> 5) & 0x01;
    const buttonL3 = (byte9 >> 6) & 0x01;
    const buttonR3 = (byte9 >> 7) & 0x01;

    const byte10 = data.getUint8(10);
    const buttonHome = (byte10 >> 0) & 0x01;
    const buttonPad = (byte10 >> 1) & 0x01;
    const buttonMute = (byte10 >> 2) & 0x01;
    const buttonLeftFunction = (byte10 >> 4) & 0x01;
    const buttonRightFunction = (byte10 >> 5) & 0x01;
    const buttonLeftPaddle = (byte10 >> 6) & 0x01;
    const buttonRightPaddle = (byte10 >> 7) & 0x01;

    const byte53 = data.getUint8(53);
    const powerPercent = (byte53 >> 0) & 0x0F;
    const powerState = (byte53 >> 4) & 0x0F;

    const byte54 = data.getUint8(54);
    const pluggedHeadphones = (byte54 >> 0) & 0x01;
    const pluggedMic = (byte54 >> 1) & 0x01;
    const micMuted = (byte54 >> 2) & 0x01;
    const pluggedUsbData = (byte54 >> 3) & 0x01;
    const pluggedUsbPower = (byte54 >> 3) & 0x01;
    const usbPowerOnBt = (byte54 >> 4) & 0x01;

    let batteryPercent = 0;
    if (powerState == 2) {
      batteryPercent = 100;
    } else if (powerState == 0 || powerState == 1) {
      batteryPercent = 10 * powerPercent;
    }
    const batteryFull = (powerState == 2);
    const batteryAbnormalVoltage = (powerState == 10);
    const batteryAbnormalTemperature = (powerState == 11);
    const chargingError = (powerState == 15);

    const dpadUp = (dpad == 0 || dpad == 1 || dpad == 7);
    const dpadRight = (dpad == 1 || dpad == 2 || dpad == 3);
    const dpadDown = (dpad == 3 || dpad == 4 || dpad == 5);
    const dpadLeft = (dpad == 5 || dpad == 6 || dpad == 7);

    const axes = { leftStickX, leftStickY, rightStickX, rightStickY, triggerLeft, triggerRight };
    const buttons = { dpadUp, dpadRight, dpadDown, dpadLeft, buttonSquare, buttonCross, buttonCircle, buttonTriangle, buttonL1, buttonR1, buttonL2, buttonR2, buttonCreate, buttonOptions, buttonL3, buttonR3, buttonHome, buttonPad, buttonMute, buttonLeftFunction, buttonRightFunction, buttonLeftPaddle, buttonRightPaddle };
    const power = { powerState, batteryPercent, batteryFull, batteryAbnormalVoltage, batteryAbnormalTemperature, chargingError, usbPowerOnBt };
    const plugged = { pluggedHeadphones, pluggedMic, pluggedUsbData, pluggedUsbPower };
    const mic = { hasMic, micMuted };

    const oldState = inputState;
    const buttonsDown = [];
    const buttonsUp = [];
    const buttonsPressed = [];
    for (const key of Object.keys(buttons)) {
      const down = (!oldState || !oldState.buttons[key]) && buttons[key];
      const up = oldState && oldState.buttons[key] && !buttons[key];
      if (buttons[key]) {
        buttonsPressed.push(key);
      }
      if (down) {
        buttonsDown.push(key);
        self.postMessage({ status: 'keydown', key });
      } else if (up) {
        buttonsUp.push(key);
        self.postMessage({ status: 'keyup', key });
      }
    }

    inputState = { hasHid, seqNo, axes, buttons, buttonsDown, buttonsUp, buttonsPressed, power, plugged, mic };
    metrics.pluggedUsbPower = pluggedUsbPower;
    metrics.pluggedHeadphones = pluggedHeadphones;
    metrics.batteryPercent = batteryPercent;
    metrics.batteryText = `${batteryPercent}%${powerState === 1 ? '🔌' : ''}${powerState === 2 ? ' (full)' : ''}`;
    if (!oldState || oldState.plugged.pluggedHeadphones != pluggedHeadphones) {
      controls.currentTarget = pluggedHeadphones ? 'headset' : 'speaker';
      const plugged = pluggedHeadphones;
      self.postMessage({ status: 'headset', plugged });
    }
  }
}

// Unified message router
self.onmessage = async (e) => {
  const { action } = e.data;

  // init-opus - Called at startup. Initializes the Opus encoder.
  if (action === 'init-opus') {
    const { config } = e.data;
    try {
      encoder = await createEncoder(config);
      self.postMessage({ status: 'ready' });
    } catch (err) {
      self.postMessage({ status: 'error', message: err.message });
    }
    return;
  }

  // init-hid - Called at various times to initiate a new device connection.
  // The page ensures there is exactly one connected device to signal which
  // device to use. Does nothing if there is not exactly one connected device.
  //
  // * Called at startup if there is a granted permission and the device is
  //   already connected.
  // * Called after worker initialization if there exactly one opened device.
  // * Called after completing the requestDevice flow.
  if (action === 'init-hid') {
    const devices = await navigator.hid.getDevices();
    if (devices.length !== 1) {
      return;
    }
    const device = devices[0];
    if (!device.opened) {
      await device.open();
    }
    if (hidDevice) {
      hidDevice.removeEventListener('inputreport', onInputReport);
    }
    hidDevice = device;
    hidDevice.addEventListener('inputreport', onInputReport);
    return;
  }

  // init-audio-port - Called after initializing both the audio worklet and the
  // worker to establish a message pipe between the two. Initializes control
  // parameters from the current UI control state.
  if (action === 'init-audio-port') {
    controls = e.data.controls;
    audioPort = e.data.port;

    let lastHeartbeat = null;

    // Called with PCM audio data once the audio worklet has collected 1024 new
    // samples. Resamples to 45kHz, encodes the Opus frames, generates haptic
    // waveforms, builds the audio report and sends it to the device.
    audioPort.onmessage = async (event) => {
      if (!encoder || !hidDevice || !hidDevice.opened) return;

      const { pcm } = event.data;

      try {
        resampleStereoLinear(pcm, 1024, resampleOutputBuffer, SAMPLES_PER_OPUS_PACKET);

        const frameA = resampleOutputBuffer.subarray(0, SAMPLES_PER_OPUS_PACKET);
        const frameB = resampleOutputBuffer.subarray(SAMPLES_PER_OPUS_PACKET, SAMPLES_PER_OPUS_PACKET * 2);

        const encodedA = encoder.encodeFloat(frameA);
        const encodedB = encoder.encodeFloat(frameB);

        const report = buildAudioReport(encodedA, encodedB, resampleOutputBuffer);

        // Send the audio report
        const now = Date.now();
        await hidDevice.sendReport(report[0], report.slice(1));
        if (lastAudioReportTimestamp) {
          metrics.deltas.push(now - lastAudioReportTimestamp);
        }
        lastAudioReportTimestamp = now;
        ++metrics.audioReportsSent;
        if (!stateReportReady && now - lastStateReportTimestamp > stateReportInterval) {
          buildStateReport();
        }

        // Send the state report
        if (stateReportReady) {
          await hidDevice.sendReport(stateReportBuffer[0], stateReportBuffer.slice(1));
          stateReportReady = false;
          ++metrics.stateReportsSent;
        }

        // Report metrics back to the page
        if (!lastHeartbeat || now - lastHeartbeat > heartbeatInterval) {
          const message = `Reports I:${metrics.inputsReceived} A:${metrics.audioReportsSent} S:${metrics.stateReportsSent} | Volume: ${controls.currentVolume}% (${controls.currentTarget}) | Haptics: ${controls.currentHaptics}% | Battery: ${inputState.power.batteryPercent}%${inputState.power.powerState === 1 ? ' (charging)' : ''}${inputState.power.powerState === 2 ? ' (full)' : ''}`;
          self.postMessage({ status: 'heartbeat', message, metrics });
          lastHeartbeat = now;
          metrics.deltas = [];
          metrics.energy = [];
        }
      } catch (err) {
        console.log(err);
      }
    };
    return;
  }

  // send-state-report - Called after changing control parameters.
  // Sends a state report to the device.
  if (action === 'send-state-report') {
    if (!hidDevice || !hidDevice.opened) {
      return;
    }
    controls = e.data.controls;
    buildStateReport();
    return;
  }
};
