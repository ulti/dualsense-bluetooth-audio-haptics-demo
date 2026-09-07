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
const audioReportPayload = audioReportBuffer.subarray(1);
const stateReportPayload = stateReportBuffer.subarray(1);
const resampleOutputBuffer = new Float32Array(SAMPLES_PER_OPUS_PACKET * 2);
const frameA = resampleOutputBuffer.subarray(0, SAMPLES_PER_OPUS_PACKET);
const frameB = resampleOutputBuffer.subarray(SAMPLES_PER_OPUS_PACKET, SAMPLES_PER_OPUS_PACKET * 2);

// --- Ring Buffer for Timing Jitter Elimination ---
const RING_CAPACITY = 8;
const ringBuffers = Array.from({ length: RING_CAPACITY }, () => new Uint8Array(FULL_REPORT_LENGTH));
const ringPayloads = ringBuffers.map(b => b.subarray(1));
let ringWriteIndex = 0;
let ringReadIndex = 0;
let ringCount = 0;

let isAudioLoopRunning = false;
let audioTimerHandle = null;
let nextAudioSendTime = 0;
let lastHeartbeatTimestamp = null;
const AUDIO_INTERVAL_MS = 21.333333;

let encoder = null;
let encoderReady = false;
let audioPort = null;
let hidDevice = null;
let inputState = null;

let stateReportReady = false;
let packetCounter = 0;
let sequenceCounter = 0;
let controls = {};

let heartbeatInterval = 1000 / 30;  // 30 Hz
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

function fillSonyCrc(report) {
  const dataLen = report.length - 4;
  let crc = ~0xEADA2D49 >>> 0;
  for (let i = 0; i < dataLen; i++) {
    crc = (crc >>> 8) ^ CRC32_TABLE[(crc ^ report[i]) & 0xFF];
  }
  crc = (~crc) >>> 0;
  report[dataLen] = crc & 0xFF;
  report[dataLen + 1] = (crc >>> 8) & 0xFF;
  report[dataLen + 2] = (crc >>> 16) & 0xFF;
  report[dataLen + 3] = (crc >>> 24) & 0xFF;
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
  if (!pcmFrame) {
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
    if (controls.isHapticsEnabled) {
      report[blockHeaderOffset] = 0xD2;
    } else {
      report[blockHeaderOffset] = 0xD0;
    }
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
      if (controls.isHapticsEnabled) {
        report[dataHeaderOffset + i * 2] = Math.round(peakLeft * 127.0) & 0xFF;
        report[dataHeaderOffset + i * 2 + 1] = Math.round(peakRight * 127.0) & 0xFF;
      } else {
        report[dataHeaderOffset + i * 2] = 0x00;
        report[dataHeaderOffset + i * 2 + 1] = 0x00;
      }
    }
    if (energy < 0.0001) {
      report[10] = 0xD0;
      report[11] = 64;
      report.fill(0, 12, 74);
      report[74] = 0xD0;
      report[75] = 64;
      report.fill(0, 76, 138);
    }
    return energy;
  }

  return populateBlock(10, 12, 0) + populateBlock(74, 76, 31);
}

function buildAudioReportIntoSlot(slotIndex, encodedA, encodedB, pcmFrame) {
  const report = ringBuffers[slotIndex];

  report[0] = AUDIO_REPORT_ID;
  report[2] = 0x91;
  report[3] = 0x06;
  report[4] = 0x7E;

  report[5] = 64;
  report[6] = 64;
  report[7] = 64;
  report[8] = 64;

  const frameEnergy = fillHapticBlocks(report, pcmFrame);
  metrics.energy.push(frameEnergy);

  const audioPacketType = (controls.currentTarget === 'headset') ? 0x16 : 0x13;
  report[140] = audioPacketType | 0xC0;
  report[141] = encodedA.length;

  report.set(encodedA, 142);
  report.set(encodedB, 342);
}

function startAudioSendLoop() {
  if (isAudioLoopRunning) return;
  isAudioLoopRunning = true;
  nextAudioSendTime = performance.now();
  scheduleAudioSendTick();
}

function stopAudioSendLoop() {
  isAudioLoopRunning = false;
  if (audioTimerHandle !== null) {
    clearTimeout(audioTimerHandle);
    audioTimerHandle = null;
  }
  ringCount = 0;
  ringReadIndex = 0;
  ringWriteIndex = 0;
  lastAudioReportTimestamp = null;
}

function scheduleAudioSendTick() {
  if (!isAudioLoopRunning) return;
  nextAudioSendTime += AUDIO_INTERVAL_MS;
  const now = performance.now();
  const delay = Math.max(0, nextAudioSendTime - now);
  audioTimerHandle = setTimeout(sendAudioReportTick, delay);
}

async function sendAudioReportTick() {
  if (!isAudioLoopRunning) return;

  if (hidDevice && hidDevice.opened && ringCount > 0) {
    const slot = ringReadIndex;
    ringReadIndex = (ringReadIndex + 1) % RING_CAPACITY;
    ringCount--;

    const report = ringBuffers[slot];
    const payload = ringPayloads[slot];

    // Stamp sequence, packet counter, and CRC directly before sending
    report[1] = getNextSequenceByte();
    packetCounter = (packetCounter + 2) & 0xFF;
    report[9] = packetCounter;
    fillSonyCrc(report);

    const now = performance.now();
    try {
      await hidDevice.sendReport(AUDIO_REPORT_ID, payload);
      if (lastAudioReportTimestamp) {
        metrics.deltas.push(now - lastAudioReportTimestamp);
      }
      lastAudioReportTimestamp = now;
      ++metrics.audioReportsSent;
    } catch (err) {
      console.log('Send audio report error:', err);
    }
  }

  // Interleaved State Report (Lights / Volume) - Decoupled and throttled
  const now = Date.now();
  if (!stateReportReady && now - lastStateReportTimestamp > controls.currentLightsInterval) {
    buildStateReport();
  }

  if (stateReportReady && hidDevice && hidDevice.opened) {
    try {
      await hidDevice.sendReport(STATE_REPORT_ID, stateReportPayload);
      stateReportReady = false;
      ++metrics.stateReportsSent;
    } catch (err) {
      console.log('Send state report error:', err);
    }
  }

  // Periodic Heartbeat to Main UI
  if (!lastHeartbeatTimestamp || now - lastHeartbeatTimestamp > heartbeatInterval) {
    self.postMessage({ status: 'heartbeat', metrics });
    lastHeartbeatTimestamp = now;
    metrics.deltas = [];
    metrics.energy = [];
  }

  scheduleAudioSendTick();
}

function buildStateReport() {
  const report = stateReportBuffer;

  const energy = metrics.energy[metrics.energy.length - 1] || 0;
  let intensity = Math.min(1.0, energy / 10);
  let coldR = 30, coldG = 0, coldB = 30;
  let hotR = 30, hotG = 255, hotB = 30;
  if (inputState && inputState.power && inputState.power.batteryPercent <= 10 && inputState.power.powerState != 1) {
    coldR = 30; coldG = 0; coldB = 0;
    hotR = 255; hotG = 0; hotB = 0;
  }
  let colorR = 0, colorG = 0, colorB = 0;

  let playerLight1 = 0;
  let playerLight2 = 0;
  let playerLight3 = 0;
  let playerLight4 = 0;
  let playerLight5 = 0;
  const playerLightFade = 1;
  let muteLight = 0;
  if (controls.isLightsEnabled) {
    colorR = Math.sqrt(0.5 * (hotR * hotR * intensity + coldR * coldR * (1 - intensity)));
    colorG = Math.sqrt(0.5 * (hotG * hotG * intensity + coldG * coldG * (1 - intensity)));
    colorB = Math.sqrt(0.5 * (hotB * hotB * intensity + coldB * coldB * (1 - intensity)));
    if (intensity > 0.9) {
      playerLight1 = 1;
      playerLight2 = 0;
      playerLight3 = 0;
      playerLight4 = 0;
      playerLight5 = 1;
    } else if (intensity > 0.8) {
      playerLight1 = 1;
      playerLight2 = 1;
      playerLight3 = 0;
      playerLight4 = 1;
      playerLight5 = 1;
    } else if (intensity > 0.7) {
      playerLight1 = 0;
      playerLight2 = 1;
      playerLight3 = 0;
      playerLight4 = 1;
      playerLight5 = 0;
    } else if (intensity > 0.6) {
      playerLight1 = 0;
      playerLight2 = 1;
      playerLight3 = 1;
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
  report[state + 43] = (playerLight1 << 0) | (playerLight2 << 1) | (playerLight3 << 2) | (playerLight4 << 3) | (playerLight5 << 4) | (playerLightFade << 5);
  report[state + 44] = Math.round(colorR) & 0xFF;
  report[state + 45] = Math.round(colorG) & 0xFF;
  report[state + 46] = Math.round(colorB) & 0xFF;

  fillSonyCrc(report);
  stateReportReady = true;
  lastStateReportTimestamp = Date.now();
}

function onInputReport(event) {
  if (!encoderReady) {
    return;
  }

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

    const dpadUp = (dpad == 0 || dpad == 1 || dpad == 7);
    const dpadRight = (dpad == 1 || dpad == 2 || dpad == 3);
    const dpadDown = (dpad == 3 || dpad == 4 || dpad == 5);
    const dpadLeft = (dpad == 5 || dpad == 6 || dpad == 7);

    let batteryPercent = 0;
    if (powerState == 2) {
      batteryPercent = 100;
    } else if (powerState == 0 || powerState == 1) {
      batteryPercent = 10 * powerPercent + 5;
    }

    const axes = { leftStickX, leftStickY, rightStickX, rightStickY, triggerLeft, triggerRight };
    const buttons = { dpadUp, dpadRight, dpadDown, dpadLeft, buttonSquare, buttonCross, buttonCircle, buttonTriangle, buttonL1, buttonR1, buttonL2, buttonR2, buttonCreate, buttonOptions, buttonL3, buttonR3, buttonHome, buttonPad, buttonMute, buttonLeftFunction, buttonRightFunction, buttonLeftPaddle, buttonRightPaddle };
    const power = { powerState, powerPercent, usbPowerOnBt, batteryPercent };
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
    if (!oldState || oldState.power.powerPercent != powerPercent || oldState.power.powerState != powerState) {
      console.log('power', power);
      const percent = batteryPercent;
      const charging = (powerState == 1);
      const full = (powerState == 2);
      const abnormalVoltage = (powerState == 10);
      const abnormalTemperature = (powerState == 11);
      const error = (powerState == 15);
      const batteryText = `${percent}%${charging ? '🔌' : ''}${full ? ' (full)' : ''}`;
      const plugged = controls.pluggedUsbPower || controls.pluggedUsbData;
      self.postMessage({ status: 'power', batteryText, percent, plugged, charging, full, error, abnormalVoltage, abnormalTemperature });
    }
    metrics.pluggedUsbPower = pluggedUsbPower;
    metrics.pluggedHeadphones = pluggedHeadphones;
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
      encoderReady = true;
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

        const encodedA = encoder.encodeFloat(frameA);
        const encodedB = encoder.encodeFloat(frameB);

        // Enqueue into ring buffer
        if (ringCount < RING_CAPACITY) {
          buildAudioReportIntoSlot(ringWriteIndex, encodedA, encodedB, resampleOutputBuffer);
          ringWriteIndex = (ringWriteIndex + 1) % RING_CAPACITY;
          ringCount++;
        } else {
          // If queue is full (overrun), overwrite oldest slot to prevent latency buildup
          buildAudioReportIntoSlot(ringWriteIndex, encodedA, encodedB, resampleOutputBuffer);
          ringWriteIndex = (ringWriteIndex + 1) % RING_CAPACITY;
          ringReadIndex = (ringReadIndex + 1) % RING_CAPACITY;
        }

        // Start send loop once buffer is primed (at least 2 packets)
        if (!isAudioLoopRunning && ringCount >= 2) {
          startAudioSendLoop();
        }

        // Recycle the incoming PCM buffer back to the AudioWorklet pool
        if (pcm && pcm.buffer) {
          audioPort.postMessage({ action: 'recycle-buffer', buffer: pcm.buffer }, [pcm.buffer]);
        }
      } catch (err) {
        console.log(err);
      }
    };
    return;
  }

  // stop-audio-stream - Called when playback is stopped.
  if (action === 'stop-audio-stream') {
    stopAudioSendLoop();
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
