import { createEncoder } from "./libopus/index.js";

const VENDOR_SONY = 0x054C;
const PRODUCT_SONY_DUALSENSE = 0x0CE6;
const STATE_REPORT_ID = 0x32;
const AUDIO_REPORT_ID = 0x39;
const CHANNELS = 2;
const FRAMES_PER_OPUS_PACKET = 480;
const SAMPLES_PER_OPUS_PACKET = FRAMES_PER_OPUS_PACKET * CHANNELS;
const FULL_REPORT_LENGTH = 547;
const STATE_REPORT_LENGTH = 142;

const resampleOutputBuffer = new Float32Array(SAMPLES_PER_OPUS_PACKET * 2);

let encoder = null;
let audioPort = null;
let hidDevice = null;
let inputState = null;

let packetCounter = 0;
let sequenceCounter = 0;
let controls = {};
let color = null;

let metrics = {
  inputsReceived: 0,
  stateReportsSent: 0,
  currentEnergy: 0,
};

function isDualSenseBluetooth(device) {
  return device.vendorId === VENDOR_SONY &&
      device.productId === PRODUCT_SONY_DUALSENSE &&
      device.collections.length === 1 &&
      device.collections[0].outputReports.some((r) => r.reportId == STATE_REPORT_ID) &&
      device.collections[0].outputReports.some((r) => r.reportId == AUDIO_REPORT_ID);
}

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
  }

  let energy = 0;

  // Block 1: pairs 0 to 30
  energy += populateBlock(10, 12, 0);

  // Block 2: pairs 31 to 61
  energy += populateBlock(74, 76, 31);

  return energy;
}

function buildAudioReport(encodedA, encodedB, pcmFrame, bufferLength) {
  const report = new Uint8Array(FULL_REPORT_LENGTH);

  report[0] = AUDIO_REPORT_ID;
  report[1] = getNextSequenceByte();
  report[2] = 0x91;
  report[3] = 0x06;
  report[4] = 0x7E;

  const bufByte = bufferLength & 0xFF;
  report[5] = bufByte;
  report[6] = bufByte;
  report[7] = bufByte;
  report[8] = bufByte;

  packetCounter = (packetCounter + 2) & 0xFF;
  report[9] = packetCounter;

  metrics.currentEnergy += fillHapticBlocks(report, pcmFrame);

  const audioPacketType = (controls.currentTarget === 'headset') ? 0x16 : 0x13;
  report[140] = audioPacketType | 0xC0;
  report[141] = encodedA.length;

  report.set(encodedA, 142);
  report.set(encodedB, 342);

  fillSonyCrc(report);
  return report;
}

function buildStateReport() {
  const report = new Uint8Array(STATE_REPORT_LENGTH);
  
  report[0] = 0x32;
  report[1] = getNextSequenceByte();
  report[2] = 0x90;
  report[3] = 0x3F;

  const state = 4;
  report[state + 0] = 0xB0;
  report[state + 1] = 0xB6;
  report[state + 4] = controls.currentVolume & 0x7F;
  report[state + 5] = controls.currentVolume & 0x7F;
  report[state + 6] = 0x40;
  report[state + 7] = (controls.currentTarget === 'headset') ? 0x20 : 0x00;
  report[state + 37] = 0x03;
  report[state + 38] = 0x02;
  report[state + 39] = 0x01;
  report[state + 41] = 0x02;
  report[state + 43] = 0x04;
  report[state + 44] = controls.r & 0xFF;
  report[state + 45] = controls.g & 0xFF;
  report[state + 46] = controls.b & 0xFF;

  fillSonyCrc(report);
  return report;
}

function onInputReport(reportId, data) {
  if (reportId === 0x31) {
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

    const oldState = inputState;
    inputState = { hasHid, hasMic, seqNo, leftStickX, leftStickY, rightStickX, rightStickY, triggerLeft, triggerRight, dpad, buttonSquare, buttonCross, buttonCircle, buttonTriangle, buttonL1, buttonR1, buttonL2, buttonR2, buttonCreate, buttonOptions, buttonL3, buttonR3, buttonHome, buttonPad, buttonMute, buttonLeftFunction, buttonRightFunction, buttonLeftPaddle, buttonRightPaddle, powerPercent, powerState, pluggedHeadphones, pluggedMic, micMuted, pluggedUsbData, pluggedUsbPower, usbPowerOnBt, batteryPercent, batteryFull, batteryAbnormalVoltage, batteryAbnormalTemperature, chargingError };
    if (!oldState || oldState.pluggedHeadphones != pluggedHeadphones) {
      controls.currentTarget = pluggedHeadphones ? 'headset' : 'speaker';
      const plugged = pluggedHeadphones;
      self.postMessage({ status: 'headset', plugged });
    }

    ++metrics.inputsReceived;
  }
}

// Unified message router
self.onmessage = async (e) => {
  const { action } = e.data;
  if (action === 'init') {
    const { config } = e.data;
    try {
      encoder = await createEncoder(config);
      self.postMessage({ status: 'ready' });
    } catch (err) {
      self.postMessage({ status: 'error', message: err.message });
    }
    return;
  }

  if (action === 'initHid') {
    let devices = await navigator.hid.getDevices();
    devices = devices.filter(isDualSenseBluetooth);
    
    if (devices.length === 0) {
      self.postMessage({ status: 'error', message: 'No permitted DualSense devices found in worker.' });
      return;
    }

    hidDevice = devices.find(d => d.opened) || devices[0];
    if (!hidDevice.opened) {
      await hidDevice.open();
    }
    if (!hidDevice.opened) {
      hidDevice = null;
      self.postMessage({ status: 'error', message: 'Failed to open device.' });
      return;
    }

    hidDevice.addEventListener('inputreport', (e) => onInputReport(e.reportId, e.data));

    self.postMessage({ status: 'hid-ready' });
    return;
  }

  if (action === 'init-audio-port') {
    controls = e.data.controls;
    audioPort = e.data.port;
    audioPort.onmessage = async (event) => {
      if (!encoder || !hidDevice || !hidDevice.opened) return;

      const { pcm } = event.data;

      try {
        resampleStereoLinear(pcm, 1024, resampleOutputBuffer, SAMPLES_PER_OPUS_PACKET);

        const frameA = resampleOutputBuffer.subarray(0, SAMPLES_PER_OPUS_PACKET);
        const frameB = resampleOutputBuffer.subarray(SAMPLES_PER_OPUS_PACKET, SAMPLES_PER_OPUS_PACKET * 2);

        const encodedA = encoder.encodeFloat(frameA);
        const encodedB = encoder.encodeFloat(frameB);

        const report = buildAudioReport(encodedA, encodedB, resampleOutputBuffer, 64);

        await hidDevice.sendReport(report[0], report.slice(1));

        // Optional: send lightweight timing/jitter telemetry back to main thread for UI
        const now = performance.now();
        self.postMessage({ status: 'metrics', timestamp: now, metrics });
        metrics.currentEnergy = 0;
      } catch (err) {
        console.log(err);
      }
    };
    return;
  }

  if (action === 'sendStateReport') {
    if (!hidDevice || !hidDevice.opened) {
      return;
    }
    controls = e.data.controls;
    color = e.data.color;
    try {
      const report = buildStateReport();
      await hidDevice.sendReport(report[0], report.slice(1));
      ++metrics.stateReportsSent;
    } catch (err) {
      console.log(err);
    }
    return;
  }
};
