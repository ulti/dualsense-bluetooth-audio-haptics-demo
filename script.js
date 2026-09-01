// --- AudioWorklet Processor Source ---
const audioWorkletCode = `
  class DualSenseAudioProcessor extends AudioWorkletProcessor {
    constructor(options) {
      super();
      this.samplesAccumulated = 0;
      this.bufferL = new Float32Array(1024);
      this.bufferR = new Float32Array(1024);
      this.active = true;

      this.customPcm = null;
      this.customIndex = 0;

      this.workerPort = null;

      this.port.onmessage = (e) => {
        if (e.data.action === 'setCustomAudio') {
          this.customPcm = e.data.pcm; // Interleaved Float32Array
          this.customIndex = 0;
        } else if (e.data.action === 'stop') {
          this.active = false;
        } else if (e.data.action === 'set-audio-port') {
          this.workerPort = e.data.port;
        }
      };
    }

    process(inputs, outputs, parameters) {
      if (!this.active) return false;

      for (let i = 0; i < 128; i++) {
        let sampleL = 0;
        let sampleR = 0;

        if (this.customPcm && this.customIndex < this.customPcm.length) {
          sampleL = this.customPcm[this.customIndex] * 0.1;       // Left
          sampleR = this.customPcm[this.customIndex + 1] * 0.1;   // Right
          this.customIndex += 2;
          // Loop back to start if end of track reached
          if (this.customIndex >= this.customPcm.length) {
            this.customIndex = 0;
          }
        }

        this.bufferL[this.samplesAccumulated] = sampleL;
        this.bufferR[this.samplesAccumulated] = sampleR;
        this.samplesAccumulated++;

        if (this.samplesAccumulated === 1024) {
          const frames = this.samplesAccumulated;
          const pcm = new Float32Array(frames * 2);
          for (let s = 0; s < frames; s++) {
            pcm[s * 2] = this.bufferL[s];
            pcm[s * 2 + 1] = this.bufferR[s];
          }
          if (this.workerPort) {
            this.workerPort.postMessage({type: 'audio-chunk', pcm, frames}, [pcm.buffer]);
          }
          this.samplesAccumulated = 0;
        }
      }
      return true;
    }
  }
  registerProcessor('dualsense-audio-processor', DualSenseAudioProcessor);
`;

// --- Protocol Constants & State ---
const VENDOR_SONY = 0x054C;
const PRODUCT_SONY_DUALSENSE = 0x0CE6;
const SAMPLE_RATE = 48000;
const CHANNELS = 2;
const FRAMES_PER_OPUS_PACKET = 480;
const SAMPLES_PER_OPUS_PACKET = FRAMES_PER_OPUS_PACKET * CHANNELS;
const OPUS_PACKET_BYTES = 200;
const FULL_REPORT_LENGTH = 547;
const STATE_REPORT_LENGTH = 142;
const STATE_REPORT_ID = 0x32;
const AUDIO_REPORT_ID = 0x39;

const DEFAULT_AUDIO_FILE = 'Not Footprints ehhhh (take 006) S80.mp3';
const HEARTBEAT_COLORS = [
  { name: "Vivid Red", hex: "#FF0000", r: 255, g: 0, b: 0 },
  { name: "Neon Green", hex: "#00FF00", r: 0, g: 255, b: 0 },
  { name: "Deep Blue", hex: "#0000FF", r: 0, g: 0, b: 255 },
  { name: "Bright Cyan", hex: "#00FFFF", r: 0, g: 255, b: 255 },
  { name: "Magenta", hex: "#FF00FF", r: 255, g: 0, b: 255 },
  { name: "Electric Yellow", hex: "#FFFF00", r: 255, g: 255, b: 0 },
  { name: "Vibrant Orange", hex: "#FF7700", r: 255, g: 119, b: 0 },
  { name: "Pure White", hex: "#FFFFFF", r: 255, g: 255, b: 255 }
];

let encoder = true;
let audioContext = null;
let workletNode = null;
let worker = null;
let isWorkletModuleLoaded = false;
let hidDevice = null;

// Decoded audio data
let audioData = null;

// Heartbeat LED
let heartbeatTimer = null;
let currentColorIndex = 0;

// UI controls (per-device)
let controls = {
  isAudioStreaming: false,
  isSoundEnabled: true,
  isHapticsEnabled: true,
  currentVolume: 100,
  currentHaptics: 100,
  currentTarget: 'speaker',
  currentEnergy: 0,
};

// Protocol state (per-device)
let protocol = {
  sequenceCounter: 0,
  packetCounter: 0,
};

// Metrics (per-device)
let metrics = {
  lastSendTimestamp: 0,
  intervalHistory: [],
  inputsReceived: 0,
  audioReportsSent: 0,
  stateReportsSent: 0,
};

const fullReportBuffer = new Uint8Array(FULL_REPORT_LENGTH);
const resampleOutputBuffer = new Float32Array(SAMPLES_PER_OPUS_PACKET * 2);

// --- DOM Elements ---
const connectBtn = document.getElementById("connect-btn");
const disconnectBtn = document.getElementById("disconnect-btn");
const connectionStatus = document.getElementById("connection-status");
const statusText = document.getElementById("status-text");
const encoderStatus = document.getElementById("encoder-status");
const toggleAudioBtn = document.getElementById("toggle-audio-btn");
const volumeSlider = document.getElementById("volume-slider");
const volumeVal = document.getElementById("volume-val");
const audioTargetSelect = document.getElementById("audio-target-select");
const toggleSoundBtn = document.getElementById("toggle-sound-btn");
const toggleHapticBtn = document.getElementById("toggle-haptic-btn");
const hapticAmpSlider = document.getElementById("haptic-amp-slider");
const hapticAmpVal = document.getElementById("haptic-amp-val");
//const metricInputsReceived = document.getElementById("metric-inputs-received");
//const metricAudioSent = document.getElementById("metric-audio-sent");
//const metricStateSent = document.getElementById("metric-state-sent");
//const metricInterval = document.getElementById("metric-interval");
//const colorPreview = document.getElementById("current-color-preview");
//const colorNameText = document.getElementById("color-name-text");
const consoleLog = document.getElementById("console-log");
const clearLogBtn = document.getElementById("clear-log-btn");
const audioFileInput = document.getElementById("audio-file-input");
const jitterCanvas = document.getElementById("jitter-canvas");
const jitterStats = document.getElementById("jitter-stats");

function log(msg) {
  consoleLog.value += `${msg}\n`;
  consoleLog.scrollTop = consoleLog.scrollHeight;
}

function hex16(v) { return ('0000' + v.toString(16)).substr(-4); }

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
  let crc = ~0xEADA2D49 >>> 0; // 0x1525D2B6
  for (let i = 0; i < data.length; i++) {
    crc = (crc >>> 8) ^ CRC32_TABLE[(crc ^ data[i]) & 0xFF];
  }
  return (~crc) >>> 0;
}

function fillSonyCrc(report) {
  const crc = sonyCrc32(report.subarray(0, report.length - 4));
  const view = new DataView(report.buffer, report.byteOffset, report.byteLength);
  view.setUint32(report.length - 4, crc, true); // Little-endian
  return crc;
}

// --- Resample Stereo Linear (1024 frames -> 960 frames) ---
function resampleStereoLinear(input, inputFrames, output, outputFrames) {
  const step = inputFrames / outputFrames; // 1024 / 960 = 1.06666667
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

// Extract interleaved channel data from the rendered AudioBuffer
function createInterleaved(buffer) {
  const chanL = buffer.getChannelData(0);
  const chanR = buffer.numberOfChannels > 1 ? buffer.getChannelData(1) : chanL;
  const interleaved = new Float32Array(chanL.length * 2);
  for (let i = 0; i < chanL.length; i++) {
    interleaved[i * 2] = chanL[i];
    interleaved[i * 2 + 1] = chanR[i];
  }
  return interleaved;
}

async function loadAudioFromBuffer(buffer) {
  // Ensure an AudioContext exists for decoding
  if (!audioContext || audioContext.state === 'closed') {
    audioContext = new AudioContext({ sampleRate: SAMPLE_RATE });
  }

  const decodedAudio = await audioContext.decodeAudioData(buffer);

  // OfflineAudioContext to force resampling to exactly 48kHz stereo
  const offlineCtx = new OfflineAudioContext(
    CHANNELS,
    Math.ceil(decodedAudio.duration * SAMPLE_RATE),
    SAMPLE_RATE
  );

  const source = offlineCtx.createBufferSource();
  source.buffer = decodedAudio;
  source.connect(offlineCtx.destination);
  source.start(0);

  audioData = await offlineCtx.startRendering();
  if (audioData && workletNode) {
    const pcm = createInterleaved(audioData);
    workletNode.port.postMessage({action: 'setCustomAudio', pcm}, [pcm.buffer]);
  }

  toggleAudioBtn.disabled = !encoder || !audioData;
}

async function loadAudio(file) {
  log(`[Audio] Loading audio file: ${file.name}...`);
  try {
    const arrayBuffer = await file.arrayBuffer();
    loadAudioFromBuffer(arrayBuffer);
    log('[Audio] Audio decoded & resampled successfully!');
  } catch (err) {
    log(`[Audio Error] Failed to decode audio: ${err.message}`);
  }
}

function loadDefaultAudio() {
  log(`[Audio] Loading audio file: ${DEFAULT_AUDIO_FILE}`);
  fetch(DEFAULT_AUDIO_FILE).then(async (response) => {
    if (!response.ok) {
      log(`[Audio Error] Failed to load ${DEFAULT_AUDIO_FILE}`);
      return;
    }
    try {
      const audioBuffer = await response.arrayBuffer();
      loadAudioFromBuffer(audioBuffer);
    } catch (err) {
      log(`[Audio Error] Failed to decode audio: ${err.message}`);
    }
  });
}

async function initOpus() {
  try {
    encoderStatus.textContent = "Opus Encoder: Ready (48kHz Stereo 160kbps CBR)";
    encoderStatus.style.color = "var(--success)";
    log("Opus encoder initialized successfully.");
    updateUiState();
  } catch (err) {
    encoderStatus.textContent = `Opus Encoder Error: ${err.message}`;
    encoderStatus.style.color = "var(--danger)";
    log(`Failed to initialize Opus: ${err.message}`);
  }
}

function updateUiState() {
  const isConnected = hidDevice && hidDevice.opened;

  if (isConnected) {
    connectionStatus.className = "status-badge connected";
    statusText.textContent = `Connected: ${hidDevice.productName || 'DualSense'}`;
    connectBtn.disabled = true;
    disconnectBtn.disabled = false;
    toggleAudioBtn.disabled = !encoder || !audioData;
    startHeartbeat();
  } else {
    connectionStatus.className = "status-badge";
    statusText.textContent = "Disconnected";
    connectBtn.disabled = false;
    disconnectBtn.disabled = true;
    toggleAudioBtn.disabled = true;
    if (controls.isAudioStreaming) stopAudioStream();
    stopHeartbeat();
  }
}

// Build 0x32 State Report
function buildStateReport({ r = 0, g = 100, b = 255, volume = 100, target = 'speaker' } = {}) {
  const report = new Uint8Array(STATE_REPORT_LENGTH);
  report[0] = STATE_REPORT_ID;
  report[1] = getNextSequenceByte();
  report[2] = 0x90;
  report[3] = 0x3F;

  const state = 4;
  // 0b1011_0000:
  // ~EnableRumbleEmulation
  // ~UseRumbleNotHaptics
  // ~AllowRightTriggerFFB
  // ~AllowLeftTriggerFFB
  // AllowHeadphoneVolume
  // AllowSpeakerVolume
  // ~AllowMicVolume
  // AllowAudioControl
  report[state + 0] = 0xB0;
  // 0b1011_0110:
  // ~AllowMuteLight
  // AllowAudioMute
  // AllowLedColor
  // ~ResetLights
  // AllowPlayerIndicators
  // AllowHapticLowPassFilter
  // ~AllowMotorPowerLevel
  // AllowAudioControl2
  report[state + 1] = 0xB6;

  report[state + 4] = volume & 0x7F;  // VolumeHeadphones
  report[state + 5] = volume & 0x7F;  // VolumeSpeaker
  report[state + 6] = 0x40;  // VolumeMic
  report[state + 7] = (target === 'headset') ? 0x20 : 0x00;  // AudioControl OutputPathSelect
  report[state + 37] = 0x03;  // SpeakerCompPreGain
  report[state + 38] = 0x02;  // AllowColorLightFadeAnimation
  report[state + 39] = 0x01;  // HapticLowPassFilter
  report[state + 41] = 0x02;  // LightFadeAnimation
  report[state + 43] = 0x04;  // PlayerLight3
  report[state + 44] = r & 0xFF;  // LedRed
  report[state + 45] = g & 0xFF;  // LedGreen
  report[state + 46] = b & 0xFF;  // LedBlue

  fillSonyCrc(report);
  return report;
}

async function sendStateReport() {
  if (!hidDevice || !hidDevice.opened) return;
  const color = HEARTBEAT_COLORS[Math.floor(currentColorIndex / 20)];
  const intensity = Math.min(1.0, 0.01 * controls.currentEnergy);
  const r = color.r * (controls.isAudioStreaming ? intensity : 1);
  const g = color.g * (controls.isAudioStreaming ? intensity : 1);
  const b = color.b * (controls.isAudioStreaming ? intensity : 1);
  const volume = controls.currentVolume;
  const target = controls.currentTarget;
  worker.postMessage({ action: 'sendStateReport', controls, color: {r, g, b}})

  metrics.stateReportsSent++;
  //metricStateSent.textContent = metrics.stateReportsSent;

  if (metrics.stateReportsSent % 100 === 0) {
    log(`[State] Reports: ${metrics.stateReportsSent}`);
  }
}

// --- Fill 128-Byte HD Haptics Waveform Blocks from Active PCM Chunk ---
function fillHapticBlocks(report, pcmFrame) {
  let isSilent = false;
  if (pcmFrame) {
    const energy = pcmFrame.reduce((a, b) => a + b * b, 0);
    isSilent = (controls.currentHaptics / 100) * energy < 0.00005;
  }

  if (!controls.isHapticsEnabled || !pcmFrame || isSilent) {
    // Silent neutral haptic blocks
    report[10] = 0xD0;
    report[11] = 64;
    report.fill(0, 12, 74);
    report[74] = 0xD0;
    report[75] = 64;
    report.fill(0, 76, 138);
    return 0;
  }

  const totalInputFrames = pcmFrame.length / 2;
  const windowSize = SAMPLES_PER_OPUS_PACKET / 62;

  // Helper to process a single haptic block (31 pairs)
  function populateBlock(blockHeaderOffset, dataHeaderOffset, startIndex) {
    report[blockHeaderOffset] = 0xD2;
    report[blockHeaderOffset + 1] = 64;

    let energy = 0;
    for (let i = 0; i < 31; i++) {
      const pairIndex = startIndex + i;
      const windowStart = Math.floor(pairIndex * windowSize);
      const windowEnd = Math.min(Math.floor((pairIndex + 1) * windowSize), totalInputFrames);

      let maxLeft = 0;
      let maxRight = 0;
      let peakLeft = 0;
      let peakRight = 0;

      // Find peak absolute amplitude within the window to preserve transients
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

  let energy = 0;

  // Block 1: pairs 0 to 30
  energy += populateBlock(10, 12, 0);

  // Block 2: pairs 31 to 61
  energy += populateBlock(74, 76, 31);

  return energy;
}

function openWorkerMessageChannel() {
  if (!worker || !workletNode) {
    return;
  }
  const channel = new MessageChannel();

  // 1. Send port2 to the Worker
  worker.postMessage({ action: 'init-audio-port', controls, port: channel.port2 }, [channel.port2]);

  // 2. Send port1 to the AudioWorklet
  workletNode.port.postMessage({ action: 'set-audio-port', port: channel.port1 }, [channel.port1]);
}

// --- Audio & Haptic Streaming Controls ---
async function startAudioStream() {
  if (controls.isAudioStreaming || !hidDevice || !encoder || !audioData) return;

  controls.isAudioStreaming = true;
  toggleAudioBtn.textContent = "⏹ Stop audio";
  toggleAudioBtn.className = "btn btn-danger pulse";

  log(`[Audio & Haptics] Initializing stream (Target: ${controls.currentTarget}, Vol: ${controls.currentVolume}, Sound: ${controls.isSoundEnabled ? 'ON' : 'OFF'}, Haptics: ${controls.isHapticsEnabled ? 'ON' : 'OFF'})...`);

  for (let i = 0; i < 8; i++) {
    if (!controls.isAudioStreaming) return;
    await sendStateReport();
    await new Promise(r => setTimeout(r, 20));
  }

  metrics.lastSendTimestamp = 0;
  metrics.intervalHistory = [];

  try {
    if (!audioContext || audioContext.state === 'closed') {
      audioContext = new AudioContext({ sampleRate: SAMPLE_RATE });
      isWorkletModuleLoaded = false;
    }
    if (audioContext.state === 'suspended') {
      await audioContext.resume();
    }

    if (!isWorkletModuleLoaded) {
      const blob = new Blob([audioWorkletCode], { type: 'application/javascript' });
      const workletUrl = URL.createObjectURL(blob);
      await audioContext.audioWorklet.addModule(workletUrl);
      isWorkletModuleLoaded = true;
    }

    workletNode = new AudioWorkletNode(audioContext, 'dualsense-audio-processor', {});

    const pcm = createInterleaved(audioData);
    workletNode.port.postMessage({action: 'setCustomAudio', pcm}, [pcm.buffer]);

    const dummyGain = audioContext.createGain();
    dummyGain.gain.value = 0.0;
    workletNode.connect(dummyGain);
    dummyGain.connect(audioContext.destination);

    if (worker) {
      openWorkerMessageChannel();
    }

    log(`[Audio & Haptics] AudioWorklet running on hardware DAC clock!`);
  } catch (err) {
    log(`AudioWorklet initialization failed: ${err.message}`);
  }
}

function stopAudioStream() {
  if (!controls.isAudioStreaming) return;
  controls.isAudioStreaming = false;
  controls.currentEnergy = 0;

  if (workletNode) {
    workletNode.port.postMessage({ action: 'stop' });
    try { workletNode.disconnect(); } catch (e) {}
    workletNode = null;
  }
  if (audioContext && audioContext.state === 'running') {
    audioContext.suspend();
  }

  toggleAudioBtn.textContent = "▶ Start audio";
  toggleAudioBtn.className = "btn btn-success";
  log(`[Audio & Haptics] Stream stopped. Audio reports sent: ${metrics.audioReportsSent}`);
}

// --- Heartbeat Logic ---
function startHeartbeat() {
  if (heartbeatTimer) return;

  const cycle = async () => {
    if (hidDevice !== null && !hidDevice.opened) {
      hidDevice = null;
      stopHeartbeat();
      log(`HID device closed`);
      return;
    }

    const color = HEARTBEAT_COLORS[Math.floor(currentColorIndex / 20)];
    currentColorIndex = (currentColorIndex + 1) % (HEARTBEAT_COLORS.length * 20);

    //colorPreview.style.backgroundColor = color.hex;
    //colorNameText.textContent = `LED color: ${color.name}`;

    try {
      await sendStateReport();
    } catch (e) {}
    controls.currentEnergy = 0;
  };

  cycle();
  heartbeatTimer = setInterval(cycle, 1000);
}

function stopHeartbeat() {
  if (heartbeatTimer) {
    clearInterval(heartbeatTimer);
    heartbeatTimer = null;
  }
  //colorNameText.textContent = "LED color: Idle";
  //colorPreview.style.backgroundColor = "#000000";
}

function onHeadphonesPlugged(plugged) {
  const target = plugged ? 'headset' : 'speaker';
  controls.currentTarget = target;
  audioTargetSelect.value = target;
}

async function onConnect(device) {
  if (hidDevice || !device) {
    return;
  }
  const vidpid = `${hex16(device.vendorId)}:${hex16(device.productId)}`;
  hidDevice = device;
  if (!hidDevice.opened) {
    log(`Opening: ${hidDevice.productName} [${vidpid}]`);
    await hidDevice.open();
  }
  if (!hidDevice.opened) {
    log(`Failed to open: ${hidDevice.productName} [${vidpid}]`);
    return;
  }
  if (worker) {
    worker.postMessage({action: 'initHid'});
  }

  log(`Connected: ${hidDevice.productName} [${vidpid}]`);
  updateUiState();

  for (let i = 0; i < 3; i++) {
    await sendStateReport();
    await new Promise(r => setTimeout(r, 30));
  }
  log("Initial handshake completed successfully!");
}

function isDualSenseBluetooth(device) {
  return device.vendorId === VENDOR_SONY &&
      device.productId === PRODUCT_SONY_DUALSENSE &&
      device.collections.length === 1 &&
      device.collections[0].outputReports.some((r) => r.reportId == STATE_REPORT_ID) &&
      device.collections[0].outputReports.some((r) => r.reportId == AUDIO_REPORT_ID);
}

async function connectToDualSense() {
  let devices = await navigator.hid.getDevices();
  devices = devices.filter(isDualSenseBluetooth);
  if (devices.length === 0) {
    return;
  }
  if (!hidDevice) {
    onConnect(devices[0]);
  }
}

// --- Canvas Jitter Renderer ---
function drawJitterChart() {
  const ctx = jitterCanvas.getContext('2d');
  const width = jitterCanvas.clientWidth;
  const height = jitterCanvas.clientHeight;

  if (jitterCanvas.width !== width || jitterCanvas.height !== height) {
    jitterCanvas.width = width;
    jitterCanvas.height = height;
  }

  ctx.clearRect(0, 0, width, height);

  // Background grid lines
  ctx.strokeStyle = '#1e2235';
  ctx.lineWidth = 1;
  ctx.beginPath();
  ctx.moveTo(0, height / 2);
  ctx.lineTo(width, height / 2);
  ctx.stroke();

  const history = metrics.intervalHistory;
  if (history.length === 0) {
    jitterStats.textContent = `Min: 0.00ms | Max: 0.00ms`;
    return;
  }

  const minVal = Math.min(...history);
  const maxVal = Math.max(...history);
  jitterStats.textContent = `Min: ${minVal.toFixed(2)}ms | Max: ${maxVal.toFixed(2)}ms`;

  // Plotting data points
  ctx.strokeStyle = 'var(--accent)';
  ctx.lineWidth = 2;
  ctx.beginPath();

  const maxDataPoints = Math.min(history.length, width);
  const startIndex = history.length - maxDataPoints;
  const stepX = width / Math.max(maxDataPoints - 1, 1);

  // Dynamically scale height bounds around typical audio packet intervals (~20ms)
  const baseRange = 15;
  const boundsMin = Math.min(10, minVal - 2);
  const boundsMax = Math.max(35, maxVal + 2);
  const range = boundsMax - boundsMin;

  for (let i = 0; i < maxDataPoints; i++) {
    const val = history[startIndex + i];
    const x = i * stepX;
    const y = height - ((val - boundsMin) / range) * height;

    if (i === 0) {
      ctx.moveTo(x, y);
    } else {
      ctx.lineTo(x, y);
    }
  }
  ctx.stroke();
}

async function initWorker() {
  worker = new Worker(new URL('./worker.js', import.meta.url), {
    type: 'module'
  });
  worker.postMessage({
    action: 'init',
    config: {
      sampleRate: SAMPLE_RATE,
      channels: CHANNELS,
      application: 2049,
      bitrate: OPUS_PACKET_BYTES * 8 * 100,
      vbr: false,
      frameSize: FRAMES_PER_OPUS_PACKET,
      complexity: 10}});
  worker.onmessage = (e) => {
    const { status } = e.data;
    if (status === 'ready') {
      log("Opus encoder worker initialized successfully.");
    } else if (status === 'error') {
      const { message } = e.data;
      log("Worker error:", message);
    } else if (status === 'metrics') {
      const { timestamp } = e.data;
      metrics.lastSendTimestamp = timestamp;
      metrics.stateReportsSent = e.data.metrics.stateReportsSent;
      metrics.audioReportsSent = e.data.metrics.audioReportsSent;
      if (metrics.lastSendTimestamp > 0) {
        const delta = timestamp - metrics.lastSendTimestamp;
        metrics.intervalHistory.push(delta);
        if (metrics.intervalHistory.length > 200) metrics.intervalHistory.shift();

        const avgInterval = metrics.intervalHistory.reduce((a, b) => a + b, 0) / metrics.intervalHistory.length;
        //metricInterval.textContent = `${avgInterval.toFixed(3)} ms`;
        //drawJitterChart();
      }
      metrics.lastSendTimestamp = timestamp;
    } else if (status === 'headset') {
      const { plugged } = e.data;
      onHeadphonesPlugged(plugged);
    }
  };

  let devices = await navigator.hid.getDevices();
  devices = devices.filter(isDualSenseBluetooth).filter((d) => d.opened);
  if (devices.length === 1) {
    worker.postMessage({action: 'initHid'});
  }

  encoderStatus.textContent = "Opus Encoder: Ready (48kHz Stereo 160kbps CBR)";
  encoderStatus.style.color = "var(--success)";
  log("Opus encoder initialized successfully.");
  updateUiState();
}

// --- Event Listeners ---

navigator.hid.addEventListener('connect', connectToDualSense);

navigator.hid.addEventListener('disconnect', (e) => {
  if (e.device === hidDevice) {
    log("Device physically disconnected.");
    hidDevice = null;
    updateUiState();
  }
});

audioFileInput.addEventListener("change", async (e) => {
  const file = e.target.files[0];
  if (!file) return;
  loadAudio(file);
});

connectBtn.addEventListener("click", async () => {
  try {
    log("Requesting WebHID device.");
    const devices = await navigator.hid.requestDevice({
      filters: [{ vendorId: VENDOR_SONY, productId: PRODUCT_SONY_DUALSENSE }]
    });

    if (devices.length === 0) {
      log("No device selected.");
      return;
    }

    const filteredDevices = devices.filter(isDualSenseBluetooth);
    if (filteredDevices.length === 0) {
      log("Must connect to the DualSense over Bluetooth.");
      devices.forEach((d) => d.forget());
      return;
    }

    onConnect(filteredDevices[0]);
  } catch (err) {
    log(`Connection failed: ${err.message}`);
  }
});

disconnectBtn.addEventListener("click", async () => {
  if (hidDevice && hidDevice.opened) {
    stopAudioStream();
    stopHeartbeat();
    await hidDevice.close();
    hidDevice.forget();
    hidDevice = null;
    log("Disconnected from device.");
    updateUiState();
  }
});

toggleAudioBtn.addEventListener("click", () => {
  if (controls.isAudioStreaming) {
    stopAudioStream();
  } else {
    startAudioStream();
  }
});

toggleSoundBtn.addEventListener("click", () => {
  controls.isSoundEnabled = !controls.isSoundEnabled;
  if (controls.isSoundEnabled) {
    controls.currentVolume = parseInt(volumeSlider.value, 10);
  } else {
    controls.currentVolume = 0;
  }
  toggleSoundBtn.textContent = controls.isSoundEnabled ? "🔊 Sound on" : "🔇 Sound muted";
  toggleSoundBtn.className = controls.isSoundEnabled ? "btn btn-haptic" : "btn btn-secondary";
  log(`Sound ${controls.isSoundEnabled ? 'on' : 'off'}`);
  if (hidDevice && hidDevice.opened) {
    sendStateReport();
  }
});

toggleHapticBtn.addEventListener("click", () => {
  controls.isHapticsEnabled = !controls.isHapticsEnabled;
  toggleHapticBtn.textContent = controls.isHapticsEnabled ? "🌶️ Haptics on" : "🧊️ Haptics muted";
  toggleHapticBtn.className = controls.isHapticsEnabled ? "btn btn-haptic" : "btn btn-secondary";
  log(`Haptics ${controls.isHapticsEnabled ? 'on' : 'off'}`);
  if (hidDevice && hidDevice.opened) {
    sendStateReport();
  }
});

hapticAmpSlider.addEventListener("input", (e) => {
  if (!controls.isHapticsEnabled) {
    controls.isHapticsEnabled = true;
    toggleHapticBtn.textContent = "🌶️ Haptics on";
    toggleHapticBtn.className = "btn btn-haptic";
  }
  hapticAmpVal.textContent = e.target.value;
  controls.currentHaptics = parseInt(e.target.value, 10);
  if (hidDevice && hidDevice.opened) {
    sendStateReport();
  }
});

audioTargetSelect.addEventListener("change", (e) => {
  controls.currentTarget = e.target.value;
  log(`Audio target switched to: ${controls.currentTarget.toUpperCase()}`);
  if (hidDevice && hidDevice.opened && controls.isSoundEnabled) {
    sendStateReport();
  }
});

volumeSlider.addEventListener("input", (e) => {
  if (!controls.isSoundEnabled) {
    controls.isSoundEnabled = true;
    toggleSoundBtn.textContent = "🔊 Sound on";
    toggleSoundBtn.className = "btn btn-haptic";
  }
  volumeVal.textContent = e.target.value;
  controls.currentVolume = parseInt(e.target.value, 10);
  if (hidDevice && hidDevice.opened) {
    sendStateReport();
  }
});

clearLogBtn.addEventListener("click", () => {
  consoleLog.value = "";
});

// Initialize Opus encoder
initWorker();

// Initialize default audio
loadDefaultAudio();

// Check for connected DualSenses
connectToDualSense();
