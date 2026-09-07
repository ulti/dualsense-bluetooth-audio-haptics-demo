// --- AudioWorklet Processor Source ---
const audioWorkletCode = `
  class DualSenseAudioProcessor extends AudioWorkletProcessor {
    constructor(options) {
      super();
      this.samplesAccumulated = 0;
      this.bufferL = new Float32Array(1024);
      this.bufferR = new Float32Array(1024);
      this.active = true;
      this.workerPort = null;
      // Pre-allocated pool of reusable transferable buffers to prevent GC
      this.bufferPool = [
        new Float32Array(2048),
        new Float32Array(2048),
        new Float32Array(2048),
        new Float32Array(2048)
      ];

      this.port.onmessage = (e) => {
        if (e.data.action === 'stop') {
          this.active = false;
        } else if (e.data.action === 'set-audio-port') {
          this.workerPort = e.data.port;
          this.workerPort.onmessage = (we) => {
            if (we.data.action === 'recycle-buffer' && we.data.buffer) {
              this.bufferPool.push(new Float32Array(we.data.buffer));
            }
          };
        }
      };
    }

    process(inputs, outputs, parameters) {
      if (!this.active) return false;

      const scale = 0.2;
      const input = inputs[0];
      const inputL = input && input[0] ? input[0] : null;
      const inputR = input && input[1] ? input[1] : inputL;
      for (let i = 0; i < 128; i++) {
        let sampleL = inputL ? inputL[i] * scale : 0;
        let sampleR = inputR ? inputR[i] * scale : 0;

        this.bufferL[this.samplesAccumulated] = sampleL;
        this.bufferR[this.samplesAccumulated] = sampleR;
        this.samplesAccumulated++;

        if (this.samplesAccumulated === 1024) {
          const frames = 1024;
          const pcm = this.bufferPool.pop() || new Float32Array(2048);
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

let audioContext = null;
let hidDevice = null;
let worker = null;
let workerReady = false;
let workletNode = null;
let workletReady = false;
let analyserNode = null;
let dataArray = null;

// Decoded audio data
let decodedAudioBuffer = null;
let activeSourceNode = null;
let isCapturing = false;

// UI controls
let controls = {
  isAudioStreaming: false,
  isSoundEnabled: true,
  isHapticsEnabled: true,
  isLightsEnabled: true,
  currentVolume: 100,
  currentHaptics: 100,
  currentLightsInterval: 1000 / 20,
  currentTarget: 'speaker',
};

// Metrics (sent from worker)
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
let intervalHistory = [];
let intensityHistory = [];

const fullReportBuffer = new Uint8Array(FULL_REPORT_LENGTH);
const resampleOutputBuffer = new Float32Array(SAMPLES_PER_OPUS_PACKET * 2);

// --- DOM Elements ---
const connectBtn = document.getElementById("connect-btn");
const disconnectBtn = document.getElementById("disconnect-btn");
const connectionStatus = document.getElementById("connection-status");
const statusText = document.getElementById("status-text");
const batteryStatus = document.getElementById("battery-status");
const batteryStatusText = document.getElementById("battery-status-text");
const toggleAudioBtn = document.getElementById("toggle-audio-btn");
const volumeSlider = document.getElementById("volume-slider");
const volumeVal = document.getElementById("volume-val");
const audioTargetSelect = document.getElementById("audio-target-select");
const toggleSoundBtn = document.getElementById("toggle-sound-btn");
const toggleHapticBtn = document.getElementById("toggle-haptic-btn");
const toggleLightsBtn = document.getElementById("toggle-lights-btn");
const hapticAmpSlider = document.getElementById("haptic-amp-slider");
const hapticAmpVal = document.getElementById("haptic-amp-val");
const lightFrameRateSlider = document.getElementById("light-frame-rate-slider");
const lightFrameRateVal = document.getElementById("light-frame-rate-val");
const metricInputsReceived = document.getElementById("metric-inputs-received");
const metricAudioSent = document.getElementById("metric-audio-sent");
const metricStateSent = document.getElementById("metric-state-sent");
const audioFileInput = document.getElementById("audio-file-input");
const jitterCanvas = document.getElementById("jitter-canvas");
const jitterStats = document.getElementById("jitter-stats");
const intensityCanvas = document.getElementById("intensity-canvas");
const intensityStats = document.getElementById("intensity-stats");
const captureSystemAudioBtn = document.getElementById("capture-system-audio-btn");
const spectralCanvas = document.getElementById('spectral-canvas');
const spectralCtx = spectralCanvas.getContext('2d');

const log = console.log;

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
  try {
    const decodeCtx = new (window.AudioContext || window.webkitAudioContext)();
    try {
      decodedAudioBuffer = await decodeCtx.decodeAudioData(buffer.slice(0));
    } finally {
      decodeCtx.close();
    }
    log('[Audio] Audio file decoded successfully into an AudioBuffer!');
  } catch (err) {
    log(`[Audio Error] Failed to decode audio: ${err.message}`);
    decodedAudioBuffer = null;
  }
  updateUiState();
}

async function loadAudio(file) {
  log(`[Audio] Loading audio file: ${file.name}...`);
  try {
    const arrayBuffer = await file.arrayBuffer();
    await loadAudioFromBuffer(arrayBuffer);
    if (isCapturing) {
      await stopCaptureSystemAudio();
    }
    if (controls.isAudioStreaming) {
      await stopAudioStream();
    }
    await startAudioStream();

    log('[Audio] Audio decoded & loaded successfully!');
  } catch (err) {
    log(`[Audio Error] Failed to decode audio: ${err.message}`);
  }
}

async function loadDefaultAudio() {
  log(`[Audio] Loading audio file: ${DEFAULT_AUDIO_FILE}`);
  const response = await fetch(DEFAULT_AUDIO_FILE)
  if (!response.ok) {
    log(`[Audio Error] Failed to load ${DEFAULT_AUDIO_FILE}`);
    return;
  }
  try {
    const audioBuffer = await response.arrayBuffer();
    await loadAudioFromBuffer(audioBuffer);
  } catch (err) {
    log(`[Audio Error] Failed to decode audio: ${err.message}`);
  }
}

function updateUiState() {
  const isConnected = hidDevice && hidDevice.opened;

  if (isConnected) {
    connectionStatus.className = "status-badge connected";
    statusText.textContent = `Connected: ${hidDevice.productName}`;
    connectBtn.disabled = true;
    disconnectBtn.disabled = false;
  } else {
    connectionStatus.className = "status-badge";
    statusText.textContent = "Disconnected";
    connectBtn.disabled = false;
    disconnectBtn.disabled = true;
  }

  // The Start audio button is enabled whenever the Opus worker is ready and audio data is loaded
  const isAudioReady = workerReady;
  toggleAudioBtn.disabled = !isAudioReady;
}

async function sendStateReport() {
  if (!worker) return;
  worker.postMessage({ action: 'send-state-report', controls })
}

function openWorkerMessageChannel() {
  if (!worker || !workletNode) {
    return;
  }
  const channel = new MessageChannel();
  worker.postMessage({ action: 'init-audio-port', controls, port: channel.port2 }, [channel.port2]);
  workletNode.port.postMessage({ action: 'set-audio-port', port: channel.port1 }, [channel.port1]);
}

async function requestDualSenseConnection() {
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

    await onConnect(filteredDevices[0]);
  } catch (err) {
    log(`Connection failed: ${err.message}`);
  }
}

// --- Audio & Haptic Streaming Controls ---
async function startAudioStream() {
  if (controls.isAudioStreaming) return;

  if (!hidDevice || !hidDevice.opened) {
    log("Please connect the DualSense controller.");
    await requestDualSenseConnection();
    if (!hidDevice || !hidDevice.opened) return;
  }

  if (!workerReady) return;

  if (!decodedAudioBuffer && !window.activeMediaStream) {
    await loadDefaultAudio();
  }

  controls.isAudioStreaming = true;
  toggleAudioBtn.textContent = "⏹ Stop audio";
  toggleAudioBtn.className = "btn btn-danger pulse";

  for (let i = 0; i < 8; i++) {
    if (!controls.isAudioStreaming) return;
    await sendStateReport();
    await new Promise(r => setTimeout(r, 20));
  }

  if (intervalHistory.length < 500) {
    intervalHistory = new Array(500).fill(20);
  }

  if (intensityHistory.length < 500) {
    intensityHistory = new Array(500).fill(0);
  }

  try {
    if (!audioContext || audioContext.state === 'closed') {
      audioContext = new AudioContext({ sampleRate: SAMPLE_RATE });
      workletReady = false;
    }
    if (audioContext.state === 'suspended') {
      await audioContext.resume();
    }

    if (!workletReady) {
      const blob = new Blob([audioWorkletCode], { type: 'application/javascript' });
      const workletUrl = URL.createObjectURL(blob);
      await audioContext.audioWorklet.addModule(workletUrl);
      workletReady = true;
    }

    workletNode = new AudioWorkletNode(audioContext, 'dualsense-audio-processor', {});

    if (window.activeMediaStream) {
      activeSourceNode = audioContext.createMediaStreamSource(window.activeMediaStream);
    } else if (decodedAudioBuffer) {
      activeSourceNode = audioContext.createBufferSource();
      activeSourceNode.buffer = decodedAudioBuffer;
      activeSourceNode.loop = true; // Loop the file track automatically
      activeSourceNode.start(0);
    } else {
      log("[Audio Error] No audio source available to play.");
      stopAudioStream();
      return;
    }

    activeSourceNode.connect(workletNode);

    analyserNode = audioContext.createAnalyser();
    analyserNode.fftSize = 4096 * 4;
    const bufferLength = analyserNode.frequencyBinCount;
    dataArray = new Uint8Array(bufferLength);
    activeSourceNode.connect(analyserNode);

    const dummyGain = audioContext.createGain();
    dummyGain.gain.value = 0.0;
    workletNode.connect(dummyGain);
    dummyGain.connect(audioContext.destination);

    if (worker) {
      openWorkerMessageChannel();
    }

    log('[Audio & Haptics] Audio routing graph active');
  } catch (err) {
    log(`Audio graph initialization failed: ${err.message}`);
  }
}

function stopAudioStream() {
  if (!controls.isAudioStreaming) return;
  controls.isAudioStreaming = false;

  if (activeSourceNode) {
    try {
      if (typeof activeSourceNode.stop === 'function') activeSourceNode.stop();
      activeSourceNode.disconnect();
    } catch (e) {}
    activeSourceNode = null;
  }

  if (workletNode) {
    workletNode.port.postMessage({ action: 'stop' });
    try { workletNode.disconnect(); } catch (e) {}
    workletNode = null;
  }

  if (audioContext && audioContext.state === 'running') {
    audioContext.suspend();
  }

  if (worker) {
    worker.postMessage({ action: 'stop-audio-stream' });
  }

  toggleAudioBtn.textContent = "▶ Start audio";
  toggleAudioBtn.className = "btn btn-success";
  log('[Audio & Haptics] Stream stopped');
}

function onHeadphonesPlugged(plugged) {
  const target = plugged ? 'headset' : 'speaker';
  controls.currentTarget = target;
  audioTargetSelect.value = target;
}

function onKeyDown(key) {
  if (key === 'buttonCross') {
    startAudioStream();
  } else if (key == 'buttonCircle') {
    stopAudioStream();
  }
}

function onKeyUp(key) {

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
    worker.postMessage({action: 'init-hid'});
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
  if (hidDevice) {
    return;
  }
  devices = devices.filter(isDualSenseBluetooth);
  if (devices.length === 0) {
    return;
  }
  onConnect(devices[0]);
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

  const history = intervalHistory;
  if (history.length === 0) {
    jitterStats.textContent = `Min: 0.00ms | Max: 0.00ms`;
    return;
  }

  const hh = history;//history.filter(s => !isNaN(s) && s < 100);
  const minVal = Math.min(...hh);
  const maxVal = Math.max(...hh);
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
  let first = true;

  for (let i = 0; i < maxDataPoints; i++) {
    const val = history[startIndex + i];
    if (isNaN(val)) {
      continue;
    }
    const x = i * stepX;
    const y = height - ((val - boundsMin) / range) * height;

    if (first) {
      ctx.moveTo(x, y);
      first = false;
    } else {
      ctx.lineTo(x, y);
    }
  }
  ctx.stroke();
}

function drawIntensityChart() {
  const ctx = intensityCanvas.getContext('2d');
  const width = intensityCanvas.clientWidth;
  const height = intensityCanvas.clientHeight;

  if (intensityCanvas.width !== width || intensityCanvas.height !== height) {
    intensityCanvas.width = width;
    intensityCanvas.height = height;
  }

  ctx.clearRect(0, 0, width, height);

  // Background grid lines
  ctx.strokeStyle = '#1e2235';
  ctx.lineWidth = 1;
  ctx.beginPath();
  ctx.moveTo(0, height / 2);
  ctx.lineTo(width, height / 2);
  ctx.stroke();

  const history = intensityHistory;
  if (history.length === 0) {
    intensityStats.textContent = `Min: 0 | Max: 0`;
    return;
  }

  const hh = history;//history.filter(s => !isNaN(s) && s < 100);
  let minVal = Math.min(...hh);
  let maxVal = Math.max(...hh);
  intensityStats.textContent = `Min: ${minVal.toFixed(2)} | Max: ${maxVal.toFixed(2)}`;
  maxVal = Math.max(Math.abs(minVal), Math.abs(maxVal));
  minVal = -maxVal;

  // Plotting data points
  ctx.strokeStyle = 'var(--accent)';
  ctx.lineWidth = 2;
  ctx.beginPath();

  const maxDataPoints = Math.min(history.length, width);
  const startIndex = history.length - maxDataPoints;
  const stepX = width / Math.max(maxDataPoints - 1, 1);

  const boundsMin = 0;
  const boundsMax = 1;
  const range = boundsMax - boundsMin;

  for (let i = 0; i < maxDataPoints; i++) {
    const val = 0.01 * Math.abs(history[startIndex + i]);
    if (isNaN(val)) {
      continue;
    }
    const x = i * stepX;
    const y0 = 0.5 * (height - ((val - boundsMin) / range) * height);
    const y1 = 0.5 * (height + ((val - boundsMin) / range) * height);

    ctx.moveTo(x, y0);
    ctx.lineTo(x, y1);
    ctx.stroke();
  }
}

let energy = 0;
function drawSpectralDisplay() {
  if (!analyserNode || !controls.isAudioStreaming) {
    // Clear canvas if not streaming
    spectralCtx.fillStyle = 'rgb(15, 18, 30)';
    spectralCtx.fillRect(0, 0, spectralCanvas.width, spectralCanvas.height);
    return;
  }

  const width = spectralCanvas.clientWidth;
  const height = spectralCanvas.clientHeight;

  if (spectralCanvas.width !== width || spectralCanvas.height !== height) {
    spectralCanvas.width = width;
    spectralCanvas.height = height;
  }

  // Pull the current frequency data into your Uint8Array
  analyserNode.getByteFrequencyData(dataArray);

  // Background clear
  //spectralCtx.fillStyle = 'rgb(15, 18, 30)';
  spectralCtx.clearRect(0, 0, width, height);

  const barWidthHz = SAMPLE_RATE / analyserNode.fftSize;
  const minHz = 20;
  const maxHz = 20000;
  const minIndex = Math.min(analyserNode.frequencyBinCount, Math.round(minHz / barWidthHz));
  const maxIndex = Math.min(analyserNode.frequencyBinCount, Math.round(maxHz / barWidthHz));
  const binCount = maxIndex - minIndex;

  const barWidth = (width / binCount);
  let barHeight;
  let nextX = 0;

  energy += intensityHistory[intensityHistory.length - 1];
  energy *= 0.9;

  let coldR = 48, coldG = 25, coldB = 52;
  let hotR = 136, hotG = 42, hotB = 113;
  let colorR = 0, colorG = 0, colorB = 0;

  const denom = Math.log10(maxHz / minHz);
  for (let i = minIndex; i < maxIndex; ++i) {
    let intensity = dataArray[i] / 255;
    barHeight = intensity * height;
    intensity *= (energy / 20);


    colorR = Math.round(Math.sqrt(0.5 * (hotR * hotR * intensity + coldR * coldR * (1 - intensity))));
    colorG = Math.round(Math.sqrt(0.5 * (hotG * hotG * intensity + coldG * coldG * (1 - intensity))));
    colorB = Math.round(Math.sqrt(0.5 * (hotB * hotB * intensity + coldB * coldB * (1 - intensity))));

    spectralCtx.fillStyle = `rgb(${colorR}, ${colorG}, ${colorB})`;
    const x = nextX;
    nextX = Math.round(Math.log10((i + 1) * barWidthHz / minHz) * width / denom);
    spectralCtx.fillRect(x, height - barHeight, nextX - x, barHeight);
  }
}

async function initWorker() {
  worker = new Worker(new URL('./worker.js', import.meta.url), {
    type: 'module'
  });
  worker.postMessage({
    action: 'init-opus',
    config: {
      sampleRate: SAMPLE_RATE,
      channels: CHANNELS,
      application: 2049,
      bitrate: OPUS_PACKET_BYTES * 8 * 100,
      vbr: false,
      frameSize: FRAMES_PER_OPUS_PACKET,
      complexity: 10}});

  let promise = new Promise((resolve, reject) => {
    worker.onmessage = (e) => {
      const { status } = e.data;
      if (status === 'ready') {
        log("Opus encoder worker initialized successfully.");
        workerReady = true;
        resolve();
      } else if (status === 'error') {
        const { message } = e.data;
        log("Worker error:", message);
        if (!workerReady) {
          reject(message);
        }
      } else if (status === 'power') {
        const { batteryText, percent, plugged, charging, full, error, abnormalVoltage, abnormalTemperature } = e.data;
        batteryStatusText.textContent = `Battery: ${batteryText}`;
        if (error || (percent <= 10 && !charging) || abnormalVoltage || abnormalTemperature) {
          batteryStatus.className = "status-badge";
        } else {
          batteryStatus.className = "status-badge connected";
        }
      } else if (status === 'heartbeat') {
        const { message } = e.data;
        //log(message);
        metrics = e.data.metrics;
        metrics.deltas.forEach((d) => intervalHistory.push(d));
        while (intervalHistory.length > 500) intervalHistory.shift();
        metrics.energy.forEach((d) => intensityHistory.push(d));
        while (intensityHistory.length > 500) intensityHistory.shift();
        metricInputsReceived.textContent = metrics.inputsReceived;
        metricStateSent.textContent = metrics.stateReportsSent;
        metricAudioSent.textContent = metrics.audioReportsSent;
        drawJitterChart();
        drawIntensityChart();
        drawSpectralDisplay();
      } else if (status === 'headset') {
        const { plugged } = e.data;
        onHeadphonesPlugged(plugged);
      } else if (status === 'keydown') {
        const { key } = e.data;
        onKeyDown(key);
      } else if (status === 'keyup') {
        const { key } = e.data;
        onKeyUp(key);
      }
    };
  });
  await promise;
  updateUiState();

  await connectToDualSense();
}

async function stopCaptureSystemAudio() {
  if (!isCapturing) {
    return;
  }
  isCapturing = false;
  if (window.activeMediaStream) {
    try {
      window.activeMediaStream.getTracks().forEach(track => track.stop());
    } catch (e) {}
    window.activeMediaStream = null;
  }
  captureSystemAudioBtn.textContent = "🖥️ Capture";
  captureSystemAudioBtn.className = "btn btn-secondary";
  if (controls.isAudioStreaming) {
    await stopAudioStream();
  }
  updateUiState();
}

async function toggleCaptureSystemAudio() {
  if (window.activeMediaStream) {
    stopCaptureSystemAudio();
    log("[Audio] System audio capture stopped.");
    return;
  }

  try {
    // Request media stream with system audio capture enabled
    const stream = await navigator.mediaDevices.getDisplayMedia({
      video: true,
      audio: {
        echoCancellation: false,
        noiseSuppression: false,
        autoGainControl: false,
        suppressLocalAudioPlayback: true
      }
    });

    const audioTracks = stream.getAudioTracks();
    if (audioTracks.length === 0) {
      alert("No audio track was shared. Please make sure to check 'Share audio' in the prompt.");
      stream.getTracks().forEach(track => track.stop());
      return;
    }

    window.activeMediaStream = stream;
    decodedAudioBuffer = null; // Clear out file buffer override if switching to live capture

    isCapturing = true;
    captureSystemAudioBtn.textContent = "🎙️ Capture";
    captureSystemAudioBtn.className = "btn btn-haptic";

    log("[Audio] System audio stream captured successfully.");
    updateUiState();

    if (controls.isAudioStreaming) {
      await stopAudioStream();
    }
    if (!controls.isAudioStreaming) {
      await startAudioStream();
    }

    // Handle user stopping the share via browser UI banner
    audioTracks[0].onended = () => {
      log("[Audio] System audio stream stopped by user.");
      stopCaptureSystemAudio();
    };

  } catch (err) {
    log(`[Audio Error] Failed to capture system audio: ${err.message}`);
    stopCaptureSystemAudio();
  }
}

async function init() {
  await initWorker();
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
  toggleSoundBtn.textContent = controls.isSoundEnabled ? "😮 Sound" : "😶 Sound";
  toggleSoundBtn.className = controls.isSoundEnabled ? "btn btn-haptic" : "btn btn-secondary";
  log(`Sound ${controls.isSoundEnabled ? 'on' : 'off'}`);
  if (hidDevice && hidDevice.opened) {
    sendStateReport();
  }
});

toggleHapticBtn.addEventListener("click", () => {
  controls.isHapticsEnabled = !controls.isHapticsEnabled;
  toggleHapticBtn.textContent = controls.isHapticsEnabled ? "📳 Haptics" : "📱 Haptics";
  toggleHapticBtn.className = controls.isHapticsEnabled ? "btn btn-haptic" : "btn btn-secondary";
  log(`Haptics ${controls.isHapticsEnabled ? 'on' : 'off'}`);
  if (hidDevice && hidDevice.opened) {
    sendStateReport();
  }
});

toggleLightsBtn.addEventListener("click", () => {
  controls.isLightsEnabled = !controls.isLightsEnabled;
  toggleLightsBtn.textContent = controls.isLightsEnabled ? "🌕 Lights" : "🌑 Lights";
  toggleLightsBtn.className = controls.isLightsEnabled ? "btn btn-haptic" : "btn btn-secondary";
  log(`Lights ${controls.isLightsEnabled ? 'on' : 'off'}`);
  if (hidDevice && hidDevice.opened) {
    sendStateReport();
  }
});

hapticAmpSlider.addEventListener("input", (e) => {
  if (!controls.isHapticsEnabled) {
    controls.isHapticsEnabled = true;
    toggleHapticBtn.textContent = "📳 Haptics";
    toggleHapticBtn.className = "btn btn-haptic";
  }
  hapticAmpVal.textContent = e.target.value;
  controls.currentHaptics = parseInt(e.target.value, 10);
  if (hidDevice && hidDevice.opened) {
    sendStateReport();
  }
});

lightFrameRateSlider.addEventListener("input", (e) => {
  const isMax = e.target.value >= 51;
  lightFrameRateVal.textContent = isMax ? 'max' : `${e.target.value} Hz`;
  controls.currentLightsInterval = isMax ? 0 : 1000 / e.target.value;
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
    toggleSoundBtn.textContent = "😮 Sound";
    toggleSoundBtn.className = "btn btn-haptic";
  }
  volumeVal.textContent = e.target.value;
  controls.currentVolume = parseInt(e.target.value, 10);
  if (hidDevice && hidDevice.opened) {
    sendStateReport();
  }
});

captureSystemAudioBtn.addEventListener("click", toggleCaptureSystemAudio);

init();
