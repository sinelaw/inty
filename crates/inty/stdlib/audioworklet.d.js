// inty stdlib: the AudioWorkletGlobalScope — the globals of the module an
// `AudioContext.audioWorklet.addModule(url)` loads. Not loaded by
// default; check such a module with `inty --lib builtin:audioworklet`.
//
// A processor extends `AudioWorkletProcessor` (its `port` talks to the
// `AudioWorkletNode` on the main thread; every message on it is an `M`)
// and is registered by name:
//
//     class Gain extends AudioWorkletProcessor {
//       constructor() { super(); this.gain = 1; }
//       process(inputs, outputs, parameters) { …; return true; }
//     }
//     registerProcessor("gain", Gain);

/** const AudioWorkletProcessor: <M>() => {port: MessagePort<M>} */
const AudioWorkletProcessor;

/** const registerProcessor: <P>(name: String, processorCtor: P) => Undefined */
const registerProcessor;

/** const sampleRate: Number */
const sampleRate;

/** const currentTime: Number */
const currentTime;

/** const currentFrame: Int */
const currentFrame;
