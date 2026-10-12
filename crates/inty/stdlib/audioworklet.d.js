// inty stdlib: the AudioWorkletGlobalScope — the globals of the module an
// `AudioContext.audioWorklet.addModule(url)` loads. Not loaded by
// default; check such a module with `inty --lib builtin:audioworklet`.
//
// A processor extends `AudioWorkletProcessor` (its `port` talks to the
// `AudioWorkletNode` on the main thread; every message on it is an `M`)
// and is registered by name. inty has no inheritance, so a processor is
// declared as an external class, without a body:
//
//     /** class Gain extends AudioWorkletProcessor { gain: Number } */
//     class Gain;
//     registerProcessor("gain", Gain);

/** const AudioWorkletProcessor: <M>() => {port: MessagePort<M>} */
const AudioWorkletProcessor;

/** const registerProcessor: <P>(name: String, processorCtor: P) => Undefined */
const registerProcessor;

/** const sampleRate: Number */
const sampleRate;

/** const currentTime: Number */
const currentTime;

/** const currentFrame: Number */
const currentFrame;
