// inty: accept
// inty: known-failing: `TextDecoder.decode` takes only a Uint8Array, not any BufferSource (review of claude/browser-apis, fix pending)
// `TextDecoder.decode` takes any BufferSource, an ArrayBuffer included.
new TextDecoder().decode(new ArrayBuffer(4));
