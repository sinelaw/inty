// An object passed to a class's constructor, whose type (a library's
// declaration) says what the class uses of it. The object's `ask` takes
// a number where the class passes a string: the error names `ask` and
// shows its two types, not the two whole records.
/** type Editor = { open: (String) => Number, close: () => Number, render: (Number, Number) => Number, focus: () => Number, scroll: (Number) => Number, select: (Number, Number) => Number, title: String, width: Number, height: Number, ask: (String) => String } */
/** const Prompter: new (Editor) => {start: () => Number} */
const Prompter;

const editor = {
  open: (s) => s.length,
  close: () => 0,
  render: (a, b) => a + b,
  focus: () => 0,
  scroll: (n) => n,
  select: (a, b) => a - b,
  title: "",
  width: 0,
  height: 0,
  ask: (n) => n * 2,
};
const p = new Prompter(editor);
