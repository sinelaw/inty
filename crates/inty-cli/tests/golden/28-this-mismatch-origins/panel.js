// The module's `editor` isn't known while it is checked: its reads become
// the fields of an object, and the first call of `ask` on it passes the
// object as `ask`'s `this`, which makes `ask` a method.
let editor;
export function attach(e) { editor = e; }
export async function rename(w) {
  const name = await editor.ask(w);
  editor.say(name);
}
