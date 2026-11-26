// An object whose `ask` is an arrow function, passed where `ask` was
// made a method: the error points at the field and at the call.
import { attach } from "./panel.js";
const editor = {
  say: (text) => { console.log(text); },
  ask: (title) => Promise.resolve(title),
};
attach(editor);
