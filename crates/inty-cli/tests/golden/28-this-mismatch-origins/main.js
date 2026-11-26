// An object whose `ask` is an arrow function, passed where `ask` is
// called as a method: JavaScript passes the receiver, which an arrow
// function ignores, so it checks (it was reported as a `this` mismatch).
import { attach } from "./panel.js";
const editor = {
  say: (text) => { console.log(text); },
  ask: (title) => Promise.resolve(title),
};
attach(editor);
