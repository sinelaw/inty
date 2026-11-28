// An object literal passed to a class's constructor: the read in the
// class's module waits for the value, and is reported where it is, as a
// mismatch at the member it reads (the record it asks for, and the
// literal's).
import { Counter } from "./panel.js";
const source = { count: "three" };
export const c = new Counter(source);
