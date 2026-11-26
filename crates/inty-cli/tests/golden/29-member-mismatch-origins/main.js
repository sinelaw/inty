// An object literal passed to a class's constructor: the member that
// doesn't fit says where each side's type came from, the read in the
// class's module and the field of the literal.
import { Counter } from "./panel.js";
const source = { count: "three" };
export const c = new Counter(source);
