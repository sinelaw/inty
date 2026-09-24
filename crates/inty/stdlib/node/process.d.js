// inty stdlib: the subset of Node's `node:process` a command-line tool
// needs. Resolved for `import process from "node:process"` (or
// `"process"`), and for named imports of the same members.

/** type Writable = {write: (String) => Boolean} */

/** const argv: String[] */
export const argv;

/** const exit: (Number) => Undefined */
export const exit;

/** const stdout: Writable */
export const stdout;

/** const stderr: Writable */
export const stderr;

/** const process: {argv: String[], exit: (Number) => Undefined, stdout: Writable, stderr: Writable} */
const process;
export default process;
