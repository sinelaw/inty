// inty stdlib: the synchronous, text subset of Node's `node:fs`.
//
// Resolved for `import … from "node:fs"` (or `"fs"`). Files are read and
// written as UTF-8 text: the encoding argument of readFileSync is
// required and typed as the literal "utf8" / "utf-8", so the result is
// always a String (without it, Node returns a Buffer). Read standard
// input with `readFileSync("/dev/stdin", "utf8")`.

/** const readFileSync: (String, "utf8" | "utf-8") => String */
export const readFileSync;

/** const writeFileSync: (String, String) => Undefined */
export const writeFileSync;

/** const appendFileSync: (String, String) => Undefined */
export const appendFileSync;

/** const existsSync: (String) => Boolean */
export const existsSync;
