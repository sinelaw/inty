// Node built-ins the Go backend implements, and the string methods an
// I/O program needs. Run as `io <input> <outdir>`; see go_backend.rs.
import { readFileSync, writeFileSync, appendFileSync, existsSync } from "node:fs";
import process from "node:process";

const args = process.argv.slice(2);
if (args.length !== 2) {
  process.stderr.write("usage: io <input> <outdir>\n");
  process.exit(2);
}
const text = readFileSync(args[0], "utf8");
const lines = text.trimEnd().split("\n");
process.stdout.write(`${lines.length} lines\n`);
for (const line of lines) {
  const [key, value] = [line.slice(0, line.indexOf("=")), line.slice(line.indexOf("=") + 1)];
  process.stdout.write(key.padEnd(6, ".") + "|" + value.trim().padStart(8) + "|\n");
}
const csv = "a,b,,c";
console.log(csv.split(",").join(" / "));
console.log(csv.split(",", 2).join(" / "));
console.log("x-y-z".replace("-", "+") + " " + "x-y-z".replaceAll("-", "[$&]"));
console.log(String("banana".lastIndexOf("an")) + " " + String("banana".indexOf("an", 2)) + " " + "banana".charAt(3));
console.log("[" + "  pad  ".trimStart() + "][" + "  pad  ".trimEnd() + "]");
console.log(String("http://x".startsWith("//", 5)) + " " + "ab".concat("cd"));

const out = args[1] + "/out.txt";
writeFileSync(out, "first\n");
appendFileSync(out, "second\n");
console.log(String(existsSync(out)) + " " + String(existsSync(args[1] + "/missing")));
process.stderr.write("done\n");
process.exit(3);
