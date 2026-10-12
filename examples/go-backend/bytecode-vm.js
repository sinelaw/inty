// A tiny stack-based bytecode interpreter — the heart of template
// engines, rule engines, emulators and scripting runtimes. It runs a
// compiled program that counts primes below a bound by trial division.
const PUSH = 0;
const LOAD = 1;
const STORE = 2;
const ADD = 3;
const SUB = 4;
const MUL = 5;
const MOD = 6;
const LT = 7;
const JMP = 8;
const JZ = 9;
const EQ = 10;
const HALT = 11;
const LE = 12;

// A one-pass assembler with back-patching for forward jumps.
/** function emit(Number[], Number, Number) => Number */
function emit(code, op, arg) {
  code.push(op);
  code.push(arg);
  return code.length - 2;
}
/** function patch(Number[], Number, Number) => Undefined */
function patch(code, at, target) {
  code[at + 1] = target;
}

const code = [];
// vars: 0 = n, 1 = count, 2 = d, 3 = isPrime, 4 = limit
const LIMIT = 200000;
emit(code, PUSH, LIMIT);
emit(code, STORE, 4);
emit(code, PUSH, 2);
emit(code, STORE, 0);
emit(code, PUSH, 0);
emit(code, STORE, 1);
const outerTop = code.length;
emit(code, LOAD, 0);
emit(code, LOAD, 4);
emit(code, LT, 0);
const exitJump = emit(code, JZ, 0);
emit(code, PUSH, 1);
emit(code, STORE, 3);
emit(code, PUSH, 2);
emit(code, STORE, 2);
const innerTop = code.length;
emit(code, LOAD, 2);
emit(code, LOAD, 2);
emit(code, MUL, 0);
emit(code, LOAD, 0);
emit(code, LE, 0);
const innerExit = emit(code, JZ, 0);
emit(code, LOAD, 0);
emit(code, LOAD, 2);
emit(code, MOD, 0);
emit(code, PUSH, 0);
emit(code, EQ, 0);
const notDivisible = emit(code, JZ, 0);
emit(code, PUSH, 0);
emit(code, STORE, 3);
const breakJump = emit(code, JMP, 0);
patch(code, notDivisible, code.length);
emit(code, LOAD, 2);
emit(code, PUSH, 1);
emit(code, ADD, 0);
emit(code, STORE, 2);
emit(code, JMP, innerTop);
patch(code, innerExit, code.length);
patch(code, breakJump, code.length);
emit(code, LOAD, 1);
emit(code, LOAD, 3);
emit(code, ADD, 0);
emit(code, STORE, 1);
emit(code, LOAD, 0);
emit(code, PUSH, 1);
emit(code, ADD, 0);
emit(code, STORE, 0);
emit(code, JMP, outerTop);
patch(code, exitJump, code.length);
emit(code, HALT, 0);

/** function run(Number[], Number[], Number[]) => Number */
function run(program, stack, vars) {
  let pc = 0;
  let sp = 0;
  let steps = 0;
  while (true) {
    const op = program[pc];
    const arg = program[pc + 1];
    pc += 2;
    steps++;
    switch (op) {
      case PUSH:
        stack[sp] = arg;
        sp++;
        break;
      case LOAD:
        stack[sp] = vars[arg];
        sp++;
        break;
      case STORE:
        sp--;
        vars[arg] = stack[sp];
        break;
      case ADD:
        sp--;
        stack[sp - 1] = stack[sp - 1] + stack[sp];
        break;
      case SUB:
        sp--;
        stack[sp - 1] = stack[sp - 1] - stack[sp];
        break;
      case MUL:
        sp--;
        stack[sp - 1] = stack[sp - 1] * stack[sp];
        break;
      case MOD:
        sp--;
        stack[sp - 1] = stack[sp - 1] % stack[sp];
        break;
      case LT:
        sp--;
        stack[sp - 1] = stack[sp - 1] < stack[sp] ? 1 : 0;
        break;
      case LE:
        sp--;
        stack[sp - 1] = stack[sp - 1] <= stack[sp] ? 1 : 0;
        break;
      case EQ:
        sp--;
        stack[sp - 1] = stack[sp - 1] === stack[sp] ? 1 : 0;
        break;
      case JMP:
        pc = arg;
        break;
      case JZ:
        sp--;
        if (stack[sp] === 0) {
          pc = arg;
        }
        break;
      default:
        return steps;
    }
  }
}

function main() {
  const lines = [];
  const stack = [];
  const vars = [];
  for (let i = 0; i < 16; i++) {
    stack.push(0);
    vars.push(0);
  }
  let steps = 0;
  for (let round = 0; round < 1; round++) {
    steps += run(code, stack, vars);
  }
  lines.push(`primes below ${LIMIT}: ${vars[1]} (${steps} instructions executed)`);
  return lines.join("\n");
}

// ---- benchmark protocol (see bench.mjs) ------------------------------
// Run the workload 4 times in one process. The first run includes JIT
// warm-up; bench.mjs reports the other three as steady-state samples.
let report = "";
for (let iteration = 0; iteration < 4; iteration++) {
  const t0 = performance.now();
  report = main();
  console.error(`inty-bench iteration ${iteration} ms ${performance.now() - t0}`);
}
console.log(report);
