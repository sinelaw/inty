# Type Declarations and Soundness in Inty

This document outlines the design for supporting external type declarations (e.g., for the DOM, Node.js built-ins, or third-party libraries) in Inty, with a strict focus on maintaining type soundness within a Rank-1 polymorphic system.

## 1. The Core Problem: Soundness & Mutation

Inty uses a Hindley-Milner (Rank-1) type system. In such systems, giving a mutable variable a polymorphic type is unsound.

**Example of Unsoundness:**
```javascript
// Suppose we declare 'id' as polymorphic: ∀a. a -> a
var id /*: <T>(x: T) => T */; 

// Assignment instantiates 'T' to 'Number'
id = function(n) { return n + 1; }; 

// Call instantiates 'T' to 'String'
id("hello"); // Runtime Crash! Tried to add 1 to "hello"
```
Because `id` is a mutable variable (`var`), we can assign a specific implementation to it (instantiating it to `Number -> Number`). Later, we can use it as a different instantiation (`String -> String`). This violates type safety.

## 2. The Solution: Immutability (Const Declarations)

To ensure soundness, **declarations must be treated as immutable bindings**. If a variable cannot be reassigned, it cannot be specialized to a specific type after declaration, thus preserving the universal quantification of its type scheme.

### 2.1. Declaration Syntax
We support two forms of declarations. Both result in **read-only** bindings in the type environment.

**A. `const` Declarations (Recommended)**
Explicitly signals immutability.
```javascript
const document /*: { getElementById: (id: String) => Element } */;
```

**B. `var` Declarations (Legacy Compatibility)**
Standard `var` declarations **without initializers** and **with type annotations** are treated as `const` by the type checker.
```javascript
// Treated as const by Inty
var console /*: { log: (msg: String) => Undefined } */;
```

**Rule:** Attempting to assign to a declared variable (e.g., `console = ...`) results in a type error.

## 3. Module System (ES6)

Inty leverages standard ECMAScript modules for organizing declarations.

### 3.1. Imports are Immutable
ES6 module bindings are live read-only views. This aligns perfectly with our soundness requirement.

```javascript
// dom.d.js
/*: <T>(x: T) => T */
export const identity;

// main.js
import { identity } from "./dom.d.js";

identity(1);       // OK: Number -> Number
identity("hello"); // OK: String -> String
identity = 5;      // Error: Assignment to constant variable
```

### 3.2. Side-Effect Imports (Global Augmentation)
To load global declarations (like the DOM), use side-effect imports.

```javascript
// app.js
import "./dom.d.js"; // Loads 'document', 'window', etc. into global scope
```

## 4. Implementation Details

### 4.1. AST Extensions
*   **`Stmt::Import`**: Represents `import { x } from "mod"` and `import "mod"`.
*   **`Stmt::Export`**: Represents `export var ...` and `export const ...`.
*   **`VarKind`**: Distinguishes between `var` (mutable) and `const` (immutable).

### 4.2. Inference Logic
1.  **Declaration Handling**:
    *   When encountering `var x /*: T */` (no init) or `const x /*: T */`:
    *   Parse the annotation `T`.
    *   Generalize `T` to create a type scheme `∀.T`.
    *   Add `x` to the environment.
    *   **Crucial**: Mark the binding as `Immutable` in the environment.

2.  **Assignment Logic**:
    *   When inferring `x = e`:
    *   Lookup `x` in the environment.
    *   If `x` is marked `Immutable`, throw a `TypeError::AssignmentToConstant`.

3.  **Module Resolution**:
    *   Simple file-system based resolution relative to the current file.
    *   Recursive parsing of imported files to build their export environments.

## 5. Rank-1 Restriction

Inty uses Hindley-Milner type inference, which is only decidable for **Rank-1** polymorphism. Type annotations in declarations must conform to this restriction.

### 5.1. What is Rank-1?

In Rank-1 types, quantifiers (`<T>`) appear only at the **outermost level** of a type, never nested inside function parameter types.

**Allowed (Rank-1):**
```javascript
const identity /*: <T>(x: T) => T */;
const map /*: <A, B>(f: (a: A) => B, arr: A[]) => B[] */;
const pair /*: <T>(x: T, y: T) => [T, T] */;
```

**Rejected (Rank-2 or higher):**
```javascript
// ❌ Nested quantifier in parameter position
const apply /*: <A>(f: <T>(x: T) => T, a: A) => A */;
//                   ^^^^^^^^^^^^^^^^ quantifier inside argument type

// ❌ Higher-rank callback
const runST /*: <A>(action: <S>(st: State<S>) => A) => A */;
```

### 5.2. Why This Matters

| Property | Rank-1 | Rank-2+ |
|----------|--------|---------|
| Type inference | Decidable, finds principal type | Undecidable in general |
| Annotations | Optional (inferred) | Required at boundaries |
| Algorithm | Unification | Subsumption checking |

Allowing higher-rank types would break the guarantee that type inference always terminates with a most general type.

### 5.3. Parser Enforcement

The type annotation parser rejects higher-rank types at parse time:

```javascript
// Parser error: "Quantified types not allowed in parameter position"
const bad /*: <A>(f: <T>(x: T) => T, a: A) => A */;
```

## 6. Polymorphic Property Assignment

To maintain soundness, **assignment** to properties with polymorphic types is rejected. However, declaring and using such properties works as expected.

### 6.1. Declaration and Usage (Allowed)

```javascript
// ✅ Declare object with polymorphic method
const obj /*: { fn: <T>(x: T) => T, value: Number } */;

// ✅ Call the polymorphic method with different types
obj.fn(42);        // T = Number → returns Number
obj.fn("hello");   // T = String → returns String
obj.fn([1, 2, 3]); // T = Number[] → returns Number[]

// ✅ Read the property
var f = obj.fn;    // f gets instantiated type
f(true);           // Works fine
```

This is the primary use case: describing external APIs (DOM, Node.js, libraries) that genuinely have polymorphic behavior.

### 6.2. The Problem with Assignment

```javascript
const obj /*: { fn: <T>(x: T) => T } */;
obj.fn = (n) => n + 1;  // Assigns Number → Number
obj.fn("hello");        // Type says T → T, runtime crashes
```

Each read of `obj` instantiates fresh type variables, "forgetting" any assignments.

### 6.2. The Solution

When assigning to a property of an immutable binding, check if the property's type (in the uninstantiated scheme) contains any quantified type variables. If so, reject the assignment.

```javascript
const obj /*: { fn: <T>(x: T) => T, count: Number } */;

obj.fn = (x) => x;      // ❌ Error: Cannot assign to polymorphic property 'fn'
obj.count = 42;         // ✅ OK: 'count' is monomorphic (Number)
```

This preserves the invariant that polymorphic types accurately describe runtime behavior.

## 7. Summary

By enforcing immutability on all external type declarations, restricting to Rank-1 types, and preventing polymorphic property mutation, Inty maintains decidable type inference and type soundness while providing a standard, JavaScript-compatible syntax for typing external code.
