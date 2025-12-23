# Revisiting Infernu's Type System - a Safe Subset of JavaScript

Infernu is a type checker for JavaScript. It is unique in that a legal program is **valid JavaScript** without any transpilation needed. The type checker inferred types and checked them without any annotations or special syntax. I did plan to add type annotations via comments for readability and limiting polymorphism when desired, but I don't think I ever got to that.

## Introduction

Infernu employs a polymorphic, structural type system based on HMF (Hindley-Milner with first-class polymorphism) [Leijen 2008], extended with row-polymorphism for structural typing, simple type classes, and equi-recursive types. The system is designed to statically type check a subset of JavaScript without requiring explicit type annotations.

The key modifications from standard HMF include:
- **[Row polymorphism](https://en.wikipedia.org/wiki/Row_polymorphism)** for typing JavaScript objects structurally
- **Equi-recursive types** for handling self-referential structures and `this`
- **Type classes** (`Plus`, `Indexable`) for overloaded operators

## Disclaimer

This type system comes with NO WARRANTY. I'm not a computer scientist and am far from an expert in type theory. The definitions should be read as aspirationally correct but may contain mistakes.

## Types

Following HMF conventions, we distinguish between different categories of types:

```
σ ::= ∀α. σ | ρ                     (type schemes / polymorphic types)
ρ ::= τ | σ → σ | {r} | [σ] | Map σ (unquantified types)
τ ::= α | c                         (monomorphic types)
c ::= Number | String | Boolean | Regex | Undefined | Null  (primitive types)
r ::= l: σ, r | α | ∅               (row types)
```

- **Primitive Types**: `Number`, `String`, `Boolean`, `Regex`, `Undefined`, `Null`.
- **Type Variables**: `α, β, ...` represent unknown types to be determined by inference.
- **Function Types**: `σ₁ → σ₂`, or `(σ₁, σ₂, ..., σₙ) → σ` for multi-argument functions.
- **Row Types**: `{l₁: σ₁, l₂: σ₂, ..., lₙ: σₙ | ρ}` represent objects with properties `lᵢ` of type `σᵢ`. `ρ` is a row variable, making the row open for extension. A closed row has `∅` (empty) in place of `ρ`.
- **Type Constructors**: `[σ]` for arrays, `Map σ` for string-keyed maps.
- **Qualified Types**: `C α ⇒ σ` is a type `σ` constrained by predicate `C α`, where `C` is a type class.
- **Type Schemes**: `∀α₁, ..., αₙ. σ` is a polymorphic type with universally quantified type variables.

## Typing Judgments

The core of the type system is the typing judgment `Γ ⊢ e : σ`, read as: "In type environment `Γ`, expression `e` has type `σ`". The environment `Γ` maps variable names to type schemes.

We use standard notation:
- `ftv(σ)` denotes free type variables in `σ`
- `σ₁ ⊑ σ₂` denotes that `σ₁` is a generic instance of `σ₂` (i.e., `σ₂` is more general)
- `S` denotes a substitution mapping type variables to types
- `Sσ` denotes application of substitution `S` to type `σ`

### Literals

`Γ ⊢ lit : τ` where `τ` is the type of the literal.

- `Γ ⊢ n : Number` (for a number literal `n`)
- `Γ ⊢ s : String` (for a string literal `s`)
- etc. for other literals.

### Variables

```
       x : σ ∈ Γ
[VAR] ─────────────
       Γ ⊢ x : σ
```

Variables are looked up in the environment. Polymorphic types are instantiated via the [INST] rule when needed.

### Instantiation

```
        Γ ⊢ e : σ₂    σ₁ ⊑ σ₂
[INST] ────────────────────────
        Γ ⊢ e : σ₁
```

A polymorphic type can be instantiated to a more specific type. The instance relation `σ₁ ⊑ σ₂` holds when `σ₁` can be obtained from `σ₂` by substituting type variables with types. For example a polymorphic function can ba instantiated to a function over specific types.

### Generalization

```
        Γ ⊢ e : σ    α ∉ ftv(Γ)
[GEN]  ─────────────────────────
        Γ ⊢ e : ∀α. σ
```

A type can be generalized over type variables that do not occur free in the environment.

### Abstraction (Function Definition)

```
        τ is a fresh type variable
        Γ, x : τ ⊢ e : ρ
[FUN]  ──────────────────────
        Γ ⊢ λx.e : τ → ρ
```

A function parameter is assigned a fresh monomorphic type variable `τ`. The body must have an unquantified type `ρ` (quantifiers appear only at the outermost level after generalization). This restriction ensures principal types exist.

For multi-argument functions `(x₁, ..., xₙ) => e`:

```
         τ₁, ..., τₙ are fresh type variables
         Γ, x₁ : τ₁, ..., xₙ : τₙ ⊢ e : ρ
[FUN-N] ─────────────────────────────────────────
         Γ ⊢ (x₁, ..., xₙ) => e : (τ₁, ..., τₙ) → ρ
```

### Application (Function Call)

```
        Γ ⊢ e₁ : σ₂ → σ    Γ ⊢ e₂ : σ₂
[APP]  ─────────────────────────────────
        Γ ⊢ e₁ e₂ : σ
```

The argument type must match the parameter type exactly (after instantiation via [INST]). Note that in HMF, argument and parameter types can be polymorphic, enabling first-class polymorphism.

### Let Expressions

```
        Γ ⊢ e₁ : σ₁    Γ, x : σ₁ ⊢ e₂ : σ₂
[LET]  ─────────────────────────────────────
        Γ ⊢ let x = e₁ in e₂ : σ₂
```

where `σ₁` is the *most general* type derivable for `e₁`, i.e., for any `Γ ⊢ e₁ : σ'₁` we have `σ₁ ⊑ σ'₁`.

### Object Literals (Rows)

```
         Γ ⊢ e₁ : σ₁    ...    Γ ⊢ eₙ : σₙ
[OBJ]   ───────────────────────────────────────────────
         Γ ⊢ {l₁: e₁, ..., lₙ: eₙ} : {l₁: σ₁, ..., lₙ: σₙ | ∅}
```

Object literals produce closed row types (with `∅` as the row tail). Row unification allows a closed row `{l: σ | ∅}` to unify with an open row `{l: σ | ρ}` by unifying `ρ` with `∅`, enabling structural subtyping via row polymorphism.

### Property Access

```
          Γ ⊢ e : {l: σ | ρ}
[PROJ]   ─────────────────────
          Γ ⊢ e.l : σ
```

Property access requires the object to have a row type containing label `l`. The row variable `ρ` may contain additional fields, enabling access on objects with more properties than strictly required.

### Property Assignment

```
           Γ ⊢ eobj : {l: σ | ρ}    Γ ⊢ eval : σ    σ ∈ τ
[ASSIGN]  ──────────────────────────────────────────────────
           Γ ⊢ eobj.l = eval : σ
```

Property assignment requires the assigned value's type to match the property's type. The constraint `σ ∈ τ` (the *value restriction*) requires the type to be monomorphic—this prevents unsound interactions between mutation and polymorphism, analogous to ML's value restriction for references.

## Recursive Types

Infernu supports equi-recursive types, where two types are considered equivalent if their infinite unfoldings are identical. In an equi-recursive system, the types `μα. σ` and `σ[α := μα. σ]` are considered equal—no explicit fold/unfold operations are needed.

Recursive types arise during unification. When unifying a type variable `α` with a type `σ` that contains `α`, instead of failing the occurs check, the system creates an equi-recursive type:

```
         unify(α, σ) where α ∈ ftv(σ)
[EQREC] ──────────────────────────────
         α := μα. σ
```

For recursive let bindings (where the bound variable may appear in its own definition):

```
           α is fresh    Γ, x : α ⊢ e : σ    S = unify(α, σ)
[LET-REC] ─────────────────────────────────────────────────────
           Γ ⊢ let rec x = e : generalize(Γ, Sα)
```

If `α` occurs in `σ`, unification produces a cyclic substitution and `Sα` is an equi-recursive type.

**Example:** For `let x = { a: x }`:
1. Assign fresh `α` to `x`
2. Type the body: `{ a: x } : {a: α | ∅}`
3. Unify `α` with `{a: α | ∅}`, yielding `α := μα. {a: α | ∅}`
4. Result type: `μα. {a: α | ∅}`

Recursive types are essential for correctly typing many common JavaScript patterns, such as self-referential objects and methods that use `this`. When an object has a method that refers to `this`, the object's type is inherently recursive—the recursive type captures this self-referential nature.

## Type Classes

Type classes constrain polymorphic types, similar to Haskell's type classes. A qualified type `C α ⇒ σ` indicates that `σ` is valid only when `α` satisfies constraint `C`.

**`Plus α`**: Types supporting the `+` operator.
- Instances: `Plus Number`, `Plus String`

**`Indexable c i e`**: Container types with indexing.
- `c`: container type, `i`: index type, `e`: element type
- Instances:
  - `Indexable [α] Number α` (arrays indexed by number)
  - `Indexable (Map α) String α` (maps indexed by string)
  - `Indexable String Number String` (strings indexed by number)

For example, the `+` operator has type:

```
Plus α ⇒ (α, α) → α
```

This means `+` takes two arguments of the same type `α` and returns `α`, where `α` must satisfy `Plus` (i.e., be `Number` or `String`).

## JavaScript Idioms and Exclusions

Infernu's type system is designed to support many common JavaScript idioms while ensuring type safety.

### Supported Idioms

- **Object-Oriented Programming**:
  - **`this` keyword**: The type of `this` is inferred and correctly handled, even with its dynamic scoping rules.
  - **`new` keyword**: Constructor functions are supported. The type of a `new` expression is the type of `this` within the constructor.
  - **Methods**: Methods are properties of row types that have function types. Polymorphic methods are supported via rank-2 types for rows.
  - **Methods with `this` and Recursive Types**:
    Infernu accurately models methods that operate on their own object (`this`) using recursive types.
    Consider the following JavaScript example:
    ```javascript
    let counter = {
      count: 0,
      inc: function() {
        this.count = this.count + 1;
      }
    };
    ```
    The inferred type for `counter` is:
    ```
    μα. {count: Number, inc: α → Undefined | ∅}
    ```
    Breaking this down:
    - `count` has type `Number` (from initialization to `0`)
    - `inc` has type `α → Undefined`, where `α` is the type of `this` (the object itself)
    - Since `inc`'s parameter type refers to the enclosing object type, we get a recursive type `μα`

    This recursive type correctly captures that `this` within `inc` has the same type as the `counter` object itself.
  - **Prototypal Inheritance**: While not directly modeled, inheritance can be simulated through object composition and row polymorphism.

- **Functional Programming**:
  - **Higher-Order Functions**: Functions as first-class citizens are naturally supported.
  - **Closures**: The type system correctly infers the types of variables in closures.

- **Structural Typing**:
  - Row polymorphism allows for "duck typing" in a statically typed way. A function that expects an object with a certain property can be called with any object that has that property, regardless of its other properties.

### Excluded Code

To ensure static type safety, Infernu excludes some of JavaScript's more dynamic and unsafe features:

- **Implicit Type Coercion**: Expressions like `3 + 'a'` are disallowed. The `Plus` type class requires both operands to be of the same type (either `Number` or `String`).
- **`eval()`**: Dynamic code evaluation is not supported.
- **Arbitrary Monkey-Patching**: While adding properties to objects is possible with open row types, modifying the type of an existing property is restricted.
- **Heterogeneous Arrays**: Arrays in Infernu must be homogeneous, meaning all elements must have the same type. JavaScript's ability to mix types in an array, like `[1, "hello", true]`, is not permitted.
- **`arguments` object**: The `arguments` object is not supported. All function arguments must be explicitly declared.

## Implementation

[Infernu](https://github.com/sinelaw/infernu) implements type inference of the above system, based on HMF. I can't say the implementation is clean, sound, or even correct (especially not 10 years after the fact). It did work pretty well over a wide variety of test programs.

## A note about TypeScript

TypeScript is commonly described as a **superset of JavaScript** in that any valid JavaScript code is theoretically also valid TypeScript. That's not exactly true because code that violates TypeScript's static typing rules triggers errors (depending on configuration), so there are many valid JavaScript programs which are not valid TypeScript programs. That being said TypeScript focuses on gradual typing and improved idioms and doesn't make as strong a statement about what parts of JavaScript are strictly excluded.

## What Next?

Back in 2015 - already 10 years ago - I built [Infernu](https://github.com/sinelaw/infernu), an experimental project to create static type checking, with type inference, for JavaScript. I started working on it before TypeScript was announced. The project was born from my frustrations while working on frontend code. As soon as I stopped working on frontend I essentially abandonded this effort to focus on other things.

At the time, TypeScript didn't exist yet, but today the situation is different - TypeScript has evolved a lot and is one of the most popular languages out there. Still, it's wildly different from what I had in mind for Infernu, which was a minimal, ML-style language and not the Java-style route taken by TypeScript. I think there's still room for something like this, maybe a re-implementation of this type system.

## References

- Luis Damas and Robin Milner. *Principal type-schemes for functional programs*. POPL 1982. The classic Hindley-Milner type inference.
- Mitchell Wand. [*Type Inference for Record Concatenation and Multiple Inheritance*](https://www.sciencedirect.com/science/article/pii/089054019190050C). Information and Computation, 1991. Row polymorphism for structural typing.
- Jacques Guarrigue and Didier Rémy. [*Semi-Explicit First-Class Polymorphism for ML*](https://caml.inria.fr/pub/papers/garrigue_remy-poly-ic99.pdf), Information and Computation 155, 13400169 (1999)
- Daan Leijen. [*HMF: Simple Type Inference for First-Class Polymorphism*](https://dl.acm.org/doi/10.1145/1411204.1411245). ICFP 2008. The basis for Infernu's type system.
