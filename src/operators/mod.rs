//! Static catalog of operator metadata.
//!
//! The catalog records, per operator: kind (binary / unary / pseudo),
//! the axis it dispatches on, and one or more *typing arms* that
//! describe the input/output shapes the typing rule accepts.
//!
//! It is **not** the primary input to typing. The actual typing logic
//! lives in `crate::infer::features::operators` (and in the dispatcher
//! arms for member access, indexing, call, and `new`). The catalog is
//! a *parallel description* of that logic. Phase 4's blame meta-test
//! cross-checks the two and reports disagreements.
//!
//! Where the catalog disagrees with the code, the **code** is the
//! source of behaviour. Adjust the catalog, or mark the arm with a
//! `notes` exemption that phase 4 skips.

use crate::parser::ast::{BinOp, UnaryOp};
use crate::types::ClassName;

/// Atomic types referenced by typing arms. A closed set distinct from
/// the full `Type` so that arms are trivially const-constructible and
/// the catalog can live in static memory.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum BaseType {
    Number,
    String,
    Boolean,
    Null,
    Undefined,
    Regex,
}

/// What kind of operator this is.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum OpKind {
    /// Binary infix operator (e.g. `+`, `<`, `&&`).
    BinOp,
    /// Unary operator (e.g. `-x`, `!x`, `typeof x`).
    UnOp,
    /// `obj.prop` member access.
    MemberAccess,
    /// `obj[expr]` indexed access.
    Index,
    /// `f(args)` function application.
    Call,
    /// `new C(args)` constructor application.
    New,
}

/// What axis the operator dispatches on.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Dispatch {
    /// Dispatch on argument type (e.g. `+` on `Number` vs `String`).
    ArgType,
    /// Dispatch on the operator symbol itself (each binop is its own
    /// rule, regardless of argument shape).
    OpSymbol,
    /// Single fixed arm regardless of arguments (e.g. `typeof`).
    Static,
}

/// The shape of an input or output position in a typing arm.
#[derive(Copy, Clone, Debug)]
pub enum TypeShape {
    /// A specific base type.
    Concrete(BaseType),
    /// "Same type as the input at index N." Used for equality and
    /// type-class arms whose output mirrors an input.
    SameAsArg(usize),
    /// Any type that's an instance of the given type-class.
    AnyOfClass(ClassName),
    /// Anything goes.
    Wildcard,
}

/// One arm of an operator's typing rule.
#[derive(Copy, Clone, Debug)]
pub struct TypingArm {
    pub inputs: &'static [TypeShape],
    pub output: TypeShape,
    /// Some(class) when the arm is mediated by a type class (e.g. Plus).
    pub class: Option<ClassName>,
    /// Free-text note. Non-empty notes mark arms phase 4 should skip
    /// blame-checking for: the typing rule has a side-condition the
    /// catalog can't express.
    pub notes: &'static str,
}

/// Metadata describing a single operator.
#[derive(Copy, Clone, Debug)]
pub struct OpInfo {
    pub name: &'static str,
    pub kind: OpKind,
    pub dispatch: Dispatch,
    pub arms: &'static [TypingArm],
}

// ---------------------------------------------------------------------
// Convenience aliases used by the static catalog tables below.
// ---------------------------------------------------------------------

use BaseType::*;
use TypeShape::{AnyOfClass, Concrete, SameAsArg, Wildcard};

const NUM_NUM_NUM: &[TypingArm] = &[TypingArm {
    inputs: &[Concrete(Number), Concrete(Number)],
    output: Concrete(Number),
    class: None,
    notes: "",
}];

const NUM_NUM: &[TypingArm] = &[TypingArm {
    inputs: &[Concrete(Number)],
    output: Concrete(Number),
    class: None,
    notes: "",
}];

const ANY_BOOL: &[TypingArm] = &[TypingArm {
    inputs: &[Wildcard],
    output: Concrete(Boolean),
    class: None,
    notes: "",
}];

const ANY_STRING: &[TypingArm] = &[TypingArm {
    inputs: &[Wildcard],
    output: Concrete(String),
    class: None,
    notes: "",
}];

const ANY_UNDEF: &[TypingArm] = &[TypingArm {
    inputs: &[Wildcard],
    output: Concrete(Undefined),
    class: None,
    notes: "",
}];

const PLUS_ARMS: &[TypingArm] = &[
    TypingArm {
        inputs: &[Concrete(Number), Concrete(Number)],
        output: Concrete(Number),
        class: None,
        notes: "",
    },
    TypingArm {
        inputs: &[Concrete(String), Concrete(String)],
        output: Concrete(String),
        class: None,
        notes: "",
    },
    TypingArm {
        inputs: &[
            AnyOfClass(ClassName::Plus),
            AnyOfClass(ClassName::Plus),
        ],
        output: SameAsArg(0),
        class: Some(ClassName::Plus),
        notes: "",
    },
];

const COMPARE_ARMS: &[TypingArm] = &[TypingArm {
    inputs: &[SameAsArg(1), SameAsArg(0)],
    output: Concrete(Boolean),
    class: None,
    notes: "operands are unified, no per-type arm enumerated",
}];

const STRICT_EQ_ARMS: &[TypingArm] = &[TypingArm {
    inputs: &[Wildcard, SameAsArg(0)],
    output: Concrete(Boolean),
    class: None,
    notes: "",
}];

const LOOSE_EQ_ARMS: &[TypingArm] = &[TypingArm {
    inputs: &[Wildcard, Wildcard],
    output: Concrete(Boolean),
    class: None,
    notes: "minfern's typing for `==` does not coerce; runtime does",
}];

const LOGICAL_ARMS: &[TypingArm] = &[TypingArm {
    inputs: &[SameAsArg(1), SameAsArg(0)],
    output: SameAsArg(0),
    class: None,
    notes: "operands unified; result is one of them",
}];

const MEMBERSHIP_ARMS: &[TypingArm] = &[TypingArm {
    inputs: &[Wildcard, Wildcard],
    output: Concrete(Boolean),
    class: None,
    notes: "membership/instanceof: no input shape constraint at typing",
}];

const MEMBER_ACCESS_ARMS: &[TypingArm] = &[TypingArm {
    inputs: &[Wildcard],
    output: Wildcard,
    class: None,
    notes: "row/array/string/promise dispatch; result depends on prop",
}];

const INDEX_ARMS: &[TypingArm] = &[
    TypingArm {
        inputs: &[Wildcard, Concrete(Number)],
        output: Wildcard,
        class: None,
        notes: "Array<T>[Number] -> T; String[Number] -> String",
    },
    TypingArm {
        inputs: &[Wildcard, Concrete(String)],
        output: Wildcard,
        class: None,
        notes: "Map<T>[String] -> T; Row[String] via Indexable class",
    },
    TypingArm {
        inputs: &[
            AnyOfClass(ClassName::Indexable),
            AnyOfClass(ClassName::Indexable),
        ],
        output: AnyOfClass(ClassName::Indexable),
        class: Some(ClassName::Indexable),
        notes: "deferred to constraint solver for type vars",
    },
];

const CALL_ARMS: &[TypingArm] = &[TypingArm {
    inputs: &[Wildcard],
    output: Wildcard,
    class: None,
    notes: "dispatcher unifies callee with `func(this, args) -> ret`",
}];

const NEW_ARMS: &[TypingArm] = &[TypingArm {
    inputs: &[Wildcard],
    output: Wildcard,
    class: None,
    notes: "constructor: result becomes `this`",
}];

const AWAIT_ARMS: &[TypingArm] = &[TypingArm {
    inputs: &[Wildcard],
    output: Wildcard,
    class: None,
    notes: "unwraps Promise<T>; phase 3 models await as identity",
}];

// ---------------------------------------------------------------------
// The catalog.
// ---------------------------------------------------------------------

/// Every operator minfern knows about, in a stable order.
pub static OPERATORS: &[OpInfo] = &[
    // --- Arithmetic --------------------------------------------------
    OpInfo {
        name: "+",
        kind: OpKind::BinOp,
        dispatch: Dispatch::ArgType,
        arms: PLUS_ARMS,
    },
    OpInfo {
        name: "-",
        kind: OpKind::BinOp,
        dispatch: Dispatch::OpSymbol,
        arms: NUM_NUM_NUM,
    },
    OpInfo {
        name: "*",
        kind: OpKind::BinOp,
        dispatch: Dispatch::OpSymbol,
        arms: NUM_NUM_NUM,
    },
    OpInfo {
        name: "/",
        kind: OpKind::BinOp,
        dispatch: Dispatch::OpSymbol,
        arms: NUM_NUM_NUM,
    },
    OpInfo {
        name: "%",
        kind: OpKind::BinOp,
        dispatch: Dispatch::OpSymbol,
        arms: NUM_NUM_NUM,
    },
    OpInfo {
        name: "**",
        kind: OpKind::BinOp,
        dispatch: Dispatch::OpSymbol,
        arms: NUM_NUM_NUM,
    },
    // --- Comparison --------------------------------------------------
    OpInfo {
        name: "<",
        kind: OpKind::BinOp,
        dispatch: Dispatch::OpSymbol,
        arms: COMPARE_ARMS,
    },
    OpInfo {
        name: ">",
        kind: OpKind::BinOp,
        dispatch: Dispatch::OpSymbol,
        arms: COMPARE_ARMS,
    },
    OpInfo {
        name: "<=",
        kind: OpKind::BinOp,
        dispatch: Dispatch::OpSymbol,
        arms: COMPARE_ARMS,
    },
    OpInfo {
        name: ">=",
        kind: OpKind::BinOp,
        dispatch: Dispatch::OpSymbol,
        arms: COMPARE_ARMS,
    },
    OpInfo {
        name: "==",
        kind: OpKind::BinOp,
        dispatch: Dispatch::OpSymbol,
        arms: LOOSE_EQ_ARMS,
    },
    OpInfo {
        name: "!=",
        kind: OpKind::BinOp,
        dispatch: Dispatch::OpSymbol,
        arms: LOOSE_EQ_ARMS,
    },
    OpInfo {
        name: "===",
        kind: OpKind::BinOp,
        dispatch: Dispatch::OpSymbol,
        arms: STRICT_EQ_ARMS,
    },
    OpInfo {
        name: "!==",
        kind: OpKind::BinOp,
        dispatch: Dispatch::OpSymbol,
        arms: STRICT_EQ_ARMS,
    },
    // --- Logical -----------------------------------------------------
    OpInfo {
        name: "&&",
        kind: OpKind::BinOp,
        dispatch: Dispatch::OpSymbol,
        arms: LOGICAL_ARMS,
    },
    OpInfo {
        name: "||",
        kind: OpKind::BinOp,
        dispatch: Dispatch::OpSymbol,
        arms: LOGICAL_ARMS,
    },
    // --- Bitwise -----------------------------------------------------
    OpInfo {
        name: "&",
        kind: OpKind::BinOp,
        dispatch: Dispatch::OpSymbol,
        arms: NUM_NUM_NUM,
    },
    OpInfo {
        name: "|",
        kind: OpKind::BinOp,
        dispatch: Dispatch::OpSymbol,
        arms: NUM_NUM_NUM,
    },
    OpInfo {
        name: "^",
        kind: OpKind::BinOp,
        dispatch: Dispatch::OpSymbol,
        arms: NUM_NUM_NUM,
    },
    OpInfo {
        name: "<<",
        kind: OpKind::BinOp,
        dispatch: Dispatch::OpSymbol,
        arms: NUM_NUM_NUM,
    },
    OpInfo {
        name: ">>",
        kind: OpKind::BinOp,
        dispatch: Dispatch::OpSymbol,
        arms: NUM_NUM_NUM,
    },
    OpInfo {
        name: ">>>",
        kind: OpKind::BinOp,
        dispatch: Dispatch::OpSymbol,
        arms: NUM_NUM_NUM,
    },
    // --- Membership --------------------------------------------------
    OpInfo {
        name: "in",
        kind: OpKind::BinOp,
        dispatch: Dispatch::OpSymbol,
        arms: MEMBERSHIP_ARMS,
    },
    OpInfo {
        name: "instanceof",
        kind: OpKind::BinOp,
        dispatch: Dispatch::OpSymbol,
        arms: MEMBERSHIP_ARMS,
    },
    // --- Unary -------------------------------------------------------
    OpInfo {
        name: "unary -",
        kind: OpKind::UnOp,
        dispatch: Dispatch::OpSymbol,
        arms: NUM_NUM,
    },
    OpInfo {
        name: "unary +",
        kind: OpKind::UnOp,
        dispatch: Dispatch::OpSymbol,
        arms: NUM_NUM,
    },
    OpInfo {
        name: "!",
        kind: OpKind::UnOp,
        dispatch: Dispatch::Static,
        arms: ANY_BOOL,
    },
    OpInfo {
        name: "~",
        kind: OpKind::UnOp,
        dispatch: Dispatch::OpSymbol,
        arms: NUM_NUM,
    },
    OpInfo {
        name: "typeof",
        kind: OpKind::UnOp,
        dispatch: Dispatch::Static,
        arms: ANY_STRING,
    },
    OpInfo {
        name: "void",
        kind: OpKind::UnOp,
        dispatch: Dispatch::Static,
        arms: ANY_UNDEF,
    },
    OpInfo {
        name: "delete",
        kind: OpKind::UnOp,
        dispatch: Dispatch::Static,
        arms: ANY_BOOL,
    },
    OpInfo {
        name: "await",
        kind: OpKind::UnOp,
        dispatch: Dispatch::Static,
        arms: AWAIT_ARMS,
    },
    OpInfo {
        name: "++ (prefix)",
        kind: OpKind::UnOp,
        dispatch: Dispatch::OpSymbol,
        arms: NUM_NUM,
    },
    OpInfo {
        name: "-- (prefix)",
        kind: OpKind::UnOp,
        dispatch: Dispatch::OpSymbol,
        arms: NUM_NUM,
    },
    OpInfo {
        name: "++ (postfix)",
        kind: OpKind::UnOp,
        dispatch: Dispatch::OpSymbol,
        arms: NUM_NUM,
    },
    OpInfo {
        name: "-- (postfix)",
        kind: OpKind::UnOp,
        dispatch: Dispatch::OpSymbol,
        arms: NUM_NUM,
    },
    // --- Pseudo-operators -------------------------------------------
    OpInfo {
        name: ".",
        kind: OpKind::MemberAccess,
        dispatch: Dispatch::ArgType,
        arms: MEMBER_ACCESS_ARMS,
    },
    OpInfo {
        name: "[]",
        kind: OpKind::Index,
        dispatch: Dispatch::ArgType,
        arms: INDEX_ARMS,
    },
    OpInfo {
        name: "()",
        kind: OpKind::Call,
        dispatch: Dispatch::ArgType,
        arms: CALL_ARMS,
    },
    OpInfo {
        name: "new",
        kind: OpKind::New,
        dispatch: Dispatch::ArgType,
        arms: NEW_ARMS,
    },
];

/// Look up the catalog entry for an operator by its catalog name.
pub fn lookup(name: &str) -> Option<&'static OpInfo> {
    OPERATORS.iter().find(|op| op.name == name)
}

/// Map a `BinOp` to its catalog name.
pub fn binop_name(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Mod => "%",
        BinOp::Pow => "**",
        BinOp::Lt => "<",
        BinOp::Gt => ">",
        BinOp::LtEq => "<=",
        BinOp::GtEq => ">=",
        BinOp::EqEq => "==",
        BinOp::NotEq => "!=",
        BinOp::EqEqEq => "===",
        BinOp::NotEqEq => "!==",
        BinOp::And => "&&",
        BinOp::Or => "||",
        BinOp::BitAnd => "&",
        BinOp::BitOr => "|",
        BinOp::BitXor => "^",
        BinOp::LShift => "<<",
        BinOp::RShift => ">>",
        BinOp::URShift => ">>>",
        BinOp::In => "in",
        BinOp::Instanceof => "instanceof",
    }
}

/// Map a `UnaryOp` to its catalog name.
pub fn unaryop_name(op: UnaryOp) -> &'static str {
    match op {
        UnaryOp::Neg => "unary -",
        UnaryOp::Pos => "unary +",
        UnaryOp::Not => "!",
        UnaryOp::BitNot => "~",
        UnaryOp::Typeof => "typeof",
        UnaryOp::Void => "void",
        UnaryOp::Delete => "delete",
        UnaryOp::Await => "await",
        UnaryOp::PreInc => "++ (prefix)",
        UnaryOp::PreDec => "-- (prefix)",
        UnaryOp::PostInc => "++ (postfix)",
        UnaryOp::PostDec => "-- (postfix)",
    }
}

#[cfg(test)]
mod tests;
