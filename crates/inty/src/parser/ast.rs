//! Abstract Syntax Tree definitions for mquickjs.

use crate::lexer::Span;

/// One function/method parameter, with its source span.
///
/// The span covers the parameter name as it appears in the source.
/// Pattern parameters (destructuring) are desugared by the parser into
/// a fresh temp name plus a destructuring `var` statement at the start
/// of the body; the temp's span anchors at the pattern's location.
#[derive(Debug, Clone)]
pub struct Param {
    pub name: String,
    pub span: Span,
}

impl Param {
    pub fn new(name: impl Into<String>, span: Span) -> Self {
        Param { name: name.into(), span }
    }
}

/// Variable declaration kind.
///
/// `Var` and `Let` share the same type-system semantics in mquickjs
/// (both mutable, neither has a TDZ at the type-checker level), but
/// they differ in scoping: `Var` is function-scoped and hoisted, while
/// `Let` is block-scoped. The parser preserves the distinction so the
/// resolver can emit accurate go-to-def / rename / find-references.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VarKind {
    /// Mutable variable declaration: `var x = …`
    Var,
    /// Mutable block-scoped declaration: `let x = …`
    Let,
    /// Immutable constant declaration: `const x = …`
    Const,
}

/// Import specifier for named imports
#[derive(Debug, Clone)]
pub enum ImportSpecifier {
    /// Named import: `{ foo }` or `{ foo as bar }`
    Named {
        imported: String,
        local: String,
        span: Source,
    },
    /// Default import: `import foo from "mod"`
    Default { local: String, span: Source },
    /// Namespace import: `import * as foo from "mod"`
    Namespace { local: String, span: Source },
}

/// Export declaration
#[derive(Debug, Clone)]
pub enum ExportDecl {
    /// Named export with variable declarations: `export const x;` or `export var x = 1;`
    Var {
        kind: VarKind,
        declarations: Vec<VarDeclarator>,
        span: Source,
    },
    /// Function export: `export function foo() {}`
    Function {
        name: String,
        params: Vec<Param>,
        body: Box<Stmt>,
        type_annotation: Option<TypeAnnotation>,
        span: Source,
    },
    /// Default export: `export default expr;` or `export default function f() {}`.
    /// A named function expression also binds its name in module scope, matching JS.
    Default { value: Expr, span: Source },
    /// Export list: `export { a, b as c };` — re-binds existing locals under
    /// (possibly renamed) export names without introducing new declarations.
    /// `default` is permitted as the local or exported name to interoperate
    /// with `export default`.
    List {
        specifiers: Vec<ExportSpecifier>,
        span: Source,
    },
    /// Re-export from another module:
    /// - `Named`: `export { a, b as c } from "./mod.js";`
    /// - `All`: `export * from "./mod.js";` (all named exports, excludes default)
    /// - `AllAs`: `export * as ns from "./mod.js";` (target's namespace under one name)
    From {
        kind: ExportFromKind,
        source: String,
        span: Source,
    },
}

/// One entry of an `export { … }` clause.
#[derive(Debug, Clone)]
pub struct ExportSpecifier {
    /// The local binding being exported.
    pub local: String,
    /// The name under which it's exported (== `local` when not renamed).
    pub exported: String,
    pub span: Source,
}

/// Shape of a re-export's binding clause.
#[derive(Debug, Clone)]
pub enum ExportFromKind {
    /// `export { foo, bar as baz } from "./mod.js";`
    /// Each spec's `local` is the name in the *target* module; `exported`
    /// is the name in *this* module.
    Named(Vec<ExportSpecifier>),
    /// `export * from "./mod.js";` — re-export every named export of the
    /// target (excluding its `default`, per ESM spec).
    All,
    /// `export * as ns from "./mod.js";` — bind the target's whole
    /// namespace under one new export name.
    AllAs(String),
}

/// Source location type alias
pub type Source = Span;

/// A node with source location information
#[derive(Debug, Clone)]
pub struct Located<T> {
    pub node: T,
    pub span: Source,
}

impl<T> Located<T> {
    pub fn new(node: T, span: Source) -> Self {
        Self { node, span }
    }
}

/// A program is a sequence of statements
#[derive(Debug, Clone)]
pub struct Program {
    pub statements: Vec<Stmt>,
    pub span: Source,
}

/// Literal values
#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    Null,
    Undefined,
    Boolean(bool),
    Number(f64),
    String(String),
    Regex { pattern: String, flags: String },
}

/// Binary operators
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    // Arithmetic
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Pow, // **

    // Comparison
    Lt,
    Gt,
    LtEq,
    GtEq,
    EqEq,
    NotEq,
    EqEqEq,
    NotEqEq,

    // Logical
    And,
    Or,

    // Bitwise
    BitAnd,
    BitOr,
    BitXor,
    LShift,
    RShift,
    URShift,

    // Membership
    In,
    Instanceof,
}

impl BinOp {
    /// Get the precedence of this operator (higher = binds tighter)
    pub fn precedence(self) -> u8 {
        match self {
            BinOp::Or => 4,
            BinOp::And => 5,
            BinOp::BitOr => 6,
            BinOp::BitXor => 7,
            BinOp::BitAnd => 8,
            BinOp::EqEq | BinOp::NotEq | BinOp::EqEqEq | BinOp::NotEqEq => 9,
            BinOp::Lt | BinOp::Gt | BinOp::LtEq | BinOp::GtEq | BinOp::In | BinOp::Instanceof => 10,
            BinOp::LShift | BinOp::RShift | BinOp::URShift => 11,
            BinOp::Add | BinOp::Sub => 12,
            BinOp::Mul | BinOp::Div | BinOp::Mod => 13,
            BinOp::Pow => 14, // ** is highest precedence among binary ops
        }
    }

    /// Check if operator is right-associative
    pub fn is_right_assoc(self) -> bool {
        // ** is the only right-associative binary operator in JavaScript
        matches!(self, BinOp::Pow)
    }
}

/// Unary operators
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    // Prefix
    Neg,    // -
    Pos,    // +
    Not,    // !
    BitNot, // ~
    Typeof, // typeof
    Void,   // void
    Delete, // delete
    Await,  // await

    // Pre/Post increment/decrement
    PreInc,  // ++x
    PreDec,  // --x
    PostInc, // x++
    PostDec, // x--
}

/// Assignment operators
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssignOp {
    Assign,        // =
    AddAssign,     // +=
    SubAssign,     // -=
    MulAssign,     // *=
    PowAssign,     // **=
    DivAssign,     // /=
    ModAssign,     // %=
    LShiftAssign,  // <<=
    RShiftAssign,  // >>=
    URShiftAssign, // >>>=
    BitAndAssign,  // &=
    BitOrAssign,   // |=
    BitXorAssign,  // ^=
}

/// Property key in object literals
#[derive(Debug, Clone, PartialEq)]
pub enum PropKey {
    Ident(String),
    String(String),
    Number(f64),
}

/// Object property definition
#[derive(Debug, Clone)]
pub enum PropDef {
    /// Regular property: key: value, or `key /*: T */: value` with a
    /// per-field type annotation that constrains the value.
    Property {
        key: PropKey,
        value: Expr,
        /// Inline annotation sitting between `key` and the colon.
        /// When present, inference unifies the value's type with the
        /// annotated type and records the property at that type.
        type_annotation: Option<TypeAnnotation>,
        span: Source,
    },
    /// Getter: get key() { ... }
    Getter {
        key: PropKey,
        body: Box<Stmt>,
        span: Source,
    },
    /// Setter: set key(param) { ... }
    Setter {
        key: PropKey,
        param: String,
        body: Box<Stmt>,
        span: Source,
    },
    /// Method shorthand: key() { ... }
    Method {
        key: PropKey,
        params: Vec<Param>,
        body: Box<Stmt>,
        span: Source,
    },
}

/// Type annotation from comments: /** name: Type */
#[derive(Debug, Clone)]
pub struct TypeAnnotation {
    pub name: String,
    pub content: String,
    pub span: Source,
}

/// Expression AST node
#[derive(Debug, Clone)]
pub enum Expr {
    /// Literal value
    Lit { value: Literal, span: Source },

    /// Variable reference
    Ident { name: String, span: Source },

    /// `this` keyword
    This { span: Source },

    /// Array literal: [a, b, c]
    Array {
        elements: Vec<Option<Expr>>, // None for holes like [1,,3]
        span: Source,
    },

    /// Object literal: {a: 1, b: 2}
    Object {
        properties: Vec<PropDef>,
        span: Source,
    },

    /// Function expression: function(a, b) { ... }
    Function {
        name: Option<String>,
        params: Vec<Param>,
        body: Box<Stmt>,
        type_annotation: Option<TypeAnnotation>,
        span: Source,
    },

    /// Property access: obj.prop
    Member {
        object: Box<Expr>,
        property: String,
        span: Source,
    },

    /// Computed property access: obj[expr]
    ComputedMember {
        object: Box<Expr>,
        property: Box<Expr>,
        span: Source,
    },

    /// Function call: func(a, b)
    Call {
        callee: Box<Expr>,
        arguments: Vec<Expr>,
        span: Source,
    },

    /// New expression: new Ctor(a, b)
    New {
        callee: Box<Expr>,
        arguments: Vec<Expr>,
        span: Source,
    },

    /// new.target
    NewTarget { span: Source },

    /// Unary operation: -x, !x, typeof x
    Unary {
        op: UnaryOp,
        argument: Box<Expr>,
        span: Source,
    },

    /// Binary operation: a + b
    Binary {
        op: BinOp,
        left: Box<Expr>,
        right: Box<Expr>,
        span: Source,
    },

    /// Assignment: a = b, a += b
    Assign {
        op: AssignOp,
        left: Box<Expr>,
        right: Box<Expr>,
        span: Source,
    },

    /// Conditional: a ? b : c
    Conditional {
        test: Box<Expr>,
        consequent: Box<Expr>,
        alternate: Box<Expr>,
        span: Source,
    },

    /// Sequence: a, b, c
    Sequence {
        expressions: Vec<Expr>,
        span: Source,
    },

    /// Template literal: `hello ${name}!`
    TemplateLiteral {
        /// The string parts (quasis) - always one more than expressions
        quasis: Vec<String>,
        /// The interpolated expressions
        expressions: Vec<Expr>,
        span: Source,
    },
}

impl Expr {
    /// Get the source span for this expression
    pub fn span(&self) -> Source {
        match self {
            Expr::Lit { span, .. } => *span,
            Expr::Ident { span, .. } => *span,
            Expr::This { span } => *span,
            Expr::Array { span, .. } => *span,
            Expr::Object { span, .. } => *span,
            Expr::Function { span, .. } => *span,
            Expr::Member { span, .. } => *span,
            Expr::ComputedMember { span, .. } => *span,
            Expr::Call { span, .. } => *span,
            Expr::New { span, .. } => *span,
            Expr::NewTarget { span } => *span,
            Expr::Unary { span, .. } => *span,
            Expr::Binary { span, .. } => *span,
            Expr::Assign { span, .. } => *span,
            Expr::Conditional { span, .. } => *span,
            Expr::Sequence { span, .. } => *span,
            Expr::TemplateLiteral { span, .. } => *span,
        }
    }

    /// Check if this expression is a valid assignment target
    pub fn is_valid_assignment_target(&self) -> bool {
        matches!(
            self,
            Expr::Ident { .. } | Expr::Member { .. } | Expr::ComputedMember { .. }
        )
    }
}

/// For loop initializer
#[derive(Debug, Clone)]
pub enum ForInit {
    /// var i = 0
    VarDecl(Vec<VarDeclarator>),
    /// i = 0
    Expr(Expr),
}

/// Variable declarator: name = init
#[derive(Debug, Clone)]
pub struct VarDeclarator {
    pub name: String,
    pub init: Option<Expr>,
    pub type_annotation: Option<TypeAnnotation>,
    pub kind: VarKind,
    pub span: Source,
}

/// Left-hand side of for-in/of
#[derive(Debug, Clone)]
pub enum ForInLhs {
    /// var x
    VarDecl(String, Option<TypeAnnotation>, Span),
    /// x (existing variable)
    Expr(Expr),
}

/// Catch clause
#[derive(Debug, Clone)]
pub struct CatchClause {
    pub param: String,
    pub body: Box<Stmt>,
    pub span: Source,
}

/// Switch case
#[derive(Debug, Clone)]
pub struct SwitchCase {
    /// None for default case
    pub test: Option<Expr>,
    pub consequent: Vec<Stmt>,
    pub span: Source,
}

/// Statement AST node
#[derive(Debug, Clone)]
pub enum Stmt {
    /// Block: { stmt; stmt; }
    Block { body: Vec<Stmt>, span: Source },

    /// Empty statement: ;
    Empty { span: Source },

    /// Expression statement: expr;
    Expr { expression: Expr, span: Source },

    /// Variable declaration: var a = 1, b = 2; or const a = 1;
    Var {
        kind: VarKind,
        declarations: Vec<VarDeclarator>,
        span: Source,
    },

    /// Import declaration: import { x } from "mod" or import "mod"
    Import {
        specifiers: Vec<ImportSpecifier>,
        source: String,
        span: Source,
    },

    /// Export declaration: export const x; or export function foo() {}
    Export {
        declaration: ExportDecl,
        span: Source,
    },

    /// If statement: if (cond) { } else { }
    If {
        test: Expr,
        consequent: Box<Stmt>,
        alternate: Option<Box<Stmt>>,
        span: Source,
    },

    /// While loop: while (cond) { }
    While {
        test: Expr,
        body: Box<Stmt>,
        span: Source,
    },

    /// Do-while loop: do { } while (cond)
    DoWhile {
        body: Box<Stmt>,
        test: Expr,
        span: Source,
    },

    /// For loop: for (init; test; update) { }
    For {
        init: Option<ForInit>,
        test: Option<Expr>,
        update: Option<Expr>,
        body: Box<Stmt>,
        span: Source,
    },

    /// For-in loop: for (x in obj) { }
    ForIn {
        left: ForInLhs,
        right: Expr,
        body: Box<Stmt>,
        span: Source,
    },

    /// For-of loop: for (x of iter) { }
    ForOf {
        left: ForInLhs,
        right: Expr,
        body: Box<Stmt>,
        span: Source,
    },

    /// Break statement: break [label];
    Break { label: Option<String>, span: Source },

    /// Continue statement: continue [label];
    Continue { label: Option<String>, span: Source },

    /// Return statement: return [expr];
    Return {
        argument: Option<Expr>,
        span: Source,
    },

    /// Throw statement: throw expr;
    Throw { argument: Expr, span: Source },

    /// Try statement: try { } catch (e) { } finally { }
    Try {
        block: Box<Stmt>,
        handler: Option<CatchClause>,
        finalizer: Option<Box<Stmt>>,
        span: Source,
    },

    /// Switch statement: switch (expr) { case: ... }
    Switch {
        discriminant: Expr,
        cases: Vec<SwitchCase>,
        span: Source,
    },

    /// Labeled statement: label: stmt
    Labeled {
        label: String,
        body: Box<Stmt>,
        span: Source,
    },

    /// Function declaration: function name(params) { }
    FunctionDecl {
        name: String,
        params: Vec<Param>,
        body: Box<Stmt>,
        type_annotation: Option<TypeAnnotation>,
        span: Source,
    },
}

impl Stmt {
    /// Get the source span for this statement
    pub fn span(&self) -> Source {
        match self {
            Stmt::Block { span, .. } => *span,
            Stmt::Empty { span } => *span,
            Stmt::Expr { span, .. } => *span,
            Stmt::Var { span, .. } => *span,
            Stmt::Import { span, .. } => *span,
            Stmt::Export { span, .. } => *span,
            Stmt::If { span, .. } => *span,
            Stmt::While { span, .. } => *span,
            Stmt::DoWhile { span, .. } => *span,
            Stmt::For { span, .. } => *span,
            Stmt::ForIn { span, .. } => *span,
            Stmt::ForOf { span, .. } => *span,
            Stmt::Break { span, .. } => *span,
            Stmt::Continue { span, .. } => *span,
            Stmt::Return { span, .. } => *span,
            Stmt::Throw { span, .. } => *span,
            Stmt::Try { span, .. } => *span,
            Stmt::Switch { span, .. } => *span,
            Stmt::Labeled { span, .. } => *span,
            Stmt::FunctionDecl { span, .. } => *span,
        }
    }
}
