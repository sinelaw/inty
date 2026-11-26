//! Error types for the inty type checker.

use crate::span::Span;
use crate::types::Type;
use thiserror::Error;

/// A type a diagnostic shows. Inference raises an error holding the
/// types themselves ([`ShownType::Type`]): rendering one (resolving it
/// against the substitution, tidying its variables, trimming large
/// records) is costly, and most errors are raised by speculative
/// attempts and dropped. An error that is reported is rendered once
/// ([`crate::infer::InferState::render_error`]), which makes its types
/// [`ShownType::Text`]. Unrendered, a type prints as it is.
///
/// An error no one will see keeps no types ([`ShownType::Elided`]): one a
/// speculative attempt raised at the top of the types it compared (it is
/// dropped), or one past where a member path stops (its member's types
/// replace it). Copying large types there made speculation slow.
#[derive(Debug, Clone)]
pub enum ShownType {
    Type(Box<Type>),
    Text(String),
    Elided,
}

impl ShownType {
    pub fn ty(t: &Type) -> Self {
        ShownType::Type(Box::new(t.clone()))
    }

    /// The rendered text (the type's plain form if not rendered).
    pub fn text(&self) -> std::borrow::Cow<'_, str> {
        match self {
            ShownType::Text(s) => s.as_str().into(),
            ShownType::Type(t) => t.to_string().into(),
            ShownType::Elided => "…".into(),
        }
    }
}

impl std::fmt::Display for ShownType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ShownType::Type(t) => write!(f, "{t}"),
            ShownType::Text(s) => f.write_str(s),
            ShownType::Elided => f.write_str("…"),
        }
    }
}

impl From<String> for ShownType {
    fn from(s: String) -> Self {
        ShownType::Text(s)
    }
}

impl From<&str> for ShownType {
    fn from(s: &str) -> Self {
        ShownType::Text(s.to_string())
    }
}

/// Where a mismatch is, in the larger types compared: " in member `m`"
/// (nothing at their top).
pub fn in_member(member: Option<&str>) -> String {
    member
        .map(|m| format!(" in member `{m}`"))
        .unwrap_or_default()
}

/// Describes where a type came from in the source code
#[derive(Debug, Clone)]
pub enum TypeOrigin {
    /// Type comes from a literal value
    Literal { value: String, span: Span },

    /// Type comes from a variable binding
    Variable { name: String, span: Span },

    /// Type comes from function parameter
    Parameter {
        param_name: String,
        param_index: usize,
        span: Span,
    },

    /// Type comes from property access
    PropertyAccess { property: String, span: Span },

    /// Type comes from binary operation
    BinaryOp {
        operator: String,
        side: String,
        span: Span,
    },

    /// Type comes from function call
    FunctionCall { span: Span },

    /// Type was inferred (fallback)
    Inferred { reason: String, span: Span },

    /// Type came from a comparison operation
    Comparison {
        operator: String,
        compared_to: String,
        span: Span,
    },
}

/// The text of [`TypeError::ThisMismatch`].
fn this_mismatch_message(
    member: Option<&str>,
    reads_this: &ShownType,
    without_this: Option<&ShownType>,
    with_this: Option<&ShownType>,
) -> String {
    let at = in_member(member);
    let shown = |f: Option<&ShownType>| f.map(|f| format!(" '{f}'")).unwrap_or_default();
    format!(
        "Type mismatch{at}: expected a function that doesn't use `this`{}, found one that reads `this` (a method of {reads_this}){}",
        shown(without_this),
        shown(with_this),
    )
}

impl TypeOrigin {
    /// Get the primary span for this origin
    pub fn span(&self) -> Span {
        match self {
            TypeOrigin::Literal { span, .. }
            | TypeOrigin::Variable { span, .. }
            | TypeOrigin::Parameter { span, .. }
            | TypeOrigin::PropertyAccess { span, .. }
            | TypeOrigin::BinaryOp { span, .. }
            | TypeOrigin::FunctionCall { span, .. }
            | TypeOrigin::Inferred { span, .. }
            | TypeOrigin::Comparison { span, .. } => *span,
        }
    }

    /// Get a human-readable description
    pub fn description(&self) -> String {
        match self {
            TypeOrigin::Literal { value, .. } => format!("literal {}", value),
            TypeOrigin::Variable { name, .. } => format!("variable '{}'", name),
            TypeOrigin::Parameter {
                param_name,
                param_index,
                ..
            } => {
                format!("parameter '{}' (position {})", param_name, param_index)
            }
            TypeOrigin::PropertyAccess { property, .. } => {
                format!("property access '.{}'", property)
            }
            TypeOrigin::BinaryOp { operator, side, .. } => {
                format!("{} operand of '{}'", side, operator)
            }
            TypeOrigin::FunctionCall { .. } => "function call".to_string(),
            TypeOrigin::Inferred { reason, .. } => format!("inferred ({})", reason),
            TypeOrigin::Comparison {
                operator,
                compared_to,
                ..
            } => {
                format!("comparison '{}' with {}", operator, compared_to)
            }
        }
    }

    /// Get a short label for error messages
    pub fn label(&self) -> String {
        match self {
            TypeOrigin::Literal { value, .. } => format!("from literal {}", value),
            TypeOrigin::Variable { name, .. } => format!("from variable '{}'", name),
            TypeOrigin::Parameter { param_name, .. } => {
                format!("from parameter '{}'", param_name)
            }
            TypeOrigin::PropertyAccess { property, .. } => {
                format!("from '.{}'", property)
            }
            TypeOrigin::BinaryOp { operator, side, .. } => {
                format!("{} side of '{}'", side, operator)
            }
            TypeOrigin::FunctionCall { .. } => "from function call".to_string(),
            TypeOrigin::Inferred { reason, .. } => reason.clone(),
            TypeOrigin::Comparison {
                operator,
                compared_to,
                ..
            } => {
                format!("from '{}' comparison with {}", operator, compared_to)
            }
        }
    }

    /// Get priority for this origin (higher = more specific, should override lower priority)
    pub fn priority(&self) -> u8 {
        match self {
            TypeOrigin::Literal { .. } => 4,    // Most specific - exact value
            TypeOrigin::Comparison { .. } => 3, // Very specific - shows constraint
            TypeOrigin::BinaryOp { .. } => 3,   // Very specific - shows operation
            TypeOrigin::PropertyAccess { .. } => 3, // Very specific - shows constraint
            TypeOrigin::FunctionCall { .. } => 2, // Somewhat specific
            TypeOrigin::Variable { .. } => 1,   // Generic
            TypeOrigin::Parameter { .. } => 1,  // Generic
            TypeOrigin::Inferred { .. } => 0,   // Least specific - fallback
        }
    }
}

/// A source file an error's span indexes into: a display path plus the
/// full text. Spans are bare byte ranges with no file identity, so a
/// diagnostic raised while checking an imported module needs to carry the
/// module's source to render against the right file instead of the entry
/// source.
#[derive(Debug, Clone)]
pub struct SourceFile {
    pub path: String,
    pub text: String,
}

/// Where the spans of an imported module live: each module's spans are
/// shifted into a range of their own, from [`SourceMap::BASE`] up, so a
/// span alone says which file it is in — a diagnostic about one module
/// can point into another (the use that required what failed). Spans
/// below `BASE` are the entry program's (or, for a parse error, the
/// file being parsed).
#[derive(Debug, Clone, Default)]
pub struct SourceMap {
    /// `(base, file)`, bases ascending.
    files: Vec<(usize, std::sync::Arc<SourceFile>)>,
}

impl SourceMap {
    /// Where the first module's spans start: past any entry program's
    /// spans. 2^40 doesn't fit a 32-bit `usize` (the wasm build of the
    /// web playground), where 1 GiB of entry source is ample.
    #[cfg(target_pointer_width = "64")]
    pub const BASE: usize = 1 << 40;
    /// Where the first module's spans start: past any entry program's
    /// spans. 2^40 doesn't fit a 32-bit `usize` (the wasm build of the
    /// web playground), where 1 GiB of entry source is ample.
    #[cfg(not(target_pointer_width = "64"))]
    pub const BASE: usize = 1 << 30;

    /// Reserve a span range for `file`, returning its base.
    pub fn add(&mut self, path: String, text: String) -> usize {
        let base = match self.files.last() {
            Some((b, f)) => b + f.text.len() + 1,
            None => Self::BASE,
        };
        self.files
            .push((base, std::sync::Arc::new(SourceFile { path, text })));
        base
    }

    /// The file `span` is in and the span within it, for a span of a
    /// registered module; `None` for an entry-program span.
    pub fn locate(&self, span: crate::span::Span) -> Option<(&SourceFile, crate::span::Span)> {
        if span.start < Self::BASE {
            return None;
        }
        let i = self.files.partition_point(|(b, _)| *b <= span.start);
        let (base, file) = self.files.get(i.checked_sub(1)?)?;
        Some((
            file,
            crate::span::Span::new(span.start - base, span.end.saturating_sub(*base)),
        ))
    }

    /// Every registered file's `(path, text)`.
    pub fn files(&self) -> impl Iterator<Item = (&str, &str)> {
        self.files
            .iter()
            .map(|(_, f)| (f.path.as_str(), f.text.as_str()))
    }

    /// The registered file with the given base.
    pub fn file_at(&self, base: usize) -> Option<SourceFile> {
        self.files
            .iter()
            .find(|(b, _)| *b == base)
            .map(|(_, f)| (**f).clone())
    }
}

/// An error paired with the source file its span refers to. `source` is
/// `None` for the entry/primary file (the common single-file case); it is
/// `Some` when the error originates in an imported module.
#[derive(Debug, Clone)]
pub struct LocatedError {
    pub error: IntyError,
    pub source: Option<SourceFile>,
}

/// Result type for inty operations.
pub type Result<T> = std::result::Result<T, IntyError>;

/// Main error type for inty.
#[derive(Debug, Clone, Error)]
pub enum IntyError {
    #[error("Lexer error: {0}")]
    Lex(#[from] LexError),

    #[error("Parser error: {0}")]
    Parse(#[from] ParseError),

    /// Boxed: a `TypeError` is large, and an `IntyError` is returned by
    /// most of the checker's functions.
    #[error("Type error: {0}")]
    Type(Box<TypeError>),
}

impl IntyError {
    /// The type error this is, if it is one.
    pub fn as_type(&self) -> Option<&TypeError> {
        match self {
            IntyError::Type(e) => Some(e),
            _ => None,
        }
    }

    pub fn as_type_mut(&mut self) -> Option<&mut TypeError> {
        match self {
            IntyError::Type(e) => Some(e),
            _ => None,
        }
    }
}

impl From<Box<TypeError>> for IntyError {
    fn from(e: Box<TypeError>) -> Self {
        IntyError::Type(e)
    }
}

impl From<TypeError> for IntyError {
    fn from(e: TypeError) -> Self {
        IntyError::Type(Box::new(e))
    }
}

/// Lexer errors.
#[derive(Debug, Clone, Error)]
pub enum LexError {
    #[error("Unexpected character '{ch}'")]
    UnexpectedCharacter { ch: char, span: Span },

    #[error("Unterminated string literal")]
    UnterminatedString { span: Span },

    #[error("Unterminated comment")]
    UnterminatedComment { span: Span },

    #[error("Invalid number literal")]
    InvalidNumber { span: Span },

    #[error("Invalid escape sequence")]
    InvalidEscapeSequence { span: Span },

    #[error("Unterminated regular expression")]
    UnterminatedRegex { span: Span },
}

impl LexError {
    pub fn span(&self) -> Span {
        match self {
            LexError::UnexpectedCharacter { span, .. } => *span,
            LexError::UnterminatedString { span } => *span,
            LexError::UnterminatedComment { span } => *span,
            LexError::InvalidNumber { span } => *span,
            LexError::InvalidEscapeSequence { span } => *span,
            LexError::UnterminatedRegex { span } => *span,
        }
    }
}

/// Parser errors.
#[derive(Debug, Clone, Error)]
pub enum ParseError {
    #[error("Unexpected token '{found}', expected {expected}")]
    UnexpectedToken {
        found: String,
        expected: String,
        span: Span,
    },

    #[error("Unexpected end of input")]
    UnexpectedEof { span: Span },

    #[error("Invalid assignment target")]
    InvalidAssignmentTarget { span: Span },

    #[error("Invalid left-hand side in for-in/of loop")]
    InvalidForInTarget { span: Span },

    #[error("Duplicate property '{name}' in object literal")]
    DuplicateProperty { name: String, span: Span },

    #[error("'break' outside of loop or switch")]
    BreakOutsideLoop { span: Span },

    #[error("'continue' outside of loop")]
    ContinueOutsideLoop { span: Span },

    #[error("'return' outside of function")]
    ReturnOutsideFunction { span: Span },

    #[error("unsupported construct: {feature}")]
    Unsupported { feature: String, span: Span },

    #[error("local variable '{name}' referenced before assignment (declare it 'global' to rebind a module-level variable)")]
    LocalReferencedBeforeAssignment { name: String, span: Span },
}

impl ParseError {
    pub fn span(&self) -> Span {
        match self {
            ParseError::UnexpectedToken { span, .. } => *span,
            ParseError::UnexpectedEof { span } => *span,
            ParseError::InvalidAssignmentTarget { span } => *span,
            ParseError::InvalidForInTarget { span } => *span,
            ParseError::DuplicateProperty { span, .. } => *span,
            ParseError::BreakOutsideLoop { span } => *span,
            ParseError::ContinueOutsideLoop { span } => *span,
            ParseError::ReturnOutsideFunction { span } => *span,
            ParseError::Unsupported { span, .. } => *span,
            ParseError::LocalReferencedBeforeAssignment { span, .. } => *span,
        }
    }
}

/// Type checking errors.
#[derive(Debug, Clone, Error)]
pub enum TypeError {
    /// Two types that don't unify. `member`: the property path
    /// (`editor.ask`) of the larger types being compared where they are,
    /// when the mismatch is inside them (`expected` and `found` are then
    /// that member's types, and `whole`, when known, the larger types).
    #[error("Cannot unify types{}: expected {expected}, found {found}", in_member(member.as_deref()))]
    UnificationError {
        expected: ShownType,
        found: ShownType,
        member: Option<String>,
        whole: Option<Box<(ShownType, ShownType)>>,
        span: Span,
        context: Option<String>,
        expected_origin: Option<TypeOrigin>,
        found_origin: Option<TypeOrigin>,
    },

    #[error("Infinite type: {var} occurs in {ty}")]
    OccursCheck { var: String, ty: String, span: Span },

    /// Unification nested deeper than [`crate::infer::MAX_UNIFY_DEPTH`]:
    /// recursive types it couldn't settle. Reported instead of
    /// overflowing the stack.
    #[error("Type too complex: unifying these recursive types did not terminate")]
    UnifyDepth { span: Span },

    #[error("Undefined variable '{name}'")]
    UndefinedVariable { name: String, span: Span },

    #[error("Property '{prop}' not found on type {obj_type}")]
    PropertyNotFound {
        prop: String,
        obj_type: String,
        span: Span,
    },

    /// A member read of a value that may be `null` or `undefined`
    /// (`T | Null`, `T | Undefined`): the nothing has no members.
    #[error("Property '{prop}' not found on type {obj_type}: the value may be {nothing}")]
    PropertyOfNullable {
        prop: String,
        obj_type: String,
        nothing: &'static str,
        span: Span,
    },

    #[error("Presence mismatch: expected {expected}, found {found}")]
    PresenceMismatch {
        expected: String,
        found: String,
        span: Span,
    },

    #[error("Type {ty} is not a function")]
    NotAFunction { ty: String, span: Span },

    #[error("Wrong number of arguments: expected {expected}, found {found}")]
    ArityMismatch {
        expected: usize,
        found: usize,
        span: Span,
    },

    #[error("Failed to parse type annotation: {message}")]
    TypeAnnotationParse { message: String, span: Span },

    #[error("Rank-1 restriction: type parameters not allowed in nested position")]
    Rank1Restriction { span: Span },

    /// Required parameter follows an optional one — TypeScript
    /// ts(1016) equivalent. Carries the offending position pair
    /// so the diagnostic can point at it. Distinct from
    /// `TypeAnnotationParse` so the type parser's
    /// backtrack-to-grouped-type fallback (`parse_func_or_grouped`)
    /// can recognise it as committed-function-type-diagnostic and
    /// not retry as a grouped expression — see the matching arm
    /// in `parse_func_or_grouped`.
    #[error(
        "required parameter at position {required_idx} cannot follow optional \
         parameter at position {optional_idx} — positional calls can't omit a \
         middle argument; reorder so optional params come last, or make the \
         trailing ones optional too"
    )]
    OptionalParameterFollowedByRequired {
        optional_idx: usize,
        required_idx: usize,
        span: Span,
    },

    #[error("Type class constraint not satisfied: {class} {ty}")]
    ConstraintNotSatisfied {
        class: String,
        ty: String,
        span: Span,
    },

    #[error("Escaped skolem variable: type is not polymorphic enough")]
    EscapedSkolem { span: Span },

    #[error("Ambiguous type: multiple valid instantiations")]
    AmbiguousType { span: Span },

    #[error("Cannot assign to constant '{name}'")]
    AssignmentToConstant { name: String, span: Span },

    #[error("{message}")]
    Module { message: String, span: Span },

    #[error("{message}")]
    InvalidSyntax { message: String, span: Span },

    /// A function that reads `this` called detached (`f()`, not
    /// `o.f()`): it gets `this` = `undefined`.
    #[error(
        "{callee} is a method (it reads `this`), so calling it detached passes `this` = undefined"
    )]
    DetachedThis { callee: String, span: Span },

    /// A function that doesn't use `this` and one that reads it met in
    /// one slot. `member`: the property path (`editor.say`) of the two
    /// types being compared where they are; `without_this` / `with_this`:
    /// the two functions (none: only their `this` types were at hand).
    #[error("{}", this_mismatch_message(member.as_deref(), reads_this, without_this.as_ref(), with_this.as_ref()))]
    ThisMismatch {
        member: Option<String>,
        reads_this: ShownType,
        without_this: Option<ShownType>,
        with_this: Option<ShownType>,
        span: Span,
    },

    #[error("Type mismatch: expected {expected}, found {found}")]
    TypeMismatch {
        expected: String,
        found: String,
        span: Span,
    },

    #[error("Cannot assign to polymorphic property '{property}' of immutable binding '{object}'")]
    AssignmentToPolymorphicProperty {
        object: String,
        property: String,
        span: Span,
    },

    /// A type annotation refers to a name that isn't a known primitive,
    /// type alias, declared type variable, or class in scope — typically
    /// a typo (`-> blabla`) or an unmodelled imported type. Lowering
    /// returns a fresh variable to keep inference going, but the error
    /// is surfaced so the user sees the dangling reference.
    #[error("Unknown type '{name}' in annotation")]
    UnknownTypeRef { name: String, span: Span },

    /// Two branches (of a conditional, the `return`s of a function, the
    /// elements of an array literal, `??`) have different types. inty
    /// doesn't guess that they form a union; an annotation says so.
    #[error("Branches have different types: {left} and {right}")]
    BranchMismatch {
        left: ShownType,
        right: ShownType,
        span: Span,
    },

    /// A field one record type has and the other lacks (or has only
    /// optionally): `field` is present in `with` and absent from
    /// `without`. `member`: where the two records are in the larger
    /// types compared (as for `UnificationError`).
    #[error("Field '{field}' is present in {with} but missing from {without}{}", in_member(member.as_deref()))]
    FieldPresenceMismatch {
        field: String,
        with: ShownType,
        without: ShownType,
        member: Option<String>,
        span: Span,
    },

    /// `inner` failed at a use of a generic function (its `span`) because
    /// of a requirement written in the function's body, at `origin`
    /// (`o.name.toUpperCase()` with `o.name` a number).
    #[error("{inner}")]
    RequiredBy { inner: Box<TypeError>, origin: Span },

    /// The elements of an array literal have different types. An array
    /// has one element type; a fixed group of values is a tuple
    /// (`[String, Number]`) or a record.
    #[error("Array elements have different types: {left} and {right}")]
    ArrayElementMismatch {
        left: ShownType,
        right: ShownType,
        span: Span,
    },
}

impl TypeError {
    pub fn span(&self) -> Span {
        match self {
            TypeError::UnificationError { span, .. } => *span,
            TypeError::OccursCheck { span, .. } => *span,
            TypeError::UnifyDepth { span } => *span,
            TypeError::UndefinedVariable { span, .. } => *span,
            TypeError::PropertyNotFound { span, .. } => *span,
            TypeError::PropertyOfNullable { span, .. } => *span,
            TypeError::PresenceMismatch { span, .. } => *span,
            TypeError::NotAFunction { span, .. } => *span,
            TypeError::ArityMismatch { span, .. } => *span,
            TypeError::TypeAnnotationParse { span, .. } => *span,
            TypeError::Rank1Restriction { span } => *span,
            TypeError::OptionalParameterFollowedByRequired { span, .. } => *span,
            TypeError::ConstraintNotSatisfied { span, .. } => *span,
            TypeError::EscapedSkolem { span } => *span,
            TypeError::AmbiguousType { span } => *span,
            TypeError::AssignmentToConstant { span, .. } => *span,
            TypeError::AssignmentToPolymorphicProperty { span, .. } => *span,
            TypeError::UnknownTypeRef { span, .. } => *span,
            TypeError::Module { span, .. } => *span,
            TypeError::InvalidSyntax { span, .. } => *span,
            TypeError::TypeMismatch { span, .. } => *span,
            TypeError::ThisMismatch { span, .. } => *span,
            TypeError::DetachedThis { span, .. } => *span,
            TypeError::BranchMismatch { span, .. } => *span,
            TypeError::ArrayElementMismatch { span, .. } => *span,
            TypeError::RequiredBy { inner, .. } => inner.span(),
            TypeError::FieldPresenceMismatch { span, .. } => *span,
        }
    }
}
