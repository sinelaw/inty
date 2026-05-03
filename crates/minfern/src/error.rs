//! Error types for the minfern type checker.

use crate::lexer::Span;
use thiserror::Error;

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

/// Result type for minfern operations.
pub type Result<T> = std::result::Result<T, MinfernError>;

/// Main error type for minfern.
#[derive(Debug, Error)]
pub enum MinfernError {
    #[error("Lexer error: {0}")]
    Lex(#[from] LexError),

    #[error("Parser error: {0}")]
    Parse(#[from] ParseError),

    #[error("Type error: {0}")]
    Type(#[from] TypeError),
}

/// Lexer errors.
#[derive(Debug, Error)]
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
#[derive(Debug, Error)]
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
        }
    }
}

/// Type checking errors.
#[derive(Debug, Error)]
pub enum TypeError {
    #[error("Cannot unify types: expected {expected}, found {found}")]
    UnificationError {
        expected: String,
        found: String,
        span: Span,
        context: Option<String>,
        expected_origin: Option<TypeOrigin>,
        found_origin: Option<TypeOrigin>,
    },

    #[error("Infinite type: {var} occurs in {ty}")]
    OccursCheck { var: String, ty: String, span: Span },

    #[error("Undefined variable '{name}'")]
    UndefinedVariable { name: String, span: Span },

    #[error("Property '{prop}' not found on type {obj_type}")]
    PropertyNotFound {
        prop: String,
        obj_type: String,
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

    #[error("Cannot assign to polymorphic property '{property}' of immutable binding '{object}'")]
    AssignmentToPolymorphicProperty {
        object: String,
        property: String,
        span: Span,
    },
}

impl TypeError {
    pub fn span(&self) -> Span {
        match self {
            TypeError::UnificationError { span, .. } => *span,
            TypeError::OccursCheck { span, .. } => *span,
            TypeError::UndefinedVariable { span, .. } => *span,
            TypeError::PropertyNotFound { span, .. } => *span,
            TypeError::NotAFunction { span, .. } => *span,
            TypeError::ArityMismatch { span, .. } => *span,
            TypeError::TypeAnnotationParse { span, .. } => *span,
            TypeError::Rank1Restriction { span } => *span,
            TypeError::ConstraintNotSatisfied { span, .. } => *span,
            TypeError::EscapedSkolem { span } => *span,
            TypeError::AmbiguousType { span } => *span,
            TypeError::AssignmentToConstant { span, .. } => *span,
            TypeError::AssignmentToPolymorphicProperty { span, .. } => *span,
            TypeError::Module { span, .. } => *span,
        }
    }
}
