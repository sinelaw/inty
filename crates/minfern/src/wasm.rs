//! WebAssembly bindings for minfern type checker.

use wasm_bindgen::prelude::*;

use crate::builtins::initial_env;
use crate::error::MinfernError;
use crate::infer::{decorate_with_types, InferState};
use crate::lexer::{Scanner, Token};
use crate::parser::{pretty::print_program, Parser};
use crate::stdlib::initial_env_with_stdlib;
use crate::types::PrettyContext;

/// Result of type checking, returned as JSON.
#[wasm_bindgen]
pub struct CheckResult {
    success: bool,
    output: String,
    program_type: String,
    errors: Vec<JsValue>,
}

#[wasm_bindgen]
impl CheckResult {
    #[wasm_bindgen(getter)]
    pub fn success(&self) -> bool {
        self.success
    }

    #[wasm_bindgen(getter)]
    pub fn output(&self) -> String {
        self.output.clone()
    }

    #[wasm_bindgen(getter)]
    pub fn program_type(&self) -> String {
        self.program_type.clone()
    }

    #[wasm_bindgen(getter)]
    pub fn errors(&self) -> Vec<JsValue> {
        self.errors.clone()
    }
}

/// Format an error into a structured object for JS.
fn format_error(error: &MinfernError) -> JsValue {
    let (message, start, end) = match error {
        MinfernError::Lex(e) => {
            let span = e.span();
            (e.to_string(), span.start, span.end)
        }
        MinfernError::Parse(e) => {
            let span = e.span();
            (e.to_string(), span.start, span.end)
        }
        MinfernError::Type(e) => {
            let span = e.span();
            (e.to_string(), span.start, span.end)
        }
    };

    let obj = js_sys::Object::new();
    js_sys::Reflect::set(&obj, &"message".into(), &message.into()).unwrap();
    js_sys::Reflect::set(&obj, &"start".into(), &JsValue::from_f64(start as f64)).unwrap();
    js_sys::Reflect::set(&obj, &"end".into(), &JsValue::from_f64(end as f64)).unwrap();
    obj.into()
}

/// Initialize the WASM module (call once at startup).
#[wasm_bindgen(start)]
pub fn init() {
    #[cfg(feature = "wasm")]
    console_error_panic_hook::set_once();
}

/// Type check JavaScript source code and return the result.
#[wasm_bindgen]
pub fn check_types(source: &str) -> CheckResult {
    let mut errors: Vec<MinfernError> = Vec::new();

    // Lexing
    let mut scanner = Scanner::new(source);
    let mut tokens = Vec::new();

    loop {
        match scanner.next_token() {
            Ok(tok) => {
                let is_eof = matches!(tok.value, Token::Eof);
                tokens.push(tok);
                if is_eof {
                    break;
                }
            }
            Err(e) => {
                errors.push(e);
                break;
            }
        }
    }

    if !errors.is_empty() {
        return CheckResult {
            success: false,
            output: String::new(),
            program_type: String::new(),
            errors: errors.iter().map(format_error).collect(),
        };
    }

    // Parsing
    let type_annotations = scanner.type_annotations().to_vec();
    let mut parser = Parser::new(tokens, type_annotations);

    let program = match parser.parse_program() {
        Ok(program) => program,
        Err(e) => {
            errors.push(e);
            return CheckResult {
                success: false,
                output: String::new(),
                program_type: String::new(),
                errors: errors.iter().map(format_error).collect(),
            };
        }
    };

    // Type inference. Prefer the full stdlib env (core + dom); fall back to
    // the bare Rust env if loading the embedded libs fails (shouldn't happen
    // for the shipped files, but we don't want to crash the playground).
    let (env, mut state) = match initial_env_with_stdlib() {
        Ok(r) => r,
        Err(_) => (initial_env(), InferState::new()),
    };

    match state.infer_program_with_env(&env, &program) {
        Ok((result_type, final_env)) => {
            // Resolve type class constraints
            if let Err(e) = state.resolve_constraints() {
                errors.push(e);
                return CheckResult {
                    success: false,
                    output: String::new(),
                    program_type: String::new(),
                    errors: errors.iter().map(format_error).collect(),
                };
            }

            // Format the program type
            let mut ctx = PrettyContext::new();
            let final_type = state.apply_subst(&result_type);
            let program_type = ctx.format_type(&final_type);

            // Decorate the AST with inferred types and print it
            let decorated = decorate_with_types(&program, &final_env, &state);
            let output = print_program(&decorated);

            CheckResult {
                success: true,
                output,
                program_type,
                errors: Vec::new(),
            }
        }
        Err(e) => {
            errors.push(e);
            CheckResult {
                success: false,
                output: String::new(),
                program_type: String::new(),
                errors: errors.iter().map(format_error).collect(),
            }
        }
    }
}
