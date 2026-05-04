//! Minfern CLI: Type inference for mquickjs JavaScript subset.

use std::env;
use std::fs;
use std::io::{self, Read};
use std::process::ExitCode;

use minfern::diagnostics::{print_error, print_error_plain, print_warning, print_warning_plain};
use minfern::error::MinfernError;
use minfern::infer::{decorate_with_types, InferState, InferWarning, TypeEnv};
use minfern::lexer::{Scanner, Token};
use minfern::parser::{pretty::print_program, Parser};
use minfern::stdlib::{initial_env_with_stdlib, load_lib};
use minfern::types::PrettyContext;

struct Args {
    input: Option<String>,
    /// Extra user-supplied declaration files (paths).
    extra_libs: Vec<String>,
    /// Skip the built-in stdlib (core.d.js, dom.d.js).
    no_stdlib: bool,
    /// Suppress ANSI color escapes in diagnostic output.
    no_color: bool,
}

fn parse_args(raw: Vec<String>) -> Result<Args, String> {
    let mut input = None;
    let mut extra_libs = Vec::new();
    let mut no_stdlib = false;
    let mut no_color = false;

    let mut iter = raw.into_iter().skip(1);
    while let Some(arg) = iter.next() {
        match arg.as_str() {
            "--help" | "-h" => {
                print_help();
                std::process::exit(0);
            }
            "--version" | "-V" => {
                println!("minfern {}", env!("CARGO_PKG_VERSION"));
                std::process::exit(0);
            }
            "--lib" => {
                let path = iter
                    .next()
                    .ok_or_else(|| "--lib requires a path argument".to_string())?;
                extra_libs.push(path);
            }
            "--no-stdlib" => {
                no_stdlib = true;
            }
            "--no-color" | "--no-colour" => {
                no_color = true;
            }
            _ if arg.starts_with("--lib=") => {
                extra_libs.push(arg["--lib=".len()..].to_string());
            }
            _ if arg.starts_with("--") => {
                return Err(format!("unknown option: {}", arg));
            }
            _ => {
                if input.is_some() {
                    return Err(format!("unexpected extra argument: {}", arg));
                }
                input = Some(arg);
            }
        }
    }

    Ok(Args {
        input,
        extra_libs,
        no_stdlib,
        no_color,
    })
}

fn main() -> ExitCode {
    let raw: Vec<String> = env::args().collect();

    // Sub-command dispatch: if argv[1] is `lsp`, hand off to the
    // language server. The CLI has no global options, so `lsp` is the
    // only sub-command and it always sits in slot 1.
    if raw.get(1).map(String::as_str) == Some("lsp") {
        return run_lsp(&raw[2..]);
    }

    let args = match parse_args(raw) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("error: {}", e);
            eprintln!();
            eprintln!("run 'minfern --help' for usage.");
            return ExitCode::from(2);
        }
    };

    let input = match args.input {
        Some(s) => s,
        None => {
            eprintln!("Usage: minfern <file.js> | minfern -");
            eprintln!("       minfern --help");
            return ExitCode::from(1);
        }
    };

    let (source, filename) = if input == "-" {
        let mut source = String::new();
        if let Err(e) = io::stdin().read_to_string(&mut source) {
            eprintln!("Error reading stdin: {}", e);
            return ExitCode::from(1);
        }
        (source, "<stdin>".to_string())
    } else {
        match fs::read_to_string(&input) {
            Ok(source) => (source, input.clone()),
            Err(e) => {
                eprintln!("Error reading file '{}': {}", input, e);
                return ExitCode::from(1);
            }
        }
    };

    // Build the initial env. Default: load embedded stdlib (core + dom). The
    // same InferState is threaded through so fresh type var IDs never clash
    // between the libs and the user program.
    let (env, state) = if args.no_stdlib {
        (minfern::builtins::initial_env(), InferState::new())
    } else {
        match initial_env_with_stdlib() {
            Ok(r) => r,
            Err(e) => {
                eprintln!("error loading built-in stdlib: {}", e);
                return ExitCode::from(1);
            }
        }
    };

    let report = |path: &str, source: &str, error: &MinfernError| {
        if args.no_color {
            print_error_plain(path, source, error);
        } else {
            print_error(path, source, error);
        }
    };

    let report_warning = |path: &str, source: &str, warning: &InferWarning| {
        if args.no_color {
            print_warning_plain(path, source, warning);
        } else {
            print_warning(path, source, warning);
        }
    };

    // Load any extra user-supplied lib files.
    let (env, mut state) = match load_extra_libs(env, state, &args.extra_libs, &report) {
        Ok(r) => r,
        Err(code) => return code,
    };

    let result = run_inference(&mut state, env, &source, &filename);

    for warning in &state.warnings {
        report_warning(&filename, &source, warning);
    }

    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(errors) => {
            for error in errors {
                report(&filename, &source, &error);
            }
            ExitCode::from(1)
        }
    }
}

fn load_extra_libs(
    mut env: TypeEnv,
    mut state: InferState,
    paths: &[String],
    report: &dyn Fn(&str, &str, &MinfernError),
) -> Result<(TypeEnv, InferState), ExitCode> {
    for path in paths {
        let source = match fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("error reading --lib file '{}': {}", path, e);
                return Err(ExitCode::from(1));
            }
        };
        match load_lib(&mut state, env.clone(), &source) {
            Ok(new_env) => env = new_env,
            Err(e) => {
                report(path, &source, &e);
                return Err(ExitCode::from(1));
            }
        }
    }
    Ok((env, state))
}

fn run_lsp(args: &[String]) -> ExitCode {
    for arg in args {
        match arg.as_str() {
            "--stdio" => {} // currently the only transport
            "--help" | "-h" => {
                println!("minfern lsp - Language Server Protocol over stdio");
                println!();
                println!("USAGE:");
                println!("    minfern lsp [--stdio]");
                println!();
                println!("Speaks LSP on stdin/stdout. Editors can launch this directly.");
                return ExitCode::SUCCESS;
            }
            _ => {
                eprintln!("error: unknown argument to 'lsp': {}", arg);
                return ExitCode::from(2);
            }
        }
    }

    match minfern_lsp::run_stdio() {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("lsp: {}", e);
            ExitCode::from(1)
        }
    }
}

fn print_help() {
    println!(
        r#"minfern - HMF-based type inference for mquickjs

USAGE:
    minfern [OPTIONS] <file.js>
    minfern [OPTIONS] -
    minfern lsp [--stdio]

OPTIONS:
    --lib <path>         Load an additional declaration file (can be repeated)
    --no-stdlib          Skip the embedded core and DOM declarations
    --no-color           Disable ANSI colors in diagnostic output
    -h, --help           Print help information
    -V, --version        Print version information

SUBCOMMANDS:
    lsp                  Start the language server (LSP over stdio)

DESCRIPTION:
    Minfern performs static type inference on mquickjs JavaScript code.
    It features:

    - Row polymorphism for structural typing of objects
    - Equi-recursive types for self-referential structures
    - Type classes (Plus, Indexable) for overloaded operators
    - HMF-based inference with first-class polymorphism
    - Type annotations in doc comments using /** var x: T */ syntax

    By default, minfern auto-loads the embedded core and DOM declarations
    (stdlib/core.d.js and stdlib/dom.d.js). Pass --no-stdlib to disable
    them, or --lib <path> to load additional user-supplied declarations
    (e.g. for a third-party library).

EXAMPLES:
    minfern example.js                         Check example.js
    minfern --lib types/lodash.d.js app.js     Add a lib before checking
    minfern --no-stdlib small.js               Check without any libs
    echo "var x = 1" | minfern -               Check from stdin
    minfern lsp                                Speak LSP on stdin/stdout

AUTHOR:
    (c) Noam Lewis
"#
    );
}

fn run_inference(
    state: &mut InferState,
    env: TypeEnv,
    source: &str,
    filename: &str,
) -> Result<(), Vec<MinfernError>> {
    let mut errors = Vec::new();

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
        return Err(errors);
    }

    // Parsing
    let type_annotations = scanner.type_annotations().to_vec();
    let mut parser = Parser::new(tokens, type_annotations);

    let program = match parser.parse_program() {
        Ok(program) => program,
        Err(e) => {
            errors.push(e);
            return Err(errors);
        }
    };

    // Resolve any `import "./foo.js"` statements relative to the file's
    // parent directory before inferring the program itself. For stdin
    // (filename == "<stdin>") we skip resolution since there's no path.
    let env = if filename != "<stdin>" {
        let base_dir = std::path::Path::new(filename)
            .parent()
            .map(|p| p.to_path_buf())
            .unwrap_or_else(|| std::path::PathBuf::from("."));
        let mut visiting = std::collections::HashSet::new();
        match minfern::modules::resolve_imports(
            state,
            env,
            &program,
            &base_dir,
            &mut visiting,
        ) {
            Ok(e) => e,
            Err(e) => {
                errors.push(e);
                return Err(errors);
            }
        }
    } else {
        env
    };

    // Type inference
    match state.infer_program_with_env(&env, &program) {
        Ok((result_type, final_env)) => {
            // Resolve type class constraints
            if let Err(e) = state.resolve_constraints() {
                errors.push(e);
                return Err(errors);
            }

            // Print the program type
            let mut ctx = PrettyContext::new();
            let final_type = state.apply_subst(&result_type);
            println!("// Program type: {}", ctx.format_type(&final_type));
            println!();

            // Decorate the AST with inferred types and print it
            let decorated = decorate_with_types(&program, &final_env, state);
            print!("{}", print_program(&decorated));

            Ok(())
        }
        Err(e) => {
            errors.push(e);
            Err(errors)
        }
    }
}
