//! Inty CLI: Type inference for mquickjs JavaScript subset.

use std::env;
use std::fs;
use std::io::{self, Read};
use std::process::ExitCode;

use inty::diagnostics::{print_error, print_error_plain, print_warning, print_warning_plain};
use inty::error::IntyError;
use inty::infer::{decorate_with_types, InferState, InferWarning, TypeEnv};
use inty::lexer::{Scanner, Token};
use inty::parser::{pretty::print_program, Parser};
use inty::stdlib::{initial_env_with_stdlib, load_lib};
use inty::types::PrettyContext;

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
                println!("inty {}", env!("CARGO_PKG_VERSION"));
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
    // language server. `declarations` is a one-shot emitter for `.d.js`.
    // Both sit in slot 1; the CLI has no global options before them.
    if raw.get(1).map(String::as_str) == Some("lsp") {
        return run_lsp(&raw[2..]);
    }
    if raw.get(1).map(String::as_str) == Some("declarations") {
        return run_declarations(&raw[2..]);
    }
    if raw.get(1).map(String::as_str) == Some("bundle") {
        return run_bundle(&raw[2..]);
    }

    let args = match parse_args(raw) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("error: {}", e);
            eprintln!();
            eprintln!("run 'inty --help' for usage.");
            return ExitCode::from(2);
        }
    };

    let input = match args.input {
        Some(s) => s,
        None => {
            eprintln!("Usage: inty <file.js> | inty -");
            eprintln!("       inty --help");
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
        (inty::builtins::initial_env(), InferState::new())
    } else {
        match initial_env_with_stdlib() {
            Ok(r) => r,
            Err(e) => {
                eprintln!("error loading built-in stdlib: {}", e);
                return ExitCode::from(1);
            }
        }
    };

    let report = |path: &str, source: &str, error: &IntyError| {
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
    report: &dyn Fn(&str, &str, &IntyError),
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

fn run_declarations(args: &[String]) -> ExitCode {
    let mut input: Option<String> = None;
    let mut no_stdlib = false;
    let mut no_color = false;
    let mut flavor = inty::declarations::DeclarationFlavor::Inty;
    for arg in args {
        match arg.as_str() {
            "--help" | "-h" => {
                println!("inty declarations <entry.js> [--format=ts|inty]");
                println!();
                println!("Type-check the entry module and emit one");
                println!("declaration per export to stdout.");
                println!();
                println!("With --format=inty (default), each export prints as");
                println!("`/** const NAME: T */ const NAME;` (an inty .d.js).");
                println!("With --format=ts, output uses TypeScript syntax:");
                println!("`declare const NAME: T;` (a .d.ts).");
                return ExitCode::SUCCESS;
            }
            "--no-stdlib" => no_stdlib = true,
            "--no-color" | "--no-colour" => no_color = true,
            "--format=ts" => flavor = inty::declarations::DeclarationFlavor::Ts,
            "--format=inty" => flavor = inty::declarations::DeclarationFlavor::Inty,
            _ if arg.starts_with("--") => {
                eprintln!("error: unknown option to 'declarations': {}", arg);
                return ExitCode::from(2);
            }
            _ => {
                if input.is_some() {
                    eprintln!("error: unexpected extra argument: {}", arg);
                    return ExitCode::from(2);
                }
                input = Some(arg.clone());
            }
        }
    }

    let path = match input {
        Some(p) => p,
        None => {
            eprintln!("Usage: inty declarations <entry.js>");
            return ExitCode::from(2);
        }
    };

    let (env, mut state) = if no_stdlib {
        (inty::builtins::initial_env(), InferState::new())
    } else {
        match initial_env_with_stdlib() {
            Ok(r) => r,
            Err(e) => {
                eprintln!("error loading built-in stdlib: {}", e);
                return ExitCode::from(1);
            }
        }
    };

    let report_err = |source_label: &str, source: &str, error: &IntyError| {
        if no_color {
            print_error_plain(source_label, source, error);
        } else {
            print_error(source_label, source, error);
        }
    };

    let (module_env, exports) =
        match inty::modules::check_module(&mut state, env, std::path::Path::new(&path)) {
            Ok(r) => r,
            Err(e) => {
                let source = fs::read_to_string(&path).unwrap_or_default();
                report_err(&path, &source, &e);
                return ExitCode::from(1);
            }
        };

    if let Err(e) = state.resolve_constraints() {
        let source = fs::read_to_string(&path).unwrap_or_default();
        report_err(&path, &source, &e);
        return ExitCode::from(1);
    }

    let module = inty::declarations::CheckedModule::new(module_env, exports);
    print!(
        "{}",
        inty::declarations::emit_declarations_with_flavor(&module, flavor)
    );

    ExitCode::SUCCESS
}

fn run_bundle(args: &[String]) -> ExitCode {
    let mut input: Option<String> = None;
    let mut out_path: Option<String> = None;
    let mut iter = args.iter();
    while let Some(arg) = iter.next() {
        match arg.as_str() {
            "--help" | "-h" => {
                println!("inty bundle <entry.js> [-o out.js]");
                println!();
                println!("Type-check the entry module's import graph,");
                println!("then emit a single self-contained JS blob");
                println!("plus a v3 source map. With -o, writes <out>");
                println!("and <out>.map; without, prints the bundle to");
                println!("stdout (no source map written).");
                return ExitCode::SUCCESS;
            }
            "-o" | "--output" => match iter.next() {
                Some(p) => out_path = Some(p.clone()),
                None => {
                    eprintln!("error: -o requires a path argument");
                    return ExitCode::from(2);
                }
            },
            _ if arg.starts_with("--output=") => {
                out_path = Some(arg["--output=".len()..].to_string());
            }
            _ if arg.starts_with("--") => {
                eprintln!("error: unknown option to 'bundle': {}", arg);
                return ExitCode::from(2);
            }
            _ => {
                if input.is_some() {
                    eprintln!("error: unexpected extra argument: {}", arg);
                    return ExitCode::from(2);
                }
                input = Some(arg.clone());
            }
        }
    }

    let entry = match input {
        Some(p) => p,
        None => {
            eprintln!("Usage: inty bundle <entry.js> [-o out.js]");
            return ExitCode::from(2);
        }
    };

    // Type-check the entry first. The bundler assumes the program
    // type-checks and won't surface a useful error if it doesn't.
    let (env, mut state) = match initial_env_with_stdlib() {
        Ok(r) => r,
        Err(e) => {
            eprintln!("error loading stdlib: {}", e);
            return ExitCode::from(1);
        }
    };
    let entry_path = std::path::Path::new(&entry);
    if let Err(e) = inty::modules::check_module(&mut state, env, entry_path) {
        let source = fs::read_to_string(entry_path).unwrap_or_default();
        print_error_plain(&entry, &source, &e);
        return ExitCode::from(1);
    }
    if let Err(e) = state.resolve_constraints() {
        let source = fs::read_to_string(entry_path).unwrap_or_default();
        print_error_plain(&entry, &source, &e);
        return ExitCode::from(1);
    }

    // Now bundle.
    let out = match inty_bundle::bundle(entry_path) {
        Ok(o) => o,
        Err(e) => {
            eprintln!("bundle error: {}", e);
            return ExitCode::from(1);
        }
    };

    match out_path {
        Some(p) => {
            if let Err(e) = fs::write(&p, &out.code) {
                eprintln!("error writing {}: {}", p, e);
                return ExitCode::from(1);
            }
            let map_path = format!("{}.map", p);
            if let Err(e) = fs::write(&map_path, &out.source_map) {
                eprintln!("error writing {}: {}", map_path, e);
                return ExitCode::from(1);
            }
        }
        None => {
            print!("{}", out.code);
        }
    }

    ExitCode::SUCCESS
}

fn run_lsp(args: &[String]) -> ExitCode {
    for arg in args {
        match arg.as_str() {
            "--stdio" => {} // currently the only transport
            "--help" | "-h" => {
                println!("inty lsp - Language Server Protocol over stdio");
                println!();
                println!("USAGE:");
                println!("    inty lsp [--stdio]");
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

    match inty_lsp::run_stdio() {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("lsp: {}", e);
            ExitCode::from(1)
        }
    }
}

fn print_help() {
    println!(
        r#"inty - a static type checker for JavaScript

USAGE:
    inty [OPTIONS] <file.js>
    inty [OPTIONS] -
    inty lsp [--stdio]

OPTIONS:
    --lib <path>         Load an additional declaration file (can be repeated)
    --no-stdlib          Skip the embedded core and DOM declarations
    --no-color           Disable ANSI colors in diagnostic output
    -h, --help           Print help information
    -V, --version        Print version information

SUBCOMMANDS:
    lsp                  Start the language server (LSP over stdio)
    declarations         Emit `/** const NAME: T */ const NAME;` lines
                         for every exported binding of a module
    bundle               Bundle a module's import graph into a single
                         self-contained JS blob plus a v3 source map

DESCRIPTION:
    Inty performs static type inference on mquickjs JavaScript code.
    It features:

    - Row polymorphism for structural typing of objects
    - Equi-recursive types for self-referential structures
    - Type classes (Plus, Indexable) for overloaded operators
    - Full type inference with first-class polymorphism
    - Type annotations in doc comments using /** var x: T */ syntax

    By default, inty auto-loads the embedded core and DOM declarations
    (stdlib/core.d.js and stdlib/dom.d.js). Pass --no-stdlib to disable
    them, or --lib <path> to load additional user-supplied declarations
    (e.g. for a third-party library).

EXAMPLES:
    inty example.js                         Check example.js
    inty --lib types/lodash.d.js app.js     Add a lib before checking
    inty --no-stdlib small.js               Check without any libs
    echo "var x = 1" | inty -               Check from stdin
    inty lsp                                Speak LSP on stdin/stdout

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
) -> Result<(), Vec<IntyError>> {
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
    let type_aliases = scanner.type_aliases().to_vec();
    let mut parser = Parser::with_source(tokens, type_annotations, source.to_string());

    let mut program = match parser.parse_program() {
        Ok(program) => program,
        Err(e) => {
            errors.push(e);
            return Err(errors);
        }
    };
    program.type_aliases = type_aliases;

    // Resolve any `import "./foo.js"` statements relative to the file's
    // parent directory before inferring the program itself. For stdin
    // (filename == "<stdin>") we skip resolution since there's no path.
    let env = if filename != "<stdin>" {
        let base_dir = std::path::Path::new(filename)
            .parent()
            .map(|p| p.to_path_buf())
            .unwrap_or_else(|| std::path::PathBuf::from("."));
        let mut visiting = std::collections::HashSet::new();
        match inty::modules::resolve_imports(state, env, &program, &base_dir, &mut visiting) {
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
