use tysearch::discover::{climb_with, discover, step_report, Config, System};
use tysearch::lang::Language;
use tysearch::langs::{
    arith::Arith, coerce::Coerce, core::Core, effects::Effects, files::Files, model::Model,
    pairs::Pairs, printf::Printf, refs::Refs, secrets::Secrets, subtyping::Subtyping, units::Units,
    unityped::Unityped,
};

const USAGE: &str = "usage: tysearch <arith|core|model|unityped|coerce|pairs|subtyping|refs|units|files|effects|secrets|printf> [--corpus N] [--check N] [--seed N]

Finds a type system for the language by itself: it starts from the
simplest, adds what types more of its safe programs (type variables,
function and object types, binders, let-generalisation, exit types,
subtyping, unions, narrowing), drops what isn't needed, and prints each
type system as it finds it.

  --features vars,refined,binders,generalise,exits,subtyping,unions,narrowing
           one run with only those capabilities (for working on the search)";

fn run<L: Language>(lang: &L, cfg: &Config, climbing: bool) {
    if climbing {
        // Each step as it comes, with the type system it leaves.
        let mut prev = System::default();
        let c = climb_with(lang, cfg, |i, s| {
            print!("{}", step_report(i, s, &prev));
            if s.kept {
                prev = s.discovery.system();
            }
            use std::io::Write;
            std::io::stdout().flush().ok();
        });
        print!("{}", c.summary());
        println!("\nthe ladder, ready for a document:\n");
        print!("{}", c.doc());
        println!("\nthe system found, in full:\n");
        print!("{}", c.result());
    } else {
        print!("{}", discover(lang, cfg));
    }
}

fn main() {
    let mut args = std::env::args().skip(1);
    let lang = args.next().unwrap_or_else(|| {
        eprintln!("{USAGE}");
        std::process::exit(2)
    });
    let mut cfg = Config::default();
    // The climb unless a developer pins the capabilities.
    let mut climbing = true;
    while let Some(flag) = args.next() {
        // The default; kept for old scripts.
        if flag == "--climb" {
            continue;
        }
        // For working on the search: `--features vars,refined,binders`
        // runs with just those capabilities.
        if flag == "--features" {
            let list = args.next().unwrap_or_default();
            let mut f = tysearch::search::Features::NONE;
            for name in list.split(',') {
                match name {
                    "vars" => f.vars = true,
                    "refined" => f.refined = true,
                    "binders" => {
                        f.binders = true;
                        f.unknown = true
                    }
                    "generalise" => f.generalise = true,
                    "exits" => f.exits = true,
                    "subtyping" => f.subtyping = true,
                    "unions" => f.unions = true,
                    "narrowing" => f.narrowing = true,
                    _ => {
                        eprintln!("{USAGE}");
                        std::process::exit(2)
                    }
                }
            }
            cfg.search.features = f;
            climbing = false;
            continue;
        }
        let n = args.next().and_then(|n| n.parse().ok());
        match (flag.as_str(), n) {
            ("--corpus", Some(n)) => cfg.corpus_size = n as usize,
            ("--check", Some(n)) => cfg.check_size = n as usize,
            ("--seed", Some(n)) => cfg.seed = n,
            _ => {
                eprintln!("{USAGE}");
                std::process::exit(2)
            }
        }
    }
    match lang.as_str() {
        "arith" => run(&Arith::default(), &cfg, climbing),
        "core" => run(&Core::default(), &cfg, climbing),
        "model" => run(&Model::default(), &cfg, climbing),
        "unityped" => run(&Unityped::default(), &cfg, climbing),
        "coerce" => run(&Coerce::default(), &cfg, climbing),
        "pairs" => run(&Pairs::default(), &cfg, climbing),
        "subtyping" => run(&Subtyping::default(), &cfg, climbing),
        "refs" => run(&Refs::default(), &cfg, climbing),
        "units" => run(&Units::default(), &cfg, climbing),
        "files" => run(&Files::default(), &cfg, climbing),
        "effects" => run(&Effects::default(), &cfg, climbing),
        "secrets" => run(&Secrets::default(), &cfg, climbing),
        "printf" => run(&Printf::default(), &cfg, climbing),
        _ => {
            eprintln!("{USAGE}");
            std::process::exit(2)
        }
    }
}
