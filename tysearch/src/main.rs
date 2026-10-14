use tysearch::discover::{climb, discover, Config};
use tysearch::lang::Language;
use tysearch::langs::{
    arith::Arith, coerce::Coerce, core::Core, model::Model, pairs::Pairs, refs::Refs,
    subtyping::Subtyping, unityped::Unityped,
};

const USAGE: &str = "usage: tysearch <arith|core|model|unityped|coerce|pairs|subtyping|refs> [--climb] [--corpus N] [--check N] [--seed N]

  --climb  grow the type language from ground rules, one capability at a
           time while it types more programs, then drop what isn't needed;
           print each step";

fn run<L: Language>(lang: &L, cfg: &Config, climbing: bool) {
    if climbing {
        let c = climb(lang, cfg);
        print!("{c}");
        println!("\nthe system found:\n");
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
    let mut climbing = false;
    while let Some(flag) = args.next() {
        if flag == "--climb" {
            climbing = true;
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
        _ => {
            eprintln!("{USAGE}");
            std::process::exit(2)
        }
    }
}
