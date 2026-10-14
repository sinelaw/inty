use tysearch::discover::{discover, Config};
use tysearch::langs::{
    arith::Arith, coerce::Coerce, core::Core, model::Model, pairs::Pairs, refs::Refs,
    subtyping::Subtyping, unityped::Unityped,
};

const USAGE: &str = "usage: tysearch <arith|core|model|unityped|coerce|pairs|subtyping|refs> [--corpus N] [--check N] [--seed N]";

fn main() {
    let mut args = std::env::args().skip(1);
    let lang = args.next().unwrap_or_else(|| {
        eprintln!("{USAGE}");
        std::process::exit(2)
    });
    let mut cfg = Config::default();
    while let Some(flag) = args.next() {
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
    let report = match lang.as_str() {
        "arith" => discover(&Arith::default(), &cfg),
        "core" => discover(&Core::default(), &cfg),
        "model" => discover(&Model::default(), &cfg),
        "unityped" => discover(&Unityped::default(), &cfg),
        "coerce" => discover(&Coerce::default(), &cfg),
        "pairs" => discover(&Pairs::default(), &cfg),
        "subtyping" => discover(&Subtyping::default(), &cfg),
        "refs" => discover(&Refs::default(), &cfg),
        _ => {
            eprintln!("{USAGE}");
            std::process::exit(2)
        }
    };
    print!("{report}");
}
