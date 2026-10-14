use tysearch::discover::{discover, Config};
use tysearch::langs::{arith::Arith, core::Core};

const USAGE: &str = "usage: tysearch <arith|core> [--learn N] [--check N]";

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
            ("--learn", Some(n)) => cfg.learn_size = n,
            ("--check", Some(n)) => cfg.check_size = n,
            _ => {
                eprintln!("{USAGE}");
                std::process::exit(2)
            }
        }
    }
    let report = match lang.as_str() {
        "arith" => discover(&Arith::default(), &cfg),
        "core" => discover(&Core::default(), &cfg),
        _ => {
            eprintln!("{USAGE}");
            std::process::exit(2)
        }
    };
    print!("{report}");
}
