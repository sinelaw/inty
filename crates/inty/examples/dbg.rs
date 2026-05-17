use inty::infer::parse_type_annotation;
use inty::lexer::Span;

fn main() {
    let cases = [
        "(start: Number, end?: Number) => String",
        "(a?: Number, b: Number) => String",
        "(start?: Number, end: Number) => String",
        "(a: Number, b?: Number, c: Number) => String",
    ];
    for src in cases {
        match parse_type_annotation(src, Span::new(0, src.len()), 1000) {
            Ok((ty, _)) => println!("OK:  {}\n     => {:?}", src, ty),
            Err(e) => println!("ERR: {}\n     => {:?}", src, e),
        }
    }
}
