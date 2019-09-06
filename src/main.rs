use copl_solver::interpreter::*;
use copl_solver::lexer::*;
use copl_solver::parser::*;
use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();
    if 1 < args.len() {
        //dbg!(lex(&args[1]));
        //dbg!(parse(lex(&args[1]).unwrap()));
        let mut i = Interpreter::new();
        dbg!(i.eval(&parse(lex(&args[1]).unwrap()).unwrap()));
    }
}
