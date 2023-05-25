
use std::fmt;

enum Expr {
    Num(i32),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
}

impl Expr {
    fn eval(self) -> i32 {
        match self {
            Expr::Num(val) => val,
            Expr::Add(a, b) => (*a).eval() + (*b).eval(),
            Expr::Sub(a, b) => (*a).eval() - (*b).eval(),
            Expr::Mul(a, b) => (*a).eval() * (*b).eval(),
            Expr::Div(a, b) => (*a).eval() / (*b).eval(),
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expr::Num(a) => write!(f, "{}", a),
            Expr::Add(ref a, ref b) => write!(f, "({} + {})", *a, *b),
            Expr::Sub(ref a, ref b) => write!(f, "({} - {})", *a, *b),
            Expr::Mul(ref a, ref b) => write!(f, "({} * {})", *a, *b),
            Expr::Div(ref a, ref b) => write!(f, "({} / {})", *a, *b),
        }
    }
}

fn add(a: Expr, b: Expr) -> Expr { Expr::Add(Box::new(a), Box::new(b)) }
fn sub(a: Expr, b: Expr) -> Expr { Expr::Sub(Box::new(a), Box::new(b)) }
fn mul(a: Expr, b: Expr) -> Expr { Expr::Mul(Box::new(a), Box::new(b)) }
fn div(a: Expr, b: Expr) -> Expr { Expr::Div(Box::new(a), Box::new(b)) }
fn num(val: i32) -> Expr { Expr::Num(val) }

enum RpnOp {
    Num(i32),
    Add,
    Sub,
    Mul,
    Div,
}
fn tokenize(text: &str) -> Vec<RpnOp> {
    let mut i = 0usize;
    let mut ops = vec![];
    for token in text.split_whitespace() {
        let rpn_op = match token {
            " " => continue,
            "+" => RpnOp::Add,
            "-" => RpnOp::Sub,
            "*" => RpnOp::Mul,
            "/" => RpnOp::Div,
            _ =>   RpnOp::Num(token.parse::<i32>().unwrap()),
        };
        ops.push(rpn_op);
    }
    ops
}
fn build_ast<F>(exprs: &mut Vec<Expr>, op: F)
    where F: Fn(Expr, Expr) -> Expr {
    let a = exprs.pop().unwrap();
    let b = exprs.pop().unwrap();
    exprs.push(op(a, b));
}
fn parse(text: &str) -> Expr {
    let mut exprs = vec![];
    for token in tokenize(text) {
        match token {
            RpnOp::Num(i) => exprs.push(num(i)),
            RpnOp::Add => { build_ast(&mut exprs, add) },
            RpnOp::Sub => { build_ast(&mut exprs, sub) },
            RpnOp::Div => { build_ast(&mut exprs, div) },
            RpnOp::Mul => { build_ast(&mut exprs, mul) },
        }
    }
    exprs.pop().unwrap() // TODO: stack のチェック
}

fn main() {
    let arith = parse("3 6 / 1 4 - * 10 +");
    //let arith = parse("3 4 + 1 2 - *");
    println!("{} = {}", arith.to_string(), arith.eval());
}

