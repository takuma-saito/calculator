
use std::fmt;
use std::ops;

enum Expr {
    NumI64(i64),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
}

struct Faction {
    num: i64,
    den: i64,
}

impl Expr {
    fn eval(self) -> i64 {
        match self {
            Expr::NumI64(val) => val,
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
            Expr::NumI64(a) => write!(f, "{}", a),
            Expr::Add(ref a, ref b) => write!(f, "({} + {})", *a, *b),
            Expr::Sub(ref a, ref b) => write!(f, "({} - {})", *a, *b),
            Expr::Mul(ref a, ref b) => write!(f, "({} * {})", *a, *b),
            Expr::Div(ref a, ref b) => write!(f, "({} / {})", *a, *b),
        }
    }
}

impl ops::Add<Expr> for Expr {
    type Output = Expr;

    fn add(self, other: Expr) -> Expr {
        Expr::Add(Box::new(self), Box::new(other))
    }
}

impl ops::Sub<Expr> for Expr {
    type Output = Expr;

    fn sub(self, other: Expr) -> Expr {
        Expr::Sub(Box::new(self), Box::new(other))
    }
}

impl ops::Mul<Expr> for Expr {
    type Output = Expr;

    fn mul(self, other: Expr) -> Expr {
        Expr::Mul(Box::new(self), Box::new(other))
    }
}

impl ops::Div<Expr> for Expr {
    type Output = Expr;
    
    fn div(self, other: Expr) -> Expr {
        Expr::Div(Box::new(self), Box::new(other))
    }
}

fn num(val: i64) -> Expr { Expr::NumI64(val) }

enum RpnOp {
    NumI64(i64),
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
            _ =>   RpnOp::NumI64(token.parse::<i64>().unwrap()),
        };
        ops.push(rpn_op);
    }
    ops
}
fn build_ast<F>(exprs: &mut Vec<Expr>, op: F)
    where F: FnOnce(Expr, Expr) -> Expr {
    let a = exprs.pop().unwrap();
    let b = exprs.pop().unwrap();
    exprs.push(op(a, b));
}
fn parse(text: &str) -> Expr {
    let mut exprs = vec![];
    for token in tokenize(text) {
        match token {
            RpnOp::NumI64(i) => exprs.push(num(i)),
            RpnOp::Add => { build_ast(&mut exprs, |a, b| a + b) },
            RpnOp::Sub => { build_ast(&mut exprs, |a, b| a - b) },
            RpnOp::Div => { build_ast(&mut exprs, |a, b| a / b) },
            RpnOp::Mul => { build_ast(&mut exprs, |a, b| a * b) },
        }
    }
    exprs.pop().unwrap() // TODO: stack のチェック
}

#[test]
fn test() {
    let mut arith = parse("1 2 +");
    assert_eq!("(2 + 1)", format!("{}", arith));
    assert_eq!(3, arith.eval());
    arith = parse("3 4 + 1 2 - *");
    assert_eq!("((2 - 1) * (4 + 3))", format!("{}", arith));
    assert_eq!(7, arith.eval());
    arith = parse("3 6 / 1 4 - * 10 +");
    assert_eq!("(10 + ((4 - 1) * (6 / 3)))", format!("{}", arith));
    assert_eq!(16, arith.eval());
}

fn main() {
}

