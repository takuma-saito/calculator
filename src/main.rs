
use std::fmt;
use std::ops::{Add, Sub, Mul, Div};

enum Expr<T: NumOp + fmt::Display> {
    NumI64(T),
    Add(Box<Expr<T>>, Box<Expr<T>>),
    Sub(Box<Expr<T>>, Box<Expr<T>>),
    Mul(Box<Expr<T>>, Box<Expr<T>>),
    Div(Box<Expr<T>>, Box<Expr<T>>),
}

struct Faction {
    num: i64,
    den: i64,
}

impl<T: NumOp + fmt::Display> Expr<T> {
    fn eval(self) -> T {
        match self {
            Expr::NumI64(val) => val,
            Expr::Add(a, b) => (*a).eval() + (*b).eval(),
            Expr::Sub(a, b) => (*a).eval() - (*b).eval(),
            Expr::Mul(a, b) => (*a).eval() * (*b).eval(),
            Expr::Div(a, b) => (*a).eval() / (*b).eval(),
        }
    }
}

impl<T: NumOp + fmt::Display> fmt::Display for Expr<T> {
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

trait NumOp<T = Self, Output = Self>:
    Add<T, Output = Output>
    + Sub<T, Output = Output>
    + Mul<T, Output = Output>
    + Div<T, Output = Output> {}

impl<T: NumOp + fmt::Display> Add for Expr<T> {
    type Output = Expr<T>;
    fn add(self, other: Expr<T>) -> Expr<T> {
        Expr::Add(Box::new(self), Box::new(other))
    }
}
impl<T: NumOp + fmt::Display> Sub for Expr<T> {
    type Output = Expr<T>;
    fn sub(self, other: Expr<T>) -> Expr<T> {
        Expr::Sub(Box::new(self), Box::new(other))
    }
}
impl<T: NumOp + fmt::Display> Mul for Expr<T> {
    type Output = Expr<T>;
    fn mul(self, other: Expr<T>) -> Expr<T> {
        Expr::Mul(Box::new(self), Box::new(other))
    }
}
impl<T: NumOp + fmt::Display> Div for Expr<T> {
    type Output = Expr<T>;
    fn div(self, other: Expr<T>) -> Expr<T> {
        Expr::Div(Box::new(self), Box::new(other))
    }
}

impl<T: NumOp + fmt::Display> NumOp for Expr<T> {}
impl NumOp for i64 {}

fn num(val: i64) -> Expr<i64> { Expr::NumI64(val) }

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
fn build_ast<F>(exprs: &mut Vec<Expr<i64>>, op: F)
    where F: FnOnce(Expr<i64>, Expr<i64>) -> Expr<i64> {
    let a = exprs.pop().unwrap();
    let b = exprs.pop().unwrap();
    exprs.push(op(a, b));
}
fn parse(text: &str) -> Expr<i64> {
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
    assert_eq!(3i64, arith.eval());
    arith = parse("3 4 + 1 2 - *");
    assert_eq!("((2 - 1) * (4 + 3))", format!("{}", arith));
    assert_eq!(7i64, arith.eval());
    arith = parse("3 6 / 1 4 - * 10 +");
    assert_eq!("(10 + ((4 - 1) * (6 / 3)))", format!("{}", arith));
    assert_eq!(16i64, arith.eval());
}

fn main() {
}

