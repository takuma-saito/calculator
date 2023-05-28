
use std::fmt;
use std::ops::{Add, Sub, Mul, Div};
use std::cmp::Ordering;

enum Expr {
    ExprPrimitive(ExprPrimitive),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
}

struct ExprPrimitive {
    primitive: Primitive,
    cast_type: CastType,
}

impl Into<ExprPrimitive> for i64 {
    fn into(self) -> ExprPrimitive {
        ExprPrimitive {
            primitive: Primitive::I64(self),
            cast_type: CastType::I64,
        }
    }
}

impl Into<ExprPrimitive> for f64 {
    fn into(self) -> ExprPrimitive {
        ExprPrimitive {
            primitive: Primitive::F64(self),
            cast_type: CastType::F64,
        }
    }
}

enum Primitive {
    I64(i64),
    F64(f64),
}

// F64 > I64
#[derive(Copy, Clone, PartialEq, Eq)]
enum CastType {
    I64,
    F64, 
}

impl PartialOrd for CastType {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (CastType::F64, x) if *x != CastType::F64 => Some(Ordering::Greater),
            (x, CastType::F64) if *x != CastType::F64 => Some(Ordering::Less),
            (_, _) => Some(Ordering::Equal),
        }
    }
}

impl Ord for CastType {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl ExprPrimitive {
    fn get_i64(&self) -> Option<i64> {
        if let Primitive::I64(val) = &self.primitive { Some(*val) } else { None }
    }
}

macro_rules! impl_number_ops {
    ($trait_name:ident, $method_name:ident) => {
        impl $trait_name for ExprPrimitive {
            type Output = ExprPrimitive;
            fn $method_name(self, other: ExprPrimitive) -> ExprPrimitive {
                let cast_type = self.cast_type.max(other.cast_type);
                let primitive = match (self.primitive, other.primitive, cast_type) {
                    (Primitive::I64(x), Primitive::I64(y), _) =>
                        Primitive::I64($trait_name::$method_name(x, y)),
                    (Primitive::F64(x), Primitive::F64(y), _) =>
                        Primitive::F64($trait_name::$method_name(x, y)),
                    (Primitive::I64(x), Primitive::F64(y), CastType::I64) =>
                        Primitive::I64($trait_name::$method_name(x, y as i64)),
                    (Primitive::I64(x), Primitive::F64(y), CastType::F64) =>
                        Primitive::F64($trait_name::$method_name(x as f64, y)),
                    (Primitive::F64(x), Primitive::I64(y), CastType::I64) =>
                        Primitive::I64($trait_name::$method_name(x as i64, y)),
                    (Primitive::F64(x), Primitive::I64(y), CastType::F64) =>
                        Primitive::F64($trait_name::$method_name(x, y as f64)),
                };
                ExprPrimitive { primitive: primitive, cast_type: cast_type }
            }
        }
    }
}

impl_number_ops!(Add, add);
impl_number_ops!(Sub, sub);
impl_number_ops!(Div, div);
impl_number_ops!(Mul, mul);

impl fmt::Display for ExprPrimitive {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.primitive {
            Primitive::I64(val) => write!(f, "{}", val),
            Primitive::F64(val) => write!(f, "{}", val),
        }
    }
}

trait NumOps<T = Self, Output = Self>:
    Add<T, Output = Output>
    + Sub<T, Output = Output>
    + Mul<T, Output = Output>
    + Div<T, Output = Output>
    + fmt::Display {}

impl Expr {
    fn eval(self) -> ExprPrimitive {
        match self {
            Self::ExprPrimitive(number) => number,
            Self::Add(a, b) => (*a).eval() + (*b).eval(),
            Self::Sub(a, b) => (*a).eval() - (*b).eval(),
            Self::Mul(a, b) => (*a).eval() * (*b).eval(),
            Self::Div(a, b) => (*a).eval() / (*b).eval(),
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::ExprPrimitive(num) => write!(f, "{}", num),
            Self::Add(ref a, ref b) => write!(f, "({} + {})", *a, *b),
            Self::Sub(ref a, ref b) => write!(f, "({} - {})", *a, *b),
            Self::Mul(ref a, ref b) => write!(f, "({} * {})", *a, *b),
            Self::Div(ref a, ref b) => write!(f, "({} / {})", *a, *b),
        }
    }
}

impl Add for Expr {
    type Output = Expr;
    fn add(self, other: Expr) -> Expr {
        Self::Add(Box::new(self), Box::new(other))
    }
}
impl Sub for Expr {
    type Output = Expr;
    fn sub(self, other: Expr) -> Expr {
        Self::Sub(Box::new(self), Box::new(other))
    }
}
impl Mul for Expr {
    type Output = Expr;
    fn mul(self, other: Expr) -> Expr {
        Self::Mul(Box::new(self), Box::new(other))
    }
}
impl Div for Expr {
    type Output = Expr;
    fn div(self, other: Expr) -> Expr {
        Self::Div(Box::new(self), Box::new(other))
    }
}

impl NumOps for Expr {}
impl NumOps for ExprPrimitive {}
impl NumOps for i64 {}

enum RpnOp {
    ExprPrimitive(ExprPrimitive),
    Add,
    Sub,
    Mul,
    Div,
}

enum TokenParserState {
    Beginning,
    Sign(bool),
    Decimal(i64),
    Float(f64),
}

// @startuml
// 
// [*] --> Sign: {+|-}
// [*] --> Decimal: {0-9}
// Sign --> Decimal: {0-9}
// Decimal --> Decimal: {0-9}
// Float --> Float: {0-9}
// Decimal --> Float: {.}
// Float --> ParsedFloat: {Null}
// Decimal --> ParsedDecimal: {Null}
// ParsedFloat -> [*]
// ParsedDecimal -> [*]
// 
// @enduml
fn tokenize_primitive(token: &str) -> ExprPrimitive { // TODO: Result 型
    let mut state = TokenParserState::Beginning;
    for ch in token.chars() {
        match state {
            TokenParserState::Beginning => {
                state = match ch {
                    '-'   => TokenParserState::Sign(false),
                    '+'   => TokenParserState::Sign(true),
                    '0' ..= '9' => TokenParserState::Decimal(ch.to_digit(10).unwrap() as i64),
                    _ => panic!("Unexpected token {}", ch),
                };
            },
            TokenParserState::Sign(b) => {
                let d = ch.to_digit(10).unwrap() as i64;
                state = TokenParserState::Decimal(if b {d} else { -1 * d });
            },
            TokenParserState::Decimal(val) => {
                state = if ch != '.' {
                    let d = ch.to_digit(10).unwrap() as i64;
                    TokenParserState::Decimal(val * 10 + d) // TODO u64 を超える場合を考慮
                } else {
                    TokenParserState::Float(val as f64)
                };
            },
            TokenParserState::Float(val) => {
                let newval = val * 10.0 + f64::from(ch.to_digit(10).unwrap()); // TODO: f64 を超える場合を考慮
                state = TokenParserState::Float(newval);
            },
        }
    }
    match state {
        TokenParserState::Decimal(val) => val.into(),
        TokenParserState::Float(val)   => val.into(),
        _ => panic!("Parse Faild"), // TODO: 適切なエラーを返却
    }
}
fn tokenize(text: &str) -> Vec<RpnOp> { // TODO: Result 型
    let mut i = 0usize;
    let mut ops = vec![];
    for token in text.split_whitespace() {
        let rpn_op = match token {
            " " => continue,
            "+" => RpnOp::Add,
            "-" => RpnOp::Sub,
            "*" => RpnOp::Mul,
            "/" => RpnOp::Div,
            _ => {
                RpnOp::ExprPrimitive(tokenize_primitive(token))
            }
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
            RpnOp::ExprPrimitive(num) => exprs.push(Expr::ExprPrimitive(num)),
            RpnOp::Add => { build_ast(&mut exprs, |a, b| a + b) },
            RpnOp::Sub => { build_ast(&mut exprs, |a, b| a - b) },
            RpnOp::Div => { build_ast(&mut exprs, |a, b| a / b) },
            RpnOp::Mul => { build_ast(&mut exprs, |a, b| a * b) },
        }
    }
    exprs.pop().unwrap() // TODO: stack のチェック
}

fn eval_and_get_i64(arith: Expr) -> i64 {
    arith.eval().get_i64().unwrap()
}

#[test]
fn test() {
    let mut arith = parse("1 2 +");
    assert_eq!("(2 + 1)", format!("{}", arith));
    assert_eq!(3i64, eval_and_get_i64(arith));
    arith = parse("3 4 + 1 2 - *");
    assert_eq!("((2 - 1) * (4 + 3))", format!("{}", arith));
    assert_eq!(7i64, eval_and_get_i64(arith));
    arith = parse("3 6 / 1 4 - * 10 +");
    assert_eq!("(10 + ((4 - 1) * (6 / 3)))", format!("{}", arith));
    assert_eq!(16i64, eval_and_get_i64(arith));
}

fn main() {
}

