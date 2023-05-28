
use std::io;
use std::fmt;
use std::ops::{Add, Sub, Mul, Div, Rem};
use std::cmp::Ordering;

enum Expr {
    ExprPrimitive(ExprPrimitive),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    Rem(Box<Expr>, Box<Expr>),
    Pow(Box<Expr>, Box<Expr>),
    Exp(Box<Expr>),
    Ln(Box<Expr>),
}

struct ExprPrimitive {
    primitive: Primitive,
    cast_type: CastType,
}

impl From<i64> for ExprPrimitive {
    fn from(value: i64) -> Self {
        Self {
            primitive: Primitive::I64(value),
            cast_type: CastType::I64,
        }
    }
}

impl From<i32> for ExprPrimitive {
    fn from(value: i32) -> Self {
        (value as i64).into()
    }
}

impl From<ExprPrimitive> for Option<i32> {
    fn from(value: ExprPrimitive) -> Option<i32> {
        Option::<i64>::from(value).map(|v| v as i32)
    }
}

impl From<ExprPrimitive> for Option<i64> {
    fn from(value: ExprPrimitive) -> Option<i64> {
        if let Primitive::I64(val) = value.primitive { Some(val) } else { None }
    }
}

impl From<f64> for ExprPrimitive {
    fn from(value: f64) -> Self {
        Self {
            primitive: Primitive::F64(value),
            cast_type: CastType::F64,
        }
    }
}

impl From<f32> for ExprPrimitive {
    fn from(value: f32) -> Self {
        (value as f64).into()
    }
}

impl From<ExprPrimitive> for Option<f64> {
    fn from(value: ExprPrimitive) -> Option<f64> {
        if let Primitive::F64(val) = value.primitive { Some(val) } else { None }
    }
}

impl From<ExprPrimitive> for Option<f32> {
    fn from(value: ExprPrimitive) -> Option<f32> {
        Option::<f64>::from(value).map(|v| v as f32)
    }
}

enum Primitive {
    I64(i64),
    F64(f64),
    Fraction(Fraction),
}

impl Primitive {
    fn as_f64(&self) -> f64 {
        match self {
            Primitive::F64(val) => *val,
            Primitive::I64(val) => (*val) as f64,
            Primitive::Fraction(frac) => (frac.top as f64) / (frac.bottom as f64)
        }
    }
    fn as_i64(&self) -> i64 {
        match self {
            Primitive::F64(val) => (*val) as i64,
            Primitive::I64(val) => *val,
            Primitive::Fraction(frac) => frac.top / frac.bottom,
        }
    }
}

// F64 > Fraction > I64
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum CastType {
    I64,
    F64,
    Fraction,
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

#[derive(Clone, Debug)]
struct Fraction {
    top: i64,
    bottom: i64,
}

fn gcd(a: i64, b: i64) -> i64 {
    let (x, y) = if a > b { (a, b) } else { (b, a) }; // x > y
    if y == 0 { x } else { gcd(y, x % y) } // TODO: ループで実装
}

impl Fraction {
    // TODO: パフォーマンス課題
    fn simplify(self) -> Fraction {
        let Fraction { top: a, bottom: b } = self;
        let g = gcd(a, b);
        Fraction {
            top: a/g,
            bottom: b/g,
        }
    }
}

impl Add for Fraction {
    type Output = Fraction;
    fn add(self, other: Fraction) -> Fraction {
        let frac = Fraction {
            top: (self.top * other.bottom + self.bottom * other.top),
            bottom: self.bottom * other.bottom,
        };
        frac.simplify()
    }
}

impl Sub for Fraction {
    type Output = Fraction;
    fn sub(self, other: Fraction) -> Fraction {
        let frac = Fraction {
            top: (self.top * other.bottom - self.bottom * other.top),
            bottom: self.bottom * other.bottom,
        };
        frac.simplify()
    }
}

impl Mul for Fraction {
    type Output = Fraction;
    fn mul(self, other: Fraction) -> Fraction {
        let frac = Fraction {
            top: self.top * other.top,
            bottom: self.bottom * other.bottom,
        };
        frac.simplify()
    }
}

impl Div for Fraction {
    type Output = Fraction;
    fn div(self, other: Fraction) -> Fraction {
        let frac = Fraction {
            top: self.top * other.bottom,
            bottom: self.bottom * other.top,
        };
        frac.simplify()
    }
}

// TODO: 実装存在しない場合の処理検討
impl Rem for Fraction {
    type Output = Fraction;
    fn rem(self, other: Fraction) -> Fraction {
        unimplemented!()
    }
}

// TODO: 実装存在しない場合の処理検討
impl Pow for Fraction {
    type Output = Fraction;
    fn pow(self, other: Fraction) -> Fraction {
        unimplemented!()
    }
}

impl fmt::Display for Fraction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}//{})", self.top, self.bottom)
    }
}
impl fmt::Display for ExprPrimitive {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.primitive)
    }
}
impl fmt::Display for Primitive {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::I64(val) => write!(f, "{}", val),
            Self::F64(val) => write!(f, "{}", val),
            Self::Fraction(val) => write!(f, "{}", val),
        }
    }
}

trait ToFrac {
    fn to_frac(self) -> Fraction;
}

impl ToFrac for i64 {
    fn to_frac(self) -> Fraction {
        Fraction { top: self, bottom: 1 }
    }
}

// TODO: Fraction と F64 の変数変換
macro_rules! impl_number_ops {
    (@binary $trait_name:ident $method_name:ident) => {
        impl $trait_name for ExprPrimitive {
            type Output = ExprPrimitive;
            fn $method_name(self, other: ExprPrimitive) -> ExprPrimitive {
                let cast_type = self.cast_type.max(other.cast_type);
                let primitive = match (self.primitive, other.primitive, cast_type) {
                    (Primitive::I64(x), Primitive::I64(y), CastType::Fraction) =>
                        Primitive::Fraction($trait_name::$method_name(x.to_frac(), y.to_frac())),
                    (Primitive::I64(x), Primitive::I64(y), _) =>
                        Primitive::I64($trait_name::$method_name(x, y)),
                    (Primitive::F64(x), Primitive::F64(y), _) =>
                        Primitive::F64($trait_name::$method_name(x, y)),
                    (Primitive::Fraction(x), Primitive::Fraction(y), _) => 
                        Primitive::Fraction($trait_name::$method_name(x, y)),
                    (Primitive::I64(x), Primitive::Fraction(y), _) =>
                        Primitive::Fraction($trait_name::$method_name(x.to_frac(), y)),
                    (Primitive::Fraction(x), Primitive::I64(y), _) =>
                        Primitive::Fraction($trait_name::$method_name(x, y.to_frac())),
                    (Primitive::I64(x), Primitive::F64(y), CastType::I64) =>
                        Primitive::I64($trait_name::$method_name(x, y as i64)),
                    (Primitive::I64(x), Primitive::F64(y), CastType::F64) =>
                        Primitive::F64($trait_name::$method_name(x as f64, y)),
                    (Primitive::F64(x), Primitive::I64(y), CastType::I64) =>
                        Primitive::I64($trait_name::$method_name(x as i64, y)),
                    (Primitive::F64(x), Primitive::I64(y), CastType::F64) =>
                        Primitive::F64($trait_name::$method_name(x, y as f64)),
                    (a, b, c) => {
                        panic!("convert error: {} {} {:?}", a, b, c);
                    }
                };
                ExprPrimitive { primitive: primitive, cast_type: cast_type }
            }
        }
    };
    (@unary $trait_name:ident $method_name:ident) => {
        impl $trait_name for ExprPrimitive {
            type Output = ExprPrimitive;
            fn $method_name(self) -> ExprPrimitive {
                ExprPrimitive {
                    primitive: Primitive::F64(self.primitive.as_f64().$method_name()),
                    cast_type: CastType::F64,
                }
            }
        }
    };
}

impl_number_ops!(@binary Add add);
impl_number_ops!(@binary Sub sub);
impl_number_ops!(@binary Div div);
impl_number_ops!(@binary Mul mul);
impl_number_ops!(@binary Rem rem);
impl_number_ops!(@binary Pow pow);
impl_number_ops!(@unary Exp exp);
impl_number_ops!(@unary Ln ln);

trait Pow<Rhs = Self> {
    type Output;
    fn pow(self, rhs: Rhs) -> Self::Output;
}

impl Pow for i64 {
    type Output = i64;
    fn pow(self, other: i64) -> i64 {
        self.pow(other as u32)
    }
}

impl Pow for f64 {
    type Output = f64;
    fn pow(self, other: f64) -> f64 {
        self.powf(other)
    }
}

trait Exp {
    type Output;
    fn exp(self) -> Self::Output;
}

trait Ln {
    type Output;
    fn ln(self) -> Self::Output;
}

trait NumOps<T = Self, Output = Self>:
    Add<T, Output = Output>
    + Sub<T, Output = Output>
    + Mul<T, Output = Output>
    + Div<T, Output = Output>
    + Rem<T, Output = Output>
    + Pow<T, Output = Output>
    + Exp<Output = Output>
    + Ln<Output = Output>
    + fmt::Display {}

impl Expr {
    fn eval(self) -> ExprPrimitive {
        match self {
            Self::ExprPrimitive(p) => p,
            Self::Add(a, b) => Add::add((*a).eval(), (*b).eval()),
            Self::Sub(a, b) => Sub::sub((*a).eval(), (*b).eval()),
            Self::Mul(a, b) => Mul::mul((*a).eval(), (*b).eval()),
            Self::Div(a, b) => Div::div((*a).eval(), (*b).eval()),
            Self::Rem(a, b) => Rem::rem((*a).eval(), (*b).eval()),
            Self::Pow(a, b) => Pow::pow((*a).eval(), (*b).eval()),
            Self::Exp(a) => Exp::exp((*a).eval()),
            Self::Ln(a) => Ln::ln((*a).eval()),
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::ExprPrimitive(num) => write!(f, "{}", num),
            Self::Add(ref a, ref b)  => write!(f, "({} + {})", *a, *b),
            Self::Sub(ref a, ref b)  => write!(f, "({} - {})", *a, *b),
            Self::Mul(ref a, ref b)  => write!(f, "({} * {})", *a, *b),
            Self::Div(ref a, ref b)  => write!(f, "({} / {})", *a, *b),
            Self::Rem(ref a, ref b)  => write!(f, "({} % {})", *a, *b),
            Self::Pow(ref a, ref b)  => write!(f, "({} ** {})", *a, *b),
            Self::Exp(ref a) => write!(f, "exp({})", *a),
            Self::Ln(ref a) => write!(f, "ln({})", *a),
        }
    }
}

macro_rules! impl_for_expr {
    (@binary $trait_name:ident $method_name:ident) => {
        impl $trait_name for Expr {
            type Output = Expr;
            fn $method_name(self, other: Expr) -> Expr {
                Self::$trait_name(Box::new(self), Box::new(other))
            }
        }
    };
    (@unary $trait_name:ident $method_name:ident) => {
        impl $trait_name for Expr {
            type Output = Expr;
            fn $method_name(self) -> Expr {
                Self::$trait_name(Box::new(self))
            }
        }
    };
}

impl_for_expr!(@binary Add add);
impl_for_expr!(@binary Sub sub);
impl_for_expr!(@binary Div div);
impl_for_expr!(@binary Mul mul);
impl_for_expr!(@binary Rem rem);
impl_for_expr!(@binary Pow pow);
impl_for_expr!(@unary Exp exp);
impl_for_expr!(@unary Ln ln);

impl NumOps for Expr {}
impl NumOps for ExprPrimitive {}

enum RpnOp {
    ExprPrimitive(ExprPrimitive),
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Pow,
    Exp,
    Ln,
}

enum TokenParserState {
    Beginning,
    Sign(bool),
    NatNum(bool, u64),
    Decimal(bool, u64, u64, i32),
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
                    '0' ..= '9' => TokenParserState::NatNum(true, ch.to_digit(10).unwrap() as u64),
                    _ => panic!("Unexpected token {}", ch),
                };
            },
            TokenParserState::Sign(b) => {
                let d = ch.to_digit(10).unwrap() as u64;
                state = TokenParserState::NatNum(b, d);
            },
            TokenParserState::NatNum(sign, val) => {
                state = if ch != '.' {
                    let d = ch.to_digit(10).unwrap() as u64;
                    TokenParserState::NatNum(sign, val * 10 + d) // TODO u64 を超える場合を考慮
                } else {
                    TokenParserState::Decimal(sign, val, 0_u64, 0)
                };
            },
            TokenParserState::Decimal(sign, val, decimal_val, pos) => {
                let new_decimal_val = 10_u64 * decimal_val + (ch.to_digit(10).unwrap() as u64); // TODO: f64 を超える場合を考慮
                state = TokenParserState::Decimal(sign, val, new_decimal_val, pos - 1);
            },
        }
    }
    match state {
        TokenParserState::NatNum(sign, val)  => 
            (if sign { val as i64 } else { -(val as i64) }).into(),
        TokenParserState::Decimal(sign, val, decimal_val, pos) => {
            let v = (val as f64) + (decimal_val as f64) * (10.0_f64).powi(pos);
            let ret = if sign { v } else { -v };
            ret.into()
        },
        _ => panic!("Parse Faild"), // TODO: 適切なエラーを返却
    }
}
fn tokenize(text: &str) -> Vec<RpnOp> { // TODO: Result 型
    let mut ops = vec![];
    for token in text.split_whitespace() {
        let rpn_op = match token {
            " " => continue,
            "+" => RpnOp::Add,
            "-" => RpnOp::Sub,
            "*" => RpnOp::Mul,
            "/" => RpnOp::Div,
            "%" => RpnOp::Rem,
            "**" => RpnOp::Pow,
            "exp" => RpnOp::Exp,
            "ln" => RpnOp::Ln,
            _ => {
                RpnOp::ExprPrimitive(tokenize_primitive(token))
            }
        };
        ops.push(rpn_op);
    }
    ops
}
fn build_ast_binary<F>(exprs: &mut Vec<Expr>, op: F)
    where F: FnOnce(Expr, Expr) -> Expr {
    let a = exprs.pop().unwrap();
    let b = exprs.pop().unwrap();
    exprs.push(op(a, b));
}
fn build_ast_unary<F>(exprs: &mut Vec<Expr>, op: F)
    where F: FnOnce(Expr) -> Expr {
    let a = exprs.pop().unwrap();
    exprs.push(op(a));
}
fn parse<N: AsRef<str>>(text: N) -> Expr {
    let mut exprs = vec![];
    for token in tokenize(text.as_ref()) {
        match token {
            RpnOp::ExprPrimitive(num) => exprs.push(Expr::ExprPrimitive(num)),
            RpnOp::Add => { build_ast_binary(&mut exprs, |a, b| Add::add(a, b)) },
            RpnOp::Sub => { build_ast_binary(&mut exprs, |a, b| Sub::sub(a, b)) },
            RpnOp::Div => { build_ast_binary(&mut exprs, |a, b| Div::div(a, b)) },
            RpnOp::Mul => { build_ast_binary(&mut exprs, |a, b| Mul::mul(a, b)) },
            RpnOp::Rem => { build_ast_binary(&mut exprs, |a, b| Rem::rem(a, b)) },
            RpnOp::Pow => { build_ast_binary(&mut exprs, |a, b| Pow::pow(a, b)) },
            RpnOp::Ln  => { build_ast_unary(&mut exprs, |a| Ln::ln(a)) },
            RpnOp::Exp => { build_ast_unary(&mut exprs, |a| Exp::exp(a)) },
        }
    }
    exprs.pop().unwrap() // TODO: stack のチェック
}

macro_rules! parser_assert_eq {
    ($input:expr, $display_expected_value:expr, $eval_expected_value:expr) => {
        let arith = parse($input);
        assert_eq!($display_expected_value, format!("{}", arith));
        assert_eq!($eval_expected_value, arith.eval().into());
    }
}

#[test]
fn test_parse() {
    parser_assert_eq!("1 2 +", "(2 + 1)", Some(3));
    parser_assert_eq!("3 4 + 1 2 - *", "((2 - 1) * (4 + 3))", Some(7));
    parser_assert_eq!("3 6 / 1 4 - * 10 +", "(10 + ((4 - 1) * (6 / 3)))", Some(16));
    parser_assert_eq!("3.1 2.4 +", "(2.4 + 3.1)", Some(5.5));
    parser_assert_eq!("-1", "-1", Some(-1));
    parser_assert_eq!("-1.234 1.534 *", "(1.534 * -1.234)", Some(-1.892956));
    parser_assert_eq!("-1 -1.5 *", "(-1.5 * -1)", Some(1.5));
    parser_assert_eq!("-1 -1.5 *", "(-1.5 * -1)", Some(1.5));
    parser_assert_eq!("2 3.1 4.2 / 3 1.5 + * -", "(((1.5 + 3) * (4.2 / 3.1)) - 2)", Some(4.096774193548388));
    parser_assert_eq!("9 100 %", "(100 % 9)", Some(1));
    parser_assert_eq!("9 100 % 1 +", "(1 + (100 % 9))", Some(2));
    parser_assert_eq!("2.0 exp", "exp(2)", Some(7.38905609893065));
    parser_assert_eq!("2.0 ln", "ln(2)", Some(0.6931471805599453));
    parser_assert_eq!("5 3 **", "(3 ** 5)", Some(243));
    parser_assert_eq!("4 2.21234 **", "(2.21234 ** 4)", Some(23.955623922523824));
    parser_assert_eq!("2.5 3 **", "(3 ** 2.5)", Some(15.588457268119896));
}

fn main() -> io::Result<()> {
    for line in io::stdin().lines() {
        let arith = parse(line?);
        println!("{} = {}", arith.to_string(), arith.eval());
    }
    Ok(())
}
