
mod

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

    
    fn to_string(&self) -> String {
        match self {
            Expr::Num(ref a) => (*a).to_string(),
            Expr::Add(ref a, ref b) => format!("({} + {})", (*a).to_string(), (*b).to_string()),
            Expr::Sub(ref a, ref b) => format!("({} - {})", (*a).to_string(), (*b).to_string()),
            Expr::Mul(ref a, ref b) => format!("({} * {})", (*a).to_string(), (*b).to_string()),
            Expr::Div(ref a, ref b) => format!("({} / {})", (*a).to_string(), (*b).to_string()),
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
fn tokenize_num(i: &mut usize, chars: &Vec<char>) -> RpnOp { // TODO: Result 型が本来は適切
    let mut val = 0i32;
    while *i < chars.len() {
        match chars[*i] {
            c @ '0' ..= '9' => {
                val = val * 10 + c.to_digit(10).unwrap() as i32; // TODO: i32 に収まらない場合の対応
                *i += 1;
            },
            _ => { *i -= 1; break; },
        }
    }
    RpnOp::Num(val)
}
fn tokenize(text: &str) -> Vec<RpnOp> {
    let mut i = 0usize;
    let mut ops = vec![];
    let chars = text.chars().collect::<Vec<_>>(); 
    while i < chars.len() {
        let c = chars[i];
        let u = match c {
            ' ' => None,
            '+' => Some(RpnOp::Add),
            '-' => Some(RpnOp::Sub),
            '*' => Some(RpnOp::Mul),
            '/' => Some(RpnOp::Div),
            _ =>   Some(tokenize_num(&mut i, &chars))
        };
        match u {
            Some(op) => ops.push(op),
            None => {},
        }
        i += 1;
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

