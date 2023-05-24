
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


mod Rpn {
    use Expr;
    enum RpnOp {
        Num(i32),
        Add,
        Sub,
        Mul,
        Div,
    }
    fn tokenize_num(mut i: &usize, text: &str) -> RpnOp { // TODO: Result 型が本来は適切
        let val = 0i32;
        while let Some(u) = text[*i].to_digit(10) {
            val += u as i32; // TODO: i32 に収まらない場合の処理
            *i += 1;
        }
        RpnOp::Num(val)
    }
    fn tokenize(text: String) -> Vec<RpnOp> {
        let mut i = 0usize;
        let mut ops = vec![];
        while i < text.len() {
            let c = text[i];
            let op = match c {
                ' ' => continue,
                '+' => RpnOp::Add,
                '-' => RpnOp::Sub,
                '*' => RpnOp::Mul,
                '/' => RpnOp::Div,
                _ => tokenize_num(&mut i, &text)
            };
            ops.push(op);
            i += 1;
        }
        ops
    }
    fn build_ast<F>(&mut exprs: Vec<Expr>, op: F)
        where F: Fn(Expr, Expr) -> Expr {
        let a = exprs.pop.unwrap();
        let b = exprs.pop.unwrap();
        exprs.push(op(a, b));
    }
    fn parse(text: String) -> Expr {
        let exprs = vec![];
        for token in tokenize(text) {
            match token {
                Num(i) => exprs.push(num(i)),
                Add => { build_ast(&mut exprs, add) },
                Sub => { build_ast(&mut exprs, sub) },
                Div => { build_ast(&mut exprs, div) },
                Mul => { build_ast(&mut exprs, mul) },
            }
        }
        exprs.pop().unwrap() // TODO: stack のチェック
    }
}

fn main() {
    let arith = add(num(1), mul(sub(num(10), num(4)), div(num(6), num(3))));
    println!("{} = {}", arith.to_string(), arith.eval());
}

