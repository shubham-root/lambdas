/// This is an example domain, heavily commented to explain how to implement your own!
use crate::*;
extern crate regex;
use ordered_float::OrderedFloat;
use regex::Regex;
use std::io::Write;
use std::str;
use std::string::String;
use std::sync::Arc;
use std::time::Duration;
use turtle::{Canvas, Turtle};

/// A simple domain with ints and polymorphic lists (allows nested lists).
/// Generally it's good to be able to imagine the hindley milner type system
/// for your domain so that it's compatible when we add that later. In this case the types
/// would look like `T := (T -> T) | Int | List(T)` where functions are handled
/// by dreamegg::domain::Val so they don't appear here.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum LogoVal {
    Int(i32),
    List(Vec<Val>),
    Canv(Canvas),
    Str(String),
    Bool(bool),
}

// aliases of various typed specialized to our LogoVal
type Val = crate::eval::Val<LogoVal>;
type Evaluator<'a> = crate::eval::Evaluator<'a, LogoVal>;
type VResult = crate::eval::VResult<LogoVal>;
type Env = crate::eval::Env<LogoVal>;

// to more concisely refer to the variants
use LogoVal::*;

// In this domain, we limit how many times "fix" can be invoked.
// This is a crude way of finding infinitely looping programs.
const MAX_FIX_INVOCATIONS: u32 = 20;

// From<Val> impls are needed for unwrapping values. We can assume the program
// has been type checked so it's okay to panic if the type is wrong. Each val variant
// must map to exactly one unwrapped type (though it doesnt need to be one to one in the
// other direction)
impl FromVal<LogoVal> for i32 {
    fn from_val(v: Val) -> Result<Self, VError> {
        match v {
            Dom(Int(i)) => Ok(i),
            _ => Err("from_val_to_i32: not an int".into()),
        }
    }
}

impl FromVal<LogoVal> for String {
    fn from_val(v: Val) -> Result<Self, VError> {
        match v {
            Dom(Str(s)) => Ok(s.to_string()),
            _ => Err("from_val_to_string: not a string".into()),
        }
    }
}

impl<T: FromVal<LogoVal>> FromVal<LogoVal> for Vec<T> {
    fn from_val(v: Val) -> Result<Self, VError> {
        match v {
            Dom(List(v)) => v.into_iter().map(|v| T::from_val(v)).collect(),
            _ => Err("from_val_to_vec: not a list".into()),
        }
    }
}

impl FromVal<LogoVal> for bool {
    fn from_val(v: Val) -> Result<Self, VError> {
        match v {
            Dom(Bool(b)) => Ok(b),
            _ => Err("from_val_to_bool: not a bool".into()),
        }
    }
}

impl FromVal<LogoVal> for Canvas {
    fn from_val(v: Val) -> Result<Self, VError> {
        // dbg!(&v);
        match v {
            Dom(Canv(b)) => Ok(b),
            _ => Err("from_val_to_canvas: not a canvas".into()),
        }
    }
}

// These Into<Val>s are convenience functions. It's okay if theres not a one to one mapping
// like this in all domains - it just makes .into() save us a lot of work if there is.
impl From<i32> for Val {
    fn from(i: i32) -> Val {
        Dom(Int(i))
    }
}

impl From<String> for Val {
    fn from(i: String) -> Val {
        Dom(Str(i))
    }
}
impl<T: Into<Val>> From<Vec<T>> for Val {
    fn from(vec: Vec<T>) -> Val {
        Dom(List(vec.into_iter().map(|v| v.into()).collect()))
    }
}

impl From<bool> for Val {
    fn from(b: bool) -> Val {
        Dom(Bool(b))
    }
}

impl From<Canvas> for Val {
    fn from(b: Canvas) -> Val {
        Dom(Canv(b))
    }
}

#[derive(Default, Debug)]
pub struct LogoData {
    fix_counter: u32,
}

// here we actually implement Domain for our domain.
impl Domain for LogoVal {
    // we dont use Data here
    type Data = LogoData;

    fn new_dsl() -> DSL<Self> {
        DSL::new(
            vec![
                Production::func(
                    "fix1",
                    "t0 -> ((t0 -> t1) -> t0 -> t1) -> t1",
                    Arc::new(fix1),
                    ordered_float::OrderedFloat(0.),
                ),
                Production::func(
                    "fix",
                    "((t0 -> t1) -> t0 -> t1) -> t0 -> t1",
                    Arc::new(fix),
                    ordered_float::OrderedFloat(0.),
                ),
                // Production::func(
                //     "logo_repeat",
                //     "int -> canvas -> canvas",
                //     Arc::new(primitive_repeat),
                //     ordered_float::OrderedFloat(0.),
                // ),
                Production::func(
                    "logo_init",
                    "t0 -> canvas",
                    Arc::new(primitive_init),
                    ordered_float::OrderedFloat(0.),
                ),
                Production::func(
                    "logo_fd",
                    "int -> t0 -> canvas",
                    Arc::new(primitive_forward),
                    ordered_float::OrderedFloat(0.),
                ),
                Production::func(
                    "logo_rt",
                    "int -> t0 -> canvas",
                    Arc::new(primitive_right),
                    ordered_float::OrderedFloat(0.),
                ),
                Production::func(
                    "logo_pu",
                    "t0 -> canvas",
                    Arc::new(primitive_penup),
                    ordered_float::OrderedFloat(0.),
                ),
                Production::func(
                    "logo_pd",
                    "t0 -> canvas",
                    Arc::new(primitive_pendown),
                    ordered_float::OrderedFloat(0.),
                ),
                Production::func(
                    "logo_repeat",
                    "canvas -> int -> canvas -> canvas",
                    Arc::new(primitive_repeat),
                    ordered_float::OrderedFloat(0.),
                ),
                Production::func(
                    "logo_svg_out",
                    "canvas -> str",
                    Arc::new(primitive_svg_out),
                    ordered_float::OrderedFloat(0.),
                ),
                Production::val(
                    "[]",
                    "(list t0)",
                    Dom(List(vec![])),
                    ordered_float::OrderedFloat(0.),
                ),
                Production::val("0", "int", Dom(Int(0)), ordered_float::OrderedFloat(0.)),
                Production::val("1", "int", Dom(Int(1)), ordered_float::OrderedFloat(0.)),
                Production::val("2", "int", Dom(Int(2)), ordered_float::OrderedFloat(0.)),
            ],
            OrderedFloat(0.0),
        )
    }

    // val_of_prim takes a symbol like "+" or "0" and returns the corresponding Val.
    // Note that it can largely just be a call to the global hashmap PRIMS that define_semantics generated
    // however you're also free to do any sort of generic parsing you want, allowing for domains with
    // infinite sets of values or dynamically generated values. For example here we support all integers
    // and all integer lists.
    fn val_of_prim_fallback(p: &Symbol) -> Option<Val> {
        // starts with digit -> Int
        // dbg!(p.clone());
        if p.chars().next().unwrap().is_ascii_digit() {
            let i: i32 = p.parse().ok()?;
            Some(Int(i).into())
        }
        // starts with `[` -> List (must be all ints)
        else if p.starts_with("['") {
            // dbg!(serde_json::from_str(p).ok()?);
            // Attempt to parse as Vec<i32> first
            let corrected_p = p.replace('\'', "\"");
            let strvec: Vec<String> = match serde_json::from_str(&corrected_p) {
                Ok(vec) => vec,
                Err(e) => {
                    eprintln!("Failed to parse JSON: {}", e);
                    return None;
                }
            };
            // dbg!(strvec.clone());
            let valvec: Vec<Val> = strvec.into_iter().map(|v| Dom(Str(v))).collect();
            Some(List(valvec).into())
        } else if p.starts_with('[') {
            // dbg!("NUM LIST");
            // dbg!(serde_json::from_str(p).ok()?);
            // Attempt to parse as Vec<i32> first

            let intvec: Vec<i32> = serde_json::from_str(p).ok()?;
            let valvec: Vec<Val> = intvec.into_iter().map(|v| Dom(Int(v))).collect();
            Some(List(valvec).into())
        } else if p.starts_with("'") && p.ends_with("'") {
            // Assuming you have a way to handle strings in your `Val` enum, like `Str(String)`
            // Remove the leading and trailing quotes and convert to your `Val` type
            let corrected_p = p.replace('\'', "\"").replace("'", "");
            let str_content = corrected_p.trim_matches('"').to_string();
            Some(Str(str_content).into())
        } else {
            None
        }
    }

    fn type_of_dom_val(&self) -> SlowType {
        match self {
            Int(_) => SlowType::base(Symbol::from("int")),
            List(xs) => {
                let elem_tp = if xs.is_empty() {
                    SlowType::Var(0) // (list t0)
                } else {
                    // todo here we just use the type of the first entry as the type
                    Self::type_of_dom_val(&xs.first().unwrap().clone().dom().unwrap())
                    // assert!(xs.iter().all(|v| Self::type_of_dom_val(v.clone().dom().unwrap())))
                };
                SlowType::Term("list".into(), vec![elem_tp])
            }
            Str(_) => SlowType::base(Symbol::from("str")),
            Bool(_) => SlowType::base("bool".into()),
            Canv(_) => SlowType::base("canvas".into()),
        }
    }
}

// *** DSL FUNCTIONS ***
// See comments throughout pointing out useful aspects

use once_cell::sync::Lazy;
pub static FIX: Lazy<Val> = Lazy::new(|| PrimFun(CurriedFn::new(Symbol::from("fix"), 2)));

/// fix f x = f(fix f)(x)
/// type i think: ((t0 -> t1) -> t0 -> t1) -> t0 -> t1
fn fix(mut args: Env, handle: &Evaluator) -> VResult {
    handle.data.borrow_mut().fix_counter += 1;
    if handle.data.borrow().fix_counter > MAX_FIX_INVOCATIONS {
        return Err(format!(
            "Exceeded max number of fix invocations. Max was {}",
            MAX_FIX_INVOCATIONS
        ));
    }
    load_args!(args, fn_val: Val, x: Val);

    // fix f x = f(fix f)(x)
    let fixf = handle.apply(FIX.clone(), fn_val.clone()).unwrap();
    let res = match handle.apply(fn_val, fixf) {
        Ok(ffixf) => handle.apply(ffixf, x),
        Err(err) => Err(format!("Could not apply fixf to f: {}", err)),
    };
    handle.data.borrow_mut().fix_counter -= 1;
    res
    // handle.apply(fn_val, fixf)
}

/// fix x f = f(fix f)(x)
/// type i think: t0 -> ((t0 -> t1) -> t0 -> t1) -> t1
/// This is to match dreamcoder.
fn fix1(mut args: Env, handle: &Evaluator) -> VResult {
    args.reverse();
    fix(args, handle)
}

fn cons(mut args: Env, _handle: &Evaluator) -> VResult {
    load_args!(args, x:Val, xs:Vec<Val>);
    let mut rxs = xs;
    rxs.insert(0, x);
    // println!("{:?}", rxs);
    ok(rxs)
}

fn car(mut args: Env, _handle: &Evaluator) -> VResult {
    load_args!(args, xs: Vec<Val>);
    if xs.is_empty() {
        Err(String::from("car called on empty list"))
    } else {
        ok(xs[0].clone())
    }
}

fn cdr(mut args: Env, _handle: &Evaluator) -> VResult {
    load_args!(args, xs: Vec<Val>);
    if xs.is_empty() {
        Err(String::from("cdr called on empty list"))
    } else {
        ok(xs[1..].to_vec())
    }
}

fn branch(mut args: Env, handle: &Evaluator) -> VResult {
    load_args!(args, b: bool, tbranch: Val, fbranch: Val);
    if b {
        tbranch.unthunk(handle)
    } else {
        fbranch.unthunk(handle)
    }
}

fn map(mut args: Env, handle: &Evaluator) -> VResult {
    load_args!(args, fn_val: Val, xs: Vec<Val>);
    ok(xs
        .into_iter()
        // sometimes you might want to apply a value that you know is a function to something else. In that
        // case handle.apply(f: &Val, x: Val) is the way to go. `handle` mainly exists to allow for this, as well
        // as to access handle.data (generic global data) which may be needed for implementation details of certain very complex domains
        // but should largely be avoided.
        .map(|x| handle.apply(fn_val.clone(), x))
        // here we just turn a Vec<Result> into a Result<Vec> via .collect()'s casting - a handy trick that collapses
        // all the results together into one (which is an Err if any of them was an Err).
        .collect::<Result<Vec<Val>, _>>()?)
}

fn primitive_init(mut args: Env, _handle: &Evaluator) -> VResult {
    // dbg!("INIT");
    let rt = Canvas::new();
    ok(Canv(rt))
}

fn primitive_forward(mut args: Env, _handle: &Evaluator) -> VResult {
    load_args!(args, distance:i32, t:Canvas);
    let mut rt: Canvas;
    if t.is_empty() {
        rt = Canvas::new();
    } else {
        rt = t;
    }
    // dbg!("FORWARD");
    rt.forward(OrderedFloat(distance as f32));
    ok(Canv(rt))
}

fn primitive_right(mut args: Env, _handle: &Evaluator) -> VResult {
    load_args!(args, angle:i32, t:Canvas);
    // let mut rt = t;
    let mut rt: Canvas;
    if t.is_empty() {
        rt = Canvas::new();
    } else {
        rt = t;
    }

    // dbg!("RIGHT");
    rt.right(OrderedFloat(angle as f32));
    ok(Canv(rt))
}

fn primitive_penup(mut args: Env, _handle: &Evaluator) -> VResult {
    load_args!(args, t:Canvas);
    let mut rt = t;
    // dbg!("RIGHT");
    rt.pen_up();
    ok(Canv(rt))
}

fn primitive_pendown(mut args: Env, _handle: &Evaluator) -> VResult {
    load_args!(args, t:Canvas);
    let mut rt = t;
    // dbg!("RIGHT");
    rt.pen_down();
    ok(Canv(rt))
}

fn primitive_repeat(mut args: Env, handle: &Evaluator) -> VResult {
    load_args!(args,init_canvas:Val,times: i32, fn_val: Val);

    // // Check for an empty input vector
    // if times.is_empty() {
    //     return Err("primitive_repeat requires at least one argument".into());
    // }

    // Initially clone the first element of xs to own the value
    let mut current_val = init_canvas;

    // Iterate over the elements starting from the second
    for _ in 0..times {
        match handle.apply(fn_val.clone(), current_val.clone()) {
            Ok(result) => current_val = result, // Update current_val with the result
            Err(e) => return Err(e),            // Return the error if apply fails
        }
    }

    Ok(current_val) // Return the final value, no need to clone here
}

fn primitive_svg_out(mut args: Env, _handle: &Evaluator) -> VResult {
    load_args!(args, t:Canvas);
    let mut svg_str = Vec::new();
    // dbg!("SVG OUT");
    t.save_svg(&mut svg_str).unwrap();
    let svg_string = str::from_utf8(&svg_str).unwrap();
    ok(String::from(svg_string))
}

fn assert_svg_eq(svg1: &str, svg2: &str) {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_types_logo() {
        use domains::logo::LogoVal;

        fn assert_unify(t1: &str, t2: &str, expected: UnifyResult) {
            let mut ctx = Context::empty();
            let res = ctx.unify(
                &t1.parse::<SlowType>().unwrap(),
                &t2.parse::<SlowType>().unwrap(),
            );
            assert_eq!(res, expected);

            let mut typeset = TypeSet::empty();
            let t1 = typeset.add_tp(&t1.parse::<SlowType>().unwrap());
            let t1 = typeset.instantiate(t1);
            let t2 = typeset.add_tp(&t2.parse::<SlowType>().unwrap());
            let t2 = typeset.instantiate(t2);
            let res = typeset.unify(&t1, &t2);
            assert_eq!(res, expected);
        }

        fn assert_infer(p: &str, expected: Result<&str, UnifyErr>) {
            let mut set = ExprSet::empty(Order::ChildFirst, false, false);
            let e = set.parse_extend(p).unwrap();
            dbg!(p.clone());
            dbg!(set.get(e).clone());
            let res = set.get(e).infer::<LogoVal>(
                &mut Context::empty(),
                &mut Default::default(),
                &LogoVal::new_dsl(),
            );

            assert_eq!(res, expected.map(|ty| ty.parse::<SlowType>().unwrap()));
        }

        assert_unify("int", "int", Ok(()));
        assert_unify("int", "t0", Ok(()));
        assert_unify("int", "t1", Ok(()));
        assert_unify("(list int)", "(list t1)", Ok(()));
        assert_unify("(int -> bool)", "(int -> t0)", Ok(()));
        assert_unify("t0", "t1", Ok(()));

        // assert_infer("3", Ok("int"));
        // assert_infer("[1,2,3]", Ok("list int"));
        // assert_infer("(+ 2 3)", Ok("int"));
        assert_infer("(logo_init 0)", Ok("canvas"));
        assert_infer("(logo_fd 1 (logo_init 0))", Ok("canvas"));
        assert_infer("(logo_fd 2 (logo_fd 1 (logo_init 0)))", Ok("canvas"));
        assert_infer(
            "(logo_svg_out (logo_fd 3 (logo_fd 1 (logo_init 0))))",
            Ok("str"),
        );
    }

    #[test]
    fn test_eval_logo_simple() {
        let raw_output: &str = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n                <svg xmlns=\"http://www.w3.org/2000/svg\"\n                version=\"1.1\" baseProfile=\"full\"\n                viewBox=\"-10 -20 120.00001 120.00001\">\n<g stroke=\"black\" stroke-width=\"0.120000005\" fill=\"none\">\n<path d=\"M0 -0 L0 -5 L0 -10\" />\n</g>\n</svg>\n";

        assert_execution::<domains::logo::LogoVal, String>(
            "(logo_svg_out (logo_rt 10 (logo_fd 5 (logo_fd 5 (logo_init 0)))))",
            &[],
            String::from(raw_output),
        );

        let raw_output: &str = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n                <svg xmlns=\"http://www.w3.org/2000/svg\"\n                version=\"1.1\" baseProfile=\"full\"\n                viewBox=\"-10 -29.848078 120.00001 120.00001\">\n<g stroke=\"black\" stroke-width=\"0.120000005\" fill=\"none\">\n<path d=\"M0 -0 L0 -5\" />\n<path d=\"M0 -10 L1.7364819 -19.848078\" />\n</g>\n</svg>\n";
        // dbg!(raw_output);
        assert_execution::<domains::logo::LogoVal, String>(
            "(logo_svg_out (logo_fd 10 (logo_rt 10 (logo_pd (logo_fd 5 (logo_pu (logo_fd 5 (logo_init 0))))))))",
            &[],
            String::from(raw_output),
        );

        let raw_output: &str = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n                <svg xmlns=\"http://www.w3.org/2000/svg\"\n                version=\"1.1\" baseProfile=\"full\"\n                viewBox=\"-10 -29.848078 120.00001 120.00001\">\n<g stroke=\"black\" stroke-width=\"0.120000005\" fill=\"none\">\n<path d=\"M0 -0 L0 -5\" />\n<path d=\"M0 -10 L1.7364819 -19.848078\" />\n</g>\n</svg>\n";
        // dbg!(raw_output);
        assert_execution::<domains::logo::LogoVal, String>(
            "(logo_svg_out (logo_fd 10 (logo_rt 10 (logo_pd (logo_fd 5 (logo_pu (logo_fd 5 (logo_init 0))))))))",
            &[],
            String::from(raw_output),
        );

        let raw_output: &str = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n                <svg xmlns=\"http://www.w3.org/2000/svg\"\n                version=\"1.1\" baseProfile=\"full\"\n                viewBox=\"-10 -31.489384 120.00001 120.00001\">\n<g stroke=\"black\" stroke-width=\"0.120000005\" fill=\"none\">\n<path d=\"M0 -0 L0 -5 L1.2940953 -9.829629 L3.7940953 -14.159756 L7.3296294 -17.69529 L11.659757 -20.19529 L16.489386 -21.489384 L21.489386 -21.489384 L26.319016 -20.195288 L30.649143 -17.695288 L34.184677 -14.159754 L36.684677 -9.829626 L37.97877 -4.9999967 L37.97877 0.00000333786 L36.684673 4.8296323 L34.184673 9.1597595\" />\n</g>\n</svg>\n";
        // dbg!(raw_output);
        assert_execution::<domains::logo::LogoVal, String>(
            "(logo_svg_out (logo_repeat (logo_init 0) 15 (lam (logo_rt 15 (logo_fd 5 $0)))))",
            &[],
            String::from(raw_output),
        );

        let raw_output: &str = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n                <svg xmlns=\"http://www.w3.org/2000/svg\"\n                version=\"1.1\" baseProfile=\"full\"\n                viewBox=\"-10 -31.489384 120.00001 120.00001\">\n<g stroke=\"black\" stroke-width=\"0.120000005\" fill=\"none\">\n<path d=\"M0 -0 L0 -5 L1.2940953 -9.829629 L3.7940953 -14.159756 L7.3296294 -17.69529 L11.659757 -20.19529 L16.489386 -21.489384 L21.489386 -21.489384 L26.319016 -20.195288 L30.649143 -17.695288 L34.184677 -14.159754 L36.684677 -9.829626 L37.97877 -4.9999967 L37.97877 0.00000333786 L36.684673 4.8296323 L34.184673 9.1597595\" />\n</g>\n</svg>\n";
        // dbg!(raw_output);
        assert_execution::<domains::logo::LogoVal, String>(
            "(logo_svg_out (logo_repeat (logo_init 0) 15 (lam (logo_rt 15 (logo_fd 5 $0)))))",
            &[],
            String::from(raw_output),
        );

        // dbg!(raw_output);
        // let mut expr =
        //     String::from("(logo_svg_out (logo_rt 10 (logo_fd 5 (logo_fd 5 (logo_init 0)))))");
        // let dsl = LogoVal::new_dsl();
        // let mut set = ExprSet::empty(Order::ChildFirst, false, false);
        // let e = set.parse_extend(&expr).unwrap();
        // let res = set.get(e).as_eval(&dsl, Some(Duration::from_secs(60)));
        // let args = Env::from(vec![]);

        // let result = res.eval_child(res.expr.idx, &args);
        // dbg!(&result);
        // dbg!(args);
        // dbg!(res.expr.idx);

        // dbg!("-----");
        // assert_eq!(true, false)
        // Test for `primitive_rvowel`
    }

    #[test]
    fn test_eval_logo_variable() {
        let mut dsl = LogoVal::new_dsl();
        let mut raw_output: &str = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n                <svg xmlns=\"http://www.w3.org/2000/svg\"\n                version=\"1.1\" baseProfile=\"full\"\n                viewBox=\"-10 -31.489384 120.00001 120.00001\">\n<g stroke=\"black\" stroke-width=\"0.120000005\" fill=\"none\">\n<path d=\"M0 -0 L0 -5 L1.2940953 -9.829629 L3.7940953 -14.159756 L7.3296294 -17.69529 L11.659757 -20.19529 L16.489386 -21.489384 L21.489386 -21.489384 L26.319016 -20.195288 L30.649143 -17.695288 L34.184677 -14.159754 L36.684677 -9.829626 L37.97877 -4.9999967 L37.97877 0.00000333786 L36.684673 4.8296323 L34.184673 9.1597595\" />\n</g>\n</svg>\n";
        // dbg!(raw_output);
        // "((lam (logo_repeat $0 15 (lam (logo_rt 15 (logo_fd 5 $0))))) $0)"
        let expr = "((lam (logo_repeat $0 15 (lam (logo_rt 15 (logo_fd 5 $0))))) $0)";
        let prod = Production::func(
            "circle",
            "canvas -> canvas",
            lambda_eval(expr),
            ordered_float::OrderedFloat(0.0),
        );

        dsl.add_entry(prod);

        assert_execution_with_dsl(
            "(logo_svg_out (circle (logo_init 0)))",
            &[],
            String::from(raw_output),
            &dsl,
        );

        raw_output = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n                <svg xmlns=\"http://www.w3.org/2000/svg\"\n                version=\"1.1\" baseProfile=\"full\"\n                viewBox=\"-10.296672 -32.915 120.00001 120.00001\">\n<g stroke=\"black\" stroke-width=\"0.120000005\" fill=\"none\">\n<path d=\"M0 -0 L0 -5 L1.2940953 -9.829629 L3.7940953 -14.159756 L7.3296294 -17.69529 L11.659757 -20.19529 L16.489386 -21.489384 L21.489386 -21.489384 L26.319016 -20.195288 L30.649143 -17.695288 L34.184677 -14.159754 L36.684677 -9.829626 L37.97877 -4.9999967 L37.97877 0.00000333786 L36.684673 4.8296323 L34.184673 9.1597595 L30.35445 12.373697 L25.82291 14.486788 L20.898872 15.355028 L15.917898 14.91925 L11.219435 13.209149 L7.123676 10.341266 L3.9097388 6.5110426 L1.7966487 1.9795032 L0.92840886 -2.9445357 L1.3641908 -7.925509 L3.0742943 -12.623971 L5.942177 -16.71973 L9.772399 -19.933668 L14.303938 -22.04676 L19.227978 -22.915003 L24.152016 -22.04676 L28.683552 -19.933666 L32.513775 -16.719727 L35.381653 -12.623964 L37.091755 -7.9255013 L37.527534 -2.944528 L36.659294 1.9795108 L34.5462 6.511049 L31.332262 10.341271 L27.2365 13.209152 L22.538036 14.91925 L17.557062 15.355027 L12.633024 14.486783 L8.101485 12.373692 L4.271265 9.159752 L1.7712669 4.8296237 L0.47717595 -0.00000667572 L0.4771777 -5.0000067 L1.7712721 -9.829636 L4.271273 -14.159761 L7.806806 -17.695297 L12.136936 -20.195293 L16.966564 -21.489391 L21.966564 -21.489386 L26.796192 -20.195288 L31.126316 -17.695284 L34.66185 -14.159749 L37.161846 -9.82962 L38.45594 -4.999991 L38.45594 0.000009059906 L36.74584 4.698471 L33.877956 8.794231 L30.04773 12.008163 L25.51619 14.12125 L20.59215 14.989489 L15.611176 14.553711 L10.912714 12.843604 L6.8169556 9.975719 L3.6030183 6.1454964 L1.489934 1.6139545 L0.6216887 -3.3100834 L1.05747 -8.291057 L2.7675705 -12.989519 L5.6354585 -17.085276 L9.465683 -20.29921 L14.164147 -22.009306 L19.14512 -22.445084 L24.06916 -21.576843 L28.600697 -19.463747 L32.430916 -16.249807 L35.298798 -12.154047 L37.0089 -7.455585 L37.444675 -2.4746113 L36.57643 2.4494276 L34.463333 6.9809628 L31.24939 10.811181 L27.153627 13.679061 L22.455164 15.389161 L17.47419 15.824932 L12.55015 14.956696 L8.220026 12.456692 L4.684493 8.921156 L2.1845007 4.5910244 L0.8904022 -0.23860359 L0.8904057 -5.2386036 L2.184511 -10.06823 L4.6845093 -14.398357 L8.220047 -17.933887 L12.550175 -20.433886 L17.379807 -21.727972 L22.379807 -21.727974 L27.209435 -20.433874 L31.539557 -17.933865 L35.075085 -14.398325 L37.57509 -10.0682 L38.443325 -5.1441603 L38.007534 -0.16318798 L36.297432 4.535275 L33.429543 8.631031 L29.599318 11.844966 L25.067774 13.958047 L20.143734 14.826289 L15.162761 14.390505 L10.464298 12.680401 L6.3685384 9.812518 L3.1545987 5.9822974 L1.0415118 1.4507565 L0.17328244 -3.4732842 L0.60906065 -8.454258 L2.3191674 -13.1527195 L5.5331097 -16.982937 L9.628872 -19.850817 L14.327335 -21.560917 L19.308308 -21.996698 L24.232344 -21.128443 L28.763885 -19.015358 L32.5941 -15.801413 L35.46198 -11.705648 L37.172077 -7.007184 L37.607853 -2.0262103 L36.739613 2.8978286 L34.626507 7.429361 L31.41256 11.259575 L27.316793 14.127449 L22.618328 15.8375435 L17.618328 15.837527 L12.788698 14.543437 L8.458577 12.043427 L4.923049 8.507888 L2.423054 4.1777577 L1.1289618 -0.65187216 L1.1289623 -5.651872 L2.4230738 -10.481497 L4.9230695 -14.811626 L8.4586115 -18.347153 L12.788743 -20.847145 L17.618374 -22.141233 L22.618374 -22.14123 L27.448002 -20.847134 L31.77812 -18.347118 L34.992054 -14.5168915 L37.10514 -9.985351 L37.97338 -5.0613112 L37.537582 -0.08033943 L35.827484 4.6181245 L32.95959 8.713877 L29.129362 11.927807 L24.59782 14.040891 L19.67378 14.909126 L14.692807 14.473345 L9.994345 12.763244 L5.8985834 9.895364 L2.6846414 6.065145 L0.5715604 1.5336013 L-0.29667193 -3.390439 L0.5715678 -8.314478 L2.684673 -12.84601 L5.8986206 -16.676224 L9.994375 -19.544113 L14.692841 -21.254208 L19.673815 -21.689981 L24.597855 -20.82174 L29.129395 -18.708649 L32.959618 -15.494713 L35.827488 -11.398945 L37.53758 -6.700478 L37.97335 -1.7195039 L37.105087 3.2045307 L34.991993 7.7360687 L31.778055 11.566291 L27.447924 14.066283 L22.618294 15.360373 L17.618294 15.360369 L12.78867 14.066254 L8.458551 11.566238 L4.9230146 8.030707 L2.4230087 3.7005835 L1.1289227 -1.1290483 L1.1289297 -6.1290483 L2.423029 -10.958676 L4.923047 -15.288793 L8.458593 -18.824314 L12.788719 -21.324318 L17.618347 -22.61842 L22.618347 -22.61841 L27.31681 -20.90831 L31.412561 -18.040413 L34.626488 -14.210182 L36.73957 -9.678638 L37.607822 -4.7546015 L37.17204 0.22637177 L35.461937 4.924834 L32.594055 9.020594 L28.763823 12.234518 L24.232277 14.347596 L19.308235 15.215825 L14.327264 14.780018 L9.628803 13.069911 L5.5330453 10.202025 L2.3191082 6.3718023 L0.6090175 1.6733356 L0.17324671 -3.3076386 L1.0415117 -8.231673 L3.1546226 -12.763203 L6.368561 -16.593426 L10.464319 -19.46131 L15.1627865 -21.171398 L20.14376 -21.607166 L25.067799 -20.738916 L29.599327 -18.625803 L33.429535 -15.411848 L36.297417 -11.316088 L38.00752 -6.617625 L38.443302 -1.636652 L37.57505 3.287385 L35.07503 7.6175013 L31.539484 11.153023 L27.209349 13.653009 L22.37972 14.947111 L17.37972 14.94712 L12.550094 13.653017 L8.219969 11.153012 L4.6844363 7.6174765 L2.1844525 3.2873402 L0.890373 -1.5422931 L0.89036745 -6.542293 L2.1844547 -11.371924 L4.6844616 -15.702047 L8.219999 -19.237577 L12.550128 -21.737576 L17.474169 -22.605804 L22.45514 -22.169998 L27.153599 -20.45989 L31.249367 -17.59202 L34.463303 -13.761797 L36.576378 -9.23025 L37.444622 -4.306212 L37.00883 0.67476034 L35.298702 5.373214 L32.430813 9.468969 L28.6006 12.682919 L24.06906 14.796008 L19.145018 15.66423 L14.164043 15.228455 L9.465585 13.518341 L5.635377 10.304386 L2.7675266 6.208604 L1.057442 1.5101347 L0.6216587 -3.4708385 L1.4899112 -8.394876 L3.6030283 -12.926403 L6.8169713 -16.75662 L10.9127445 -19.624483 L15.611221 -21.334547 L20.592194 -21.770346 L25.516233 -20.90211 L30.047768 -18.789007 L33.877995 -15.575076 L36.745872 -11.479312 L38.45595 -6.780841 L38.455917 -1.7808409 L37.16181 3.0487857 L34.66182 7.378918 L31.126282 10.914448 L26.796143 13.414429 L21.966513 14.708524 L16.966513 14.708507 L12.136892 13.414379 L7.8067713 10.91437 L4.27123 7.378843 L1.7712355 3.0487127 L0.47716212 -1.7809224 L0.47716308 -6.7809224 L1.7712752 -11.610547 L4.271304 -15.940657 L8.101529 -19.15459 L12.63306 -21.267696 L17.557098 -22.135937 L22.53807 -21.700142 L27.236536 -19.990047 L31.33229 -17.122156 L34.546207 -13.291917 L36.659294 -8.760376 L37.52755 -3.83634 L37.09177 1.1446338 L35.381653 5.843091 L32.513775 9.938854 L28.683546 13.152784 L24.151997 15.26585 L19.227957 16.134085 L14.303921 15.265829 L9.772379 13.152744 L5.942163 9.938799 L3.0743022 5.843024 L1.3642057 1.1445594 L0.9284479 -3.8364158 L1.7967257 -8.760448 L3.9098313 -13.291981 L7.123765 -17.122208 L11.219531 -19.990082 L15.918003 -21.700157 L20.898977 -22.135931 L25.823013 -21.26767 L30.354536 -19.154545 L34.184746 -15.940595 L36.684757 -11.610474 L37.978848 -6.7808433 L37.97883 -1.7808433 L36.684734 3.0487866 L34.184723 7.3789063 L30.649166 10.914418 L26.319035 13.41441 L21.489408 14.708517 L16.489408 14.708513 L11.659784 13.414398 L7.3296566 10.914399 L3.7941334 7.3788543 L1.2941611 3.0487113 L0.00007557869 -1.7809205 L0.00006397602 -6.7809205 L1.7101625 -11.479384 L4.5780563 -15.575136 L8.4082985 -18.789051 L12.939841 -20.902134 L17.863884 -21.77035 L22.844854 -21.33453 L27.543324 -19.624447 L31.639084 -16.756565 L34.853012 -12.926333 L36.96611 -8.394798 L37.834343 -3.470758 L37.39854 1.5102134 L35.688435 6.208675 L32.820534 10.304423 L28.990313 13.518362 L24.291847 15.228456 L19.310871 15.66421 L14.386833 14.795967 L9.855287 12.682893 L6.0250874 9.468927 L3.1572165 5.3731594 L1.447144 0.67468596 L1.0113738 -4.3062882 L1.8796391 -9.230323 L3.9927332 -13.76186 L7.2066574 -17.592094 L11.302439 -20.459948 L16.000906 -22.170034 L20.981882 -22.605783 L25.905918 -21.737534 L30.236036 -19.237518 L33.771545 -15.70196 L36.271534 -11.371826 L37.56564 -6.542199 L37.56563 -1.5421991 L36.27155 3.2874336 L33.771515 7.6175404 L30.235968 11.153061 L25.905823 13.65303 L21.07619 14.947113 L16.07619 14.947122 L11.246564 13.653019 L6.91643 11.15303 L3.3809252 7.617468 L0.88094187 3.2873316\" />\n</g>\n</svg>\n";

        assert_execution_with_dsl(
            "(logo_svg_out (logo_repeat (logo_init 0) 25 (lam (logo_rt 5 (circle $0)))))",
            &[],
            String::from(raw_output),
            &dsl,
        );
    }

    //     // Test for `primitive_rconsonant`
    //     assert_execution::<domains::logo::LogoVal, String>(
    //         "(_rconsonant)",
    //         &[],
    //         String::from("'[^aeiou]'"),
    //     );

    //     // Test for `primitive_emptystr`
    //     assert_execution::<domains::logo::LogoVal, bool>("(_emptystr '')", &[], true);

    //     // Test for `primitive_rdot`
    //     assert_execution::<domains::logo::LogoVal, String>("(_rdot)", &[], String::from("."));

    //     // Test for `primitive_rnot`
    //     assert_execution::<domains::logo::LogoVal, String>(
    //         "(_rnot '[a-z]+')",
    //         &[],
    //         String::from("'[^[a-z]+]'"),
    //     );

    //     assert_execution::<domains::logo::LogoVal, String>(
    //         "(_ror '[a-z]+' '[0-9]+')",
    //         &[],
    //         String::from("'([a-z]+|[0-9]+)'"),
    //     );

    //     assert_execution::<domains::logo::LogoVal, String>(
    //         "(_rconcat '[a-z]+' '[0-9]+')",
    //         &[],
    //         String::from("'[a-z]+[0-9]+'"),
    //     );

    //     assert_execution::<domains::logo::LogoVal, bool>("(_rmatch '[a-z]+' 'Hello')", &[], false);

    //     assert_execution::<domains::logo::LogoVal, String>(
    //         "(_rtail ['hello','dear'])",
    //         &[],
    //         String::from("dear"),
    //     );

    //     assert_execution::<domains::logo::LogoVal, String>(
    //         "(_rflatten ['hello','dear'])",
    //         &[],
    //         String::from("hellodear"),
    //     );

    //     assert_execution::<domains::logo::LogoVal, Vec<String>>(
    //         "(_rrevcdr ['a','b','c','d'])",
    //         &[],
    //         vec![
    //             String::from("c"),
    //             String::from("b"),
    //             String::from("a"),
    //             String::from("d"),
    //         ],
    //     );

    //     assert_execution::<domains::logo::LogoVal, Vec<String>>(
    //         "(_rappend 'yo' ['hello','dear'])",
    //         &[],
    //         vec![
    //             String::from("hello"),
    //             String::from("dear"),
    //             String::from("yo"),
    //         ],
    //     );

    //     assert_execution::<domains::logo::LogoVal, Vec<String>>(
    //         "(_rsplit ',' 'one,two,three')",
    //         &[],
    //         vec![
    //             String::from("one"),
    //             String::from(","),
    //             String::from("two"),
    //             String::from(","),
    //             String::from("three"),
    //         ],
    //     );

    //     // "match ."
    //     let arg1 = dsl.val_of_prim(&"'t'".into()).unwrap();
    //     assert_execution::<domains::logo::LogoVal, bool>("(_rmatch _rdot $0)", &[arg1], true);

    //     // "match ab"
    //     let arg1 = dsl.val_of_prim(&"'ab'".into()).unwrap();
    //     assert_execution::<domains::logo::LogoVal, bool>(
    //         "(_rmatch (_rconcat _a _b) $0)",
    //         &[arg1],
    //         true,
    //     );

    //     // "match ab"
    //     let arg1 = dsl.val_of_prim(&"'cde'".into()).unwrap();
    //     assert_execution::<domains::logo::LogoVal, bool>(
    //         "(_rmatch (_rconcat _a _b) $0)",
    //         &[arg1],
    //         false,
    //     );

    //     // match [^ae]
    //     let arg1 = dsl.val_of_prim(&"_b".into()).unwrap();
    //     assert_execution::<domains::logo::LogoVal, bool>(
    //         "(_rmatch (_rnot (_rconcat _a _e)) $0)",
    //         &[arg1],
    //         true,
    //     );

    //     // "match [^ae]d"
    //     let arg1 = dsl.val_of_prim(&"'ed'".into()).unwrap();
    //     assert_execution::<domains::logo::LogoVal, bool>(
    //         "(_rmatch (_rconcat (_rnot (_rconcat _a _e)) _d) $0)",
    //         &[arg1],
    //         false,
    //     );

    //     // single string tests

    //     let arg1 = dsl.val_of_prim(&"'te'".into()).unwrap();
    //     assert_execution::<domains::logo::LogoVal, String>(
    //         postpend_te,
    //         &[arg1],
    //         String::from("'tef'"),
    //     );

    //     let arg1 = dsl.val_of_prim(&"'te'".into()).unwrap();
    //     assert_execution::<domains::logo::LogoVal, String>(replace_te, &[arg1], String::from("f"));
    // }
    // #[test]
    // fn test_eval_logo_lists() {
    //     let dsl = LogoVal::new_dsl();
    //     // let arg1 = dsl.val_of_prim(&"'te'".into()).unwrap();
    //     // assert_execution::<domains::logo::LogoVal, String>(
    //     //     replace_te,
    //     //     &[arg1],
    //     //     String::from("f"),
    //     // );

    //     // let raw = String::from("(_rflatten (map ")
    //     //     + &String::from(replace_te)
    //     //     + &String::from(" (_rsplit (_rconcat _t _e) $0)))");
    //     // dbg!(raw.clone());
    //     let arg1 = dsl.val_of_prim(&"'tehellote'".into()).unwrap();
    //     assert_execution::<domains::logo::LogoVal, Vec<String>>(
    //         "(_rsplit (_rconcat _t _e) $0)",
    //         &[arg1],
    //         vec![
    //             String::from("te"),
    //             String::from("hello"),
    //             String::from("te"),
    //         ],
    //     );

    //     let arg1 = dsl.val_of_prim(&"'tebyete'".into()).unwrap();
    //     assert_execution::<domains::logo::LogoVal, Vec<String>>(
    //         "(_rsplit (_rconcat _t _e) $0)",
    //         &[arg1],
    //         vec![String::from("te"), String::from("bye"), String::from("te")],
    //     );

    //     let raw = String::from("(_rflatten (map (lam ")
    //         + &String::from(replace_te)
    //         + &String::from(") (_rsplit (_rconcat _t _e) $0)))");
    //     dbg!(raw.clone());
    //     let arg1 = dsl.val_of_prim(&"'tehellote'".into()).unwrap();
    //     assert_execution::<domains::logo::LogoVal, String>(&raw, &[arg1], String::from("fhellof"));

    //     let raw = String::from("(_rflatten (map (lam ")
    //         + &String::from(remove_te)
    //         + &String::from(") (_rsplit (_rconcat _t _e) $0)))");
    //     dbg!(raw.clone());
    //     let arg1 = dsl.val_of_prim(&"'tehellote'".into()).unwrap();
    //     assert_execution::<domains::logo::LogoVal, String>(&raw, &[arg1], String::from("hello"));

    //     // let raw = String::from("((lam (_rflatten (_rappend (")
    //     //     + &String::from(prepend_te)
    //     //     + &String::from(" (_rtail $0)) (_rrevcdr $0)))) (_rsplit (_rconcat _t _e) $0))");
    //     // let raw = String::from(
    //     //     "((lam (_rflatten (_rappend 'b' (_rrevcdr $0)))) (_rsplit (_rconcat _t _e) $0))",
    //     // );
    //     let raw = String::from(
    //         "((lam (_rflatten (_rappend 'b' (_rrevcdr $0)))) (_rsplit (_rconcat _t _e) $0))",
    //     );
    //     // (if (_rmatch (_rconcat _t _e) $0) '' $0)
    //     dbg!(raw.clone());
    //     let arg1 = dsl.val_of_prim(&"'tehellote'".into()).unwrap();
    //     assert_execution::<domains::logo::LogoVal, String>(
    //         &raw,
    //         &[arg1],
    //         String::from("helloteteb"),
    //     );
    // }
}
