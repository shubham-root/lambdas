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

    fn check_match(sym1: &Val, sym2: &Val) -> bool {
        sym1 == sym2
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

        raw_output = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n                <svg xmlns=\"http://www.w3.org/2000/svg\"\n                version=\"1.1\" baseProfile=\"full\"\n                viewBox=\"-10.302198 -34.096504 120.00001 120.00001\">\n<g stroke=\"black\" stroke-width=\"0.120000005\" fill=\"none\">\n<path d=\"M0 -0 L0 -5 L1.2940953 -9.829629 L3.7940953 -14.159756 L7.3296294 -17.69529 L11.659757 -20.19529 L16.489386 -21.489384 L21.489386 -21.489384 L26.319016 -20.195288 L30.649143 -17.695288 L34.184677 -14.159754 L36.684677 -9.829626 L37.97877 -4.9999967 L37.97877 0.00000333786 L36.684673 4.8296323 L34.184673 9.1597595 L30.088913 12.027641 L25.39045 13.737741 L20.409475 14.17352 L15.485437 13.305277 L10.953898 11.192186 L7.1236753 7.9782486 L4.2557945 3.8824878 L2.5456927 -0.8159752 L2.1099126 -5.796949 L2.9781542 -10.720987 L5.0912457 -15.252526 L8.305183 -19.082748 L12.400944 -21.95063 L17.099407 -23.660728 L22.080381 -24.096506 L26.778843 -22.386404 L30.874601 -19.518518 L34.08854 -15.688295 L36.20163 -11.156755 L37.06987 -6.2327166 L36.63409 -1.2517433 L34.923985 3.4467182 L32.0561 7.542477 L28.225878 10.756416 L23.694338 12.869507 L18.770298 13.737749 L13.789324 13.30197 L9.090862 11.591866 L4.9951024 8.723983 L1.7811625 4.893762 L0.4870715 0.06413174 L0.48707327 -4.9358683 L1.7811676 -9.765497 L4.281169 -14.095623 L7.816702 -17.631159 L12.1468315 -20.131155 L16.97646 -21.425253 L21.97646 -21.425247 L26.806087 -20.13115 L31.136211 -17.631145 L34.671745 -14.095611 L37.17174 -9.765482 L38.465836 -4.9358525 L38.465836 0.06414747 L37.171738 4.8937764 L33.957798 8.723997 L29.862038 11.591879 L25.163572 13.301973 L20.182598 13.737748 L15.258559 12.869506 L10.72702 10.756415 L6.896802 7.542473 L4.028922 3.4467106 L2.318822 -1.2517529 L1.8830411 -6.232726 L2.7512867 -11.156764 L4.86438 -15.688302 L8.078325 -19.518518 L12.174089 -22.386395 L16.872555 -24.09649 L21.853527 -23.660706 L26.551989 -21.950602 L30.647749 -19.08272 L33.861683 -15.252493 L35.97477 -10.720952 L36.84301 -5.7969127 L36.40723 -0.81593895 L34.697124 3.882522 L31.829239 7.9782805 L27.999016 11.192218 L23.467478 13.305311 L18.543438 14.173547 L13.562466 13.737756 L8.864002 12.027655 L4.768246 9.159767 L2.2682538 4.8296356 L0.9741553 0.0000076293945 L0.9741588 -4.9999924 L2.268264 -9.829618 L4.768263 -14.159746 L8.303801 -17.695276 L12.633928 -20.195274 L17.46356 -21.48936 L22.46356 -21.489363 L27.293188 -20.195263 L31.62331 -17.695253 L35.158836 -14.159714 L37.65884 -9.829589 L38.952934 -4.999959 L38.952923 0.000041007996 L36.83983 4.531579 L33.625893 8.361801 L29.530128 11.229678 L24.831667 12.939784 L19.850693 13.375562 L14.926655 12.507313 L10.395119 10.394217 L6.5648985 7.1802764 L3.6970165 3.084516 L1.9869224 -1.6139493 L1.5511576 -6.594924 L2.4194002 -11.518963 L4.5324993 -16.050499 L7.746442 -19.880718 L11.842204 -22.748598 L16.766243 -23.616833 L21.747215 -23.181051 L26.445679 -21.470951 L30.541441 -18.603071 L33.755367 -14.7728405 L35.86845 -10.241297 L36.736683 -5.3172565 L36.3009 -0.3362832 L34.590797 4.362179 L31.722898 8.457928 L27.892677 11.671867 L23.361141 13.784963 L18.4371 14.653192 L13.456127 14.217403 L8.757666 12.507297 L5.2221375 8.971757 L2.7221425 4.641627 L1.4280503 -0.18800306 L1.4280508 -5.188003 L2.7221622 -10.017628 L5.222158 -14.347757 L8.7577 -17.883284 L13.0878315 -20.383276 L17.917461 -21.677364 L22.917461 -21.67736 L27.74709 -20.383265 L32.07721 -17.88325 L35.612732 -14.347705 L38.11274 -10.017582 L39.406826 -5.18795 L38.538574 -0.26391315 L36.425476 4.267622 L33.211533 8.09784 L29.11577 10.965719 L24.417307 12.675819 L19.436333 13.1116 L14.512297 12.243344 L9.9807625 10.130242 L6.150546 6.916297 L3.2826695 2.8205328 L1.5725727 -1.8779316 L1.1368145 -6.8589067 L2.0050542 -11.782946 L4.1181593 -16.314478 L7.332107 -20.144691 L11.863644 -22.257788 L16.787685 -23.126017 L21.76866 -22.690248 L26.467121 -20.98014 L30.56288 -18.112255 L33.776817 -14.282032 L35.889893 -9.750486 L36.758118 -4.826445 L36.322327 0.15452719 L34.612236 4.8529935 L31.744349 8.94875 L27.914124 12.162684 L23.382584 14.275774 L18.458542 15.143997 L13.47757 14.708203 L9.147451 12.208188 L5.6119146 8.672657 L3.1119087 4.342533 L1.8178227 -0.4870987 L1.8178297 -5.4870987 L3.111929 -10.316727 L5.611947 -14.646843 L9.147493 -18.182364 L13.477619 -20.682367 L18.307247 -21.976469 L23.307247 -21.97646 L28.136875 -20.682358 L32.467 -18.182354 L36.002518 -14.646805 L38.502502 -10.3166685 L38.93828 -5.335695 L38.070038 -0.4116559 L35.95695 4.1198845 L32.743004 7.9500985 L28.647238 10.817972 L23.948772 12.528066 L18.967796 12.96382 L14.043758 12.095577 L9.512219 9.982487 L5.6819954 6.768551 L2.8141239 2.672783 L1.1040331 -2.0256839 L0.66826236 -7.006658 L1.5365273 -11.930693 L3.6496382 -16.462223 L7.479863 -19.676157 L12.011403 -21.789246 L16.935442 -22.657488 L21.916414 -22.221693 L26.614872 -20.51158 L30.710627 -17.643688 L33.924572 -13.813473 L36.03766 -9.281931 L36.9059 -4.3578916 L36.47012 0.62308216 L34.760002 5.3215394 L31.892109 9.417292 L28.06188 12.631222 L23.53033 14.744288 L18.60629 15.612524 L13.776664 14.318421 L9.446539 11.818417 L5.9110065 8.282881 L3.4110227 3.9527445 L2.1169431 -0.87688875 L2.1169376 -5.8768888 L3.411025 -10.70652 L5.911032 -15.036643 L9.446569 -18.572174 L13.776698 -21.072172 L18.606333 -22.36625 L23.606333 -22.366213 L28.435959 -21.072104 L32.76609 -18.57211 L36.301617 -15.03657 L38.011707 -10.338102 L38.44746 -5.357126 L37.579212 -0.4330883 L35.466103 4.098441 L32.252163 7.9286633 L28.156393 10.796532 L23.457932 12.506638 L18.476957 12.942405 L13.552923 12.074137 L9.021387 9.9610405 L5.1911793 6.7470856 L2.323329 2.6513033 L0.6132443 -2.0471659 L0.177461 -7.028139 L1.0457135 -11.952176 L3.9136071 -16.047928 L7.743849 -19.261843 L12.275391 -21.374926 L17.199434 -22.243141 L22.180408 -21.80736 L26.878864 -20.09724 L30.974625 -17.22936 L34.188553 -13.399129 L36.301617 -8.867577 L37.16985 -3.9435363 L36.734047 1.037435 L35.02394 5.735897 L32.156044 9.831646 L28.325823 13.045586 L23.794277 15.158664 L18.794277 15.158647 L13.964657 13.864519 L9.634536 11.36451 L6.0989947 7.828983 L3.599 3.4988527 L2.3049266 -1.3307824 L2.3049276 -6.3307824 L3.5990396 -11.160407 L6.0990686 -15.490517 L9.634611 -19.026043 L13.964733 -21.52605 L18.794365 -22.820139 L23.794365 -22.820116 L28.623993 -21.52602 L32.95411 -19.026005 L35.821976 -14.930233 L37.532043 -10.231757 L37.967808 -5.2507825 L37.099575 -0.32674217 L34.986477 4.204793 L31.772518 8.034998 L27.676756 10.902877 L22.978287 12.612959 L17.99731 13.048701 L13.073275 12.180446 L8.541733 10.06736 L4.711517 6.8534145 L1.8436561 2.7576394 L0.13355958 -1.940825 L-0.30219823 -6.9218 L1.4079239 -11.620255 L4.2758074 -15.716015 L8.106041 -18.92994 L12.637578 -21.043034 L17.561619 -21.911263 L22.542591 -21.475454 L27.24105 -19.765347 L31.336798 -16.897446 L34.550735 -13.067223 L36.66381 -8.535676 L37.532055 -3.6116376 L37.096264 1.3693347 L35.386135 6.0677876 L32.518246 10.163544 L28.688007 13.377463 L23.858381 14.67157 L18.858381 14.671566 L14.028757 13.377451 L9.698629 10.877452 L6.163106 7.341907 L3.6631336 3.011764 L2.369048 -1.8178678 L2.3690364 -6.8178678 L3.6631362 -11.647495 L6.1631546 -15.977612 L9.6986885 -19.513145 L14.028824 -22.013132 L18.858461 -23.307196 L23.858461 -23.307184 L28.688084 -22.013063 L32.51831 -18.799133 L35.38619 -14.703369 L37.096268 -10.004898 L37.532043 -5.0239244 L36.663822 -0.099882126 L34.550697 4.431642 L31.33675 8.261856 L27.240973 11.129714 L22.542507 12.8398075 L17.561531 13.275562 L12.637493 12.407319 L8.105947 10.294245 L4.2757473 7.0802794 L1.4078765 2.9845114 L-0.30219603 -1.7139621 L0.13357666 -6.6949363 L1.843723 -11.393383 L4.711627 -15.489128 L8.541853 -18.703062 L13.0734005 -20.816133 L17.99744 -21.684374 L22.978413 -21.248579 L27.676878 -19.538483 L31.77261 -16.67056 L34.986526 -12.840321 L37.099613 -8.308779 L37.96783 -3.384736 L37.53205 1.5962377 L35.821934 6.294695 L32.954056 10.390458 L28.62391 12.890428 L23.794277 14.18451 L18.794277 14.184519 L13.96465 12.890415 L9.634516 10.390427 L6.099011 6.854864 L3.5990276 2.5247278 L2.304967 -2.3049107 L2.304981 -7.3049107 L3.5990686 -12.134542 L6.0990763 -16.464664 L9.634601 -20.000208 L13.964748 -22.500172 L18.794384 -23.794249 L23.794384 -23.794212\" />\n</g>\n</svg>\n";
        assert_execution_with_dsl(
            "(logo_svg_out (logo_repeat (logo_init 0) 25 (lam (logo_rt 10 (circle $0)))))",
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
