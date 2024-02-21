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
        dbg!(&v);
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
                Production::func(
                    "logo_init",
                    "t0 -> canvas",
                    Arc::new(primitive_init),
                    ordered_float::OrderedFloat(0.),
                ),
                Production::func(
                    "logo_fd",
                    "int -> canvas -> canvas",
                    Arc::new(primitive_forward),
                    ordered_float::OrderedFloat(0.),
                ),
                Production::func(
                    "logo_rt",
                    "int -> canvas -> canvas",
                    Arc::new(primitive_right),
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
        dbg!(p.clone());
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
            dbg!("NUM LIST");
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
    dbg!("INIT");
    let rt = Canvas::new();
    ok(Canv(rt))
}

fn primitive_forward(mut args: Env, _handle: &Evaluator) -> VResult {
    load_args!(args, distance:i32, t:Canvas);
    let mut rt = t;
    dbg!("FORWARD");
    rt.forward(OrderedFloat(distance as f32));
    ok(Canv(rt))
}

fn primitive_right(mut args: Env, _handle: &Evaluator) -> VResult {
    load_args!(args, angle:i32, t:Canvas);
    let mut rt = t;
    dbg!("RIGHT");
    rt.right(OrderedFloat(angle as f32));
    ok(Canv(rt))
}

fn primitive_svg_out(mut args: Env, _handle: &Evaluator) -> VResult {
    load_args!(args, t:Canvas);
    let mut svg_str = Vec::new();
    dbg!("SVG OUT");
    t.save_svg(&mut svg_str).unwrap();
    let svg_string = str::from_utf8(&svg_str).unwrap();
    ok(String::from(svg_string))
}

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
