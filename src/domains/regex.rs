/// This is an example domain, heavily commented to explain how to implement your own!
use crate::*;
extern crate regex;
use regex::Regex;
use std::string::String;

/// A simple domain with ints and polymorphic lists (allows nested lists).
/// Generally it's good to be able to imagine the hindley milner type system
/// for your domain so that it's compatible when we add that later. In this case the types
/// would look like `T := (T -> T) | Int | List(T)` where functions are handled
/// by dreamegg::domain::Val so they don't appear here.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum RegexVal {
    Int(i32),
    List(Vec<Val>),
    Str(String),
    Bool(bool),
}

// aliases of various typed specialized to our RegexVal
type Val = crate::eval::Val<RegexVal>;
type Evaluator<'a> = crate::eval::Evaluator<'a, RegexVal>;
type VResult = crate::eval::VResult<RegexVal>;
type Env = crate::eval::Env<RegexVal>;

// to more concisely refer to the variants
use RegexVal::*;

// In this domain, we limit how many times "fix" can be invoked.
// This is a crude way of finding infinitely looping programs.
const MAX_FIX_INVOCATIONS: u32 = 20;

// From<Val> impls are needed for unwrapping values. We can assume the program
// has been type checked so it's okay to panic if the type is wrong. Each val variant
// must map to exactly one unwrapped type (though it doesnt need to be one to one in the
// other direction)
impl FromVal<RegexVal> for i32 {
    fn from_val(v: Val) -> Result<Self, VError> {
        match v {
            Dom(Int(i)) => Ok(i),
            _ => Err("from_val_to_i32: not an int".into()),
        }
    }
}

impl FromVal<RegexVal> for String {
    fn from_val(v: Val) -> Result<Self, VError> {
        match v {
            Dom(Str(s)) => Ok(s.to_string()),
            _ => Err("from_val_to_string: not a string".into()),
        }
    }
}

impl<T: FromVal<RegexVal>> FromVal<RegexVal> for Vec<T> {
    fn from_val(v: Val) -> Result<Self, VError> {
        match v {
            Dom(List(v)) => v.into_iter().map(|v| T::from_val(v)).collect(),
            _ => Err("from_val_to_vec: not a list".into()),
        }
    }
}

impl FromVal<RegexVal> for bool {
    fn from_val(v: Val) -> Result<Self, VError> {
        match v {
            Dom(Bool(b)) => Ok(b),
            _ => Err("from_val_to_bool: not a bool".into()),
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

#[derive(Default, Debug)]
pub struct RegexData {
    fix_counter: u32,
}

// here we actually implement Domain for our domain.
impl Domain for RegexVal {
    // we dont use Data here
    type Data = RegexData;

    fn new_dsl() -> DSL<Self> {
        DSL::new(
            vec![
                Production::func("fix1", "t0 -> ((t0 -> t1) -> t0 -> t1) -> t1", fix1, 0.0),
                Production::func("fix", "((t0 -> t1) -> t0 -> t1) -> t0 -> t1", fix, 0.0),
                Production::func("cons", "t0 -> list t0 -> list t0", cons, 0.0),
                Production::func("car", "list t0 -> t0", car, 0.0),
                Production::func("cdr", "list t0 -> list t0", cdr, 0.0),
                Production::func_custom("if", "bool -> t0 -> t0 -> t0", Some(&[1, 2]), branch, 0.0),
                Production::val("_rvowel", "str", Dom(Str(String::from("'[aeiou]'"))), 0.0),
                Production::val(
                    "_rconsonant",
                    "str",
                    Dom(Str(String::from("'[^aeiou]'"))),
                    0.0,
                ),
                Production::func("_emptystr", "str -> bool", primitive_emptystr, 0.0),
                Production::val("_rdot", "str", Dom(Str(String::from("."))), 0.0),
                Production::func("_rnot", "str -> str", primitive_rnot, 0.0),
                Production::func("_ror", "str -> str -> str", primitive_ror, 0.0),
                Production::func("_rconcat", "str -> str -> str", primitive_rconcat, 0.0),
                Production::func("_rmatch", "str -> str -> bool", primitive_rmatch, 0.0),
                Production::func("_rtail", "list str -> str", primitive_rtail, 0.0),
                Production::func("_rflatten", "list str -> str", primitive_rflatten, 0.0),
                Production::func("_rsplit", "str -> str -> list str", primitive_rsplit, 0.0),
                Production::func(
                    "_rappend",
                    "str -> list str -> list str",
                    primitive_rappend,
                    0.0,
                ),
                Production::func("_rrevcdr", "list str -> list str", primitive_rrevcdr, 0.0),
                Production::func("map", "(t0 -> t1) -> (list t0) -> (list t1)", map, 0.0),
                Production::val("_a", "str", Dom(Str(String::from("a"))), 0.0),
                Production::val("_b", "str", Dom(Str(String::from("b"))), 0.0),
                Production::val("_c", "str", Dom(Str(String::from("c"))), 0.0),
                Production::val("_d", "str", Dom(Str(String::from("d"))), 0.0),
                Production::val("_e", "str", Dom(Str(String::from("e"))), 0.0),
                Production::val("_f", "str", Dom(Str(String::from("f"))), 0.0),
                Production::val("_g", "str", Dom(Str(String::from("g"))), 0.0),
                Production::val("_h", "str", Dom(Str(String::from("h"))), 0.0),
                Production::val("_i", "str", Dom(Str(String::from("i"))), 0.0),
                Production::val("_j", "str", Dom(Str(String::from("j"))), 0.0),
                Production::val("_k", "str", Dom(Str(String::from("k"))), 0.0),
                Production::val("_l", "str", Dom(Str(String::from("l"))), 0.0),
                Production::val("_m", "str", Dom(Str(String::from("m"))), 0.0),
                Production::val("_n", "str", Dom(Str(String::from("n"))), 0.0),
                Production::val("_o", "str", Dom(Str(String::from("o"))), 0.0),
                Production::val("_p", "str", Dom(Str(String::from("p"))), 0.0),
                Production::val("_q", "str", Dom(Str(String::from("q"))), 0.0),
                Production::val("_r", "str", Dom(Str(String::from("r"))), 0.0),
                Production::val("_s", "str", Dom(Str(String::from("s"))), 0.0),
                Production::val("_t", "str", Dom(Str(String::from("t"))), 0.0),
                Production::val("_u", "str", Dom(Str(String::from("u"))), 0.0),
                Production::val("_v", "str", Dom(Str(String::from("v"))), 0.0),
                Production::val("_w", "str", Dom(Str(String::from("w"))), 0.0),
                Production::val("_x", "str", Dom(Str(String::from("x"))), 0.0),
                Production::val("_y", "str", Dom(Str(String::from("y"))), 0.0),
                Production::val("_z", "str", Dom(Str(String::from("z"))), 0.0),
                Production::val("[]", "(list t0)", Dom(List(vec![])), 0.0),
            ],
            0.0,
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
            let corrected_p = p.replace('\'', "\"");
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

fn primitive_emptystr(mut args: Env, _handle: &Evaluator) -> VResult {
    load_args!(args, input:String);
    ok(input.is_empty())
}

fn primitive_rnot(mut args: Env, _handle: &Evaluator) -> VResult {
    load_args!(args, pattern:String);
    let pattern = format!(r"'[^{}]'", &pattern);
    ok(pattern)
}

// create regex condition pattern element1 OR element2
fn primitive_ror(mut args: Env, _handle: &Evaluator) -> VResult {
    load_args!(args, pattern1:String, pattern2:String);
    let pattern = format!(r"'({}|{})'", &pattern1, &pattern2);
    ok(pattern)
}

// concatenate regex pattern element1 to element2
fn primitive_rconcat(mut args: Env, _handle: &Evaluator) -> VResult {
    load_args!(args, element1:String, element2:String);
    let result = format!("'{}{}'", &element1, &element2);
    ok(result)
}

fn primitive_rmatch(mut args: Env, _handle: &Evaluator) -> VResult {
    load_args!(args, s1:String, s2:String);
    let regex =
        Regex::new(&format!("^{}$", &s1)).map_err(|e| format!("Invalid regex pattern: {}", e))?;
    ok(regex.is_match(&s2))
}

fn primitive_rflatten(mut args: Env, _handle: &Evaluator) -> VResult {
    load_args!(args, xs: Vec<String>);
    // Check if the vector is empty
    if xs.is_empty() {
        // Return an error if the array is empty
        Err("Array is empty".into())
    } else {
        // Return the last element of the array if it is not empty
        ok(xs.join(""))
    }
}

fn primitive_rtail(mut args: Env, _handle: &Evaluator) -> VResult {
    load_args!(args, xs: Vec<String>);
    // Check if the vector is empty
    if xs.is_empty() {
        // Return an error if the array is empty
        Err("Array is empty".into())
    } else {
        // Return the last element of the array if it is not empty
        ok(xs.last().unwrap().clone())
    }
}

// fn primitive_rsplit(mut args: Env, _handle: &Evaluator) -> VResult {
//     load_args!(args, pattern:String, input:String);
//     // Check if the vector is empty
//     // Use the split method with the pattern, collect results into a Vec<String>
//     // dbg!(pattern.clone());
//     // dbg!(input.clone().split(&pattern));
//     let result: Vec<String> = input.split(&pattern).map(|s| s.to_string()).collect();

//     ok(result)
// }

fn primitive_rsplit(mut args: Env, _handle: &Evaluator) -> VResult {
    load_args!(args, pattern:String, input:String);
    // Check if the vector is empty
    // Use the split method with the pattern, collect results into a Vec<String>
    // dbg!(pattern.clone());
    // dbg!(input.clone().split(&pattern));
    let regex = Regex::new(&pattern).map_err(|e| format!("Invalid regex pattern: {}", e))?;
    let mut result = Vec::new();

    let mut last_end = 0;
    for mat in regex.find_iter(&input) {
        if last_end != mat.start() {
            result.push(input[last_end..mat.start()].to_string());
        }
        result.push(mat.as_str().to_string());
        last_end = mat.end();
    }
    if last_end < input.len() {
        result.push(input[last_end..].to_string());
    }

    ok(result)
}

fn primitive_rappend(mut args: Env, _handle: &Evaluator) -> VResult {
    load_args!(args, element:String, main_array:Vec<String>);
    let mut mutable_array = main_array.clone();

    mutable_array.push(element);
    ok(mutable_array)
}

// Reverse List Except Last Element
fn primitive_rrevcdr(mut args: Env, _handle: &Evaluator) -> VResult {
    load_args!(args, xs: Vec<String>);
    // Check if the vector is empty
    let mut mutable_xs = xs.clone();
    if mutable_xs.len() < 2 {
        return Err("Array has insufficient elements to reverse".into());
    } else {
        let last_element = mutable_xs.pop().unwrap(); // Safely remove the last element
        mutable_xs.reverse(); // Reverse the remaining elements
        mutable_xs.push(last_element); // Add the last element back
        Ok(mutable_xs.into()) // Return the modified vector
    }
}

const replace_te: &str = "(if (_rmatch (_rconcat _t _e) $0) _f $0)";
const postpend_te: &str = "(if (_rmatch (_rconcat _t _e) $0) (_rconcat $0 _f) $0)";
const prepend_te: &str = "(if (_rmatch (_rconcat _t _e) $0) (_rconcat _f $0) $0)";
const remove_te: &str = "(if (_rmatch (_rconcat _t _e) $0) '' $0)";

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_types_regex() {
        use domains::regex::RegexVal;

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
            let res = set.get(e).infer::<RegexVal>(
                &mut Context::empty(),
                &mut Default::default(),
                &RegexVal::new_dsl(),
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
        assert_infer("(_rvowel)", Ok("str"));
        assert_infer("(_rconsonant)", Ok("str"));
        assert_infer("(_emptystr '')", Ok("bool"));
        assert_infer("(_rdot)", Ok("str"));
        assert_infer("(_rnot '[a-z]+')", Ok("str"));
        assert_infer("(_ror '[a-z]+' '[0-9]+')", Ok("str"));
        assert_infer("(_rconcat '[a-z]+' '[0-9]+')", Ok("str"));
        assert_infer("(_rmatch '[a-z]+' 'hello')", Ok("bool"));
        assert_infer("(_rtail ['hello','dear'])", Ok("str"));
        assert_infer("(_rflatten ['hello','dear'])", Ok("str"));
        assert_infer("(_rsplit ',' 'one,two,three')", Ok("list str"));
        assert_infer("(_rappend 'yo' ['hello','dear'])", Ok("list str"));
        assert_infer("(_rrevcdr ['a','b','c','d'])", Ok("list str"));
        assert_infer("(lam $0)", Ok("t0 -> t0"));
        assert_infer("(lam (_ror $0 '[0-9]+'))", Ok("str -> str"));
        assert_infer("(lam (_rsplit (_rconcat _t _e) $0))", Ok("str -> list str"));
        assert_infer("map", Ok("((t0 -> t1) -> (list t0) -> (list t1))"));
        assert_infer("(map (lam (_ror $0 '[0-9]+')))", Ok("list str -> list str"));
    }

    #[test]
    fn test_eval_regex_simple() {
        let dsl = RegexVal::new_dsl();

        // Test for `primitive_rvowel`
        assert_execution::<domains::regex::RegexVal, String>(
            "(_rvowel)",
            &[],
            String::from("[aeiou]"),
        );

        // Test for `primitive_rconsonant`
        assert_execution::<domains::regex::RegexVal, String>(
            "(_rconsonant)",
            &[],
            String::from("[^aeiou]"),
        );

        // Test for `primitive_emptystr`
        assert_execution::<domains::regex::RegexVal, bool>("(_emptystr '')", &[], true);

        // Test for `primitive_rdot`
        assert_execution::<domains::regex::RegexVal, String>("(_rdot)", &[], String::from("."));

        // Test for `primitive_rnot`
        assert_execution::<domains::regex::RegexVal, String>(
            "(_rnot '[a-z]+')",
            &[],
            String::from("[^[a-z]+]"),
        );

        assert_execution::<domains::regex::RegexVal, String>(
            "(_ror '[a-z]+' '[0-9]+')",
            &[],
            String::from("([a-z]+|[0-9]+)"),
        );

        assert_execution::<domains::regex::RegexVal, String>(
            "(_rconcat '[a-z]+' '[0-9]+')",
            &[],
            String::from("[a-z]+[0-9]+"),
        );

        assert_execution::<domains::regex::RegexVal, bool>(
            "(_rmatch '[a-z]+' 'Hello')",
            &[],
            false,
        );

        assert_execution::<domains::regex::RegexVal, String>(
            "(_rtail ['hello','dear'])",
            &[],
            String::from("dear"),
        );

        assert_execution::<domains::regex::RegexVal, String>(
            "(_rflatten ['hello','dear'])",
            &[],
            String::from("hellodear"),
        );

        assert_execution::<domains::regex::RegexVal, Vec<String>>(
            "(_rrevcdr ['a','b','c','d'])",
            &[],
            vec![
                String::from("c"),
                String::from("b"),
                String::from("a"),
                String::from("d"),
            ],
        );

        assert_execution::<domains::regex::RegexVal, Vec<String>>(
            "(_rappend 'yo' ['hello','dear'])",
            &[],
            vec![
                String::from("hello"),
                String::from("dear"),
                String::from("yo"),
            ],
        );

        assert_execution::<domains::regex::RegexVal, Vec<String>>(
            "(_rsplit ',' 'one,two,three')",
            &[],
            vec![
                String::from("one"),
                String::from(","),
                String::from("two"),
                String::from(","),
                String::from("three"),
            ],
        );

        // "match ."
        let arg1 = dsl.val_of_prim(&"'t'".into()).unwrap();
        assert_execution::<domains::regex::RegexVal, bool>("(_rmatch _rdot $0)", &[arg1], true);

        // "match ab"
        let arg1 = dsl.val_of_prim(&"'ab'".into()).unwrap();
        assert_execution::<domains::regex::RegexVal, bool>(
            "(_rmatch (_rconcat _a _b) $0)",
            &[arg1],
            true,
        );

        // "match ab"
        let arg1 = dsl.val_of_prim(&"'bab'".into()).unwrap();
        assert_execution::<domains::regex::RegexVal, bool>(
            "(_rmatch (_rconcat _a _b) $0)",
            &[arg1],
            false,
        );

        // match [^ae]
        let arg1 = dsl.val_of_prim(&"_b".into()).unwrap();
        assert_execution::<domains::regex::RegexVal, bool>(
            "(_rmatch (_rnot (_rconcat _a _e)) $0)",
            &[arg1],
            true,
        );

        // "match [^ae]d"
        let arg1 = dsl.val_of_prim(&"'ed'".into()).unwrap();
        assert_execution::<domains::regex::RegexVal, bool>(
            "(_rmatch (_rconcat (_rnot (_rconcat _a _e)) _d) $0)",
            &[arg1],
            false,
        );

        // single string tests

        let arg1 = dsl.val_of_prim(&"'te'".into()).unwrap();
        assert_execution::<domains::regex::RegexVal, String>(
            postpend_te,
            &[arg1],
            String::from("tef"),
        );

        let arg1 = dsl.val_of_prim(&"'te'".into()).unwrap();
        assert_execution::<domains::regex::RegexVal, String>(
            replace_te,
            &[arg1],
            String::from("f"),
        );
    }
    #[test]
    fn test_eval_regex_lists() {
        let dsl = RegexVal::new_dsl();
        // let arg1 = dsl.val_of_prim(&"'te'".into()).unwrap();
        // assert_execution::<domains::regex::RegexVal, String>(
        //     replace_te,
        //     &[arg1],
        //     String::from("f"),
        // );

        // let raw = String::from("(_rflatten (map ")
        //     + &String::from(replace_te)
        //     + &String::from(" (_rsplit (_rconcat _t _e) $0)))");
        // dbg!(raw.clone());
        let arg1 = dsl.val_of_prim(&"'tehellote'".into()).unwrap();
        assert_execution::<domains::regex::RegexVal, Vec<String>>(
            "(_rsplit (_rconcat _t _e) $0)",
            &[arg1],
            vec![
                String::from("te"),
                String::from("hello"),
                String::from("te"),
            ],
        );

        let arg1 = dsl.val_of_prim(&"'tebyete'".into()).unwrap();
        assert_execution::<domains::regex::RegexVal, Vec<String>>(
            "(_rsplit (_rconcat _t _e) $0)",
            &[arg1],
            vec![String::from("te"), String::from("bye"), String::from("te")],
        );

        let raw = String::from("(_rflatten (map (lam ")
            + &String::from(replace_te)
            + &String::from(") (_rsplit (_rconcat _t _e) $0)))");
        dbg!(raw.clone());
        let arg1 = dsl.val_of_prim(&"'tehellote'".into()).unwrap();
        assert_execution::<domains::regex::RegexVal, String>(
            &raw,
            &[arg1],
            String::from("fhellof"),
        );

        let raw = String::from("(_rflatten (map (lam ")
            + &String::from(remove_te)
            + &String::from(") (_rsplit (_rconcat _t _e) $0)))");
        dbg!(raw.clone());
        let arg1 = dsl.val_of_prim(&"'tehellote'".into()).unwrap();
        assert_execution::<domains::regex::RegexVal, String>(&raw, &[arg1], String::from("hello"));

        // let raw = String::from("((lam (_rflatten (_rappend (")
        //     + &String::from(prepend_te)
        //     + &String::from(" (_rtail $0)) (_rrevcdr $0)))) (_rsplit (_rconcat _t _e) $0))");
        // let raw = String::from(
        //     "((lam (_rflatten (_rappend 'b' (_rrevcdr $0)))) (_rsplit (_rconcat _t _e) $0))",
        // );
        let raw = String::from(
            "((lam (_rflatten (_rappend 'b' (_rrevcdr $0)))) (_rsplit (_rconcat _t _e) $0))",
        );
        // (if (_rmatch (_rconcat _t _e) $0) '' $0)
        dbg!(raw.clone());
        let arg1 = dsl.val_of_prim(&"'tehellote'".into()).unwrap();
        assert_execution::<domains::regex::RegexVal, String>(
            &raw,
            &[arg1],
            String::from("helloteteb"),
        );
    }
}
