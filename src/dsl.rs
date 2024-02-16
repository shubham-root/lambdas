use crate::*;

use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;
use std::sync::Arc;
use std::time::Duration;

pub type DSLFn<D> = Arc<(dyn Fn(Env<D>, &Evaluator<D>) -> VResult<D>)>;

#[derive(Clone)]
pub struct Production<D: Domain> {
    pub name: Symbol, // eg "map" or "0" or "[1,2,3]"
    pub val: Val<D>,
    pub tp: SlowType,
    pub arity: usize,
    pub lazy_args: HashSet<usize>,
    pub fn_ptr: Option<DSLFn<D>>,
    pub log_variable: f32,
}

impl<D: Domain> Debug for Production<D> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Production")
            .field("name", &self.name)
            .field("val", &self.val)
            .field("tp", &self.tp)
            .field("arity", &self.arity)
            .field("log_variable", &self.log_variable)
            .finish()
    }
}

#[derive(Clone, Debug)]
pub struct DSL<D: Domain> {
    pub productions: HashMap<Symbol, Production<D>>,
    pub log_variable: f32,
    // pub continuationType: str
    // pub lookup_fn_ptr: HashMap<Symbol,DSLFn<D>>,
}

impl<D: Domain> Production<D> {
    pub fn val(name: &str, tp: &str, val: Val<D>, ll: f32) -> Self {
        Production::val_raw(name.into(), tp.parse().unwrap(), val, ll)
    }

    pub fn func(name: &str, tp: &str, fn_ptr: DSLFn<D>, ll: f32) -> Self {
        Production::func_custom(name.into(), tp, Default::default(), fn_ptr, ll)
    }

    pub fn func_custom(
        name: &str,
        tp: &str,
        lazy_args: Option<&[usize]>,
        fn_ptr: DSLFn<D>,
        ll: f32,
    ) -> Self {
        let lazy_args = lazy_args
            .map(|args| args.iter().copied().collect())
            .unwrap_or_default();
        Production::func_raw(name.into(), tp.parse().unwrap(), lazy_args, fn_ptr, ll)
    }

    pub fn val_raw(name: Symbol, tp: SlowType, val: Val<D>, ll: f32) -> Self {
        assert_eq!(tp.arity(), 0);
        Production {
            name,
            val,
            tp,
            arity: 0,
            lazy_args: Default::default(),
            fn_ptr: None,
            log_variable: ll,
        }
    }

    pub fn func_raw(
        name: Symbol,
        tp: SlowType,
        lazy_args: HashSet<usize>,
        fn_ptr: DSLFn<D>,
        ll: f32,
    ) -> Self {
        let arity = tp.arity();
        Production {
            name: name.clone(),
            val: PrimFun(CurriedFn::<D>::new(name, arity)),
            tp,
            arity,
            lazy_args,
            fn_ptr: Some(fn_ptr),
            log_variable: ll,
        }
    }
}
impl<D: Domain> DSL<D> {
    pub fn new(productions: Vec<Production<D>>, log_variable: f32) -> Self {
        DSL {
            productions: productions
                .into_iter()
                .map(|entry| (entry.name.clone(), entry))
                .collect(),
            log_variable,
        }
    }

    /// add an entry to the DSL
    pub fn add_entry(&mut self, entry: Production<D>) {
        assert!(!self.productions.contains_key(&entry.name));
        self.productions.insert(entry.name.clone(), entry);
    }

    /// given a primitive's symbol return a runtime Val object. For function primitives
    /// this should return a PrimFun(CurriedFn) object.
    pub fn val_of_prim(&self, p: &Symbol) -> Option<Val<D>> {
        self.productions
            .get(p)
            .map(|entry| entry.val.clone())
            .or_else(|| D::val_of_prim_fallback(p))
    }

    pub fn type_of_prim(&self, p: &Symbol) -> SlowType {
        self.productions
            .get(p)
            .map(|entry| entry.tp.clone())
            .unwrap_or_else(|| D::type_of_dom_val(&self.val_of_prim(p).unwrap().dom().unwrap()))
    }
}

/// The key trait that defines a domain
pub trait Domain: Clone + Debug + PartialEq + Eq + Hash + Send + Sync {
    type Data: Debug + Default;

    fn val_of_prim_fallback(p: &Symbol) -> Option<Val<Self>>;

    fn type_of_dom_val(&self) -> SlowType;

    fn new_dsl() -> DSL<Self>;
}

pub fn lambda_eval<D: Domain>(expr: &str) -> DSLFn<D> {
    let expr = expr.to_owned();


    Arc::new(move |args: Env<D>, handle: &Evaluator<D>| -> VResult<D> {
        let mut set = ExprSet::empty(Order::ChildFirst, false, false);
        let e = set.parse_extend(&expr).unwrap();
        dbg!(e);
        let res = set.get(e).as_eval(&handle.dsl, Some(Duration::from_secs(60)));
        dbg!(&res);
        let result = res.eval_child(res.expr.idx, &args);
        dbg!(args);
        dbg!(res.expr.idx);

        dbg!(&result);

        result
    })
}

