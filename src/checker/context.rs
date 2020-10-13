use crate::ast as syn;

use std::ptr::NonNull;
use std::collections::{ HashSet, HashMap, BTreeSet };

pub type EqualityClass<X> = BTreeSet<X>;// NOTE: The least element is considered a "normal form".


trait EqualityChecker<X> {
    fn equal(&self, lhs: &X, rhs: &X) -> bool;
}

trait Reducer<X> {
    type Output;

    fn reduce(&self, val: X) -> Option<Self::Output>;
}

#[derive(Debug, Clone)]
pub struct Context {
    parent: Option<NonNull<Self>>,

    characteristic: usize,// How many universes exist (0 implies infinitely many)

    equalities: HashSet<(syn::MaybeType, syn::Open<EqualityClass<syn::Term>>)>,
    variables: HashMap<String, syn::MaybeType>,
}

// Context-level Constructions
//
impl Context {
    pub fn new(characteristic: usize) -> Self {
        Context {
            parent: None,
            characteristic,

            equalities: HashSet::new(),
            variables: HashMap::new(),
        }
    }

    pub fn new_instance(&self) -> Self {
        Context {
            parent: NonNull::new(self as *const _ as *mut _),
            characteristic: self.characteristic,

            equalities: HashSet::new(),
            variables: HashMap::new(),
        }
    }

    pub fn assume_var(&mut self, name: String, ty: syn::MaybeType) {
        self.variables.insert(name, ty);
    }
}

// Type-level Constructions
//
impl Context {
    pub fn make_universe(&self, lvl: usize) -> syn::Type {
        assert![self.characteristic == 0 || lvl <= self.characteristic, "cannot construct universe of level {}", lvl];

        syn::Type::Universe(lvl)
    }

    // TODO: Typecheck
    //
    pub fn make_func(&self, arg: Option<String>, source: syn::MaybeType, target: syn::Open<syn::MaybeType>) -> Option<syn::Type> {
        if arg.as_ref().map(|arg_name| self.equal(&source, target.bound.get(arg_name).unwrap())).unwrap_or(true) {
            Some(syn::Type::Func(
                arg,
                Box::new(source),
                Box::new(target),
            ))

        } else {
            None
        }
    }
}


impl EqualityChecker<syn::MaybeType> for Context {
    fn equal(&self, lhs: &syn::MaybeType, rhs: &syn::MaybeType) -> bool {
        match (lhs, rhs) {
            (syn::MaybeType::Type(lhs), syn::MaybeType::Type(rhs)) =>
                self.equal(lhs, rhs),

            (syn::MaybeType::Opaque(lhs), syn::MaybeType::Opaque(rhs)) =>
                self.equal(lhs, rhs),

            (lhs, rhs) => unimplemented![],
        }
    }
}

impl EqualityChecker<syn::Type> for Context {
    fn equal(&self, lhs: &syn::Type, rhs: &syn::Type) -> bool {
        match (lhs, rhs) {
            (syn::Type::Universe(lhs), syn::Type::Universe(rhs)) =>
                lhs == rhs,

            (syn::Type::Func(_, lhs_src, lhs_trg), syn::Type::Func(_, rhs_src, rhs_trg)) =>
                self.equal(&**lhs_src, &**rhs_src) && self.equal(&**lhs_trg, &**rhs_trg),

            (syn::Type::Pair(_, lhs_src, lhs_trg), syn::Type::Pair(_, rhs_src, rhs_trg)) =>
                self.equal(&**lhs_src, &**rhs_src) && self.equal(&**lhs_trg, &**rhs_trg),

            (syn::Type::Eq(lhs_ty, lhs_a, lhs_b), syn::Type::Eq(rhs_ty, rhs_a, rhs_b)) =>
                unimplemented![],

            (syn::Type::Eq(lhs_ty, lhs_a, lhs_b), rhs) =>
                unimplemented![],

            (lhs, syn::Type::Eq(rhs_ty, rhs_a, rhs_b)) =>
                unimplemented![],

            _ => false,
        }
    }
}

impl EqualityChecker<syn::Opaque> for Context {
    fn equal(&self, lhs: &syn::Opaque, rhs: &syn::Opaque) -> bool {
        unimplemented!()
    }
}

impl<X> EqualityChecker<syn::Open<X>> for Context where Context: EqualityChecker<X> {
    fn equal(&self, lhs: &syn::Open<X>, rhs: &syn::Open<X>) -> bool {
        if lhs.bound == rhs.bound {
            let mut child = self.new_instance();

            for (var, ty) in &lhs.bound {
                child.assume_var(var.clone(), ty.clone());
            }

            child.equal(&lhs.body, &rhs.body)

        } else {
            false
        }
    }
}


impl Reducer<syn::MaybeType> for Context {
    type Output = syn::Type;

    fn reduce(&self, val: syn::MaybeType) -> Option<Self::Output> {
        match val {
            syn::MaybeType::Type(ty) => Some(ty),

            syn::MaybeType::Opaque(o) => unimplemented![],
        }
    }
}
