use crate::ast as syn;

use std::ptr::NonNull;
use std::collections::{ HashSet, HashMap, BTreeSet };

pub type EqualityClass<X> = BTreeSet<X>;


trait EqualityChecker<X> {
    fn equal(&self, lhs: &X, rhs: &X) -> bool;
}

#[derive(Debug, Clone)]
pub struct Context {
    parent: Option<NonNull<Self>>,

    characteristic: usize,// How many universes exist (0 implies infinitely many)

    equalities: HashSet<syn::Open<EqualityClass<syn::Term>>>,
    variables: HashMap<String, syn::Type>,

    children: Vec<Self>,
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

            children: Vec::new(),
        }
    }

    pub fn new_instance(&mut self) -> Self {
        Context {
            parent: NonNull::new(self),
            characteristic: self.characteristic,

            equalities: HashSet::new(),
            variables: HashMap::new(),

            children: Vec::new(),
        }
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
        unimplemented!()
    }
}
