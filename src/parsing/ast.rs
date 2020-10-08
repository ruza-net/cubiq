use std::collections::HashMap;


/// Represents an open syntax element.
///
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Open<X> {
    pub bound: HashMap<String, MaybeType>,
    pub body: X,
}
pub type OpenTerm = Open<Term>;
pub type OpenType = Open<Type>;

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Type {
    Universe(usize),

    Func(Option<String>, Box<MaybeType>, Open<Box<MaybeType>>),
    Pair(Option<String>, Box<MaybeType>, Open<Box<MaybeType>>),
}

// Syntax element which isn't reduced and has an unknown type.
//
// NOTE: This in particular excludes lambda expressions and types.
//
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Opaque {
    Var(String),
    Call(Box<Term>, Box<Term>),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum MaybeType {
    Type(Type),
    Opaque(Opaque),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Term {
    Type(Type),
    Lambda(String, Box<Term>),
    Opaque(Opaque),
}

impl From<Type> for Term {
    fn from(ty: Type) -> Self {
        Term::Type(ty)
    }
}
impl From<Opaque> for Term {
    fn from(o: Opaque) -> Self {
        Term::Opaque(o)
    }
}
impl<S: ToString> From<S> for Term {
    fn from(s: S) -> Self {
        Term::Opaque(Opaque::Var(s.to_string()))
    }
}
impl<S: ToString> From<S> for Opaque {
    fn from(s: S) -> Self {
        Opaque::Var(s.to_string())
    }
}

impl From<Type> for MaybeType {
    fn from(ty: Type) -> Self {
        MaybeType::Type(ty)
    }
}
impl From<Opaque> for MaybeType {
    fn from(o: Opaque) -> Self {
        MaybeType::Opaque(o)
    }
}

impl<X> From<X> for Open<X> {
    fn from(x: X) -> Self {
        Open {
            bound: HashMap::new(),
            body: x,
        }
    }
}
