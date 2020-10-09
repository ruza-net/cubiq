use std::collections::HashMap;


/// Represents an open syntax element.
///
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Open<X> {
    pub bound: HashMap<String, MaybeType>,
    pub body: X,
}
pub type OpenTerm = Open<Term>;
pub type OpenType = Open<MaybeType>;

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Type {
    Universe(usize),

    Func(Option<String>, Box<MaybeType>, Box<OpenType>),
    Pair(Option<String>, Box<MaybeType>, Box<OpenType>),
}

/// Syntax element which isn't reduced and has an unknown type.
///
/// NOTE: This in particular excludes lambda expressions and types.
///
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Opaque {
    Var(String),
    Call(Box<MaybeTerm>, Box<Term>),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum MaybeType {
    Type(Type),
    Opaque(Opaque),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum MaybeTerm {
    Lambda(String, Box<Term>),
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
impl From<MaybeType> for Term {
    fn from(o: MaybeType) -> Self {
        match o {
            MaybeType::Type(ty) => Term::Type(ty),
            MaybeType::Opaque(o) => Term::Opaque(o),
        }
    }
}
impl From<MaybeTerm> for Term {
    fn from(o: MaybeTerm) -> Self {
        match o {
            MaybeTerm::Lambda(arg_name, body) => Term::Lambda(arg_name, body),
            MaybeTerm::Opaque(o) => Term::Opaque(o),
        }
    }
}

impl<S: ToString> From<S> for Term {
    fn from(s: S) -> Self {
        Term::Opaque(Opaque::Var(s.to_string()))
    }
}
impl<S: ToString> From<S> for MaybeTerm {
    fn from(s: S) -> Self {
        MaybeTerm::Opaque(Opaque::Var(s.to_string()))
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
impl From<Opaque> for MaybeTerm {
    fn from(o: Opaque) -> Self {
        MaybeTerm::Opaque(o)
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
