use std::collections::HashMap;


/// Represents an open syntax element.
///
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Open<X> {
    pub bound: HashMap<String, Reducible>,
    pub body: X,
}
pub type OpenTerm = Open<Term>;
pub type OpenType = Open<Type>;

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Type {
    Universe(usize),

    Func(Box<Reducible>, Open<Box<Reducible>>),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Reducible {
    Type(Type),

    Var(String),
    Call(Box<Term>, Box<Term>),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Term {
    Reducible(Reducible),
    Lambda(String, Box<Term>),
}