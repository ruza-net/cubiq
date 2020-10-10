use std::convert::TryFrom;
use std::collections::HashMap;

use nom::error::VerboseError;
use super::parser::{ parse_term, parse_type, parse_opaque, parse_maybe_type };

pub trait Parse<X> {
    fn into_ast(&self) -> Result<X, nom::Err<VerboseError<&str>>>;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConvertError {
    TermWhereOpaque(Term),
    TypeWhereOpaque(Type),
}

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

    Eq(Box<MaybeType>, Box<Term>, Box<Term>),
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

    PathAction { var: String, action: Box<OpenTerm>, out_ty: Box<MaybeType> },// NOTE: A function
    ReflStretch(Box<MaybeType>),// NOTE: A function
    Refl(Box<MaybeTerm>),
    Opaque(Opaque),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Term {
    Type(Type),
    Lambda(String, Box<Term>),

    PathAction { var: String, action: Box<OpenTerm>, out_ty: Box<MaybeType> },
    ReflStretch(Box<MaybeType>),
    Refl(Box<MaybeTerm>),
    Opaque(Opaque),
}


// Conversions
//
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

            MaybeTerm::PathAction { var, action, out_ty } => Term::PathAction { var, action, out_ty },
            MaybeTerm::ReflStretch(ty) => Term::ReflStretch(ty),

            MaybeTerm::Refl(x) => Term::Refl(x),
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

impl TryFrom<MaybeTerm> for Opaque {
    type Error = ConvertError;

    fn try_from(tm: MaybeTerm) -> Result<Self, Self::Error> {
        match tm {
            MaybeTerm::Refl(v) => Opaque::try_from(*v),
            MaybeTerm::Opaque(o) => Ok(o),

            tm => Err(ConvertError::TermWhereOpaque(tm.into())),
        }
    }
}
impl TryFrom<Term> for Opaque {
    type Error = ConvertError;

    fn try_from(tm: Term) -> Result<Self, Self::Error> {
        match tm {
            Term::Refl(v) => Opaque::try_from(*v),
            Term::Opaque(o) => Ok(o),

            tm => Err(ConvertError::TermWhereOpaque(tm.into())),
        }
    }
}
impl TryFrom<MaybeType> for Opaque {
    type Error = ConvertError;

    fn try_from(tm: MaybeType) -> Result<Self, Self::Error> {
        match tm {
            MaybeType::Type(ty) => Err(ConvertError::TypeWhereOpaque(ty)),
            MaybeType::Opaque(o) => Ok(o),
        }
    }
}

// Parsing
//
macro_rules! parsing {
    ( $class:ident ~ $func:ident ) => (
        impl Parse<$class> for &'_ str {
            fn into_ast(&self) -> Result<$class, nom::Err<VerboseError<&str>>> {
                let (_, ret) = $func(self)?;

                Ok(ret)
            }
        }
        impl Parse<$class> for &'_ String {
            fn into_ast(&self) -> Result<$class, nom::Err<VerboseError<&str>>> {
                let (_, ret) = $func(self)?;

                Ok(ret)
            }
        }
        impl Parse<$class> for String {
            fn into_ast(&self) -> Result<$class, nom::Err<VerboseError<&str>>> {
                let (_, ret) = $func(self)?;

                Ok(ret)
            }
        }
    );
}
parsing! { Type ~ parse_type }
parsing! { Term ~ parse_term }
parsing! { MaybeType ~ parse_maybe_type }
parsing! { Opaque ~ parse_opaque }
