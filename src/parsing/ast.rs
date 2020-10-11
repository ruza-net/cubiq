use std::convert::TryFrom;
use std::collections::HashMap;
use std::marker::PhantomData as pd;

use nom::error::VerboseError;
use super::parser::{ parse_term, parse_type, parse_opaque, parse_maybe_type };


pub trait Substitution<X> {
    type Output;

    fn subst(self, name: &str, val: X) -> Result<Self::Output, SubstError>;
}
pub trait Parse<X> {
    fn into_ast(&self) -> Result<X, nom::Err<VerboseError<&str>>>;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SubstError {
    TypeWhereTerm(Type),
    TermWhereType(Term),
    FuncWherePair(Term),
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConvertError<Target, Source>(pd<Target>, Source);

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

    Induction(Box<MaybeType>),// NOTE: A function

    Opaque(Opaque),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Term {
    Type(Type),
    Lambda(String, Box<Term>),

    PathAction { var: String, action: Box<OpenTerm>, out_ty: Box<MaybeType> },
    ReflStretch(Box<MaybeType>),
    Refl(Box<MaybeTerm>),

    Induction(Box<MaybeType>),

    Opaque(Opaque),
}


impl<X: Clone> Substitution<X> for Term
    where
        Opaque: Substitution<X>,
        Term: From<<Opaque as Substitution<X>>::Output>,
{
    type Output = Self;

    fn subst(self, name: &str, val: X) -> Result<Self::Output, SubstError> {
        match self {
            Term::Type(ty) => Ok(Term::Type(ty.subst(name, val)?)),
            Term::Lambda(arg_name, body) => {
                if arg_name == name {
                    Ok(Term::Lambda(arg_name, body))

                } else {
                    Ok(Term::Lambda(arg_name, Box::new(body.subst(name, val)?)))
                }
            },

            Term::PathAction { var, action, out_ty } => {
                let action = if var == name {
                    action
                } else {
                    Box::new(action.subst(name, val.clone())?)
                };

                let out_ty = Box::new(out_ty.subst(name, val.clone())?);

                Ok(Term::PathAction { var, action, out_ty })
            },
            Term::ReflStretch(ty) => Ok(Term::ReflStretch(Box::new(ty.subst(name, val)?))),
            Term::Refl(x) => Ok(Term::Refl(Box::new(x.subst(name, val)?))),

            Term::Induction(ty) => Ok(Term::Induction(Box::new(ty.subst(name, val)?))),

            Term::Opaque(x) => Ok(x.subst(name, val)?.into()),
        }
    }
}

impl<X: Clone> Substitution<X> for Type
    where
        Opaque: Substitution<X>,
        Term: From<<Opaque as Substitution<X>>::Output>,
{
    type Output = Self;

    fn subst(self, name: &str, val: X) -> Result<Self::Output, SubstError> {
        match self {
            Type::Universe(lvl) => Ok(Type::Universe(lvl)),

            Type::Func(arg_name, source, target) => {
                let target = if arg_name.as_ref().map(|n| n == name).unwrap_or(false) {
                    target

                } else {
                    Box::new(target.subst(name, val.clone())?)
                };

                let source = Box::new(source.subst(name, val)?);

                Ok(Type::Func(arg_name, source, target))
            },
            Type::Pair(arg_name, first, second) => {
                let second = if arg_name.as_ref().map(|n| n == name).unwrap_or(false) {
                    second

                } else {
                    Box::new(second.subst(name, val.clone())?)
                };

                let first = Box::new(first.subst(name, val)?);

                Ok(Type::Pair(arg_name, first, second))
            },

            Type::Eq(ty, a, b) => Ok(Type::Eq(
                Box::new(ty.subst(name, val.clone())?),
                Box::new(a.subst(name, val.clone())?),
                Box::new(b.subst(name, val)?),
            )),
        }
    }
}

impl<X: Clone> Substitution<X> for MaybeType
    where
        Opaque: Substitution<X>,
        Term: From<<Opaque as Substitution<X>>::Output>,
{
    type Output = Self;

    fn subst(self, name: &str, val: X) -> Result<Self::Output, SubstError> {
        match self {
            MaybeType::Type(ty) => Ok(MaybeType::Type(ty.subst(name, val)?)),
            MaybeType::Opaque(o) => {
                let out = Term::from(o.subst(name, val)?);

                match out {
                    Term::Type(ty) => Ok(MaybeType::Type(ty)),
                    Term::Opaque(o) => Ok(MaybeType::Opaque(o)),

                    tm => Err(SubstError::TermWhereType(tm)),
                }
            },
        }
    }
}

impl<X: Clone> Substitution<X> for MaybeTerm
    where
        Opaque: Substitution<X>,
        Term: From<<Opaque as Substitution<X>>::Output>,
{
    type Output = Self;

    fn subst(self, name: &str, val: X) -> Result<Self::Output, SubstError> {
        match self {
            MaybeTerm::Lambda(arg, body) => {
                let body = if arg == name {
                    body

                } else {
                    Box::new(body.subst(name, val)?)
                };

                Ok(MaybeTerm::Lambda(arg, body))
            },

            MaybeTerm::PathAction { var, action, out_ty } => {
                let action = if var == name {
                    action

                } else {
                    Box::new(action.subst(name, val.clone())?)
                };

                let out_ty = Box::new(out_ty.subst(name, val)?);

                Ok(MaybeTerm::PathAction { var, action, out_ty })
            },
            MaybeTerm::ReflStretch(ty) => Ok(MaybeTerm::ReflStretch(Box::new(ty.subst(name, val)?))),
            MaybeTerm::Refl(x) => Ok(MaybeTerm::Refl(Box::new(x.subst(name, val)?))),

            MaybeTerm::Induction(ty) => Ok(MaybeTerm::Induction(Box::new(ty.subst(name, val)?))),
            MaybeTerm::Opaque(o) => {
                let out = o.subst(name, val)?.into();

                match out {
                    Term::Type(ty) => Err(SubstError::TypeWhereTerm(ty)),

                    Term::Lambda(arg, body) => Ok(MaybeTerm::Lambda(arg, body)),

                    Term::PathAction { var, action, out_ty } => Ok(MaybeTerm::PathAction { var, action, out_ty }),

                    Term::ReflStretch(ty) => Ok(MaybeTerm::ReflStretch(ty)),

                    Term::Refl(x) => Ok(MaybeTerm::Refl(x)),

                    Term::Induction(ty) => Ok(MaybeTerm::Induction(ty)),

                    Term::Opaque(o) => Ok(MaybeTerm::Opaque(o)),
                }
            },
        }
    }
}

impl<X, Y> Substitution<Y> for Open<X>
    where
        X: Substitution<Y>,
        X: From<<X as Substitution<Y>>::Output>,
{
    type Output = Self;

    fn subst(self, name: &str, val: Y) -> Result<Self::Output, SubstError> {
        let Open { mut bound, body } = self;

        if bound.contains_key(name) {
            bound.remove(name);
        }

        let body = body.subst(name, val)?.into();

        Ok(Open { bound, body })
    }
}

impl Substitution<Opaque> for Opaque {
    type Output = Self;

    fn subst(self, name: &str, val: Opaque) -> Result<Self::Output, SubstError> {
        match self {
            Opaque::Var(v_name) => {
                if v_name == name {
                    Ok(val)

                } else {
                    Ok(Opaque::Var(v_name))
                }
            },

            Opaque::Call(f, a) =>
                Ok(Opaque::Call(
                    Box::new(f.subst(name, val.clone())?),
                    Box::new(a.subst(name, val)?),
                )),
        }
    }
}
impl Substitution<MaybeType> for Opaque {
    type Output = MaybeType;

    fn subst(self, name: &str, val: MaybeType) -> Result<Self::Output, SubstError> {
        match self {
            Opaque::Var(v_name) => {
                if v_name == name {
                    Ok(val)

                } else {
                    Ok(Opaque::Var(v_name).into())
                }
            },

            Opaque::Call(f, a) => {
                let f = f.subst(name, val.clone())?;

                Ok(Opaque::Call(
                    Box::new(f),
                    Box::new(a.subst(name, val)?),
                ).into())
            },
        }
    }
}
impl Substitution<MaybeTerm> for Opaque {
    type Output = MaybeTerm;

    fn subst(self, name: &str, val: MaybeTerm) -> Result<Self::Output, SubstError> {
        match self {
            Opaque::Var(v_name) => {
                if v_name == name {
                    Ok(val)

                } else {
                    Ok(Opaque::Var(v_name).into())
                }
            },

            Opaque::Call(f, a) => {
                let f = f.subst(name, val.clone())?;

                Ok(Opaque::Call(
                    Box::new(f),
                    Box::new(a.subst(name, val)?),
                ).into())
            },
        }
    }
}
impl Substitution<Type> for Opaque {
    type Output = MaybeType;

    fn subst(self, name: &str, val: Type) -> Result<Self::Output, SubstError> {
        match self {
            Opaque::Var(v_name) => {
                if v_name == name {
                    Ok(val.into())

                } else {
                    Ok(Opaque::Var(v_name).into())
                }
            },

            Opaque::Call(f, a) => {
                let f = f.subst(name, val.clone())?;

                Ok(Opaque::Call(
                    Box::new(f),
                    Box::new(a.subst(name, val)?),
                ).into())
            },
        }
    }
}
impl Substitution<Term> for Opaque {
    type Output = Term;

    fn subst(self, name: &str, val: Term) -> Result<Self::Output, SubstError> {
        match self {
            Opaque::Var(v_name) => {
                if v_name == name {
                    Ok(val)

                } else {
                    Ok(Opaque::Var(v_name).into())
                }
            },
            Opaque::Call(f, a) => {
                let f = f.subst(name, val.clone())?;

                Ok(Opaque::Call(
                    Box::new(f),
                    Box::new(a.subst(name, val)?),
                ).into())
            },
        }
    }
}


// Conversions
//
macro_rules! convert_str {
    ( $this:ident ) => (
        impl<S: ToString> From<S> for $this {
            fn from(s: S) -> $this {
                Opaque::Var(s.to_string()).into()
            }
        }
    );
}
macro_rules! convert_straight {
    ( $src:ident => $this:ident ) => (
        impl From<$src> for $this {
            fn from(x: $src) -> $this {
                $this::$src(x)
            }
        }
    );
}

macro_rules! convert_struct {
    ( $src:ident { $( $t_var:ident ( $($t_arg:ident),* ) ),* | $( $s_var:ident { $($s_arg:ident),* } ),* } => $this:ident ) => (
        impl From<$src> for $this {
            fn from(x: $src) -> $this {
                match x {
                    $(
                        $src::$t_var($($t_arg),*) => $this::$t_var($($t_arg),*),
                    )*

                    $(
                        $src::$s_var{ $($s_arg),* } => $this::$s_var{ $($s_arg),* },
                    )*
                }
            }
        }
    );
}

macro_rules! try_convert {
    ( $src:ident | $($success:ident),* | { $( $t_var:ident ),* } => $this:ident ) => (
        impl TryFrom<$src> for $this {
            type Error = ConvertError<$this, $src>;

            fn try_from(x: $src) -> Result<$this, Self::Error> {
                match x {
                    $(
                        $src::$success(x) => Ok(x),
                    )*

                    $(
                        $src::$t_var(x) => $this::try_from($src::from(*x)),
                    )*

                    rest => Err(ConvertError(pd, rest)),
                }
            }
        }
    );
}

convert_straight! { Type => Term }
convert_straight! { Opaque => Term }
convert_straight! { Type => MaybeType }
convert_straight! { Opaque => MaybeType }
convert_straight! { Opaque => MaybeTerm }

convert_struct! { MaybeType { Type(ty), Opaque(o) | } => Term }
convert_struct! {
    MaybeTerm {
        Lambda(arg_name, body),
        Opaque(o),
        ReflStretch(ty),
        Refl(x),
        Induction(ty)
        | PathAction { var, action, out_ty }
    } => Term
}

convert_str! { Term }
convert_str! { Opaque }
convert_str! { MaybeType }
convert_str! { MaybeTerm }

impl<X> From<X> for Open<X> {
    fn from(x: X) -> Self {
        Open {
            bound: HashMap::new(),
            body: x,
        }
    }
}

try_convert! { MaybeTerm |Opaque| { Refl } => Opaque }
try_convert! { Term |Opaque| { Refl } => Opaque }
try_convert! { MaybeType |Opaque| { } => Opaque }

// Parsing
//
macro_rules! parse_via {
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
parse_via! { Type ~ parse_type }
parse_via! { Term ~ parse_term }
parse_via! { MaybeType ~ parse_maybe_type }
parse_via! { Opaque ~ parse_opaque }
