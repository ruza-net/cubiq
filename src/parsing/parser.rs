use std::collections::HashMap;

use nom:: {
    branch::alt,

    bytes::complete::{ tag, take_while },
    character::complete::{ space0, digit0 },

    combinator::{ cut, map, map_res, verify },
    sequence::{ preceded, tuple },

    error::{ context, VerboseError },
    IResult,
};

use crate::ast::*;


macro_rules! parse_dep_ty {
    ( $fn_name:ident , $variant:expr , $domain:expr , $range:expr ; $op:tt ) => {
        fn $fn_name(i: &str) -> IResult<&str, Type, VerboseError<&str>> {
            if let Ok((res, (_, (bound, source), _))) =
                tuple((
                    tag("("),
                    parse_binding,
                    tag(")"),
                ))(i)
            {// ANCHOR: Is dependent
                let (res, (_, target)) =
                    tuple((
                        atomic![tag(stringify![$op])],
                        context($range, cut(parse_maybe_type)),
                    ))(res)?;

                Ok((res, $variant(
                    Some(bound.clone()),
                    Box::new(source.clone()),
                    Box::new(Open {
                        bound: { let mut tmp = HashMap::new(); tmp.insert(bound, source); tmp },
                        body: target,
                    }),
                )))

            } else {// ANCHOR: Isn't dependent
                map(
                    tuple((
                        context($domain, parse_atomic_ty),
                        atomic![tag(stringify![$op])],
                        context($range, cut(parse_maybe_type)),
                    )),
                    |(source, _, target)| $variant(None, Box::new(source), Box::new(target.into())),
                )(i)
            }
        }
    };
}

macro_rules! atomic {
    ( $parser:expr ) => {
        map(
            tuple((
                space0,
                $parser,
                space0,
            )),
            |(_, res, _)| res,
        )
    };
}

macro_rules! enclosed {
    ( $parser:expr ) => {
        map(
            tuple((
                atomic![tag("(")],
                $parser,
                tag(")"),
            )),
            |(_, res, _)| res,
        )
    };
}

macro_rules! into {
    ( $parser:expr ) => {
        map(
            $parser,
            |res| res.into(),
        )
    };
}


const KEYWORDS: [&str; 4] = ["type", "refl", "ap", "stretch"];

fn parse_ident(i: &str) -> IResult<&str, &str, VerboseError<&str>> {
    atomic![
        verify(
            take_while(|c| '_' == c || c.is_alphanumeric()),
            |ident: &str| !KEYWORDS.contains(&ident) && ident.len() > 0
        )
    ](i)
}

fn parse_universe(i: &str) -> IResult<&str, Type, VerboseError<&str>> {
    map_res(
        preceded(atomic![tag("type")], atomic![digit0]),
        |num: &str| {
            if num.len() == 0 {
                Ok(Type::Universe(0))

            } else {
                num.parse().map(Type::Universe)
            }
        }
    )(i)
}

parse_dep_ty! { parse_func_ty, Type::Func, "function domain", "function range"; -> }
parse_dep_ty! { parse_pair_ty, Type::Pair, "pair domain", "pair range"; # }

//            TODO: Support general patterns.
//                                          ↓
fn parse_binding(i: &str) -> IResult<&str, (String, MaybeType), VerboseError<&str>> {
    map(
        tuple((
            parse_ident,
            tag(":"),
            parse_maybe_type,
        )),

        |(ident, _, ty): (&str, &str, MaybeType)| (ident.to_string(), ty)
    )(i)
}

fn parse_atomic_ty(i: &str) -> IResult<&str, MaybeType, VerboseError<&str>> {
    alt((
        into![parse_opaque],
        into![parse_universe],
        into![enclosed![parse_type]],
    ))(i)
}

fn parse_call(i: &str) -> IResult<&str, Opaque, VerboseError<&str>> {
    // ANCHOR: The lambda
    //
    let (res, lam) = alt((
        enclosed![
            alt((
                parse_lambda,
                into![parse_opaque],
            ))
        ],
        into![parse_ident],
    ))(i)?;

    // ANCHOR: The argument
    //
    let (res, arg) = alt((
        enclosed![parse_term],
        into![parse_universe],
        into![parse_ident],
    ))(res)?;

    Ok((res, Opaque::Call(Box::new(lam), Box::new(arg))))
}

fn parse_lambda(i: &str) -> IResult<&str, MaybeTerm, VerboseError<&str>> {
    map(
        tuple((
            parse_ident,
            tag("=>"),
            parse_term,
        )),
        |(arg_name, _, body)| MaybeTerm::Lambda(arg_name.to_string(), Box::new(body)),
    )(i)
}

// Without enclosion
//
fn _parse_type(i: &str) -> IResult<&str, Type, VerboseError<&str>> {
    alt((
        parse_func_ty,
        parse_pair_ty,
        parse_universe,
    ))(i)
}

// Without enclosion
//
fn _parse_opaque(i: &str) -> IResult<&str, Opaque, VerboseError<&str>> {
    alt((
        parse_call,
        into![parse_ident],
    ))(i)
}

/// Parses a term expression: a type, opaque expression or lambda expression.
///
pub fn parse_term(i: &str) -> IResult<&str, Term, VerboseError<&str>> {
    alt((
        into![parse_lambda],
        into![_parse_type],
        into![_parse_opaque],
        enclosed![parse_term],
    ))(i)
}

/// Parses an expression that might be a type: a type or opaque expression.
///
pub fn parse_maybe_type(i: &str) -> IResult<&str, MaybeType, VerboseError<&str>> {
    alt((
        into![parse_type],
        into![parse_opaque],
    ))(i)
}

/// Parses a type expression: a universe, function type or pair type.
///
pub fn parse_type(i: &str) -> IResult<&str, Type, VerboseError<&str>> {
    alt((
        _parse_type,
        enclosed![parse_type],
    ))(i)
}

/// Parses an opaque expression: variable or a function call.
///
pub fn parse_opaque(i: &str) -> IResult<&str, Opaque, VerboseError<&str>> {
    alt((
        _parse_opaque,
        enclosed![parse_opaque],
    ))(i)
}
