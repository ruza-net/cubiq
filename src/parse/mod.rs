use std::collections::HashMap;

use nom:: {
    branch::alt,

    bytes::complete::tag,
    character::complete::{ alpha1, digit0 },

    combinator::{ cut, map, map_res, map_parser },
    sequence::{ preceded, tuple },

    error::{ context, VerboseError },
    IResult,
};

use crate::ast::syntax::*;


fn parse_universe(i: &str) -> IResult<&str, Type, VerboseError<&str>> {
    map_res(
        preceded(tag("type"), digit0),
        |num: &str| {
            if num.len() == 0 {
                Ok(Type::Universe(0))

            } else {
                num.parse().map(Type::Universe)
            }
        }
    )(i)
}

fn parse_function(i: &str) -> IResult<&str, Type, VerboseError<&str>> {
    if let Ok((res, (_, (bound, source), _))) =// Is dependent
        tuple((
            tag("("),
            parse_binding,
            tag(")"),
        ))(i)
    {
        let (res, (_, target)) =
            tuple((
                tag("->"),
                context("function range", cut(parse_reducible)),
            ))(res)?;

        Ok((res, Type::Func(
            Box::new(source.clone()),
            Open {
                bound: { let mut tmp = HashMap::new(); tmp.insert(bound, source); tmp },
                body: Box::new(target),
            }
        )))

    } else {// Isn't dependent
        map(
            tuple((
                context("function domain", cut(parse_atomic)),
                tag("->"),
                context("function range", cut(parse_reducible)),
            )),
            |(source, _, target)| Type::Func(Box::new(source), Open{ bound: HashMap::new(), body: Box::new(target) }),
        )(i)
    }
}

//            TODO: Support general patterns.
//                                          ↓
fn parse_binding(i: &str) -> IResult<&str, (String, Reducible), VerboseError<&str>> {
    map(
        tuple((
            alpha1,
            tag(":"),
            parse_reducible,
        )),

        |(ident, _, ty): (&str, &str, Reducible)| (ident.to_string(), ty)
    )(i)
}

fn parse_type(i: &str) -> IResult<&str, Type, VerboseError<&str>> {
    unimplemented!()
}

fn parse_atomic(i: &str) -> IResult<&str, Reducible, VerboseError<&str>> {
    unimplemented!()
}

fn parse_reducible(i: &str) -> IResult<&str, Reducible, VerboseError<&str>> {
    unimplemented!()
}