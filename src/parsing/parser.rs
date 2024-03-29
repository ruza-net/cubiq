use std::collections::{ VecDeque, HashMap };

use nom:: {
    branch::alt,

    bytes::complete::{ tag, take_while },
    character::complete::{ space0, space1, digit1 },

    combinator::{ cut, map, map_res, verify },
    sequence::{ preceded, tuple },

    error::{ context, VerboseError },
    IResult,
};

use crate::ast::*;


#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
enum ProjKind {
    Fst,
    Snd,
}

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
    alt((
        map_res(
            preceded(preceded(space0, tag("type")), preceded(space1, atomic![digit1])),
            |num: &str| num.parse().map(Type::Universe)
        ),
        map(
            atomic![tag("type")],
            |_| Type::Universe(0),
        ),
    ))(i)
}

fn parse_eq(i: &str) -> IResult<&str, Type, VerboseError<&str>> {
    map(
        tuple((
            parse_atomic_term,
            preceded(preceded(atomic![tag("=")], atomic![tag("(")]), parse_maybe_type),
            preceded(tag(")"), parse_atomic_term),
        )),
        |(x, ty, y)| Type::Eq(Box::new(ty), Box::new(x), Box::new(y)),
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
        parse_sgl_term,
        enclosed![
            alt((
                parse_lambda,
                into![parse_opaque],
            ))
        ],
    ))(i)?;

    // ANCHOR: The argument
    //
    let (res, arg) = alt((
        enclosed![parse_term],
        into![parse_sgl_term],
        into![parse_universe],
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
        parse_eq,
        parse_universe,
    ))(i)
}

// Without enclosion
//
fn _parse_opaque(i: &str) -> IResult<&str, Opaque, VerboseError<&str>> {
    alt((
        parse_call,
        parse_proj,
        into![parse_ident],
    ))(i)
}

fn _parse_opaque_tm(i: &str) -> IResult<&str, MaybeTerm, VerboseError<&str>> {
    alt((
        into![parse_call],
        parse_sgl_term,
    ))(i)
}

fn parse_ap(i: &str) -> IResult<&str, MaybeTerm, VerboseError<&str>> {
    map(
        tuple((
            parse_sgl_ty,
            tag("::"),
            atomic![tag("ap")],
            tag("["),
            parse_ident,
            tag("=>"),
            parse_term,
            atomic![tag("]")],
        )),
        |(out_ty, _, _, _, var, _, body, _)|
            MaybeTerm::PathAction {
                var: var.to_string(),
                action: Box::new(Open {
                    bound: { let mut tmp = HashMap::new(); tmp.insert(var.to_string(), out_ty.clone()); tmp },
                    body,
                }),
                out_ty: Box::new(out_ty),
            },
    )(i)
}

fn parse_refl(i: &str) -> IResult<&str, Opaque, VerboseError<&str>> {
    preceded(
        atomic![tag("refl")],
        map(
            tuple((
                tag("["),
                parse_maybe_term,
                atomic![tag("]")],
            )),
            |(_, x, _)| Opaque::Refl(Box::new(x)),
        )
    )(i)
}

fn parse_stretch(i: &str) -> IResult<&str, MaybeTerm, VerboseError<&str>> {
    map(
        tuple((
            parse_sgl_ty,
            tag("::"),
            atomic![tag("stretch")],
        )),
        |(ty, _, _)| MaybeTerm::ReflStretch(Box::new(ty)),
    )(i)
}

fn parse_induction(i: &str) -> IResult<&str, MaybeTerm, VerboseError<&str>> {
    map(
        tuple((
            parse_sgl_ty,
            tag("::"),
            atomic![tag("ind")],
        )),
        |(ty, _, _)| MaybeTerm::Induction(Box::new(ty)),
    )(i)
}

fn parse_proj_tele(i: &str) -> IResult<&str, VecDeque<ProjKind>, VerboseError<&str>> {
    let (mut res, kind) = map(
        alt((
            atomic![tag(".1")],
            atomic![tag(".2")],
        )),
        |t| if t == ".1" { ProjKind::Fst } else { ProjKind::Snd },
    )(i)?;

    let mut tele = VecDeque::new();
    tele.push_back(kind);

    loop {
        if let Ok((new_res, kind)) = map::<_, _, _, VerboseError<_>, _, _>(
            alt((
                atomic![tag(".1")],
                atomic![tag(".2")],
            )),
            |t| if t == ".1" { ProjKind::Fst } else { ProjKind::Snd },
        )(res) {
            res = new_res;
            tele.push_back(kind);

        } else {
            break;
        }
    }

    Ok((res, tele))
}

fn parse_proj(i: &str) -> IResult<&str, Opaque, VerboseError<&str>> {
    map(
        tuple((
            alt((
                parse_refl,
                into![parse_ident],
                enclosed![parse_opaque],
            )),
            parse_proj_tele,
        )),
        |(x, mut tele)| {
            let mut ret =
                if let ProjKind::Fst = tele.pop_front().unwrap() {
                    Opaque::Proj1(Box::new(x))
                } else {
                    Opaque::Proj2(Box::new(x))
                };

            for kind in tele {
                if let ProjKind::Fst = kind {
                    ret = Opaque::Proj1(Box::new(ret));
                } else {
                    ret = Opaque::Proj2(Box::new(ret));
                }
            }

            ret
        },
    )(i)
}

fn parse_sgl_ty(i: &str) -> IResult<&str, MaybeType, VerboseError<&str>> {
    alt((
        into![parse_universe],
        into![parse_ident],
        enclosed![parse_atomic_ty],
    ))(i)
}

fn parse_sgl_term(i: &str) -> IResult<&str, MaybeTerm, VerboseError<&str>> {
    alt((
        parse_ap,
        into![parse_refl],
        parse_stretch,
        parse_induction,
        into![parse_proj],
        into![parse_ident],
    ))(i)
}

fn parse_atomic_term(i: &str) -> IResult<&str, Term, VerboseError<&str>> {
    alt((
        into![_parse_opaque],
        into![parse_universe],
        enclosed![parse_term],
    ))(i)
}

fn parse_maybe_term(i: &str) -> IResult<&str, MaybeTerm, VerboseError<&str>> {
    alt((
        parse_lambda,
        into![_parse_opaque_tm],
        enclosed![parse_maybe_term],
    ))(i)
}

/// Parses a term expression: a type, opaque expression or lambda expression.
///
pub fn parse_term(i: &str) -> IResult<&str, Term, VerboseError<&str>> {
    alt((
        into![parse_lambda],
        into![_parse_opaque_tm],
        into![_parse_type],
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
