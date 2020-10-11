extern crate nom;

#[macro_use] mod utils;
mod checker;
mod parsing;

pub use parsing::ast;
pub use checker::context;


macro_rules! assert_parse {
    ( $via:ident ( $text:expr ) => $expected:expr ) => {
        assert_eq![
            ("", $expected),
            $via ( $text ).expect("couldn't parse"),
            "`{}` didn't parse",
            $text,
        ]
    };
}

#[cfg(test)]
mod term_parse_tests {
    use super::parsing::parser::*;
    use super::ast::*;

    #[test]
    fn identifiers() {
        let idents = ["foo", "ĎáblóŇ", "你好"];

        for ident in &idents {
            assert_parse![
                parse_opaque(ident) => Opaque::Var(ident.to_string())
            ];
        }
    }

    #[test]
    fn call_simple() {
        let ast =
            Opaque::Call(
                Box::new("a".into()),
                Box::new("b".into()),
            );

        assert_parse![ parse_opaque("a b") => ast ];
    }

    #[test]
    fn call_complex() {
        let ast =
            Opaque::Call(
                Box::new(Opaque::Call(
                    Box::new("a".into()),
                    Box::new(Term::Opaque(Opaque::Call(
                        Box::new("b".into()),
                        Box::new("c".into()),
                    ))),
                ).into()),
                Box::new(Opaque::Call(
                    Box::new(Opaque::Call(
                        Box::new("d".into()),
                        Box::new("e".into()),
                    ).into()),
                    Box::new("f".into()),
                ).into()),
            );

        assert_parse![ parse_opaque("(a (b c)) ((d e) f)") => ast ];
    }

    #[test]
    fn lambda_simple() {
        let ast =
            Term::Lambda(
                "x".to_string(),
                Box::new(Term::Opaque(
                    Opaque::Call(
                        Box::new("x".into()),
                        Box::new("x".into()),
                    )
                )),
            );

        assert_parse![ parse_term("x => x x") => ast ];
    }

    #[test]
    fn lambda_complex() {
        let ast =
            Term::Lambda(
                "x".to_string(),
                Box::new(Term::Lambda(
                    "y".to_string(),
                    Box::new(Term::Lambda(
                        "z".to_string(),
                        Box::new(
                            Opaque::Call(
                                Box::new(MaybeTerm::Lambda(
                                    "q".to_string(),
                                    Box::new(
                                        Opaque::Call(
                                            Box::new("q".into()),
                                            Box::new("z".into()),
                                        ).into()
                                    ),
                                )),
                                Box::new("y".into()),
                            ).into()
                        ),
                    )),
                )),
            );

        assert_parse![ parse_term("x => y => z => (q => q z) y") => ast ];
    }

    #[test]
    fn refl() {
        let ast =
            Term::Refl(
                Box::new(Opaque::Call(
                    Box::new("a".into()),
                    Box::new("b".into()),
                ).into())
            );

        assert_parse! { parse_term("refl   [ a  b]  ") => ast }
    }

    #[test]
    fn ap() {
        let ast =
            Term::PathAction {
                var: "x".to_string(),
                out_ty: Box::new(Type::Universe(1).into()),
                action: Box::new(Open {
                    bound: map!{ "x".to_string() => Type::Universe(1).into() },
                    body: "x".into(),
                }),
            };

        assert_parse! { parse_term("type 1::ap[x => x]") => ast }
    }

    #[test]
    fn stretch() {
        let ast =
            Opaque::Call(
                Box::new(MaybeTerm::ReflStretch(Box::new(Type::Universe(0).into()))),
                Box::new("P".into()),
            ).into();

        assert_parse! { parse_term("type::stretch P") => ast }
    }

    #[test]
    fn induction() {
        let ast =
            Term::Induction(Box::new("N".into()));

        assert_parse! { parse_term("N::ind") => ast }
    }

    #[test]
    fn ind_complex() {
        let ast =
            Opaque::Call(
                Box::new(MaybeTerm::Induction(Box::new("N".into()))),
                Box::new(Type::Universe(0).into()),
            ).into();

        assert_parse! { parse_term("N::ind type") => ast }
    }

    #[test]
    fn stretch_complex() {
        let ast =
            Opaque::Call(
                Box::new(MaybeTerm::ReflStretch(Box::new(Opaque::Call(
                    Box::new("a".into()),
                    Box::new("b".into()),
                ).into()))),
                Box::new("x".into()),
            ).into();

        assert_parse! { parse_term("(a b)::stretch x") => ast }
    }
}

#[cfg(test)]
mod type_parse_tests {
    use super::parsing::parser::*;
    use super::ast::*;

    use std::collections::HashMap;

    #[test]
    fn universe() {
        assert_parse![ parse_type("type 42") => Type::Universe(42) ];
    }

    #[test]
    fn func_simple() {
        let ast =
            Type::Func(
                None,
                Box::new(Type::Universe(1).into()),
                Box::new(MaybeType::from(Type::Universe(0)).into()),
            );

        assert_parse![ parse_type("type 1 -> type") => ast ];
    }

    #[test]
    fn func_complex() {
        let ast =
            Type::Func(
                None,
                Box::new(Type::Func(
                    None,
                    Box::new(Type::Universe(1).into()),
                    Box::new(MaybeType::from(Type::Universe(123)).into()),
                ).into()),
                Box::new(MaybeType::from(Type::Func(
                    None,
                    Box::new(Type::Universe(321).into()),
                    Box::new(MaybeType::from(Type::Universe(0)).into()),
                )).into()),
            );

        assert_parse![ parse_type("(type 1 -> type 123) -> type 321 -> type") => ast ];
    }

    #[test]
    fn bindings() {
        let ast =
            Type::Pair(
                Some("x".to_string()),
                Box::new(Type::Universe(1).into()),
                Box::new(Open {
                    bound: {
                        let mut tmp = HashMap::new();
                        tmp.insert("x".to_string(), Type::Universe(1).into());
                        tmp
                    },
                    body: MaybeType::from(Type::Universe(0))
                }),
            );

        assert_parse![ parse_type("(x: type 1) # type") => ast ];
    }

    #[test]
    fn eq() {
        let ast = Type::Eq(
            Box::new(Type::Universe(43).into()),
            Box::new(Type::Universe(42).into()),
            Box::new(Type::Universe(1).into()),
        );

        assert_parse! { parse_type("type 42   =(  type43 )type 1") => ast }
    }
}

#[cfg(test)]
mod misc_parse_tests {
    use super::parsing::parser::*;
    use super::ast::*;

    #[test]
    #[ignore]// It's slow
    fn parentheses() {
        let opaque_ast =
            Opaque::Call(
                Box::new("a".into()),
                Box::new("b".into()),
            );

        assert_parse![ parse_opaque("(((a b)))") => opaque_ast ];


        let ty_ast = Type::Universe(42);

        assert_parse![ parse_type("(((((type 42)))))") => ty_ast ];


        let term_ast =
            Term::Lambda(
                "x".to_string(),
                Box::new(Opaque::Call(
                    Box::new("b".into()),
                    Box::new("x".into()),
                ).into()),
            );

        assert_parse![ parse_term("(((x  =>  (((b ((x))))))))") => term_ast ];
    }
}


#[cfg(test)]
mod subst_tests {
    use super::ast::*;

    macro_rules! subst_test {
        ( ( $src:expr )[ $($old:ident := $new:expr),* ] as $kind:ident ) => {
            let mut old_ast: $kind = format![$src, $($old = stringify![$old]),*].into_ast().unwrap();

            let subst_str = format![$src, $($old = $new),*];

            let new_ast: $kind = subst_str.into_ast().unwrap();
            $(
                let subst_item: $kind = $new.into_ast().unwrap();

                old_ast = old_ast.subst(stringify![$old], subst_item).expect("couldn't substitute");
            )*

            assert_eq![
                new_ast,
                old_ast,
                "invalid substitution",
            ];
        };
    }

    // Types
    //
    #[test]
    fn func_pair_subst() {
        subst_test! { ("type 1 -> type # a {b}")[b := "type 42"] as Type }
    }

    #[test]
    fn eq_subst() {
        subst_test! { ("{x} =(type 43) {y}")[x := "type 42", y := "type 3"] as Type }
    }

    // Terms
    //
    #[test]
    fn lambda_subst() {
        subst_test! { ("x => x {y}")[y := "type 42"] as Term }
    }

    #[test]
    fn lambda_non_subst() {
        subst_test! { ("(x => x x) {x}")[x := "type 42"] as Term }
    }

    #[test]
    fn call_subst() {
        subst_test! { ("{x} {x}")[x := "(x => (x x) x)"] as Term }
    }
}
