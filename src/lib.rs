extern crate nom;

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
                Box::new(Term::Opaque(Opaque::Var("a".to_string()))),
                Box::new(Term::Opaque(Opaque::Var("b".to_string()))),
            );

        assert_parse![ parse_opaque("a b") => ast ];
    }

    #[test]
    fn call_complex() {
        let ast =
            Opaque::Call(
                Box::new(Term::Opaque(Opaque::Call(
                    Box::new(Term::Opaque(Opaque::Var("a".to_string()))),
                    Box::new(Term::Opaque(Opaque::Call(
                        Box::new(Term::Opaque(Opaque::Var("b".to_string()))),
                        Box::new(Term::Opaque(Opaque::Var("c".to_string()))),
                    ))),
                ))),
                Box::new(Term::Opaque(Opaque::Call(
                    Box::new(Term::Opaque(Opaque::Call(
                        Box::new(Term::Opaque(Opaque::Var("d".to_string()))),
                        Box::new(Term::Opaque(Opaque::Var("e".to_string()))),
                    ))),
                    Box::new(Term::Opaque(Opaque::Var("f".to_string()))),
                ))),
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
                        Box::new(Term::Opaque(Opaque::Var("x".to_string()))),
                        Box::new(Term::Opaque(Opaque::Var("x".to_string()))),
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
                        Box::new(Term::Opaque(
                            Opaque::Call(
                                Box::new(Term::Lambda(
                                    "q".to_string(),
                                    Box::new(Term::Opaque(
                                        Opaque::Call(
                                            Box::new(Term::Opaque(Opaque::Var("q".to_string()))),
                                            Box::new(Term::Opaque(Opaque::Var("z".to_string()))),
                                        )
                                    )),
                                )),
                                Box::new(Term::Opaque(Opaque::Var("y".to_string()))),
                            )
                        )),
                    )),
                )),
            );

        assert_parse![ parse_term("x => y => z => (q => q z) y") => ast ];
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
                Box::new(Type::Universe(1).into()),
                Box::new(MaybeType::from(Type::Universe(0))).into(),
            );

        assert_parse![ parse_type("type 1 -> type") => ast ];
    }

    #[test]
    fn func_complex() {
        let ast =
            Type::Func(
                Box::new(Type::Func(
                    Box::new(Type::Universe(1).into()),
                    Box::new(MaybeType::from(Type::Universe(123))).into(),
                ).into()),
                Box::new(MaybeType::from(Type::Func(
                    Box::new(Type::Universe(321).into()),
                    Box::new(MaybeType::from(Type::Universe(0))).into(),
                ))).into(),
            );

        assert_parse![ parse_type("(type 1 -> type 123) -> type 321 -> type") => ast ];
    }

    #[test]
    fn bindings() {
        let ast =
            Type::Pair(
                Box::new(Type::Universe(1).into()),
                Open {
                    bound: {
                        let mut tmp = HashMap::new();
                        tmp.insert("x".to_string(), Type::Universe(1).into());
                        tmp
                    },
                    body: Box::new(MaybeType::from(Type::Universe(0)))
                },
            );

        assert_parse![ parse_type("(x: type 1) # type") => ast ];
    }
}

#[cfg(test)]
mod misc_parse_tests {
    use super::parsing::parser::*;
    use super::ast::*;

    #[test]
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
