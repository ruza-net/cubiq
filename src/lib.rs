extern crate nom;

mod ast;
mod parse;
mod checker;

pub use ast::syntax;
pub use checker::context;


#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}