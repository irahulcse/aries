use std::sync::Arc;

pub struct Fluent {
    name: S<String>,
    value: S<Type>,
    parameters: Vec<S<Type>>,
    definition: Source,
}
pub enum Function {
    Plus,
    Minus,
}

pub enum Literal {}

pub struct StateVariable {
    fluent_name: String,
}

pub enum Expr {
    Constant(S<Literal>),
    Sv(S<Fluent>, Vec<S<Expr>>),
    App(S<Function>, Vec<S<Expr>>),
}

#[cfg(test)]
mod test {
    use crate::{Source, UserType};

    #[test]
    fn test_base() {
        let a = UserType::new("a", Source::none());
        let b = UserType::new_with_parent("b", a, Source::none());
    }
}
