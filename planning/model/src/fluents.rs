use crate::source::{Source, S};
use crate::types::Type;
use aries::utils::input::{ErrLoc, Sym};
use itertools::Itertools;
use std::fmt::{Debug, Display, Formatter};
use std::sync::Arc;

#[derive(Clone)]
pub struct Param {
    pub name: Sym,
    pub tpe: Type,
}

impl Param {
    pub fn new(name: impl Into<Sym>, tpe: impl Into<Type>) -> Self {
        Param {
            name: name.into(),
            tpe: tpe.into(),
        }
    }
}

impl Display for Param {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl Debug for Param {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.name, self.tpe)
    }
}

#[derive(Clone)]
pub struct Fluent {
    name: Sym,
    params: Vec<Param>,
    return_type: S<Type>,
    definition: Source,
}

impl Fluent {
    pub fn new(
        name: impl Into<Sym>,
        params: Vec<Param>,
        return_type: impl Into<S<Type>>,
        definition: impl Into<Source>,
    ) -> Self {
        Fluent {
            name: name.into(),
            params,
            return_type: return_type.into(),
            definition: definition.into(),
        }
    }
}

impl Display for Fluent {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl Debug for Fluent {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}(", self.name)?;
        write!(f, "{:?}", self.params.iter().format(", "))?;
        write!(f, "): {}", self.return_type)
    }
}

#[derive(Debug, Clone, Default)]
pub struct Fluents {
    fluents: Vec<Arc<Fluent>>,
}

impl Fluents {
    pub fn add_fluent(&mut self, f: Fluent) -> Result<(), ErrLoc> {
        if let Some(prev) = self.fluents.iter().find(|prev| prev.name == f.name) {
            return f
                .name
                .invalid("Fluent already defined")
                .with_hint(prev.definition.loc(), "Previous definition was here")
                .failed();
        }
        self.fluents.push(Arc::new(f));
        Ok(())
    }
    pub(crate) fn iter(&self) -> impl Iterator<Item = &Fluent> {
        self.fluents.iter().map(|f| f.as_ref())
    }
}
