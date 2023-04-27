use aries::utils::input::{ErrLoc, Sym};
use std::borrow::Borrow;
use std::fmt::{Debug, Display, Formatter};
use std::sync::Arc;

#[derive(Clone)]
pub struct UserType {
    name: Sym,
    parent: SymbolicType,
}

impl Display for UserType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl Debug for UserType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}: {})", self.name, self.parent)
    }
}

impl UserType {
    pub fn new(name: impl Into<Sym>) -> Self {
        Self::new_with_parent(name, SymbolicType::Any)
    }

    pub fn new_with_parent(name: impl Into<Sym>, parent: SymbolicType) -> Self {
        UserType {
            name: name.into(),
            parent,
        }
    }
}

#[derive(Debug, Clone)]
pub enum SymbolicType {
    Any,
    User(Arc<UserType>),
}

impl Display for SymbolicType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            SymbolicType::Any => {
                write!(f, "<any>")
            }
            SymbolicType::User(u) => {
                write!(f, "{u}")
            }
        }
    }
}

impl From<UserType> for SymbolicType {
    fn from(value: UserType) -> Self {
        SymbolicType::User(Arc::new(value))
    }
}

#[derive(Debug, Clone)]
pub enum Type {
    Bool,
    Symbolic(SymbolicType),
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Bool => {
                write!(f, "<bool>")
            }
            Type::Symbolic(s) => {
                write!(f, "{s}")
            }
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct Types {
    types: Vec<Arc<UserType>>,
}

impl Types {}

impl Types {
    pub(crate) fn is_empty(&self) -> bool {
        self.types.is_empty()
    }
    pub(crate) fn as_slice(&self) -> &[Arc<UserType>] {
        &self.types
    }

    pub fn add_user_type(&mut self, tpe: UserType) {
        assert!(self.types.iter().all(|prev| prev.name != tpe.name));
        self.types.push(Arc::new(tpe))
    }

    pub fn get_type(&self, name: &Sym) -> Option<Arc<UserType>> {
        self.types.iter().find(|tpe| &tpe.name == name).cloned()
    }

    pub fn has_type(&self, name: &Sym) -> bool {
        self.get_type(name).is_some()
    }
}

#[derive(Clone)]
pub struct Instance {
    pub name: Sym,
    pub tpe: SymbolicType,
}

impl Instance {
    pub fn new(name: impl Into<Sym>, tpe: SymbolicType) -> Self {
        Self { name: name.into(), tpe }
    }
}
impl Display for Instance {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl Debug for Instance {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.name, self.tpe)
    }
}

#[derive(Debug, Default, Clone)]
pub struct Instances {
    instances: Vec<Instance>,
}

impl Instances {
    pub fn get(&self, name: impl Borrow<str>) -> Option<&Instance> {
        let name: &str = name.borrow();
        self.instances.iter().find(|i| i.name.canonical_str() == name)
    }

    pub fn add_instance(&mut self, instance: Instance) -> Result<(), ErrLoc> {
        if let Some(prev) = self.get(&instance.name) {
            return instance
                .name
                .invalid("Instance already defined.")
                .with_hint(&prev.name.loc(), "Previous definition")
                .failed();
        }
        self.instances.push(instance);
        Ok(())
    }

    pub fn is_empty(&self) -> bool {
        self.instances.is_empty()
    }
}
