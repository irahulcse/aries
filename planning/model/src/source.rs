use aries::utils::input::Loc;
use std::fmt::{Debug, Display, Formatter};
use std::sync::Arc;

#[derive(Debug, Clone)]
pub struct Source {
    loc: Option<Loc>,
}

impl Source {
    pub fn none() -> Self {
        Source { loc: None }
    }

    pub fn loc(&self) -> &Loc {
        self.loc.as_ref().unwrap()
    }
}

impl From<Loc> for Source {
    fn from(value: Loc) -> Self {
        Source { loc: Some(value) }
    }
}
impl From<&Loc> for Source {
    fn from(value: &Loc) -> Self {
        Source {
            loc: Some(value.clone()),
        }
    }
}

#[derive(Clone)]
pub struct Annotated<E> {
    data: Arc<E>,
    source: Source,
}

pub(crate) type S<E> = Annotated<E>;

impl<E: Debug> Debug for Annotated<E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.data)
    }
}

impl<E: Display> Display for Annotated<E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.data)
    }
}

pub trait Annotable<E> {
    fn annotate(self) -> Annotated<E>;
}

impl<E, E2: Into<E>> Annotable<E> for E2 {
    fn annotate(self: E2) -> Annotated<E> {
        Annotated {
            data: Arc::new(self.into()),
            source: Source::none(),
        }
    }
}
