use std::collections::HashSet;
use std::hash::Hash;

pub trait Seq<T> {
    fn to_vec(self) -> Vec<T>;
    fn to_set(self) -> HashSet<T>
    where
        T: Hash + Eq;
}

impl<Collection, T> Seq<T> for Collection
where
    Collection: IntoIterator<Item = T>,
{
    fn to_vec(self) -> Vec<T> {
        self.into_iter().collect()
    }

    fn to_set(self) -> HashSet<T>
    where
        T: Hash + Eq,
    {
        self.into_iter().collect()
    }
}
