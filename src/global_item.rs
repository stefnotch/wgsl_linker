use std::ops::Range;

pub struct GlobalItem(pub Range<usize>);

#[derive(Default)]
pub struct GlobalItems {
    pub items: Vec<GlobalItem>,
}

impl GlobalItems {
    pub fn single(item: GlobalItem) -> Self {
        Self { items: vec![item] }
    }
    pub fn join(mut self, other: impl Into<GlobalItems>) -> GlobalItems {
        self.items.append(&mut other.into().items);
        GlobalItems { items: self.items }
    }
}

impl From<Option<GlobalItems>> for GlobalItems {
    fn from(value: Option<GlobalItems>) -> Self {
        value.unwrap_or_default()
    }
}

impl FromIterator<GlobalItem> for GlobalItems {
    fn from_iter<T: IntoIterator<Item = GlobalItem>>(iter: T) -> Self {
        Self {
            items: iter.into_iter().collect(),
        }
    }
}

impl FromIterator<GlobalItems> for GlobalItems {
    fn from_iter<T: IntoIterator<Item = GlobalItems>>(iter: T) -> Self {
        iter.into_iter()
            .fold(GlobalItems::default(), |acc, x| acc.join(x))
    }
}
