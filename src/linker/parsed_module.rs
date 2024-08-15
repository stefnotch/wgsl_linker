use std::{borrow::Borrow, collections::HashMap};

use indexmap::IndexMap;

use crate::parser::Ast;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ModulePath(pub Vec<String>);
impl ModulePath {
    pub fn from_slice(slice: &[&str]) -> Self {
        Self(slice.iter().map(|s| s.to_string()).collect())
    }
}

/// The name of an item in a module. Always a single string.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ItemName(pub String);
impl ItemName {
    pub fn new<S: Into<String>>(name: S) -> Self {
        Self(name.into())
    }
}

impl Borrow<str> for ItemName {
    fn borrow(&self) -> &str {
        &self.0
    }
}

/// A reference to an item in a module.
pub struct ModuleItem {
    pub module_path: ModulePath,
    pub name: ItemName,
}

pub enum GlobalItem {
    Private,
    Exported,
}

pub struct ParsedModule {
    pub source: String,
    pub ast: Ast,
    pub global_items: HashMap<ItemName, GlobalItem>,
    pub imports: IndexMap<ItemName, ModuleItem>,
}
