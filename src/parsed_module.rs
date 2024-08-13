use std::{borrow::Borrow, collections::HashMap};

use indexmap::IndexMap;

use crate::{linker::ModuleKey, parser_output::Ast};

/// The name of an item in a module. Always a single string.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ItemName(pub String);

impl Borrow<str> for ItemName {
    fn borrow(&self) -> &str {
        &self.0
    }
}

/// A reference to an item in a module.
/// In source code, it is written as `module_name::item_name`.
pub struct ModuleItem {
    pub module: ModuleKey,
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
