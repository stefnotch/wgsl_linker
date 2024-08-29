use std::{borrow::Borrow, collections::HashMap};

use indexmap::IndexMap;

use crate::parser::Ast;

/// A path to a module, either relative to the current module or absolute.
/// Relative paths start with "." or "..", absolute paths do not.
/// "." and ".." may only appear at the beginning of the path.
#[derive(Debug)]
pub enum ImportPath {
    Relative {
        parent_count: u32,
        path: Vec<String>,
    },
    Absolute(ModulePath),
}
impl ImportPath {
    pub fn new_relative(parent_count: u32, slice: &[&str]) -> Self {
        assert!(!slice.is_empty());
        Self::Relative {
            parent_count,
            path: slice.iter().map(|s| s.to_string()).collect(),
        }
    }

    pub fn new_absolute(slice: &[&str]) -> Self {
        Self::Absolute(ModulePath::from_slice(slice))
    }

    pub fn resolve<'a>(&'a self, base: &ModulePath) -> ModulePath {
        match self {
            ImportPath::Relative { parent_count, path } => {
                // -1, because the last element is the name of the module itself
                let base_path_skip = (base.path.len() - 1)
                    .checked_sub(*parent_count as usize)
                    .expect("Escaped root directory");
                let path = base.path[0..base_path_skip]
                    .iter()
                    .chain(path.iter())
                    .cloned()
                    .collect();
                ModulePath { path }
            }
            ImportPath::Absolute(v) => v.clone(),
        }
    }
}

/// A fully resolved path to a module.
/// Can refer to a file outside of the root directory.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ModulePath {
    pub path: Vec<String>,
}

impl ModulePath {
    pub fn from_slice(slice: &[&str]) -> Self {
        assert!(!slice.is_empty());
        Self {
            path: slice.iter().map(|s| s.to_string()).collect(),
        }
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

/// A reference to items in a module.
pub enum ImportedItem {
    Item { path: ImportPath, name: ItemName },
    AllItems(ImportPath),
}
impl ImportedItem {
    pub fn path<'a>(&'a self) -> &ImportPath {
        match self {
            ImportedItem::Item { path, .. } => path,
            ImportedItem::AllItems(path) => path,
        }
    }

    pub fn resolve<'a>(&'a self, base: &ModulePath) -> ModuleItem {
        match self {
            ImportedItem::Item { path, name } => ModuleItem::Item {
                module_path: path.resolve(base),
                name: name.clone(),
            },
            ImportedItem::AllItems(path) => ModuleItem::AllItems(path.resolve(base)),
        }
    }
}

/// A reference to items in a module.
pub enum ModuleItem {
    Item {
        module_path: ModulePath,
        name: ItemName,
    },
    AllItems(ModulePath),
}
impl ModuleItem {
    pub fn module_path<'a>(&'a self) -> &ModulePath {
        match self {
            ModuleItem::Item { module_path, .. } => module_path,
            ModuleItem::AllItems(module_path) => module_path,
        }
    }
}

pub enum GlobalItem {
    Private,
    Exported,
}

pub struct ParsedModule {
    pub source: String,
    pub ast: Ast,
    pub global_items: HashMap<ItemName, GlobalItem>,
    pub imports: IndexMap<ItemName, ImportedItem>,
}
