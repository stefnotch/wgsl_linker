use std::collections::{HashMap, HashSet};

use slotmap::{new_key_type, SecondaryMap, SlotMap};
use thiserror::Error;

use crate::{
    parse,
    parser_output::Ast,
    rewriter::{Rewriter, Visitor},
    WgslParseError,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ModulePath(pub Vec<String>);

#[derive(Default)]
pub struct Linker {
    pub module_names: SlotMap<ModuleKey, ModulePath>,
    pub modules: SecondaryMap<ModuleKey, ParsedModule>,
}

new_key_type! {
    /// A key for a module in the linker.
    pub struct ModuleKey;
}

pub enum GlobalItem {
    Private,
    Exported,
}

pub struct ParsedModule {
    pub source: String,
    pub ast: Ast,
    pub global_items: HashMap<String, GlobalItem>,
    pub imports: HashMap<String, (ModuleKey, String)>,
}

#[derive(Error, Debug)]
pub enum LinkingError {
    #[error("the imported item {variable} was redefined")]
    Redefinition { variable: String },
    #[error("multiple errors occurred {0:?}")]
    Aggregate(Vec<LinkingError>),
}

// To generate a linked module, we need
// - Module
// - Imports:
//   Name: Refers to (other module, item)
// We then generate new code with mangled names.
// We also strip the import and export statements in this step.
// The code isn't usable by itself.

// And to generate the final module, we join all the modules together.

pub struct UnmangledName<'a> {
    pub module: ModuleKey,
    pub name: &'a str,
}

impl Linker {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_module_source(
        &mut self,
        name: ModulePath,
        source: String,
    ) -> Result<ModuleKey, WgslParseError> {
        let module_key = self.module_names.insert(name);
        let ast = parse(&source)?;
        let global_items = ast.get_global_items(&source);
        let imports = HashMap::new(); // TODO: ast.get_imports(&source);
        self.modules.insert(
            module_key,
            ParsedModule {
                source,
                ast,
                global_items,
                imports,
            },
        );
        Ok(module_key)
    }

    fn module_name_for_mangling(&self, module: ModuleKey) -> String {
        self.module_names[module].0.join("_")
    }

    pub fn mangle_name(&self, module: ModuleKey, name: &str) -> String {
        format!("{}_{}", self.module_name_for_mangling(module), name)
    }
    pub fn unmangle_name<'a>(&self, module: ModuleKey, mangled_name: &'a str) -> UnmangledName<'a> {
        let module_name = self.module_name_for_mangling(module);
        assert!(mangled_name.starts_with(&module_name));
        let name = &mangled_name[module_name.len() + "_".len()..];
        UnmangledName { module, name }
    }

    pub fn compile_module(&self, module: ModuleKey) -> Result<String, LinkingError> {
        let parsed_module = &self.modules[module];
        let mut visitor = LinkerVisitor::new(self, module);
        let result = parsed_module
            .ast
            .rewrite(&parsed_module.source, &mut visitor);
        if visitor.errors.is_empty() {
            Ok(result)
        } else {
            Err(LinkingError::Aggregate(visitor.errors))
        }
    }
}

struct LinkerVisitor<'a> {
    linker: &'a Linker,
    module_key: ModuleKey,
    imports: &'a HashMap<String, (ModuleKey, String)>,
    global_items: &'a HashMap<String, GlobalItem>,
    /// Keeps track of function scopes. Ignores the top-level scope.
    scoped_items: Vec<HashSet<&'a str>>,
    errors: Vec<LinkingError>,
}

impl<'a> LinkerVisitor<'a> {
    fn new(linker: &'a Linker, module_key: ModuleKey) -> Self {
        let module = linker.modules.get(module_key).unwrap();
        let imports = &module.imports;
        let global_items = &module.global_items;
        Self {
            linker,
            module_key,
            imports,
            global_items,
            scoped_items: Default::default(),
            errors: Default::default(),
        }
    }

    pub fn is_local(&self, variable: &'a str) -> bool {
        self.scoped_items
            .iter()
            .any(|scope| scope.contains(variable))
    }
}

impl<'a> Rewriter<'a> for LinkerVisitor<'a> {
    fn open_block(&mut self) {
        self.scoped_items.push(HashSet::new());
    }

    fn close_block(&mut self) {
        self.scoped_items.pop();
    }

    fn declare(&mut self, variable: &'a str) -> Option<String> {
        if let Some(local_scope) = self.scoped_items.last_mut() {
            // Variables in inner scopes can shadow outer variables.
            local_scope.insert(variable);
            None
        } else {
            // Global scope!
            if self.imports.contains_key(variable) {
                self.errors.push(LinkingError::Redefinition {
                    variable: variable.to_string(),
                });
            }
            Some(self.linker.mangle_name(self.module_key, variable))
        }
    }

    fn use_variable(&mut self, variable: &'a str) -> Option<String> {
        if self.is_local(variable) {
            // Keep local variable names
            None
        } else if let Some((module, name)) = self.imports.get(variable) {
            // Replace imports
            // Notice how this also handles "import cat as dog" renames
            Some(self.linker.mangle_name(*module, name))
        } else if self.global_items.contains_key(variable) {
            // Mangle all globals
            Some(self.linker.mangle_name(self.module_key, variable))
        } else {
            // It must be a predeclared item. Don't bother mangling them.
            None
        }
    }
}

impl Ast {
    pub fn get_global_items<'a>(&self, source: &'a str) -> HashMap<String, GlobalItem> {
        let mut visitor = GlobalItemsVisitor::default();
        self.visit(source, &mut visitor);
        visitor.items
    }
}

#[derive(Default)]
struct GlobalItemsVisitor {
    items: HashMap<String, GlobalItem>,
    block_level: usize,
}

impl<'a> Visitor<'a> for GlobalItemsVisitor {
    fn open_block(&mut self) {
        self.block_level += 1;
    }

    fn close_block(&mut self) {
        self.block_level -= 1;
    }

    fn declare(&mut self, variable: &'a str) {
        if self.block_level == 0 {
            self.items
                .insert(variable.to_string(), GlobalItem::Exported);
        }
    }

    fn use_variable(&mut self, _variable: &str) {}
}
