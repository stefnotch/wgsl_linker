mod mangling;
mod parsed_module;

use std::collections::{HashMap, HashSet};

use indexmap::IndexMap;
use slotmap::{new_key_type, SecondaryMap, SlotMap};
use thiserror::Error;

use crate::parser::{parse, Ast, WgslParseError};
use crate::parser::{Rewriter, Visitor};
pub use mangling::{mangle_name, unmangle_name, write_mangled_name};
use parsed_module::{GlobalItem, ParsedModule};
pub use parsed_module::{ItemName, ModuleItem, ModulePath};

/// Links multiple modules together into a single module.
/// Main entry point of the library.
#[derive(Default)]
pub struct Linker {
    /// Whenever a module is updated, we generate a new key for it.
    modules: SlotMap<ModuleKey, ParsedModule>,
    module_names: SecondaryMap<ModuleKey, ModulePath>,
    module_paths: HashMap<ModulePath, ModuleKey>,
}

/// A cache for compiled modules. This is useful when linking multiple times, as it avoids reparsing.
#[derive(Default)]
pub struct LinkerCache {
    compiled_modules: HashMap<ModuleKey, CompiledModule>,
}
impl LinkerCache {
    pub fn new() -> Self {
        Default::default()
    }
}

new_key_type! {
    /// A key for a module in the linker.
    pub struct ModuleKey;
}

/// Module compilation is independent of other modules. It only depends on the source code of the module.
pub(crate) struct CompiledModule {
    pub mangled_source: String,
}

#[derive(Error, Debug)]
pub enum LinkingError {
    #[error("the imported item {variable} was redefined")]
    Redefinition { variable: String },
    #[error("the module {module:?} was not found")]
    ModuleNotFound { module: ModulePath },
    #[error("multiple errors occurred {0:?}")]
    Aggregate(Vec<LinkingError>),
}

impl Linker {
    pub fn new() -> Self {
        Self::default()
    }

    /// Adds or updates a module in the linker.
    pub fn insert_module(
        &mut self,
        name: ModulePath,
        source: String,
    ) -> Result<ModuleKey, WgslParseError> {
        let ast = parse(&source)?;
        let global_items = ast.get_global_items(&source);
        let imports = IndexMap::new(); // TODO: ast.get_imports(&source); and strip the import and export statements
        let module_key = self.modules.insert(ParsedModule {
            source,
            ast,
            global_items,
            imports,
        });

        self.module_names.insert(module_key, name.clone());
        if let Some(old_module) = self.module_paths.insert(name.clone(), module_key) {
            self.remove_module(old_module);
        }

        Ok(module_key)
    }

    /// Removes a module from the linker. On success, returns the module path.
    pub fn remove_module(&mut self, module: ModuleKey) -> Option<ModulePath> {
        let _ = self.modules.remove(module);
        let module_path = self.module_names.remove(module)?;
        let _ = self.module_paths.remove(&module_path);
        Some(module_path)
    }

    /// Add imports to a module, in the form of (new name, location).
    /// This changes the module key.
    pub fn add_imports<Imports: IntoIterator<Item = (ItemName, ModuleItem)>>(
        &mut self,
        module_key: ModuleKey,
        imports: Imports,
    ) -> ModuleKey {
        let mut module = self.modules.remove(module_key).unwrap();
        let module_path = self.module_names.remove(module_key).unwrap();

        module.imports.extend(imports);
        let new_key = self.modules.insert(module);
        let _ = self.module_names.insert(new_key, module_path.clone());
        let _ = self.module_paths.insert(module_path, new_key);
        new_key
    }

    fn compile_single_module(&self, module: ModuleKey) -> Result<CompiledModule, LinkingError> {
        let parsed_module = &self.modules[module];
        let mut visitor = LinkerVisitor::new(self, module);
        let result = parsed_module
            .ast
            .rewrite(&parsed_module.source, &mut visitor);
        if visitor.errors.is_empty() {
            Ok(CompiledModule {
                mangled_source: result,
            })
        } else {
            Err(LinkingError::Aggregate(visitor.errors))
        }
    }

    /// Compile multiple modules into one output file.
    pub fn compile(
        &self,
        entry_point: ModuleKey,
        cache: &mut LinkerCache,
    ) -> Result<String, LinkingError> {
        let sorted_modules = self.collect_imports(entry_point)?;
        // Independently compile each module, order does NOT matter.
        for module in sorted_modules.iter() {
            if !cache.compiled_modules.contains_key(module) {
                let compiled_module = self.compile_single_module(*module)?;
                cache.compiled_modules.insert(*module, compiled_module);
            }
        }
        // Concatenate all the compiled modules. Entry point comes last.
        let mut result = String::new();
        for module in sorted_modules.iter().rev() {
            result.push_str(&cache.compiled_modules[module].mangled_source);
            result.push('\n');
        }
        Ok(result)
    }

    /// Pre-order traversal of the import graph.
    /// Entry point is the first module.
    fn collect_imports(&self, entry_point: ModuleKey) -> Result<Vec<ModuleKey>, LinkingError> {
        let mut result = vec![];
        let mut stack = vec![entry_point];
        let mut seen = HashSet::new();
        seen.insert(entry_point);

        while let Some(module_key) = stack.pop() {
            result.push(module_key);
            // Iterate in reverse order to keep the order of imports
            let module_imports = self.modules[module_key].imports.values().rev();
            for ModuleItem { module_path, .. } in module_imports {
                let module = self.module_paths.get(module_path).ok_or_else(|| {
                    LinkingError::ModuleNotFound {
                        module: module_path.clone(),
                    }
                })?;
                if seen.insert(*module) {
                    stack.push(*module);
                }
            }
        }

        Ok(result)
    }
}

struct LinkerVisitor<'a> {
    linker: &'a Linker,
    module_key: ModuleKey,
    imports: &'a IndexMap<ItemName, ModuleItem>,
    global_items: &'a HashMap<ItemName, GlobalItem>,
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
            Some(mangle_name(
                &self.linker.module_names[self.module_key],
                variable,
            ))
        }
    }

    fn use_variable(&mut self, variable: &'a str) -> Option<String> {
        if self.is_local(variable) {
            // Keep local variable names
            None
        } else if let Some(ModuleItem { module_path, name }) = self.imports.get(variable) {
            // Replace imports
            // Notice how this also handles "import cat as dog" renames
            Some(mangle_name(module_path, &name.0))
        } else if self.global_items.contains_key(variable) {
            // Mangle all globals
            Some(mangle_name(
                &self.linker.module_names[self.module_key],
                variable,
            ))
        } else {
            // It must be a predeclared item. Don't bother mangling them.
            None
        }
    }
}

impl Ast {
    pub fn get_global_items(&self, source: &str) -> HashMap<ItemName, GlobalItem> {
        let mut visitor = GlobalItemsVisitor::default();
        self.visit(source, &mut visitor);
        visitor.items
    }
}

#[derive(Default)]
struct GlobalItemsVisitor {
    items: HashMap<ItemName, GlobalItem>,
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
                .insert(ItemName(variable.to_string()), GlobalItem::Exported);
        }
    }

    fn use_variable(&mut self, _variable: &str) {}
}

#[cfg(test)]
mod tests {
    use crate::linker::{ItemName, ModuleItem};

    use super::{Linker, ModulePath};

    #[test]
    fn basic_linking() {
        let mut linker = Linker::new();
        let foo_module = linker
            .insert_module(
                ModulePath::from_slice(&["foo"]),
                "fn uno() -> u32 { return 1; }".to_string(),
            )
            .unwrap();
        let bar_module = linker
            .insert_module(
                ModulePath::from_slice(&["bar"]),
                "fn dos() -> u32 { return uno() + uno   (); }".to_string(),
            )
            .unwrap();

        // Manually add the import
        let bar_module = linker.add_imports(
            bar_module,
            [(
                ItemName("uno".to_string()),
                ModuleItem {
                    module_path: ModulePath::from_slice(&["foo"]),
                    name: ItemName("uno".to_string()),
                },
            )],
        );

        assert_eq!(
            &linker
                .compile_single_module(foo_module)
                .unwrap()
                .mangled_source,
            "fn foo_uno() -> u32 { return 1; }",
        );
        assert_eq!(
            &linker
                .compile_single_module(bar_module)
                .unwrap()
                .mangled_source,
            "fn bar_dos() -> u32 { return foo_uno() + foo_uno   (); }",
        );
    }
}
