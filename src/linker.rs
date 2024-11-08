pub mod filesystem;
mod mangling;
mod parsed_module;

use std::collections::{HashMap, HashSet};

use arcstr::ArcStr;
use filesystem::ReadonlyFilesystem;
use indexmap::IndexMap;
use slotmap::{new_key_type, SecondaryMap, SlotMap};
use thiserror::Error;

use crate::parser::{
    parse, Ast, AstNode, PropertiesIter, RewriteAction, VariableRewriteAction, WgslParseError,
};
use crate::parser::{Rewriter, Visitor};
pub use mangling::{mangle_name, unmangle_name, write_mangled_name, UnmangledName};
use parsed_module::{GlobalItem, ParsedModule};
pub use parsed_module::{ImportPath, ImportedItem, ItemName, ModuleItem, ModulePath};

/// Links multiple modules together into a single module.
/// Main entry point of the library.
#[derive(Default)]
pub struct Linker {
    /// Whenever a module is updated, we generate a new key for it.
    modules: SlotMap<ModuleKey, ParsedModule>,
    module_names: SecondaryMap<ModuleKey, ModulePath>,
    module_paths: HashMap<ModulePath, ModuleKey>,
}

#[derive(Default)]
pub struct LinkingOptions {
    #[cfg(feature = "source_map")]
    pub generate_source_map: bool,
}

/// A cache for compiled modules. This is useful when linking multiple times, as it avoids reparsing.
#[derive(Default)]
pub struct LinkerCache {
    /// There are no re-exported items, so we do not need to track the module dependencies!
    /// If there were, then the compiled code could change (e.g. a mangled name can change, because of a re-export)
    imports: HashMap<ModuleKey, HashMap<ItemName, ModuleItem>>,
    compiled_modules: HashMap<ModuleKey, CompiledModule>,
}
impl LinkerCache {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn invalidate_cache(&mut self, module_exists: impl Fn(ModuleKey) -> bool) {
        self.imports.retain(|k, _| module_exists(*k));
        self.compiled_modules.retain(|k, _| module_exists(*k));
    }
}

new_key_type! {
    /// A key for a module in the linker.
    pub struct ModuleKey;
}

pub(crate) struct CompiledModule {
    pub mangled_source: String,
}

#[derive(Error, Debug)]
pub enum LinkingError {
    #[error("the imported item {variable} was redefined")]
    Redefinition { variable: String },
    #[error("the module {module:?} was not found")]
    ModuleNotFound { module: ModulePath },
    #[error("module {module:?} usage expects a variable")]
    MissingVariable { module: String },
    #[error("invalid import path {path:?}")]
    InvalidImport { path: Vec<String> },
    #[error("multiple errors occurred {0:?}")]
    Aggregate(Vec<LinkingError>),
}

#[derive(Error, Debug)]
pub enum CollectModulesError<FSError> {
    #[error(transparent)]
    ModuleNotFound(FSError),
    #[error(transparent)]
    ParseError(#[from] WgslParseError),
    #[error(transparent)]
    LinkingError(#[from] LinkingError),
}

impl<T> From<AddModuleError> for CollectModulesError<T> {
    fn from(e: AddModuleError) -> Self {
        match e {
            AddModuleError::ParseError(e) => e.into(),
            AddModuleError::LinkingError(e) => e.into(),
        }
    }
}

#[derive(Error, Debug)]
pub enum AddModuleError {
    #[error(transparent)]
    ParseError(#[from] WgslParseError),
    #[error(transparent)]
    LinkingError(#[from] LinkingError),
}

impl Linker {
    pub fn new() -> Linker {
        Self::default()
    }

    /// Adds or updates a module in the linker.
    pub fn insert_module<Source: Into<ArcStr>>(
        &mut self,
        name: ModulePath,
        source: Source,
    ) -> Result<ModuleKey, AddModuleError> {
        let source: ArcStr = source.into();
        let ast = parse(&source)?;
        let global_items = ast.get_global_items(&source);
        let imports = ast.get_imports(&source)?;
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

    fn get_exact_module(&self, module: &ModulePath, source: &str) -> Option<ModuleKey> {
        let module_key = self.module_paths.get(module)?;
        if self.modules[*module_key].source == source {
            Some(*module_key)
        } else {
            None
        }
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
    pub fn add_imports<Imports: IntoIterator<Item = (ItemName, ImportedItem)>>(
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

    /// Compile multiple modules into one output file.
    /// Module compilation is mostly independent.
    /// The overall process is:
    /// 1. Resolve all imports
    /// 2. Compile the main module
    /// 3. Independently compile all other modules
    pub fn compile(
        &self,
        entry_point: ModuleKey,
        options: LinkingOptions,
        cache: &mut LinkerCache,
    ) -> Result<String, LinkingError> {
        cache.invalidate_cache(|v| self.modules.contains_key(v));
        let sorted_modules = self.collect_modules(entry_point)?;

        // Independently compile each module, order does NOT matter.
        // We do not have re-exports yet, which simplifies the process.
        for module in sorted_modules.iter() {
            let imports = cache
                .imports
                .entry(*module)
                .or_insert_with(|| self.resolve_imports(*module));
            if !cache.compiled_modules.contains_key(module) {
                let compiled_module = self.compile_single_module(*module, imports)?;
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

    /// Parses and inserts all missing modules from the filesystem.
    pub fn collect_fs<
        'a,
        FS: ReadonlyFilesystem,
        EntryPoints: IntoIterator<Item = &'a ModulePath>,
    >(
        &mut self,
        fs: &FS,
        entry_points: EntryPoints,
    ) -> Result<(), CollectModulesError<FS::Error>> {
        // No collecting a result here, because that would make the parallelism harder.
        let mut stack = vec![];
        let mut seen = HashSet::new();

        for module_path in entry_points {
            // Can happen in parallel (no issues there)
            // (Can return the same ArcStr, because it is a reference)
            let source = fs
                .read(module_path)
                .map_err(CollectModulesError::ModuleNotFound)?;

            // Should happen on a single thread. Order independent
            let module = match self.get_exact_module(module_path, &source) {
                Some(v) => v,
                None => self.insert_module(module_path.clone(), source)?,
            };

            // Should happen on a single thread
            // Order independent, *because* we are not returning a result!
            if seen.insert(module) {
                stack.push(module);
            }
        }

        while let Some(module_key) = stack.pop() {
            // Order of imports doesn't matter (no result to collect)
            // So we can iterate in any order.
            let module_base = &self.module_names[module_key];
            let module_imports = self.modules[module_key]
                .imports
                .values()
                .map(|v| v.path().resolve(module_base))
                .collect::<Vec<_>>();

            for module_path in module_imports {
                let source = fs
                    .read(&module_path)
                    .map_err(CollectModulesError::ModuleNotFound)?;

                let module = match self.get_exact_module(&module_path, &source) {
                    Some(v) => v,
                    None => self.insert_module(module_path, source)?,
                };

                if seen.insert(module) {
                    stack.push(module);
                }
            }
        }

        Ok(())
    }

    fn resolve_imports(&self, module: ModuleKey) -> HashMap<ItemName, ModuleItem> {
        self.modules[module]
            .imports
            .iter()
            .map(|(k, v)| (k.clone(), v.resolve(&self.module_names[module])))
            .collect()
    }

    /// Pre-order traversal of the import graph.
    /// Entry point is the first module.
    fn collect_modules(&self, entry_point: ModuleKey) -> Result<Vec<ModuleKey>, LinkingError> {
        let mut result = vec![];
        let mut stack = vec![entry_point];
        let mut seen = HashSet::new();
        seen.insert(entry_point);

        while let Some(module_key) = stack.pop() {
            result.push(module_key);
            // Iterate in reverse order to keep the order of imports
            let module_base = &self.module_names[module_key];
            let module_imports = self.modules[module_key]
                .imports
                .values()
                .rev()
                .map(|v| v.path().resolve(module_base));
            for module_path in module_imports {
                let module = self.module_paths.get(&module_path).ok_or_else(|| {
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

    fn compile_single_module(
        &self,
        module: ModuleKey,
        imports: &HashMap<ItemName, ModuleItem>,
    ) -> Result<CompiledModule, LinkingError> {
        let parsed_module = &self.modules[module];
        let mut visitor = LinkerVisitor::new(self, module, imports);
        let mangled_source = parsed_module
            .ast
            .rewrite(&parsed_module.source, &mut visitor);
        if visitor.errors.is_empty() {
            Ok(CompiledModule { mangled_source })
        } else {
            Err(LinkingError::Aggregate(visitor.errors))
        }
    }
}

struct LinkerVisitor<'a> {
    linker: &'a Linker,
    module_key: ModuleKey,
    imports: &'a HashMap<ItemName, ModuleItem>,
    global_items: &'a HashMap<ItemName, GlobalItem>,
    /// Keeps track of function scopes. Ignores the top-level scope.
    scoped_items: Vec<HashSet<&'a str>>,
    errors: Vec<LinkingError>,
}

impl<'a> LinkerVisitor<'a> {
    fn new(
        linker: &'a Linker,
        module_key: ModuleKey,
        imports: &'a HashMap<ItemName, ModuleItem>,
    ) -> Self {
        let module = linker.modules.get(module_key).unwrap();
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

    fn declare(&mut self, variable: &'a str) -> RewriteAction {
        if let Some(local_scope) = self.scoped_items.last_mut() {
            // Variables in inner scopes can shadow outer variables.
            local_scope.insert(variable);
            RewriteAction::Keep
        } else {
            // Global scope!
            if self.imports.contains_key(variable) {
                self.errors.push(LinkingError::Redefinition {
                    variable: variable.to_string(),
                });
            }
            RewriteAction::Replace(mangle_name(
                &self.linker.module_names[self.module_key],
                variable,
            ))
        }
    }

    fn use_variable(
        &mut self,
        variable: &'a str,
        mut properties: PropertiesIter<'a, '_>,
    ) -> VariableRewriteAction {
        if self.is_local(variable) {
            // Keep local variable names
            VariableRewriteAction::Keep
        } else if let Some(module_item) = self.imports.get(variable) {
            // Replace imports
            // Notice how this also handles "import cat as dog" renames
            match module_item {
                ModuleItem::Item { module_path, name } => {
                    VariableRewriteAction::ReplaceVariable(mangle_name(module_path, &name.0))
                }
                ModuleItem::AllItems(module_path) => {
                    // The syntax after a star import is "module.variable"
                    match properties.next() {
                        Some(name) => {
                            // properties can still contain values,
                            // because it is ok for a property access to happen after the variable name.
                            VariableRewriteAction::ReplaceVariable(mangle_name(module_path, name))
                        }
                        None => {
                            self.errors.push(LinkingError::MissingVariable {
                                module: variable.to_string(),
                            });
                            VariableRewriteAction::Keep
                        }
                    }
                }
            }
        } else if self.global_items.contains_key(variable) {
            // Mangle all globals
            VariableRewriteAction::ReplaceVariable(mangle_name(
                &self.linker.module_names[self.module_key],
                variable,
            ))
        } else {
            // It must be a predeclared item. Don't bother mangling them.
            VariableRewriteAction::Keep
        }
    }
}

impl Ast {
    pub fn get_global_items(&self, source: &str) -> HashMap<ItemName, GlobalItem> {
        let mut items = HashMap::new();
        let mut block_level = 0;
        for node in &self.0 {
            match node {
                AstNode::OpenBlock => block_level += 1,
                AstNode::CloseBlock => block_level -= 1,
                AstNode::Declare(var) if block_level == 0 => {
                    items.insert(ItemName(var.text(source).to_string()), GlobalItem::Exported);
                }
                _ => {}
            }
        }
        assert_eq!(block_level, 0);
        items
    }

    pub fn get_imports(
        &self,
        source: &str,
    ) -> Result<IndexMap<ItemName, ImportedItem>, LinkingError> {
        #[derive(Default)]
        struct ImportVisitor<'a> {
            items: IndexMap<ItemName, ImportedItem>,
            module_parts: Vec<&'a str>,
            block_stack: Vec<usize>,
            errors: Vec<LinkingError>,
        }

        impl<'a> ImportVisitor<'a> {
            fn get_import_path(&mut self) -> ImportPath {
                match self.module_parts.last() {
                    None | Some(&"") | Some(&".") | Some(&"..") => {
                        self.errors.push(LinkingError::InvalidImport {
                            path: self.module_parts.iter().map(|v| v.to_string()).collect(),
                        });
                        return ImportPath::new_absolute(&[]);
                    }
                    _ => {}
                }

                if self.module_parts[0] == "." || self.module_parts[0] == ".." {
                    let path_parts = self
                        .module_parts
                        .iter()
                        .skip(1)
                        .skip_while(|v| **v == "..")
                        .map(|v| v.to_string())
                        .collect();
                    let parent_count =
                        self.module_parts.iter().take_while(|v| **v == "..").count() as u32;
                    ImportPath::Relative {
                        parent_count,
                        path: path_parts,
                    }
                } else {
                    ImportPath::new_absolute(&self.module_parts)
                }
            }
        }

        impl<'a> Visitor<'a> for ImportVisitor<'a> {
            fn import_start(&mut self) {
                assert!(self.module_parts.is_empty());
                assert!(self.block_stack.is_empty());
            }
            fn import_module_part(&mut self, part: &'a str) {
                self.module_parts.push(part);
            }
            fn open_block(&mut self) {
                self.block_stack.push(self.module_parts.len());
            }
            fn close_block(&mut self) {
                let len = self.block_stack.pop().unwrap();
                self.module_parts.truncate(len);
            }
            fn import_star(&mut self, alias: Option<&'a str>) {
                let alias = alias.unwrap_or_else(|| self.module_parts.last().unwrap());
                let module_items = ImportedItem::AllItems(self.get_import_path());
                let old_value = self.items.insert(ItemName(alias.to_string()), module_items);
                if old_value.is_some() {
                    self.errors.push(LinkingError::Redefinition {
                        variable: alias.to_string(),
                    });
                }
            }
            fn import_variable(&mut self, variable: &'a str, alias: Option<&'a str>) {
                let alias = alias.unwrap_or(variable);
                let module_items = ImportedItem::Item {
                    path: self.get_import_path(),
                    name: ItemName(variable.to_string()),
                };
                let old_value = self.items.insert(ItemName(alias.to_string()), module_items);
                if old_value.is_some() {
                    self.errors.push(LinkingError::Redefinition {
                        variable: alias.to_string(),
                    });
                }
            }
            fn import_end(&mut self) {
                self.module_parts.clear();
                assert!(self.block_stack.is_empty());
            }
        }

        let mut visitor = ImportVisitor::default();
        self.visit(source, &mut visitor);
        if visitor.errors.is_empty() {
            Ok(visitor.items)
        } else {
            Err(LinkingError::Aggregate(visitor.errors))
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::linker::{
        parsed_module::{ImportPath, ImportedItem},
        ItemName,
    };

    use super::{Linker, ModulePath};

    #[test]
    fn basic_linking() {
        let mut linker = Linker::new();
        let foo_module = linker
            .insert_module(
                ModulePath::from_slice(&["foo"]),
                arcstr::literal!("fn uno() -> u32 { return 1; }"),
            )
            .unwrap();
        let bar_module = linker
            .insert_module(
                ModulePath::from_slice(&["bar"]),
                arcstr::literal!("fn dos() -> u32 { return uno() + uno   (); }"),
            )
            .unwrap();

        // Manually add the import
        let bar_module = linker.add_imports(
            bar_module,
            [(
                ItemName("uno".to_string()),
                ImportedItem::Item {
                    path: ImportPath::new_absolute(&["foo"]),
                    name: ItemName("uno".to_string()),
                },
            )],
        );

        assert_eq!(
            &linker
                .compile_single_module(foo_module, &linker.resolve_imports(foo_module))
                .unwrap()
                .mangled_source,
            "fn foo_uno() -> u32 { return 1; }",
        );
        assert_eq!(
            &linker
                .compile_single_module(bar_module, &linker.resolve_imports(bar_module))
                .unwrap()
                .mangled_source,
            "fn bar_dos() -> u32 { return foo_uno() + foo_uno   (); }",
        );
    }
}
