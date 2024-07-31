use std::collections::{HashMap, HashSet};

use slotmap::{new_key_type, SecondaryMap, SlotMap};

use crate::{
    parser_output::Ast,
    rewriter::{Rewriter, Visitor},
};

pub struct Linker {
    pub module_names: SlotMap<ModuleKey, String>,
    pub modules: SecondaryMap<ModuleKey, ParsedModule>,
}

new_key_type! {
    /// A key for a module in the linker.
    pub struct ModuleKey;
}

pub struct ParsedModule {
    pub source: String,
    pub ast: Ast,
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
    pub fn mangle_name(&self, module: ModuleKey, name: &str) -> String {
        format!("{}_{}", self.module_names[module], name)
    }
    pub fn unmangle_name<'a>(&self, module: ModuleKey, mangled_name: &'a str) -> UnmangledName<'a> {
        let module_name = &self.module_names[module];
        assert!(mangled_name.starts_with(module_name));
        let name = &mangled_name[module_name.len() + 1..];
        UnmangledName { module, name }
    }

    pub fn compile_module(
        &self,
        module: ModuleKey,
        imports: &HashMap<String, (ModuleKey, String)>,
    ) -> String {
        let mut visitor = LinkerVisitor {
            linker: self,
            module_key: module,
            imports,
            scoped_items: Vec::new(),
        };
        let parsed_module = &self.modules[module];
        parsed_module
            .ast
            .rewrite(&parsed_module.source, &mut visitor)
    }
}

struct LinkerVisitor<'a> {
    linker: &'a Linker,
    module_key: ModuleKey,
    imports: &'a HashMap<String, (ModuleKey, String)>,
    /// Keeps track of function scopes. Ignores the top-level scope.
    scoped_items: Vec<HashSet<&'a str>>,
}

impl<'a> Rewriter<'a> for LinkerVisitor<'a> {
    fn open_block(&mut self) {
        self.scoped_items.push(HashSet::new());
    }

    fn close_block(&mut self) {
        self.scoped_items.pop();
    }

    fn declare(&mut self, variable: &'a str) {
        // Only variables in inner scopes can shadow outer variables.
        if let Some(scope) = self.scoped_items.last_mut() {
            scope.insert(variable);
        } else {
            assert!(
                !self.imports.contains_key(variable),
                "Cannot shadow imports"
            );
        }
    }

    fn use_variable(&mut self, variable: &'a str) -> Option<String> {
        // If it is a local variable, keep the name.
        if self
            .scoped_items
            .iter()
            .any(|scope| scope.contains(variable))
        {
            return None;
        }
        // If it is an import, replace the name.
        // Notice how this also handles "import cat as dog" renames
        if let Some((module, name)) = self.imports.get(variable) {
            Some(self.linker.mangle_name(*module, name))
        } else {
            // Mangle all other names.
            Some(self.linker.mangle_name(self.module_key, variable))
        }
    }
}

impl Ast {
    pub fn get_exports<'a>(&self, source: &'a str) -> Vec<&'a str> {
        let mut visitor = ExportsVisitor::<'a>::default();
        self.visit(source, &mut visitor);
        visitor.exports
    }
}

#[derive(Default)]
struct ExportsVisitor<'a> {
    exports: Vec<&'a str>,
    block_level: usize,
}

impl<'a> Visitor<'a> for ExportsVisitor<'a> {
    fn open_block(&mut self) {
        self.block_level += 1;
    }

    fn close_block(&mut self) {
        self.block_level -= 1;
    }

    fn declare(&mut self, variable: &'a str) {
        if self.block_level == 0 {
            self.exports.push(variable);
        }
    }

    fn use_variable(&mut self, _variable: &str) {}
}
