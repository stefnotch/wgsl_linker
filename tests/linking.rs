use wgsl_linker_reference::linker::{Linker, ModulePath};

fn module_path(items: &[&str]) -> ModulePath {
    let items = items.into_iter().map(|item| item.to_string()).collect();
    ModulePath(items)
}

#[test]
fn basic_linking() {}

// TODO: example with underscore_names
// TODO: example where the underscore_names look like module names
// TODO: Unmangling
// - Module: foo
//   Items: uno, bar_baz
// - Module: foo_bar
//   Items baz
// would that cause them to be mangled to the same name? (aka ambiguous)
// so we have to do the escaping during mangling!
// TODO: struct with a field called u32 and sin. And a function called sin.
