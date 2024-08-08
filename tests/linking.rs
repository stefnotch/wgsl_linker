use wgsl_linker_reference::linker::{Linker, ModulePath};

fn module_path(items: &[&str]) -> ModulePath {
    let items = items.into_iter().map(|item| item.to_string()).collect();
    ModulePath(items)
}

#[test]
fn basic_linking() {}
