use wgsl_linker_reference::linker::{Linker, ModulePath};

fn module_path(items: &[&str]) -> ModulePath {
    let items = items.into_iter().map(|item| item.to_string()).collect();
    ModulePath(items)
}

#[test]
fn basic_linking() {
    let mut linker = Linker::new();
    let foo_module = linker
        .add_module_source(
            module_path(&["foo"]),
            "fn uno() -> u32 { return 1; }".to_string(),
        )
        .unwrap();
    let bar_module = linker
        .add_module_source(
            module_path(&["bar"]),
            "fn dos() -> u32 { return uno() + uno   (); }".to_string(),
        )
        .unwrap();

    // Manually inject the import
    let parsed_bar = linker.modules.get_mut(bar_module).unwrap();
    parsed_bar
        .imports
        .insert("uno".to_string(), (foo_module, "uno".to_string()));

    let result = linker.compile_module(foo_module).unwrap()
        + "\n"
        + &linker.compile_module(bar_module).unwrap();
    assert_eq!(
        &result,
        "fn foo_uno() -> u32 { return 1; }
fn bar_dos() -> u32 { return foo_uno() + foo_uno   (); }"
    );
}
