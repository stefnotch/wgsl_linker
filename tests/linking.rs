use wgsl_linker::linker::{ItemName, Linker, LinkerCache, ModuleItem, ModulePath};

#[test]
fn basic_linking() {
    let mut linker = Linker::new();

    let _foo_module = linker
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

    let output = linker
        .compile(bar_module, &mut LinkerCache::default())
        .unwrap();
    assert_eq!(output.as_str(), "fn foo_uno() -> u32 { return 1; }\nfn bar_dos() -> u32 { return foo_uno() + foo_uno   (); }\n");
}

// TODO: struct with a field called u32 and sin. And a function called sin.
