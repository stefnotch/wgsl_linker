use wgsl_linker_reference::{
    linker::{Linker, LinkerCache, ModulePath},
    parsed_module::{ItemName, ModuleItem},
};

#[test]
fn basic_linking() {
    let mut linker = Linker::new();

    let foo_module = linker
        .add_module_source(
            ModulePath::from_slice(&["foo"]),
            "fn uno() -> u32 { return 1; }".to_string(),
        )
        .unwrap();
    let bar_module = linker
        .add_module_source(
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
                module: foo_module,
                name: ItemName("uno".to_string()),
            },
        )],
    );

    let output = linker
        .compile(bar_module, &mut LinkerCache::default())
        .unwrap();
    assert_eq!(output.as_str(), "fn foo_uno() -> u32 { return 1; }\nfn bar_dos() -> u32 { return foo_uno() + foo_uno   (); }\n");
}

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
