use proptest::collection;
use test_strategy::proptest;
use wgsl_linker::linker::{mangle_name, unmangle_name, ModulePath};

#[proptest]
fn mangle_proptest(
    #[strategy(collection::vec("[a-z]([a-z0-9_])*", 1..=3))] module_path: Vec<String>,
    #[strategy("[a-z]([a-z0-9_])*")] name: String,
) {
    let module_path = ModulePath { path: module_path };
    let mangled = mangle_name(&module_path, &name);
    let unmangled = unmangle_name(&mangled);
    assert_eq!(module_path, unmangled.module);
    assert_eq!(name, unmangled.name);
}
