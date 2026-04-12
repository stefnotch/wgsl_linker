use no_panic::no_panic;
use wasm_bindgen::prelude::wasm_bindgen;

use wesl_linker::ParseEntryPoint;
// uwu
#[cfg(target_family = "wasm")]
#[global_allocator]
static TALC: talc::wasm::WasmDynamicTalc = talc::wasm::new_wasm_dynamic_allocator();

#[no_panic]
#[wasm_bindgen]
pub fn main_1(input: &str) -> String {
    let a = wesl_linker::parse_entrypoint(input, ParseEntryPoint::File);
    a.debug_tree()
}
