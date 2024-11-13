// #![no_std]

//! A WGSL linker, which parses and links multiple WGSL files into a single module.
//!
//! # Example
//! ```rust
//! use wgsl_linker::linker::{Linker, LinkerCache, ModulePath, ItemName, ImportedItem, ImportPath};
//!
//! let mut linker = Linker::new();
//!
//! let foo_path = ModulePath::from_slice(&["foo"]);
//! let _foo_module = linker.insert_module(
//!     foo_path.clone(),
//!     "fn uno() -> u32 { return 1; }".to_string(),
//! ).unwrap();
//!
//! let bar_path = ModulePath::from_slice(&["bar"]);
//! let bar_module = linker.insert_module(
//!    bar_path.clone(),
//!   "fn dos() -> u32 { return uno() + 1; }".to_string(),
//! ).unwrap();
//!
//! let bar_module = linker.add_imports(
//!    bar_module,
//!   [(ItemName::new("uno"), ImportedItem::Item {
//!      path: ImportPath::Absolute(foo_path),
//!      name: ItemName::new("uno"),
//!  })],
//! );
//!
//! let output = linker.compile(bar_module, &mut LinkerCache::default()).unwrap();
//! ```

mod parser;

use no_panic::no_panic;
use wasm_bindgen::prelude::wasm_bindgen;

/*
pub mod linker;
pub mod parser;

pub use linker::Linker;
 */
/// SAFETY: The runtime environment must be single-threaded WASM.
#[global_allocator]
static ALLOCATOR: talc::Talck<talc::locking::AssumeUnlockable, talc::ClaimOnOom> = {
    static mut MEMORY: [u8; 0x1000000] = [0; 0x1000000];
    let span = talc::Span::from_const_array(std::ptr::addr_of!(MEMORY));
    talc::Talc::new(unsafe { talc::ClaimOnOom::new(span) }).lock()
};

#[no_panic]
#[wasm_bindgen]
pub fn main(input: &str) -> String {
    let a = parser::parse(input).unwrap();

    if a.0.len() > 3 {
        return "Hi".to_string();
    } else {
        return "Bye".to_string();
    }
}
