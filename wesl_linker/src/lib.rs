// #![no_std]

//! A WGSL linker, which parses and links multiple WGSL files into a single module.
//!
//! # Example
//! ```rust
//! use wesl_linker::linker::{Linker, LinkerCache, ModulePath, ItemName, ImportedItem, ImportPath};
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

// pub mod linker;
// pub use linker::Linker;

pub mod parser;
