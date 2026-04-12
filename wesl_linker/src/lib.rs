mod lexer;
mod parser;
mod syntax_kind;

use std::fmt::{self, Debug, Write as _};

pub use parser::{Diagnostic, parse_entrypoint};

pub struct Parse {
    cst: CstData,
    errors: Vec<Diagnostic>,
}
impl fmt::Debug for Parse {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Parse")
            .field("cst", &self.cst)
            .field("errors", &self.errors)
            .finish()
    }
}

impl Parse {
    #[must_use]
    pub fn debug_tree(&self) -> String {
        let mut buffer = String::new();

        let tree = format!("{:#?}", self.cst);

        // We cut off the last byte because formatting the SyntaxNode adds on a newline at the end.
        buffer.push_str(&tree[0..tree.len() - 1]);

        if !self.errors.is_empty() {
            buffer.push('\n');
        }
        for diagnostic in &self.errors {
            write!(buffer, "\n{diagnostic}").unwrap();
        }
        buffer
    }

    #[must_use]
    pub fn errors(&self) -> &[Diagnostic] {
        &self.errors
    }
}

pub use syntax_kind::SyntaxKind;

use crate::parser::CstData;

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum WeslLanguage {}

#[derive(Copy, PartialEq, Eq, Clone, Hash, Debug)]
pub enum ParseEntryPoint {
    File,
    Expression,
    Statement,
    Type,
    Attribute,
}
