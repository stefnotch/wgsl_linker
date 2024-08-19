use thiserror::Error;
use winnow::error::StrContext;

use super::Span;

#[derive(Error, Debug)]
pub struct WgslParseError {
    pub message: String,
    pub position: usize,
    pub context: Vec<StrContext>,
}

impl std::fmt::Display for WgslParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

pub type VariableSpan = Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AstNode {
    Declare(VariableSpan),
    Use(VariableSpan),
    /// A property use, like the `bar` in `foo.bar`.
    PropertyUse {
        dot: usize,
        property: VariableSpan,
    },
    OpenBlock,
    CloseBlock,
    TemplateStart,
    TemplateEnd,
    /// Starts an import statement.
    ImportStart {
        keyword: Span,
    },
    ImportModulePart(VariableSpan),
    ImportVariable {
        variable: VariableSpan,
        alias: Option<VariableSpan>,
    },
    ImportStar {
        alias: Option<VariableSpan>,
    },
    ImportEnd {
        semicolon: usize,
    },
}

#[derive(Default, Debug, PartialEq, Eq)]
pub struct Ast(pub Vec<AstNode>);
impl Ast {
    pub fn new() -> Self {
        Self(Vec::new())
    }
    pub fn single(item: AstNode) -> Self {
        Self(vec![item])
    }
    pub fn join(mut self, other: impl Into<Ast>) -> Ast {
        self.0.append(&mut other.into().0);
        self
    }
}

impl From<Option<Ast>> for Ast {
    fn from(value: Option<Ast>) -> Self {
        value.unwrap_or_default()
    }
}

impl FromIterator<AstNode> for Ast {
    fn from_iter<T: IntoIterator<Item = AstNode>>(iter: T) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl FromIterator<Ast> for Ast {
    fn from_iter<T: IntoIterator<Item = Ast>>(iter: T) -> Self {
        iter.into_iter().fold(Ast::default(), |acc, x| acc.join(x))
    }
}
