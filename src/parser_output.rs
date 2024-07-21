use std::ops::Range;

pub struct Variable(pub Range<usize>);

pub enum AstNode {
    Declare(Variable),
    Use(Variable),
    OpenBlock,
    CloseBlock,
}

#[derive(Default)]
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
