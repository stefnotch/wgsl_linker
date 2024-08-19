use super::{Ast, AstNode};

impl Ast {
    pub fn iter<'a>(&'a self, source: &'a str) -> AstIter<'a> {
        AstIter::new(source, self)
    }
}

struct AstIter<'a> {
    source: &'a str,
    ast: &'a Ast,
    index: usize,
    end_at: AstIterEnd,
}

struct AstNodeWrapper<'a> {
    node: &'a AstNode,
    index: usize,
    children: AstIter<'a>,
}

enum AstIterEnd {
    FileEnd,
    Immediate,
    VariableEnd,
    BlockEnd,
    TemplateEnd,
    ImportEnd,
}

impl<'a> AstIter<'a> {
    fn new(source: &'a str, ast: &'a Ast) -> Self {
        Self {
            source,
            ast,
            index: 0,
            end_at: AstIterEnd::FileEnd,
        }
    }

    fn child_iter(&self, end_at: AstIterEnd) -> AstIter<'a> {
        AstIter {
            source: self.source,
            ast: self.ast,
            index: self.index,
            end_at,
        }
    }
}

impl<'a> Iterator for AstIter<'a> {
    type Item = AstNodeWrapper<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index > self.ast.0.len() {
            return None;
        }
        let index = self.index;
        let node = &self.ast.0[index];
        match (&self.end_at, node) {
            (AstIterEnd::FileEnd, _) => {}
            (AstIterEnd::Immediate, _) => return None,
            (AstIterEnd::VariableEnd, AstNode::PropertyUse { .. }) => {}
            (AstIterEnd::VariableEnd, _) => return None,
            (AstIterEnd::BlockEnd, AstNode::CloseBlock) => return None,
            (AstIterEnd::TemplateEnd, AstNode::TemplateEnd) => return None,
            (AstIterEnd::ImportEnd, AstNode::ImportEnd { .. }) => return None,
            _ => {}
        }
        self.index += 1;
        let children = match node {
            AstNode::Use(_) => self.child_iter(AstIterEnd::VariableEnd),
            AstNode::OpenBlock => self.child_iter(AstIterEnd::BlockEnd),
            AstNode::TemplateStart => self.child_iter(AstIterEnd::TemplateEnd),
            AstNode::ImportStart { .. } => self.child_iter(AstIterEnd::ImportEnd),
            _ => self.child_iter(AstIterEnd::Immediate),
        };
        Some(AstNodeWrapper {
            node,
            index,
            children,
        })
    }
}
