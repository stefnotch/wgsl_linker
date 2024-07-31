use crate::parser_output::{Ast, AstNode};

pub trait Rewriter {
    /// Like a sax parser, this will be called for each node in the AST.
    fn open_block(&mut self);
    fn close_block(&mut self);
    fn declare(&mut self, variable: &str);
    /// To change the variable name, return a new name.
    /// To keep the variable name, return None.
    fn use_variable(&mut self, variable: &str) -> Option<String>;
}

pub trait Visitor {
    /// Like a sax parser, this will be called for each node in the AST.
    fn open_block(&mut self);
    fn close_block(&mut self);
    fn declare(&mut self, variable: &str);
    fn use_variable(&mut self, variable: &str);
}

impl Ast {
    pub fn visit(&self, source: &str, mut visitor: impl Visitor) {
        for node in &self.0 {
            match node {
                AstNode::OpenBlock => visitor.open_block(),
                AstNode::CloseBlock => visitor.close_block(),
                AstNode::Declare(var) => visitor.declare(&source[var.range()]),
                AstNode::Use(var) => visitor.use_variable(&source[var.range()]),
            }
        }
    }
    pub fn rewrite(&self, source: &str, mut visitor: impl Rewriter) -> String {
        let mut result = String::new();
        let mut source_index = 0;
        for node in &self.0 {
            match node {
                AstNode::OpenBlock => visitor.open_block(),
                AstNode::CloseBlock => visitor.close_block(),
                AstNode::Declare(var) => {
                    visitor.declare(&source[var.range()]);
                }
                AstNode::Use(var) => {
                    let range = var.range();
                    result.push_str(&source[source_index..range.start]);
                    source_index = range.end;
                    match visitor.use_variable(&source[range.clone()]) {
                        Some(new_var) => result.push_str(&new_var),
                        None => result.push_str(&source[range]),
                    }
                }
            }
        }
        result
    }
}
