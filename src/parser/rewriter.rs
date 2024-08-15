use super::{Ast, AstNode};

pub trait Rewriter<'a> {
    /// Like a sax parser, this will be called for each node in the AST.
    fn open_block(&mut self);
    fn close_block(&mut self);
    /// Change the variable by returning a new name.
    fn declare(&mut self, variable: &'a str) -> Option<String>;
    /// Change the variable by returning a new name.
    fn use_variable(&mut self, variable: &'a str) -> Option<String>;
}

pub trait Visitor<'a> {
    /// Like a sax parser, this will be called for each node in the AST.
    fn open_block(&mut self);
    fn close_block(&mut self);
    fn declare(&mut self, variable: &'a str);
    // TODO: we will add more methods along the lines of "use_variable()", "module_fragment(name)", "finish_variable(name)".
    // Aka module::something::variable ends up emitting
    // 1. use_variable()
    // 2. module_fragment("module") <= For resolving the module that the variable is in
    // 3. module_fragment("something") <= For resolving the module that the variable is in
    // 4. finish_variable("variable") <= Actual item name
    fn use_variable(&mut self, variable: &'a str);
}

impl Ast {
    pub fn visit<'a, T: Visitor<'a>>(&self, source: &'a str, visitor: &mut T) {
        for node in &self.0 {
            match node {
                AstNode::OpenBlock => visitor.open_block(),
                AstNode::CloseBlock => visitor.close_block(),
                AstNode::Declare(var) => visitor.declare(&source[var.range()]),
                AstNode::Use(var) => visitor.use_variable(&source[var.range()]),
                AstNode::TemplateStart => {}
                AstNode::TemplateEnd => {}
            }
        }
    }
    pub fn rewrite<'a, T: Rewriter<'a>>(&self, source: &'a str, visitor: &mut T) -> String {
        let mut result = String::new();
        let mut source_index = 0;
        for node in &self.0 {
            match node {
                AstNode::OpenBlock => visitor.open_block(),
                AstNode::CloseBlock => visitor.close_block(),
                AstNode::Declare(var) => {
                    let range = var.range();
                    result.push_str(&source[source_index..range.start]);
                    source_index = range.end;
                    match visitor.declare(&source[range.clone()]) {
                        Some(new_var) => result.push_str(&new_var),
                        None => result.push_str(&source[range]),
                    }
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
                AstNode::TemplateStart => {}
                AstNode::TemplateEnd => {}
            }
        }
        result.push_str(&source[source_index..]);
        result
    }
}
