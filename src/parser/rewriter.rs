use super::{Ast, AstNode};

pub enum RewriteAction {
    Keep,
    Replace(String),
}

pub enum VariableRewriteAction {
    Keep,
    ReplaceVariable(String),
    ReplaceAll(String),
}

pub struct PropertiesIter<'a, 'b> {
    source: &'a str,
    nodes: &'b [AstNode],
    index: usize,
}

impl<'a> Iterator for PropertiesIter<'a, '_> {
    type Item = &'a str;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.nodes.len() {
            return None;
        }
        match self.nodes[self.index] {
            AstNode::PropertyUse { property, .. } => {
                self.index += 1;
                Some(property.text(self.source))
            }
            _ => None,
        }
    }
}

pub trait Rewriter<'a> {
    fn open_block(&mut self);
    fn close_block(&mut self);
    fn declare(&mut self, variable: &'a str) -> RewriteAction;
    fn use_variable(
        &mut self,
        variable: &'a str,
        properties: PropertiesIter<'a, '_>,
    ) -> VariableRewriteAction;
}

pub trait Visitor<'a> {
    /// Like a sax parser, this will be called for each node in the AST.
    fn open_block(&mut self) {}
    fn close_block(&mut self) {}
    fn declare(&mut self, variable: &'a str) {
        let _ = variable;
    }

    fn use_variable(&mut self, variable: &'a str) {
        let _ = variable;
    }
    fn use_property(&mut self, property: &'a str) {
        let _ = property;
    }

    fn import_start(&mut self) {}
    fn import_module_part(&mut self, module_part: &'a str) {
        let _ = module_part;
    }
    fn import_variable(&mut self, variable: &'a str, alias: Option<&'a str>) {
        let _ = variable;
        let _ = alias;
    }
    fn import_star(&mut self, alias: Option<&'a str>) {
        let _ = alias;
    }
    fn import_end(&mut self) {}
}

struct StringRewriter<'a> {
    source: &'a str,
    result: String,
    source_index: usize,
}
impl<'a> StringRewriter<'a> {
    fn new(source: &'a str) -> Self {
        Self {
            source,
            result: String::new(),
            source_index: 0,
        }
    }

    fn replace_range(&mut self, range: std::ops::Range<usize>, new_value: &str) {
        self.result
            .push_str(&self.source[self.source_index..range.start]);
        self.source_index = range.end;
        self.result.push_str(new_value);
    }

    fn replace_char(&mut self, index: usize, new_value: &str) {
        self.replace_range(index..(index + 1), new_value)
    }

    fn finish(mut self) -> String {
        self.result.push_str(&self.source[self.source_index..]);
        self.result
    }
}

impl Ast {
    pub fn visit<'a, T: Visitor<'a>>(&self, source: &'a str, visitor: &mut T) {
        for node in &self.0 {
            match node {
                AstNode::OpenBlock => visitor.open_block(),
                AstNode::CloseBlock => visitor.close_block(),
                AstNode::Declare(var) => visitor.declare(var.text(source)),
                AstNode::Use(var) => visitor.use_variable(var.text(source)),
                AstNode::PropertyUse { property, .. } => {
                    visitor.use_property(property.text(source))
                }
                AstNode::TemplateStart => {}
                AstNode::TemplateEnd => {}
                AstNode::ImportStart { .. } => visitor.import_start(),
                AstNode::ImportModulePart(part) => visitor.import_module_part(part.text(source)),
                AstNode::ImportDotPart => visitor.import_module_part("."),
                AstNode::ImportDotDotPart => visitor.import_module_part(".."),
                AstNode::ImportVariable { variable, alias } => visitor.import_variable(
                    variable.text(source),
                    alias.as_ref().map(|a| a.text(source)),
                ),
                AstNode::ImportStar { alias } => {
                    visitor.import_star(alias.as_ref().map(|a| a.text(source)))
                }
                AstNode::ImportEnd { .. } => visitor.import_end(),
            }
        }
    }
    pub fn rewrite<'a, T: Rewriter<'a>>(&self, source: &'a str, visitor: &mut T) -> String {
        let mut result = StringRewriter::new(source);
        let mut import_start_index = 0;
        for (i, node) in self.0.iter().enumerate() {
            match node {
                AstNode::OpenBlock => visitor.open_block(),
                AstNode::CloseBlock => visitor.close_block(),
                AstNode::Declare(var) => match visitor.declare(var.text(source)) {
                    RewriteAction::Replace(new_var) => result.replace_range(var.range(), &new_var),
                    RewriteAction::Keep => {}
                },
                AstNode::Use(var) => {
                    let replace_action = visitor.use_variable(
                        var.text(source),
                        PropertiesIter {
                            source,
                            nodes: &self.0[(i + 1)..],
                            index: 0,
                        },
                    );
                    match replace_action {
                        VariableRewriteAction::ReplaceVariable(new_var) => {
                            result.replace_range(var.range(), &new_var)
                        }
                        VariableRewriteAction::ReplaceAll(new_var) => {
                            result.replace_range(var.range(), &new_var);
                            for node in &self.0[(i + 1)..] {
                                match node {
                                    AstNode::PropertyUse { dot, property } => {
                                        result.replace_char(*dot, "");
                                        result.replace_range(property.range(), "");
                                    }
                                    _ => {
                                        break;
                                    }
                                }
                            }
                        }
                        VariableRewriteAction::Keep => {}
                    }
                }
                AstNode::PropertyUse { .. } => {}
                AstNode::TemplateStart => {}
                AstNode::TemplateEnd => {}
                AstNode::ImportStart { .. } => {
                    import_start_index = i;
                }
                AstNode::ImportModulePart(_) => {}
                AstNode::ImportDotPart => {}
                AstNode::ImportDotDotPart => {}
                AstNode::ImportVariable { .. } => {}
                AstNode::ImportStar { .. } => {}
                AstNode::ImportEnd { semicolon } => {
                    let start = match self.0[import_start_index] {
                        AstNode::ImportStart { keyword } => keyword.range().start,
                        _ => panic!("Expected import start node"),
                    };
                    let end = semicolon + 1;
                    // Even the Typescript compiler doesn't preserve comments when completely rewriting a part of the AST.
                    result.replace_range(start..end, "");
                }
            }
        }
        result.finish()
    }
}
