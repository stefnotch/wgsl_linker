// https://www.w3.org/TR/WGSL/#parsing

pub mod linker;
pub mod parsed_module;
pub mod parser;
pub mod parser_output;
pub mod rewriter;
pub mod token;
pub mod tokenizer;

pub struct WgslParseError {
    pub message: String,
    pub position: usize,
    pub context: winnow::error::ContextError,
}

impl std::fmt::Debug for WgslParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "WgslParseError: {}", self.message)?;
        f.debug_struct("WgslParseError")
            .field("message", &"...")
            .field("position", &self.position)
            .field("context", &self.context)
            .finish()
    }
}

impl std::fmt::Display for WgslParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

pub fn parse(input: &str) -> Result<parser_output::Ast, WgslParseError> {
    let tokens = tokenizer::Tokenizer::tokenize(input)?;
    let ast = parser::WgslParser::parse(&tokens)?;
    Ok(ast)
}
