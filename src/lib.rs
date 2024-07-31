// https://www.w3.org/TR/WGSL/#parsing

pub mod linker;
pub mod parser;
pub mod parser_output;
pub mod rewriter;
pub mod token;
pub mod tokenizer;

#[derive(Debug)]
pub struct WgslParseError {
    pub message: String,
    pub position: usize,
    pub context: winnow::error::ContextError,
}

pub fn parse(input: &str) -> Result<parser_output::Ast, WgslParseError> {
    let tokens = tokenizer::Tokenizer::tokenize(input)?;
    let ast = parser::WgslParser::parse(&tokens)?;
    Ok(ast)
}
