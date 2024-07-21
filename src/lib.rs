// https://www.w3.org/TR/WGSL/#parsing

pub mod parser;
pub mod parser_output;
pub mod tokenizer;

// TODO: Get rid of the 'b lifetime
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
