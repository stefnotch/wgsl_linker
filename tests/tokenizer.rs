use wgsl_linker_reference::{token::Token, tokenizer::Tokenizer};

#[test]
fn floats() {
    let sources = ["0x0.0", "0x0.0p1", "0xa.bp0h", "0XA.fp+2", "0x.fp0"];
    for source in sources.iter() {
        let tokens = Tokenizer::tokenize(source).unwrap();
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0].token, Token::Number);
    }
}

#[test]
fn tokenizer() {
    use Token::{Keyword, Number, Paren, Symbol, Word};
    let source = "@binding(0) @group(0) var<uniform> frame : u32;
@vertex
fn vtx_main(@builtin(vertex_index) vertex_index : u32) -> @builtin(position) vec4f {
const pos = array(
  vec2( 0.0,  0.5),
  vec2(-0.5, -0.5),
  vec2( 0.5, -0.5)
);

return vec4f(pos[vertex_index], 0, 1);
}

@fragment
fn frag_main() -> @location(0) vec4f {
return vec4(1, sin(f32(frame) / 128), 0, 1);
}
";
    let tokens = Tokenizer::tokenize(source)
        .unwrap()
        .into_iter()
        .map(|t| t.token)
        .collect::<Vec<_>>();
    assert_eq!(
        tokens,
        [
            Symbol('@'),
            Word("binding"),
            Paren('('),
            Number,
            Paren(')'),
            Symbol('@'),
            Word("group"),
            Paren('('),
            Number,
            Paren(')'),
            Keyword("var"),
            Symbol('<'),
            Word("uniform"),
            Symbol('>'),
            Word("frame"),
            Symbol(':'),
            Word("u32"),
            Symbol(';'),
            Symbol('@'),
            Word("vertex"),
            Keyword("fn"),
            Word("vtx_main"),
            Paren('('),
            Symbol('@'),
            Word("builtin"),
            Paren('('),
            Word("vertex_index"),
            Paren(')'),
            Word("vertex_index"),
            Symbol(':'),
            Word("u32"),
            Paren(')'),
            Symbol('-'),
            Symbol('>'),
            Symbol('@'),
            Word("builtin"),
            Paren('('),
            Word("position"),
            Paren(')'),
            Word("vec4f"),
            Paren('{'),
            Keyword("const"),
            Word("pos"),
            Symbol('='),
            Word("array"),
            Paren('('),
            Word("vec2"),
            Paren('('),
            Number,
            Symbol(','),
            Number,
            Paren(')'),
            Symbol(','),
            Word("vec2"),
            Paren('('),
            Symbol('-'),
            Number,
            Symbol(','),
            Symbol('-'),
            Number,
            Paren(')'),
            Symbol(','),
            Word("vec2"),
            Paren('('),
            Number,
            Symbol(','),
            Symbol('-'),
            Number,
            Paren(')'),
            Paren(')'),
            Symbol(';'),
            Keyword("return"),
            Word("vec4f"),
            Paren('('),
            Word("pos"),
            Paren('['),
            Word("vertex_index"),
            Paren(']'),
            Symbol(','),
            Number,
            Symbol(','),
            Number,
            Paren(')'),
            Symbol(';'),
            Paren('}'),
            Symbol('@'),
            Word("fragment"),
            Keyword("fn"),
            Word("frag_main"),
            Paren('('),
            Paren(')'),
            Symbol('-'),
            Symbol('>'),
            Symbol('@'),
            Word("location"),
            Paren('('),
            Number,
            Paren(')'),
            Word("vec4f"),
            Paren('{'),
            Keyword("return"),
            Word("vec4"),
            Paren('('),
            Number,
            Symbol(','),
            Word("sin"),
            Paren('('),
            Word("f32"),
            Paren('('),
            Word("frame"),
            Paren(')'),
            Symbol('/'),
            Number,
            Paren(')'),
            Symbol(','),
            Number,
            Symbol(','),
            Number,
            Paren(')'),
            Symbol(';'),
            Paren('}')
        ]
        .to_vec()
    );
}
