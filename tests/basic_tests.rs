use wgsl_linker_reference::{
    parse,
    parser::{Input, WgslParser},
    parser_output::{Ast, AstNode, Variable},
    tokenizer::Tokenizer,
};

#[test]
fn tokenizer() {
    use wgsl_linker_reference::token::Token::{Number, Paren, Symbol, Word};
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
            Word("var"),
            Symbol('<'),
            Word("uniform"),
            Symbol('>'),
            Word("frame"),
            Symbol(':'),
            Word("u32"),
            Symbol(';'),
            Symbol('@'),
            Word("vertex"),
            Word("fn"),
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
            Word("const"),
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
            Word("return"),
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
            Word("fn"),
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
            Word("return"),
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
    println!("{:?}", tokens);
}

#[test]
fn global_directive() {
    let source = "diagnostic(off,    derivative_uniformity);
/*hi*/
requires readonly_and_readwrite_storage_textures,/*a*/packed_4x8_integer_dot_product;
";

    assert_eq!(parse(source).unwrap(), Ast(vec![]));
}

#[test]
fn global_directive_and_main() {
    let source = "diagnostic(off, derivative_uniformity);
    diagnostic(off, derivative_uniformity);
    diagnostic(off, derivative_uniformity);
fn main() -> f32 {
        return f32(bind::arr[0]);
    }";

    println!("{:?}", parse(source).unwrap());
}

#[test]
fn attribute_bindings() {
    let source = "@group(0) @binding(0) var<storage> lights : LightStorage;

// Texture and sampler.
@group(1) @binding(0) var baseColorSampler : sampler;
@group(1) @binding(1) var baseColorTexture : texture_2d<f32>;";

    println!("{:?}", parse(source).unwrap());
}

#[test]
fn attribute_bindings1() {
    let source = "var<storage> lights : LightStorage;
";

    println!("{:?}", parse(source).unwrap());
}

#[test]
fn attribute_binding2() {
    let source = "override lights : LightStorage;
";

    println!("{:?}", parse(source).unwrap());
}

#[test]
fn parse_attribute() {
    let source = "@group(0)";
    let t = Tokenizer::tokenize(source).unwrap();

    println!("{:?}", WgslParser::attribute(&mut Input::new(&t)).unwrap());
}

#[test]
fn parse_templates() {
    // Like in a var<private>
    {
        let source = "<private>";
        let t = Tokenizer::tokenize(source).unwrap();

        assert_eq!(
            WgslParser::maybe_template_args(&mut Input::new(&t)).unwrap(),
            Ast([AstNode::Use(Variable((1, 8)))].to_vec())
        );
    }
    {
        let source = "";
        let t = Tokenizer::tokenize(source).unwrap();

        assert_eq!(
            WgslParser::maybe_template_args(&mut Input::new(&t)).unwrap(),
            Ast([].to_vec())
        );
    }
    {
        let source = "<f32,8>";
        let t = Tokenizer::tokenize(source).unwrap();

        assert_eq!(
            WgslParser::maybe_template_args(&mut Input::new(&t)).unwrap(),
            Ast([AstNode::Use(Variable((1, 4)))].to_vec())
        );
    }
}
