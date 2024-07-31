use wgsl_linker_reference::{
    parse,
    parser::WgslParser,
    parser_output::{Ast, AstNode, Variable},
    tokenizer::Tokenizer,
};

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
        return f32(arr[0]);
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

    println!("{:?}", WgslParser::attribute(&mut &*t).unwrap());
}

#[test]
fn parse_templates() {
    // Like in a var<private>
    {
        let source = "<private>";
        let t = Tokenizer::tokenize(source).unwrap();

        assert_eq!(
            WgslParser::template_args(&mut &*t).unwrap(),
            Ast([AstNode::Use(Variable((1, 8)))].to_vec())
        );
    }
    {
        let source = "<f32,8>";
        let t = Tokenizer::tokenize(source).unwrap();

        assert_eq!(
            WgslParser::template_args(&mut &*t).unwrap(),
            Ast([AstNode::Use(Variable((1, 4)))].to_vec())
        );
    }
}

#[test]
fn parse_hard_templates() {
    let source = "@binding(0) @group(0) var<uniform> frame : u32;
@vertex
fn vtx_main(@builtin(vertex_index) vertex_index : u32) -> @builtin(position) vec4f {
  const pos = array<vec2f, u32(3<5) + 2>( // Cursed template
    vec2( 0.0,  0.5),
    vec2(-0.5, -0.5),
    vec2( 0.5, -0.5)
  );

  return vec4f(pos[vertex_index], 0, 1);
}

@fragment
fn frag_main() -> @location(0) vec4f {
  return vec4(1, sin(f32(frame) / 128), 0, 1);
}";
    let t = Tokenizer::tokenize(source).unwrap();

    assert_eq!(
        WgslParser::parse(&t).unwrap(),
        Ast([AstNode::Use(Variable((1, 8)))].to_vec())
    );
}
