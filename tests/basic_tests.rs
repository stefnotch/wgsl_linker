use wgsl_linker_reference::{
    parse,
    parser::WgslParser,
    parser_output::{Ast, AstNode, VariableSpan},
    token::SpannedToken,
    tokenizer::Tokenizer,
};
use winnow::Parser;

fn tokenize(source: &str) -> Vec<SpannedToken> {
    Tokenizer::tokenize(source).unwrap()
}

#[test]
fn translation_unit() {
    let source = "fn main() -> f32 {
    return 1.0;
}";
    assert_eq!(
        WgslParser::translation_unit
            .parse(&tokenize(&source))
            .unwrap(),
        Ast(vec![
            AstNode::Declare(VariableSpan((3, 7))),
            AstNode::OpenBlock,
            AstNode::Use(VariableSpan((13, 16))),
            AstNode::OpenBlock,
            AstNode::CloseBlock,
            AstNode::CloseBlock
        ])
    );
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
        return f32(arr[0]);
    }";

    assert!(parse(source).is_ok());
}

#[test]
fn attribute_bindings() {
    let source = "@group(0) @binding(0) var<storage> lights : LightStorage;

var<storage> lights1 : LightStorage;
override lights2 : LightStorage;

// Texture and sampler.
@group(1) @binding(0) var baseColorSampler : sampler;
@group(1) @binding(1) var baseColorTexture : texture_2d<f32>;";

    assert!(parse(source).is_ok());
}

#[test]
fn parse_attribute() {
    let source = "@group(0)";
    let t = Tokenizer::tokenize(source).unwrap();

    assert!(WgslParser::attribute.parse(&t).is_ok());
}

#[test]
fn parse_templates() {
    // Like in a var<private>
    {
        let source = "<private>";
        let t = Tokenizer::tokenize(source).unwrap();

        assert_eq!(
            WgslParser::template_args.parse(&t).unwrap(),
            Ast([
                AstNode::TemplateStart,
                AstNode::Use(VariableSpan((1, 8))),
                AstNode::TemplateEnd
            ]
            .to_vec())
        );
    }
    {
        let source = "<f32,8>";
        let t = Tokenizer::tokenize(source).unwrap();

        assert_eq!(
            WgslParser::template_args.parse(&t).unwrap(),
            Ast([
                AstNode::TemplateStart,
                AstNode::Use(VariableSpan((1, 4))),
                AstNode::TemplateEnd
            ]
            .to_vec())
        );
    }
}

#[test]
fn parse_bracketed_arguments() {
    let source = "( 0.0,  0.5)";
    let t = Tokenizer::tokenize(source).unwrap();
    assert_eq!(
        WgslParser::argument_expression_list.parse(&t),
        Ok(Ast::new())
    );
}

#[test]
fn parse_templated_expression() {
    {
        let source = "array<vec2f>(
    vec2( 0.0,  0.5),
  )";
        let t = Tokenizer::tokenize(source).unwrap();
        /*
        Debug printing using the following
        println!(
            "{}",
            WgslParser::expression
                .parse(&t)
                .map_err(|e| WgslParseError::from(e))
                .unwrap_err()
        );*/
        assert_eq!(
            WgslParser::expression.parse(&t),
            Ok(Ast([
                AstNode::Use(VariableSpan((0, 5))),
                AstNode::TemplateStart,
                AstNode::Use(VariableSpan((6, 11))),
                AstNode::TemplateEnd,
                AstNode::Use(VariableSpan((18, 22)))
            ]
            .to_vec()))
        );
    }
    {
        let source = "array<vec2f||3>(
          vec2( 0.0,  0.5)
        )";
        let t = Tokenizer::tokenize(source).unwrap();
        assert_eq!(
            WgslParser::expression.parse(&t),
            Ok(Ast([
                AstNode::Use(VariableSpan((0, 5))),
                AstNode::Use(VariableSpan((6, 11))),
                AstNode::Use(VariableSpan((27, 31)))
            ]
            .to_vec()))
        );
    }
}

#[test]
fn parse_hard_templates() {
    let source = "@binding(0) @group(0) var<uniform> frame : u32;
@vertex
fn vtx_main(@builtin(vertex_index) vertex_index : u32) -> @builtin(position) vec4f {
  let a = 1;
  const pos = array<vec2f, u32(3<5) + 2 + u32(a<a)>( // Cursed template
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
    assert!(parse(&source).is_ok());
}
