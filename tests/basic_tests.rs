use wgsl_linker_reference::parser::{
    Ast, AstNode, SpannedToken, Tokenizer, VariableSpan, WgslParseError, WgslParser,
};
use winnow::Parser;

fn tokenize(source: &str) -> Vec<SpannedToken> {
    Tokenizer::tokenize(source).unwrap()
}
fn parse(input: &str) -> Result<Ast, WgslParseError> {
    let tokens = Tokenizer::tokenize(input)?;
    let ast = WgslParser::parse(&tokens)?;
    Ok(ast)
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
    let source = "
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
    let parse_result = parse(&source);
    assert!(parse_result.is_ok());
    let parse_result = parse_result.unwrap();
    assert_eq!(
        parse_result
            .0
            .iter()
            .filter(|x| matches!(x, AstNode::Declare(_)))
            .count(),
        5
    );
    assert_eq!(
        parse_result
            .0
            .iter()
            .filter(|x| matches!(x, AstNode::TemplateStart))
            .count(),
        1
    );
}

#[test]
fn parse_atomics() {
    use PrintableNode::*;
    // Simplified version of https://github.com/bevyengine/naga_oil/blob/master/src/compose/tests/atomics/mod.wgsl
    let source = "var<workgroup> atom: atomic<u32>;
    
fn start() -> f32 {
    atomicStore(&atom, 1u);
    var y = atomicLoad(&atom);
    y += atomicAdd(&atom, 2u);
    let exchange = atomicCompareExchangeWeak(&atom, 12u, 0u);
    if exchange.exchanged {
        y += exchange.old_value;
    }
    return f32(y);
}";
    let parse_result = parse(&source).unwrap();
    assert_eq!(
        ast_to_printable(&parse_result, &source),
        [
            TemplateStart,
            Use("workgroup"),
            TemplateEnd,
            Declare("atom"),
            Use("atomic"),
            TemplateStart,
            Use("u32"),
            TemplateEnd,
            Declare("start"),
            OpenBlock,
            Use("f32"),
            OpenBlock,
            Use("atomicStore"),
            Use("atom"),
            Declare("y"),
            Use("atomicLoad"),
            Use("atom"),
            Use("y"),
            Use("atomicAdd"),
            Use("atom"),
            Declare("exchange"),
            Use("atomicCompareExchangeWeak"),
            Use("atom"),
            Use("exchange"),
            OpenBlock,
            Use("y"),
            Use("exchange"),
            CloseBlock,
            Use("f32"),
            Use("y"),
            CloseBlock,
            CloseBlock
        ]
        .to_vec()
    );
}

#[test]
fn for_loop() {
    use PrintableNode::*;
    let source = "
    for (var i = 0u; i < 10u; i++) {
        return f32(i);
    }";
    let mut t = Tokenizer::tokenize(source).unwrap();
    let parse_result = WgslParser::statements
        .parse(&mut t)
        .map_err(WgslParseError::from)
        .unwrap();
    assert_eq!(
        ast_to_printable(&parse_result, &source),
        [
            OpenBlock,
            Declare("i"),
            Use("i"),
            Use("i"),
            OpenBlock,
            Use("f32"),
            Use("i"),
            CloseBlock,
            CloseBlock
        ]
        .to_vec()
    );
}

#[test]
fn nested_template() {
    use PrintableNode::*;
    let source = "alias a = array<vec3<u32>>;";
    let parse_result = parse(&source).map_err(WgslParseError::from).unwrap();
    assert_eq!(
        ast_to_printable(&parse_result, &source),
        [
            Declare("a"),
            Use("array"),
            TemplateStart,
            Use("vec3"),
            TemplateStart,
            Use("u32"),
            TemplateEnd,
            TemplateEnd
        ]
        .to_vec()
    );
}

#[test]
fn ptr_uses_predeclared_enumerants() {
    use PrintableNode::*;
    let source = "alias function = i32;
    alias a = ptr<storage,function,read_write>;";
    let parse_result = parse(&source).map_err(WgslParseError::from).unwrap();
    assert_eq!(
        ast_to_printable(&parse_result, &source),
        [
            Declare("function"),
            Use("i32"),
            Declare("a"),
            Use("ptr"),
            TemplateStart,
            Use("storage"),
            Use("function"),
            Use("read_write"),
            TemplateEnd
        ]
        .to_vec()
    );
}

#[test]
fn break_if() {
    use PrintableNode::*;
    let source = "fn a(){
   loop{
     if(1<2){break;} 
     continuing{break if 1<2;}
   }
}
";
    let parse_result = parse(&source).map_err(WgslParseError::from).unwrap();
    assert_eq!(
        ast_to_printable(&parse_result, &source),
        [
            Declare("a"),
            OpenBlock,
            OpenBlock,
            OpenBlock,
            CloseBlock,
            OpenBlock,
            CloseBlock,
            CloseBlock,
            CloseBlock
        ]
        .to_vec()
    );
}

// TODO: Example with operators (including <, <<, >, >=, <<=, etc)

// TODO: Test per parser rule

#[derive(Debug, Clone, PartialEq, Eq)]
enum PrintableNode<'a> {
    Declare(&'a str),
    Use(&'a str),
    TemplateStart,
    TemplateEnd,
    OpenBlock,
    CloseBlock,
}

fn ast_to_printable<'a>(ast: &Ast, source: &'a str) -> Vec<PrintableNode<'a>> {
    ast.0
        .iter()
        .map(|node| match node {
            AstNode::Declare(var) => PrintableNode::Declare(var.text(source)),
            AstNode::Use(var) => PrintableNode::Use(var.text(source)),
            AstNode::TemplateStart => PrintableNode::TemplateStart,
            AstNode::TemplateEnd => PrintableNode::TemplateEnd,
            AstNode::OpenBlock => PrintableNode::OpenBlock,
            AstNode::CloseBlock => PrintableNode::CloseBlock,
        })
        .collect()
}
