use wgsl_linker_reference::parser::WgslParser;

#[test]
fn global_directive() {
    let source = "diagnostic(off,    derivative_uniformity);
/*hi*/
requires readonly_and_readwrite_storage_textures,/*a*/packed_4x8_integer_dot_product;
";
    /*"fn main() -> f32 {
        return f32(bind::arr[0]);
    }"*/

    assert!(WgslParser::parse(source).is_ok());
}

#[test]
fn global_directive_and_main() {
    let source = "diagnostic(off, derivative_uniformity);
    diagnostic(off, derivative_uniformity);
    diagnostic(off, derivative_uniformity);
fn main() -> f32 {
        return f32(bind::arr[0]);
    }";

    assert!(WgslParser::parse(source).is_ok());
}

#[test]
fn attribute_bindings() {
    let source = "@group(0) @binding(0) var<storage> lights : LightStorage;

// Texture and sampler.
@group(1) @binding(0) var baseColorSampler : sampler;
@group(1) @binding(1) var baseColorTexture : texture_2d<f32>;";

    assert!(WgslParser::parse(source).is_ok());
}
