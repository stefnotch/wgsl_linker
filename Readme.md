
# WGSL Linker Implementation

Split your WGSL code into multiple files, and import it!


This is a straightforward implementation of the [WGSL importing specification](https://github.com/wgsl-tooling-wg/wgsl-import-spec/tree/main?tab=readme-ov-file#summary). It grew out of a personal experiment to implement a straightforward WGSL linker.

## Example

Write WGSL+ code like

```wgsl
// common.wgsl
struct EncodedPatch { u: u32, v: u32 };
struct Patch { min: vec2<f32>, max: vec2<f32> };

fn patch_decode(encoded: EncodedPatch) -> Patch {
   // implementation ...
}
```

```wgsl
// my_code.wgsl
import ./common/{EncodedPatch, patch_decode};

@group(0) @binding(0) var<storage, read> patches : array<EncodedPatch>;

@compute @workgroup_size(64, 1, 1)
fn main(@builtin(workgroup_id) workgroup_id : vec3<u32>) {
    let patch_index: u32 = workgroup_id.x;
    let quad = patch_decode(patches_from_buffer.patches[patch_index]);
}
```

and then point the wgsl_linker at your code!

TODO: How? Example please.

## Running

This project is heavily test-driven. To run the tests 
```
cargo test
```

To continously run the tests

```
cargo watch -x test
```

## TODO

- Source Maps https://github.com/kaleidawave/source-map
