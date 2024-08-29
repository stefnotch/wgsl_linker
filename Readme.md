
# WGSL Linker Implementation

Split your WGSL code into multiple files, and import it!


This is a straightforward implementation of the [WGSL importing specification](https://github.com/wgsl-tooling-wg/wgsl-import-spec/tree/main?tab=readme-ov-file#summary). It grew out of a personal experiment to implement a straightforward WGSL linker.

## Example

Write WGSL+ code such as

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

## Architecture

The overall idea is to
1. Parse the WGSL files, and extract the rough structure
2. Surgically modify the source codes, and link them together.

This project is split into two main parts: the parser and the linker. The parser is responsible for extracting a minimal AST from the WGSL source code. The linker is responsible for linking files, together with their AST, into a final WGSL module. It tries to implement the bare minimum to achieve this.

1. [Tokenizer](./src/parser/tokenizer.rs): Takes the text and splits it into tokens. Due to the complexity of this (nested comments), we are using a parser library to do this.
2. [Parser](./src/parser.rs): Does the actual parsing. Handles template lists by joining the two ambiguous parsing paths into one, and reporting which path was the correct one. Avoids the arbitrary lookahead. It produces [a minimal, partial AST](./src/parser/parser_output.rs).
3. [Linker](./src/linker.rs): Takes the source code, modifies it in memory using the parsed AST, and joins the files together.




## TODO

- Re-exports
- Source Maps https://github.com/kaleidawave/source-map
