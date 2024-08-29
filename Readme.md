
# WGSL Linker Implementation

This is a personal experiment to implement a straightforward WGSL linker. I am using this to experiment with different module syntaxes in ways which are hard to do in naga_oil.

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