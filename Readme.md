
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

## TODO

- Source Maps https://github.com/kaleidawave/source-map
- Import statements
- Qualified names