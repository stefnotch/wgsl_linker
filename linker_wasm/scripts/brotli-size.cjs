const brotli = require("brotli-wasm"); // https://github.com/httptoolkit/brotli-wasm/pull/39
const fs = require("node:fs");

const input = fs.readFileSync("./dist/linker_wasm_bg.wasm");
const compressedData = brotli.compress(input);

console.log(
  "File was compressed to",
  compressedData.byteLength,
  "bytes from an original size of",
  input.byteLength,
  "bytes"
);
console.log("That's", (compressedData.length / 1024).toFixed(2), "KiB");
