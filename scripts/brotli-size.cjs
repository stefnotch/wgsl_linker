const brotli = require("brotli-wasm"); // https://github.com/httptoolkit/brotli-wasm/pull/39
const fs = require("node:fs");

const textEncoder = new TextEncoder();

const input = fs.readFileSync("./dist/wgsl_linker_bg.wasm", {
  encoding: "utf-8",
});

const uncompressedData = textEncoder.encode(input);
const compressedData = brotli.compress(uncompressedData);

console.log(
  "File was compressed to",
  compressedData.length,
  "bytes from an original size of",
  uncompressedData.length,
  "bytes"
);
console.log("That's", (compressedData.length / 1024).toFixed(2), "Kib");
