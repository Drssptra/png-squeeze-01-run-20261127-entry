# png-squeeze

Lossless PNG re-encoder: squeezes 1280x720 RGBA screenshots into the smallest valid PNG.

`main.ts` (Node, no dependencies) decodes each screenshot, picks the smallest
colour form (palette by count/luminance, grey, RGB, RGBA, plus a tRNS key when a
single colour is fully transparent) and the best per-row PNG filter by screening
with zlib, then re-deflates the winning filtered data with a custom optimal-parse
DEFLATE (hash-chain matcher with best-length pruning, length-limited dynamic
Huffman). Deterministic: two runs produce byte-identical output. Falls back to
zlib level 9 whenever the custom parse is larger.

Run: `MAKEFUN_INPUT_DIR=<input> MAKEFUN_OUTPUT_DIR=<output> node main.ts`
