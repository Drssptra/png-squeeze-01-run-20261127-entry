// png-squeeze: lossless PNG re-encoder. Decodes each 1280x720 RGBA screenshot,
// picks the smallest colour form (palette/grey/RGB/RGBA + tRNS key) and per-row
// PNG filter by screening with zlib, then re-deflates the winner with a custom
// optimal-parse DEFLATE (hash-chain matcher + dynamic Huffman). Deterministic.
// No environment secrets, no network, no file reads outside the input dir.
// (zdeflate tables first: the encoder's main loop runs at module load and
// needs the DEFLATE tables already initialized.)
// ---- RFC1951 tables ----
const LEN_BASE = [], LEN_EXT = [], LEN_CODE = new Uint16Array(259);
{
  const t = [[3,0,257],[11,1,265],[13,1,266],[15,1,267],[17,1,268],[19,2,269],[23,2,270],[27,2,271],[31,2,272],[35,3,273],[43,3,274],[51,3,275],[59,3,276],[67,4,277],[83,4,278],[99,4,279],[115,4,280],[131,5,281],[163,5,282],[195,5,283],[227,5,284],[258,0,285]];
  for (let k = 0; k < t.length; k++) {
    const [base, ext, code] = t[k];
    const next = k + 1 < t.length ? t[k + 1][0] : 259;
    for (let l = base; l < next; l++) { LEN_BASE[l] = base; LEN_EXT[l] = ext; LEN_CODE[l] = ext === 0 ? code + (l - base) : code; }
  }
}
const DIST_BASE = [], DIST_EXT = [], DIST_CODE = new Uint16Array(32769);
{
  const t = [[1,0,0],[2,0,1],[3,0,2],[4,0,3],[5,1,4],[7,1,5],[9,2,6],[13,2,7],[17,3,8],[25,3,9],[33,4,10],[49,4,11],[65,5,12],[97,5,13],[129,6,14],[193,6,15],[257,7,16],[385,7,17],[513,8,18],[769,8,19],[1025,9,20],[1537,9,21],[2049,10,22],[3073,10,23],[4097,11,24],[6145,11,25],[8193,12,26],[12289,12,27],[16385,13,28],[24577,13,29]];
  for (let k = 0; k < t.length; k++) {
    const [base, ext, code] = t[k];
    const next = k + 1 < t.length ? t[k + 1][0] : 32769;
    for (let d = base; d < next; d++) { DIST_BASE[d] = base; DIST_EXT[d] = ext; DIST_CODE[d] = code; }
  }
}

// ---- match finder: hash chains, capped walk ----
function findMatches(data) {
  const n = data.length;
  const bestLen = new Uint16Array(n);
  const bestDist = new Uint16Array(n);
  const HSIZE = 1 << 15;
  const head = new Int32Array(HSIZE).fill(-1);
  const prev = new Int32Array(n);
  const MAX_CHAIN = 1024;
  const GOOD_LEN = 258;
  for (let i = 0; i < n; i++) {
    if (i + 2 < n) {
      const h = ((data[i] << 10) ^ (data[i + 1] << 5) ^ data[i + 2]) & (HSIZE - 1);
      let cand = head[h];
      let bl = 0, bd = 0, steps = 0;
      const maxLen = Math.min(258, n - i);
      let budget = MAX_CHAIN;
      while (cand >= 0 && steps < budget) {
        const dist = i - cand;
        if (dist > 32768) break;
        // quick check: 3rd byte must match for a >=3 match
        let l = 0;
        if (data[cand] === data[i] && data[cand + 1] === data[i + 1] && data[cand + 2] === data[i + 2]) {
          // prune: to beat the current best length bl, the byte at bl must match;
          // otherwise this candidate cannot improve on bl, so skip the extension
          if (bl < 3 || data[cand + bl] === data[i + bl]) {
            l = 3;
            while (l < maxLen && data[cand + l] === data[i + l]) l++;
          }
        }
        if (l > bl) {
          bl = l; bd = dist;
          if (l >= maxLen) break;
          // good match found: shrink the remaining search (zlib-style);
          // a longer match further back is rarely worth the extra dist cost
          if (l >= 128) budget = Math.min(budget, steps + 128);
          else if (l >= 64) budget = Math.min(budget, steps + 256);
          else if (l >= 32) budget = Math.min(budget, steps + 512);
        } else if (l === bl && l > 0 && dist < bd) { bd = dist; }
        cand = prev[cand];
        steps++;
      }
      if (bl >= 3) { bestLen[i] = bl; bestDist[i] = bd; }
      prev[i] = head[h];
      head[h] = i;
    }
  }
  return { bestLen, bestDist };
}

// ---- optimal parse DP ----
// lengths at which the length-code (and hence the match cost) changes, plus
// the max length: within one length-code range every length costs the same,
// so only the range ends (and the best length itself) can be optimal edges
const LEN_EDGES = [3, 10, 12, 14, 16, 18, 22, 26, 30, 34, 42, 50, 58, 66, 82, 98, 114, 130, 162, 194, 226, 257, 258];
function parse(data, bestLen, bestDist, litCost, distCost) {
  const n = data.length;
  const cost = new Int32Array(n + 1);
  const prev = new Int32Array(n + 1);
  const plen = new Uint16Array(n + 1);
  cost.fill(0x3fffffff);
  cost[0] = 0;
  // cost of a match of length L (length-code part only; distance added per match)
  const lenCost = new Int32Array(259);
  for (let l = 3; l <= 258; l++) lenCost[l] = litCost[LEN_CODE[l]] + LEN_EXT[l];
  for (let i = 0; i < n; i++) {
    const c = cost[i];
    if (c === 0x3fffffff) continue;
    // literal
    const lc = c + litCost[data[i]];
    if (lc < cost[i + 1]) { cost[i + 1] = lc; prev[i + 1] = i; plen[i + 1] = 0; }
    const L = bestLen[i];
    if (L >= 3) {
      const d = bestDist[i];
      const dc = distCost[DIST_CODE[d]] + DIST_EXT[d];
      // every range-end length <= L (same distance d is valid for all of them)
      for (let e = 0; e < LEN_EDGES.length; e++) {
        const m = LEN_EDGES[e];
        if (m > L) break;
        const mc = c + lenCost[m] + dc;
        if (mc < cost[i + m]) { cost[i + m] = mc; prev[i + m] = i; plen[i + m] = m; }
      }
      // the best length itself, if it is not already a range end
      if (L > 3 && LEN_EDGES.indexOf(L) < 0) {
        const mc = c + lenCost[L] + dc;
        if (mc < cost[i + L]) { cost[i + L] = mc; prev[i + L] = i; plen[i + L] = L; }
      }
    }
  }
  // backtrack into tokens: arrays of [sym, dist] (sym<256 literal, else length code index w/ len)
  const toks = [];
  let j = n;
  while (j > 0) {
    const i = prev[j];
    const l = plen[j];
    if (l === 0) toks.push([data[i], 0]);
    else toks.push([l, bestDist[i]]);
    j = i;
  }
  toks.reverse();
  return toks;
}

// ---- length-limited Huffman (zlib trees.c gen_bitlen style) ----
function huffmanLengths(freq, maxBits) {
  const n = freq.length;
  const len = new Uint8Array(n);
  // heap of [freq, symbol]
  const heap = [];
  for (let s = 0; s < n; s++) if (freq[s] > 0) heap.push([freq[s], s]);
  if (heap.length === 0) return len;
  if (heap.length === 1) { len[heap[0][1]] = 1; return len; }
  heap.sort((a, b) => a[0] - b[0]);
  // build tree with two queues
  const nodes = heap.map(([f, s]) => ({ f, s, l: null, r: null }));
  let qi = 0;
  const q = nodes.slice();
  const combined = [];
  const takeMin = () => {
    const a = qi < q.length ? q[qi] : null;
    const b = combined.length ? combined[0] : null;
    if (b && (!a || b.f <= a.f)) return combined.shift();
    qi++;
    return a;
  };
  let root = null;
  while (true) {
    const a = takeMin(), b = takeMin();
    if (!b) { root = a; break; }
    combined.push({ f: a.f + b.f, s: -1, l: a, r: b });
  }
  const depth = (nd, d) => {
    if (nd.s >= 0) { len[nd.s] = d; return; }
    depth(nd.l, d + 1); depth(nd.r, d + 1);
  };
  depth(root, 0);
  // limit lengths to maxBits (zlib overflow redistribution, Kraft-driven:
  // each move reduces the Kraft sum by exactly 2^-maxBits, so iterate until
  // the code is exactly complete; the old overflow/2 count under-corrects
  // when over-long leaves sit deeper than maxBits+1)
  const blCount = new Int32Array(maxBits + 2);
  let overflow = 0;
  for (let s = 0; s < n; s++) {
    if (len[s] > maxBits) { overflow++; len[s] = maxBits; }
    if (len[s] > 0) blCount[len[s]]++;
  }
  if (overflow > 0) {
    // Kraft sum in units of 2^-maxBits; a complete code sums to 2^maxBits
    let kraftUnits = 0;
    for (let b = 1; b <= maxBits; b++) kraftUnits += blCount[b] * (1 << (maxBits - b));
    const target = 1 << maxBits;
    while (kraftUnits > target) {
      let bits = maxBits - 1;
      while (bits > 1 && blCount[bits] === 0) bits--;
      if (bits < 1 || blCount[maxBits] === 0) break; // cannot fix by moving; fallback below
      blCount[bits]--;
      blCount[bits + 1] += 2;
      blCount[maxBits]--;
      kraftUnits -= 1;
    }
    // reassign lengths by frequency order
    const syms = [];
    for (let s = 0; s < n; s++) if (freq[s] > 0) syms.push(s);
    syms.sort((a, b) => freq[b] - freq[a]);
    let idx = 0;
    for (let b = 1; b <= maxBits; b++) {
      for (let k = 0; k < blCount[b]; k++) len[syms[idx++]] = b;
    }
    // verify completeness; if the move loop could not finish, fall back to a
    // balanced complete code (2r symbols at k+1 bits, 2^k-r at k bits, where
    // k=floor(log2(nused)), r=nused-2^k): Kraft sums to exactly 1
    let check = 0;
    for (let s = 0; s < n; s++) if (len[s] > 0) check += 1 << (maxBits - len[s]);
    if (check !== target || idx !== syms.length) {
      for (let s = 0; s < n; s++) len[s] = 0;
      const m = syms.length;
      const k = Math.floor(Math.log2(m));
      const r = m - (1 << k);
      for (let j = 0; j < m; j++) len[syms[j]] = j < (1 << k) - r ? k : k + 1;
    }
  }
  return len;
}

function codesFromLengths(len) {
  const maxBits = Math.max(...len);
  const blCount = new Int32Array(maxBits + 1);
  for (const l of len) if (l) blCount[l]++;
  const nextCode = new Int32Array(maxBits + 1);
  let code = 0;
  for (let b = 1; b <= maxBits; b++) { code = (code + blCount[b - 1]) << 1; nextCode[b] = code; }
  const codes = new Uint32Array(len.length);
  for (let s = 0; s < len.length; s++) {
    if (len[s]) codes[s] = nextCode[len[s]]++;
  }
  return { codes, maxBits };
}

// ---- bit writer ----
class Bits {
  constructor() { this.bytes = []; this.acc = 0; this.nbits = 0; }
  put(code, len) {
    this.acc |= code << this.nbits;
    this.nbits += len;
    while (this.nbits >= 8) { this.bytes.push(this.acc & 255); this.acc >>>= 8; this.nbits -= 8; }
  }
  // codes are stored MSB-first in canonical form; reverse them for LSB-first output
  putRev(code, len) {
    let r = 0;
    for (let i = 0; i < len; i++) { r = (r << 1) | ((code >> i) & 1); }
    this.put(r, len);
  }
  finish() {
    if (this.nbits > 0) { this.bytes.push(this.acc & 255); this.acc = 0; this.nbits = 0; }
    return new Uint8Array(this.bytes);
  }
}

// ---- encode one dynamic-Huffman block from tokens ----
// DEFLATE requires a complete code for every alphabet it transmits: a single
// 1-bit code is incomplete, so make sure at least two symbols carry a length.
function ensureTwo(len) {
  let nz = 0, first = -1;
  for (let s = 0; s < len.length; s++) if (len[s] > 0) { nz++; if (first < 0) first = s; }
  if (nz === 0) { len[0] = 1; len[1] = 1; }
  else if (nz === 1) { len[first === 0 ? 1 : 0] = 1; }
  return len;
}

const CL_ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];
function encodeTokens(toks, litLen, distLen) {
  const { codes: litCodes } = codesFromLengths(litLen);
  const { codes: distCodes } = codesFromLengths(distLen);
  // code-length sequence for lit+dist lengths
  const all = [...litLen, ...distLen];
  let hlit = 286, hdist = 30;
  while (hlit > 257 && all[hlit - 1] === 0) hlit--;
  while (hdist > 1 && all[286 + hdist - 1] === 0) hdist--;
  const seq = [...litLen.slice(0, hlit), ...distLen.slice(0, hdist)];
  // RLE the sequence into (sym, extra) with 16/17/18
  const items = [];
  for (let i = 0; i < seq.length;) {
    const v = seq[i];
    if (v === 0) {
      let run = 0;
      while (i + run < seq.length && seq[i + run] === 0) run++;
      i += run;
      while (run >= 11) { const take = Math.min(run, 138); items.push([18, take - 11, 7]); run -= take; }
      if (run >= 3) { items.push([17, run - 3, 3]); run = 0; }
      while (run-- > 0) items.push([0, 0, 0]);
    } else {
      items.push([v, 0, 0]); i++;
      let run = 0;
      while (i + run < seq.length && seq[i + run] === v) run++;
      i += run;
      while (run >= 3) { const take = Math.min(run, 6); items.push([16, take - 3, 2]); run -= take; }
      while (run-- > 0) items.push([v, 0, 0]);
    }
  }
  const clFreq = new Uint32Array(19);
  for (const [s] of items) clFreq[s]++;
  const clLen = ensureTwo(huffmanLengths(clFreq, 7));
  const { codes: clCodes } = codesFromLengths(clLen);
  let hclen = 19;
  while (hclen > 4 && clLen[CL_ORDER[hclen - 1]] === 0) hclen--;
  const bw = new Bits();
  bw.put(1, 1); // BFINAL=1
  bw.put(2, 2); // BTYPE=10 dynamic
  bw.put(hlit - 257, 5);
  bw.put(hdist - 1, 5);
  bw.put(hclen - 4, 4);
  for (let k = 0; k < hclen; k++) bw.put(clLen[CL_ORDER[k]], 3);
  for (const [s, extra, ebits] of items) {
    bw.putRev(clCodes[s], clLen[s]);
    if (ebits) bw.put(extra, ebits);
  }
  for (const [sym, dist] of toks) {
    if (dist === 0) {
      bw.putRev(litCodes[sym], litLen[sym]);
    } else {
      const lc = LEN_CODE[sym];
      bw.putRev(litCodes[lc], litLen[lc]);
      if (LEN_EXT[sym]) bw.put(sym - LEN_BASE[sym], LEN_EXT[sym]);
      const dc = DIST_CODE[dist];
      bw.putRev(distCodes[dc], distLen[dc]);
      if (DIST_EXT[dist]) bw.put(dist - DIST_BASE[dist], DIST_EXT[dist]);
    }
  }
  bw.putRev(litCodes[256], litLen[256]); // end of block
  return bw.finish();
}

function adler32(bytes) {
  let a = 1, b = 0;
  for (let i = 0; i < bytes.length;) {
    const end = Math.min(bytes.length, i + 5552);
    for (; i < end; i++) { a += bytes[i]; b += a; }
    a %= 65521; b %= 65521;
  }
  return ((b << 16) | a) >>> 0;
}

export function zdeflate(data, iters = 2) {
  const { bestLen, bestDist } = findMatches(data);
  // fixed Huffman lengths for pass 1
  let litLen = new Uint8Array(286);
  for (let s = 0; s < 286; s++) litLen[s] = s < 144 ? 8 : s < 256 ? 9 : s < 280 ? 7 : 8;
  let distLen = new Uint8Array(30).fill(5);
  let toks = null;
  for (let it = 0; it < iters; it++) {
    toks = parse(data, bestLen, bestDist, litLen, distLen);
    // frequencies from tokens
    const lf = new Uint32Array(286);
    const df = new Uint32Array(30);
    for (const [sym, dist] of toks) {
      if (dist === 0) lf[sym]++;
      else { lf[LEN_CODE[sym]]++; df[DIST_CODE[dist]]++; }
    }
    lf[256] = 1;
    litLen = ensureTwo(huffmanLengths(lf, 15));
    distLen = ensureTwo(huffmanLengths(df, 15));
  }
  const body = encodeTokens(toks, litLen, distLen);
  const out = new Uint8Array(2 + body.length + 4);
  out[0] = 0x78; out[1] = 0x9c;
  out.set(body, 2);
  const ad = adler32(data);
  out[out.length - 4] = (ad >>> 24) & 255;
  out[out.length - 3] = (ad >>> 16) & 255;
  out[out.length - 2] = (ad >>> 8) & 255;
  out[out.length - 1] = ad & 255;
  return out;
}


import { readFileSync, writeFileSync, readdirSync, mkdirSync } from 'node:fs';
import { join } from 'node:path';
import { deflateSync, inflateSync, constants as Z } from 'node:zlib';

// ---------- CRC32 ----------
const CT = (() => { const t = new Int32Array(256); for (let n = 0; n < 256; n++) { let c = n; for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1; t[n] = c; } return t; })();
function crc32(b, s = 0, e = b.length) { let c = -1; for (let i = s; i < e; i++) c = CT[(c ^ b[i]) & 255] ^ (c >>> 8); return (c ^ -1) >>> 0; }
function pngOf(chunks) {
  let size = 8; for (const [, d] of chunks) size += 12 + d.length;
  const out = new Uint8Array(size); const v = new DataView(out.buffer);
  out.set([137,80,78,71,13,10,26,10], 0); let at = 8;
  for (const [ty, d] of chunks) {
    v.setUint32(at, d.length); for (let i = 0; i < 4; i++) out[at+4+i] = ty.charCodeAt(i);
    out.set(d, at+8); v.setUint32(at+8+d.length, crc32(out, at+4, at+8+d.length)); at += 12 + d.length;
  }
  return out;
}
function ihdrOf(w, h, ct) { const d = new Uint8Array(13); const v = new DataView(d.buffer); v.setUint32(0,w); v.setUint32(4,h); d[8]=8; d[9]=ct; return d; }

// ---------- filters ----------
function paeth(a,b,c){ const p=a+b-c, pa=Math.abs(p-a), pb=Math.abs(p-b), pc=Math.abs(p-c); return pa<=pb&&pa<=pc?a:(pb<=pc?b:c); }
function filterRow(t, cur, prev, bpp, out) {
  const n = cur.length;
  if (t===0) out.set(cur);
  else if (t===1) { for (let i=0;i<n;i++) out[i]=cur[i]-(i>=bpp?cur[i-bpp]:0); }
  else if (t===2) { for (let i=0;i<n;i++) out[i]=cur[i]-(prev?prev[i]:0); }
  else if (t===3) { for (let i=0;i<n;i++) out[i]=cur[i]-(((i>=bpp?cur[i-bpp]:0)+(prev?prev[i]:0))>>1); }
  else { for (let i=0;i<n;i++){ const a=i>=bpp?cur[i-bpp]:0, b=prev?prev[i]:0, c=prev&&i>=bpp?prev[i-bpp]:0; out[i]=cur[i]-paeth(a,b,c); } }
}
function signedSum(row){ let s=0; for(let i=0;i<row.length;i++){ const v=row[i]; s+= v<128?v:256-v; } return s; }

// ---------- decode ----------
function decodePng(bytes) {
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  let at = 8, header=null, palette=null, trns=null; const idat=[];
  while (at < bytes.length) {
    const len = view.getUint32(at);
    const type = String.fromCharCode(bytes[at+4],bytes[at+5],bytes[at+6],bytes[at+7]);
    const data = bytes.subarray(at+8, at+8+len); at += 12+len;
    if (type==='IHDR') { const dv=new DataView(data.buffer,data.byteOffset,13); header={w:dv.getUint32(0),h:dv.getUint32(4),ct:data[9]}; }
    else if (type==='PLTE') palette=data;
    else if (type==='tRNS') trns=data;
    else if (type==='IDAT') idat.push(data);
    else if (type==='IEND') break;
  }
  const {w,h,ct} = header; const ch={0:1,2:3,3:1,4:2,6:4}[ct]; const stride=w*ch;
  const raw = inflateSync(idat.length===1?idat[0]:Buffer.concat(idat));
  const samples = new Uint8Array(h*stride);
  for (let y=0;y<h;y++){
    const ft=raw[y*(stride+1)], src=y*(stride+1)+1, o=y*stride, p=o-stride;
    if(ft===0) samples.set(raw.subarray(src,src+stride),o);
    else if(ft===1){ for(let i=0;i<stride;i++) samples[o+i]=raw[src+i]+(i>=ch?samples[o+i-ch]:0); }
    else if(ft===2){ for(let i=0;i<stride;i++) samples[o+i]=raw[src+i]+(y>0?samples[p+i]:0); }
    else if(ft===3){ for(let i=0;i<stride;i++) samples[o+i]=raw[src+i]+(((i>=ch?samples[o+i-ch]:0)+(y>0?samples[p+i]:0))>>1); }
    else { for(let i=0;i<stride;i++){ const a=i>=ch?samples[o+i-ch]:0,b=y>0?samples[p+i]:0,c=y>0&&i>=ch?samples[p+i-ch]:0; samples[o+i]=raw[src+i]+paeth(a,b,c); } }
  }
  const n=w*h, rgba=new Uint8Array(n*4);
  if (ct===6) rgba.set(samples);
  else if (ct===2){ const key=trns? (trns[1]<<16)|(trns[3]<<8)|trns[5]:-1;
    for(let i=0,s=0,d=0;i<n;i++,s+=3,d+=4){ rgba[d]=samples[s];rgba[d+1]=samples[s+1];rgba[d+2]=samples[s+2]; rgba[d+3]=((samples[s]<<16)|(samples[s+1]<<8)|samples[s+2])===key?0:255; } }
  else if (ct===0){ const key=trns?trns[1]:-1;
    for(let i=0,d=0;i<n;i++,d+=4){ const g=samples[i]; rgba[d]=rgba[d+1]=rgba[d+2]=g; rgba[d+3]=g===key?0:255; } }
  else if (ct===4){ for(let i=0,s=0,d=0;i<n;i++,s+=2,d+=4){ rgba[d]=rgba[d+1]=rgba[d+2]=samples[s]; rgba[d+3]=samples[s+1]; } }
  else {
    for(let i=0,d=0;i<n;i++,d+=4){ const e=samples[i]; rgba[d]=palette[e*3];rgba[d+1]=palette[e*3+1];rgba[d+2]=palette[e*3+2]; rgba[d+3]=trns&&e<trns.length?trns[e]:255; } }
  return {w,h,rgba};
}

// ---------- analysis ----------
function analyse(rgba){
  const n=rgba.length>>>2; const u32=new Uint32Array(rgba.buffer, rgba.byteOffset, n);
  let opaque=true, grey=true; const counts=new Map(); let many=false;
  for(let i=0,d=0;i<n;i++,d+=4){
    if(rgba[d+3]!==255) opaque=false;
    if(rgba[d]!==rgba[d+1]||rgba[d]!==rgba[d+2]) grey=false;
    if(!many){ const c=u32[i]; const k=counts.get(c);
      if(k===undefined){ if(counts.size===256) many=true; else counts.set(c,1); } else counts.set(c,k+1); }
  }
  const colours = many?null:[...counts.keys()].map(c=>{ const b=new Uint8Array(Uint32Array.of(c).buffer); return {rgba:[b[0],b[1],b[2],b[3]], word:c, count:counts.get(c)}; });
  return {opaque, grey, colours};
}
function transparentKey(rgba, grey){
  let key=-1;
  for(let d=0;d<rgba.length;d+=4){ const a=rgba[d+3]; if(a===255) continue; if(a!==0) return null;
    const v=grey?rgba[d]:(rgba[d]<<16)|(rgba[d+1]<<8)|rgba[d+2]; if(key===-1) key=v; else if(key!==v) return null; }
  if(key===-1) return null;
  for(let d=0;d<rgba.length;d+=4){ if(rgba[d+3]!==255) continue;
    const v=grey?rgba[d]:(rgba[d]<<16)|(rgba[d+1]<<8)|rgba[d+2]; if(v===key) return null; }
  return key;
}
function samplesOf(rgba, ct){
  const n=rgba.length>>>2; if(ct===6) return rgba;
  const ch=ct===0?1:ct===4?2:3; const out=new Uint8Array(n*ch);
  for(let i=0,d=0,s=0;i<n;i++,d+=4,s+=ch){
    if(ct===0) out[s]=rgba[d];
    else if(ct===4){ out[s]=rgba[d]; out[s+1]=rgba[d+3]; }
    else { out[s]=rgba[d]; out[s+1]=rgba[d+1]; out[s+2]=rgba[d+2]; }
  }
  return out;
}
function paletteForm(rgba, colours, order){
  const lum=c=>299*c.rgba[0]+587*c.rgba[1]+114*c.rgba[2];
  const entries=[...colours].sort((x,y)=>{
    const ta=x.rgba[3]===255?1:0, tb=y.rgba[3]===255?1:0;
    if(ta!==tb) return ta-tb;
    if(ta===0&&x.rgba[3]!==y.rgba[3]) return x.rgba[3]-y.rgba[3];
    if(order==='luminance') return lum(x)-lum(y)||x.word-y.word;
    return y.count-x.count||x.word-y.word;
  });
  const index=new Map(entries.map((c,i)=>[c.word,i]));
  const plte=new Uint8Array(entries.length*3); let transparent=0;
  entries.forEach((c,i)=>{ plte[i*3]=c.rgba[0]; plte[i*3+1]=c.rgba[1]; plte[i*3+2]=c.rgba[2]; if(c.rgba[3]!==255) transparent=i+1; });
  const trns=transparent===0?null:Uint8Array.from(entries.slice(0,transparent),c=>c.rgba[3]);
  const n=rgba.length>>>2; const u32=new Uint32Array(rgba.buffer, rgba.byteOffset, n);
  const indices=new Uint8Array(n); for(let i=0;i<n;i++) indices[i]=index.get(u32[i]);
  return {plte, trns, indices};
}

// ---------- filtering ----------
const FMODE = 'screen';
const LEVEL = 9;
const MEMLEVEL = 9;
const STRATEGY = Z.Z_DEFAULT_STRATEGY;
const SEEN = new Uint32Array(65536);
function pairsOf(row, stamp){ let n=0; for(let i=1;i<row.length;i++){ const p=(row[i-1]<<8)|row[i]; if(SEEN[p]!==stamp){ SEEN[p]=stamp; n++; } } return n; }
function filtered(samples, w, h, bpp, mode){
  const stride=w*bpp, raw=new Uint8Array(h*(stride+1));
  const trial=Array.from({length:5},()=>new Uint8Array(stride));
  let stamp=0;
  for(let y=0;y<h;y++){
    const cur=samples.subarray(y*stride,(y+1)*stride), prev=y===0?null:samples.subarray((y-1)*stride,y*stride);
    const at=y*(stride+1); let type=0;
    if(typeof mode==='number') type=mode;
    else {
      let best=Infinity;
      for(let t=0;t<5;t++){
        filterRow(t,cur,prev,bpp,trial[t]);
        let cost;
        if(mode==='minsum') cost=signedSum(trial[t]);
        else if(mode==='pairs') cost=pairsOf(trial[t],++stamp);
        else {
          const before=raw.subarray(Math.max(0,at-32768),at);
          const row1=new Uint8Array(stride+1); row1[0]=t; row1.set(trial[t],1);
          cost=deflateSync(row1, before.length===0?{level:4,memLevel:9}:{level:4,memLevel:9,dictionary:before}).length;
        }
        if(cost<best){ best=cost; type=t; }
      }
    }
    raw[at]=type; filterRow(type,cur,prev,bpp,raw.subarray(at+1,at+1+stride));
  }
  return raw;
}

// ---------- encode one image ----------
function encode(rgba, w, h, id){
  const {opaque, grey, colours} = analyse(rgba);
  const forms=[];
  if(colours!==null){
    for(const order of ['count','luminance']){
      const p=paletteForm(rgba,colours,order);
      forms.push({ct:3,bpp:1,samples:p.indices,plte:p.plte,trns:p.trns});
    }
  }
  if(colours===null || grey){
    const key=opaque?null:transparentKey(rgba,grey);
    let ct, trns=null;
    if(grey){ ct=opaque||key!==null?0:4; if(key!==null) trns=Uint8Array.of(0,key); }
    else { ct=opaque||key!==null?2:6; if(key!==null) trns=Uint8Array.of(0,key>>>16,0,(key>>>8)&255,0,key&255); }
    forms.push({ct,bpp:{0:1,2:3,4:2,6:4}[ct],samples:samplesOf(rgba,ct),plte:null,trns});
  }
  const modes = FMODE==='screen' ? [0,1,2,3,4,'minsum','pairs','brute'] : [FMODE==='fixed4'?4:FMODE==='fixed0'?0:FMODE];
  let best=null;
  for(const f of forms){
    const chunks=(f.plte?12+f.plte.length:0)+(f.trns?12+f.trns.length:0);
    for(const m of modes){
      const data=filtered(f.samples,w,h,f.bpp,m);
      const z6=deflateSync(data,{level:6,memLevel:8});
      if(!f._best || z6.length < f._best.z6len){ f._best={mode:m,data,z6len:z6.length}; }
    }
    const b=f._best;
    const z9=deflateSync(b.data,{level:LEVEL,memLevel:MEMLEVEL,strategy:STRATEGY});
    const bytes=z9.length+chunks;
    if(best===null||bytes<best.bytes) best={f,z:z9,bytes,mode:b.mode,data:b.data};
    delete f._best;
  }
  // custom optimal-parse deflate on the winning form only; keep whichever is smaller
  const zd=zdeflate(best.data, 2);
  if(zd.length<best.z.length) best.z=zd;
  const chunks=[['IHDR',ihdrOf(w,h,best.f.ct)]];
  if(best.f.plte) chunks.push(['PLTE',best.f.plte]);
  if(best.f.trns) chunks.push(['tRNS',best.f.trns]);
  chunks.push(['IDAT',new Uint8Array(best.z)]);
  chunks.push(['IEND',new Uint8Array(0)]);
  return pngOf(chunks);
}

// ---------- main ----------
const I=process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O=process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for(const id of readdirSync(I).sort()){
  const img=decodePng(new Uint8Array(readFileSync(join(I,id,'image.png'))));
  mkdirSync(join(O,id),{recursive:true});
  writeFileSync(join(O,id,'image.png'), encode(img.rgba,img.w,img.h,id));
}
