#!/usr/bin/env node
"use strict";

// Deterministic witness regeneration for fixed dimensions 4,5,6,7.
// Truth-table indices use least-significant ternary coordinate first.

const fs = require("fs");
const path = require("path");
const crypto = require("crypto");
const zlib = require("zlib");

const base = {
  1:  "000000000000000000000000000",
  3:  "111000000111000000111000000",
  6:  "210000000210000000210000000",
  7:  "110100000110100000110100000",
  9:  "100000000100000000100000000",
  12: "022202220021021021012201120",
  13: "012011012021102200212012012",
  14: "101101200011102001021110100",
  15: "012001122021102210012002112",
  16: "021002220200111112021102210",
  17: "201112221012201120022012212",
  18: "021021021000222111112012212",
  19: "011012212012212200010022011",
  20: "122010210201101220010021212",
  21: "021210102000011222120220120",
  22: "000100220021000102000220000",
  23: "000122122012020111012202011",
  24: "110210102211001212000110121",
  25: "011010201010020000011201022",
  26: "120111212210000020000000200",
  27: "100000000000000000000000000",
};

const rounds = [
  [3, 42581572, 7000, 1800000],
  [4, 10861014, 6700, 1950000],
  [5, 37118503, 6700, 2450000],
  [6, 71166928, 10500, 2350000],
];

function oneRound(previous, d, initialSeed, poolSize, samples) {
  let seed = initialSeed >>> 0;
  const M = 3 ** d;
  const R = n => {
    seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0;
    return Math.floor(seed / 2 ** 32 * n);
  };
  const C = Array.from({length: M}, (_, i) => i);
  const ps = Array.from({length: d}, (_, j) => 3 ** j);
  const digits = C.map(i => ps.map(p => Math.floor(i / p) % 3));
  const plus = digits.map(A => Uint16Array.from(digits, B =>
    A.reduce((s, x, j) => s + ps[j] * ((x + B[j]) % 3), 0)));
  const phase = digits.map(A => Uint8Array.from(digits, B =>
    A.reduce((s, x, j) => s + x * B[j], 0) % 3));
  const known = Object.values(previous).map(f => [...f].map(Number));

  function apply(f) {
    let sub = [0], fr = [];
    for (let i = 0; i < d; ++i) {
      let x;
      do x = 1 + R(M - 1); while (sub.includes(x));
      fr.push([0, x, plus[x][x]]);
      sub = sub.flatMap(v => [v, plus[v][x], plus[v][plus[x][x]]]);
    }
    const a = R(M), t = R(M), sgn = 1 + R(2), c = R(3);
    return C.map(i => {
      let v = a;
      for (let j = 0; j < d; ++j) v = plus[v][fr[j][digits[i][j]]];
      return (sgn * f[v] + phase[t][i] + c) % 3;
    });
  }

  function spectrum(f) {
    const a = Int32Array.from(f, ch => ch === 0 ? 1 : ch === 1 ? 0 : -1);
    const b = Int32Array.from(f, ch => ch === 1 ? 1 : ch === 0 ? 0 : -1);
    for (let step = 1; step < M; step *= 3) {
      for (let off = 0; off < M; off += 3 * step) {
        for (let j = 0; j < step; ++j) {
          const i = off + j, k = i + step, l = k + step;
          const a0=a[i],b0=b[i],a1=a[k],b1=b[k],a2=a[l],b2=b[l];
          a[i]=a0+a1+a2; b[i]=b0+b1+b2;
          a[k]=a0+b1-a1-b2; b[k]=b0-a1+a2-b2;
          a[l]=a0-b1+b2-a2; b[l]=b0+a1-b1-a2;
        }
      }
    }
    const out = new Int16Array(2 * M);
    for (let i = 0; i < M; ++i) { out[2*i]=a[i]; out[2*i+1]=b[i]; }
    return out;
  }

  const pool = Array.from({length: poolSize}, (_, i) => {
    const f = apply(known[R(known.length)]);
    if (i % 3 === 0) {
      for (let j = R(d === 3 ? 16 : 45); j > 0; --j) {
        const x = R(M);
        f[x] = (f[x] + 1 + R(2)) % 3;
      }
    }
    return {f, W: spectrum(f)};
  });

  function count(A, B, Cc) {
    let s = 0;
    for (let i = 0; i < 2 * M; i += 2) {
      const a=A[i],d0=A[i+1],b=B[i],e=B[i+1],c=Cc[i],f=Cc[i+1];
      s += Number(!!(a+b+c || d0+e+f));
      s += Number(!!(a+e-b-f || d0-b+c-f));
      s += Number(!!(a-e+f-c || d0+b-e-c));
    }
    return s;
  }

  const found = {};
  for (const [s, w] of Object.entries(previous)) found[s] = w.repeat(3);
  let attained = Object.keys(found).length;
  let used = 0;
  const target = 3 * M - 6;
  for (; used < samples && attained < target; ++used) {
    const A=pool[R(pool.length)], B=pool[R(pool.length)], Cc=pool[R(pool.length)];
    const s=count(A.W,B.W,Cc.W);
    if (!found[s]) {
      found[s]=[A.f,B.f,Cc.f].flat().join("");
      ++attained;
    }
  }
  if (attained !== target) throw new Error(`round n=${d+1}: ${attained}/${target}`);
  const missing=[];
  for(let s=1;s<=3*M;++s) if(!found[s]) missing.push(s);
  if (missing.join(",") !== "2,4,5,8,10,11") throw new Error(`bad missing n=${d+1}`);
  return {found, used, attained, finalSeed: seed};
}

function digestObject(o) {
  return crypto.createHash("sha256").update(JSON.stringify(o)).digest("hex");
}

const all={"3":base};
const metadata=[];
let previous=base;
for(const [d,seed,poolSize,samples] of rounds){
  const ans=oneRound(previous,d,seed,poolSize,samples);
  all[String(d+1)]=ans.found;
  metadata.push({dimension:d+1,seed,poolSize,samples,used:ans.used,
                 attained:ans.attained,finalSeed:ans.finalSeed,
                 witness_sha256:digestObject(ans.found)});
  console.error(`n=${d+1} attained=${ans.attained} used=${ans.used} sha256=${metadata.at(-1).witness_sha256}`);
  previous=ans.found;
}
const payload={format:"ternary Walsh truth tables; least-significant trit first",metadata,witnesses:all};
const out=path.join(__dirname,"witnesses-fixed.json.gz");
const encoded=JSON.stringify(payload)+"\n";
const zipped=zlib.gzipSync(Buffer.from(encoded),{level:9,mtime:0});
if(process.argv.includes("--write")) fs.writeFileSync(out,zipped);
else if(!fs.readFileSync(out).equals(zipped)) throw new Error("frozen gzip differs from regeneration");
console.log(JSON.stringify(metadata));
