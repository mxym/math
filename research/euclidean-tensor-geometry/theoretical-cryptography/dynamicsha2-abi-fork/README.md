# An LP64 semantic fork and 32-bit zero-rotate UB in the Dynamic SHA2 reference implementation

**Status:** exact, executable implementation result.  
**Date checked:** 2026-11-27.  
**Scope:** the historical *Dynamic SHA2* first-round SHA-3 candidate and its
published C reference code. This is **not** the standardized SHA-2 family and
not a claim of a collision, preimage attack, or break of a deployed primitive.

## Result

The submitted Dynamic SHA2 header does not provide portable, architecture-independent
semantics for its 256-bit hash path.

The proposal describes the 224/256-bit path using sixteen 32-bit message words,
eight 32-bit working variables, and eight 32-bit chaining words. The reference
header, however, contains all three of the following:

```c
typedef unsigned long uint_32t;
unsigned long hashval[16];
#define ROTR32(x,n) (((x) >> (n)) | ((x) << (32 - (n))))
```

Consequently:

1. On an **LP64** C implementation, `unsigned long` is 64 bits. The
   224/256-bit path therefore performs additions, complements, and most state
   operations modulo 2^64, while `ROTR32` still contains the literal
   32. It is not the intended modulo-2^32 computation.
2. Truncating each final state word to 32 bits does not repair the error.
   Upper-half bits created by an earlier addition/left shift re-enter the low
   half through later right shifts.
3. On an implementation where the operand is actually 32 bits, a rotate count
   of zero evaluates `x << 32`, which is undefined by C. The empty-message
   padded block starts with `w[0] = 0x80000000`, hence the very first
   `ROTR32(..., w[0] & 31)` has count zero.

Thus the original source has a defined but widened LP64 function, while a
32-bit execution encounters undefined behavior on this minimal input. A
fixed-width, zero-safe implementation is required before the specification's
32-bit-word algorithm can be implemented portably.

## Minimal certificate

For the empty message and all eight outer message-injection loop iterations of
the 256-bit path:

| semantics | digest |
|---|---|
| specification-level, zero-safe 32-bit model | `8a9510725f8bc37cc1c3cf7488c77d18e25cee2cb386cb55614a09d32c4d047b` |
| original source on LP64 | `6de691d001c1dcb6b044a77251a8f8cd4612cb336222454a28ab1000c03b1516` |

The same divergence appears in all three reduced outer-loop variants used by
CryptanalysisBench:

| outer-loop iterations | specification-level fixed32 model | original LP64 build |
|---:|---|---|
| 2 | `e3491cc1781737fefd334b0e7e6bd7f40432706ac5716aab06d99cdab9f30ea9` | `895f5512d4a8ad4cdc5204be5e3c652592f50e4877ba14c57c8a989d28e70e91` |
| 4 | `a43c5d67f6435db7479e013e8f43ae3f06c5ea27c890866f304cb8f262da387e` | `3f082668a6e5cb1cebc3444201f2291c5d60e3267c2b7cc0f12dd054d55fbe2a` |
| 6 | `21e9768d735b1b5b35513a8848dede0aa6d915cddb9977f1d62b44bb24c9ad85` | `4accf68006adeeb9d09ab5ebfce2e54105779909af11f8e924bde57f95f0cce2` |
| 8 | `8a9510725f8bc37cc1c3cf7488c77d18e25cee2cb386cb55614a09d32c4d047b` | `6de691d001c1dcb6b044a77251a8f8cd4612cb336222454a28ab1000c03b1516` |

Three cross-checks were used:

* `verify_dynamicsha2_abi_fork.py` is a clean-room executable model of both
  semantics.
* A separate reviewer independently transcribed the 32-bit equations from
  Tables 2.1 and 2.3–2.6 of the designer PDF, without using the tested
  submission source, and obtained the same full-path empty digest
  `8a9510725f8bc37cc1c3cf7488c77d18e25cee2cb386cb55614a09d32c4d047b`.
* The unmodified reference header and the fixed header were separately compiled
  with GCC `-O3 -std=c99` on one x86-64 Linux host. The resulting C programs
  produced the same vectors as the model. These are observed build outputs,
  not a claim that every LP64 compiler must emit identical code.

Run the portable certificate:

```bash
python3 verify_dynamicsha2_abi_fork.py --self-test
```

## Proof sketch

Let `pi(x) = x mod 2^32`. If every operation were addition, Boolean
arithmetic, or left shift followed immediately by `pi`, then evaluating with
wider words and truncating at the end could sometimes commute with `pi`.
Here it does not. After a wide addition or `x << (32-n)`, the LP64 state may
contain nonzero bits 32 through 63. A later `x >> n`, with `1 <= n <= 31`,
moves some of those bits into positions below 32. In general,

```text
pi(ROTR32_LP64(x,n)) != rotr32(pi(x),n).
```

An independent transcription also localized the first low-word divergence. In
the first COMP call, the count-zero rotation produces `d9c88015` in fixed32
and `d9c88015d9c88015` on LP64; their low halves still agree. After both
initial COMP calls, all low state words still agree. The first message-free R1
step then derives rotation counts 5 (fixed32) and 7 (LP64), yielding low words
`d52a7fa9` and `754a9fea`. This explicitly shows widened state changing later
data-dependent control before final serialization.

The executable empty-message vector is a concrete witness for the whole
compression and finalization path.

## Repair

`reference_fix.patch` makes the word sizes explicit and makes zero-count
rotations defined. The essential changes are:

* use `uint32_t` for `uint_32t` and every 32-bit chaining-word slot;
* use `uint64_t` for the 64-bit alias;
* replace both rotate macros with fixed-width helpers that return `x` when the
  count is zero.

The fixed32 vectors agree with an independent transcription of the designer
PDF's equations. They have not yet been compared with the submission's KAT
archive; that remaining archival check does not affect the source-level
LP64/undefined-shift finding.

This repair is about portability and semantic correctness. It does not assert
that Dynamic SHA2 has modern collision or preimage security.

## Why this matters

A digest primitive used across different ABIs must name one function.
Architecture-dependent semantics can break KAT reproducibility, file digests,
sign/verify workflows, and cross-platform protocol interoperability. The
finding is therefore a real implementation defect even though it is not a
collision attack.

For the benchmark specifically, any result against the compiled LP64 binary
must be described as a result against that LP64-derived function, not silently
identified with the proposal's intended 32-bit function.

## Sources and reproducibility anchors

* [Dynamic SHA2 proposal](https://ehash.isec.tugraz.at/uploads/5/5b/DyamicSHA2.pdf)
  specifies 32-bit words for the 224/256-bit path.
* [Reference header mirror, pinned commit](https://github.com/QudsLab/NextSSL/blob/60654bf63498464964f67973ea9669767ddf2790/algos/hash/dynamicsha2-sha3r1/dynamicsha2-384-sha3r1/upstream/DynamicSHA_2/Reference%20Implementation/dsha2_Ref.h)
  contains the type aliases, state layout, rotate macros, and compression code.
* [CryptanalysisBench Dynamic SHA2 task, pinned commit](https://github.com/ethz-spylab/cryptanalysis-benchmark/tree/d243a0a03d7aa367472411114f140d0aace583cd/algorithms/T2_dynamicsha2)
  and its [build script](https://github.com/ethz-spylab/cryptanalysis-benchmark/blob/d243a0a03d7aa367472411114f140d0aace583cd/algorithms/T2_dynamicsha2/environment/algorithm_src/build_cli.sh)
  establish the current benchmark context and GCC command.
* [CryptanalysisBench paper](https://arxiv.org/abs/2607.18538) defines the
  verifier-driven research setting.
* [MiniMax practical-cryptanalysis report](https://www.minimax.io/blog/practical-cryptanalysis-with-minimaxs-latest-internal-model)
  motivated the reduced-scale, executable-witness workflow.

## Prior-art check

Before recording the result, searches were run over the web and GitHub for the
exact `typedef unsigned long uint_32t` line together with “Dynamic SHA2,” for
the two certified digests, and for Dynamic SHA2 portability/LP64/64-bit
implementation reports. The searches found the proposal, source mirrors, and
the benchmark, but no disclosure of this ABI fork or these vectors. This is a
best-effort negative search, not a proof of novelty.
