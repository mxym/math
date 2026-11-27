# Dynamic SHA family: truncated-output buffer overrun

## Result

The historical NIST SHA-3 round-1 reference implementations of **Dynamic SHA** and **Dynamic SHA2** write a full 256- or 512-bit chaining value even when the caller requests the truncated 224- or 384-bit variant.

This is a reference-implementation memory-safety and API-conformance defect:

| requested digest | API buffer size | bytes written by `Final` | overrun |
|---:|---:|---:|---:|
| 224 bits | 28 | 32 | 4 bytes |
| 256 bits | 32 | 32 | 0 |
| 384 bits | 48 | 64 | 16 bytes |
| 512 bits | 64 | 64 | 0 |

The finding concerns two withdrawn competition candidates. It is **not** about standardized SHA-2 or SHA-3, and it is not a cryptanalytic break of the hash designs.

## Root cause

Both reference headers serialize the complete internal state into `hv`, then use the compression block size to decide how much to copy:

```c
t = state->blocksize / 16;
for (i = 0; i < t; i++) hashval[i] = hv[i];
```

For the 32-bit family, `blocksize == 512`, so 32 bytes are copied for both 224 and 256. For the 64-bit family, `blocksize == 1024`, so 64 bytes are copied for both 384 and 512. But `hashval` is storage for the requested `hashbitlen`-bit result, and both design documents specify truncation for 224 and 384.

The copy length should be derived from the requested digest size:

```c
t = (state->hashbitlen + 7) / 8;
```

All four supported lengths are byte-aligned, so this preserves the intended digest bytes and stops the overrun.

## Reproduction

Pinned sources:

- Dynamic SHA proposal: <https://eprint.iacr.org/2007/476.pdf>
- Dynamic SHA2 proposal: <https://ehash.isec.tugraz.at/uploads/5/5b/DyamicSHA2.pdf>
- NIST SHA-3 C API profile: <https://csrc.nist.gov/CSRC/media/Projects/Hash-Functions/documents/SHA3-C-API.pdf>
- Dynamic SHA reference mirror: <https://github.com/QudsLab/NextSSL/blob/60654bf63498464964f67973ea9669767ddf2790/algos/hash/dynamicsha-sha3r1/dynamicsha-384-sha3r1/upstream/DynamicSHA/Reference%20Implementation/dsha_ref.h>
- Dynamic SHA2 reference mirror: <https://github.com/QudsLab/NextSSL/blob/60654bf63498464964f67973ea9669767ddf2790/algos/hash/dynamicsha2-sha3r1/dynamicsha2-384-sha3r1/upstream/DynamicSHA_2/Reference%20Implementation/dsha2_Ref.h>

Use the supplied source-level checker:

```bash
python3 verify_copy_extent.py /path/to/dsha_ref.h /path/to/dsha2_Ref.h
```

Use the supplied two-canary C harness against either header-only implementation:

```bash
TMPDIR=/dev/shm gcc -O0 -std=c99 \
  -include '/path/to/dsha2_Ref.h' canary_harness.c -o canary
./canary
```

On x86-64 GCC with the pinned unmodified sources and an empty message:

```text
Dynamic SHA
224: expected=28 written=32 extra=4  suffix=c5af1c00
256: expected=32 written=32 extra=0
384: expected=48 written=64 extra=16 suffix=dc1efbd69dc50f4833ef670f9dd24684
512: expected=64 written=64 extra=0

Dynamic SHA2
224: expected=28 written=32 extra=4  suffix=cd8a82eb
256: expected=32 written=32 extra=0
384: expected=48 written=64 extra=16 suffix=82089dc171ebbd11ed895ff3c71fa01a
512: expected=64 written=64 extra=0
```

After applying `reference_fix.patch`, the canaries remain unchanged for all four variants; the intended first 28/32/48/64 digest bytes are unchanged.

## Impact and scope

A caller following the API and allocating exactly `hashbitlen / 8` bytes receives an out-of-bounds write for the 224- and 384-bit variants. Depending on the caller's layout, this can corrupt adjacent state. The extra bytes are the untruncated suffix of the final chaining value, so wrappers that deliberately hash into a larger scratch buffer and copy only the requested prefix avoid the overwrite.

No claim of remote exploitability is made. The result is a precise source-level defect, reproducer, and minimal repair.

## Prior-art boundary

Mouha et al., *Finding Bugs in Cryptographic Hash Function Implementations* (2019), reports that Dynamic SHA and Dynamic SHA2 fail its bit-exclusion/summary tests, but does not identify this copy-length overrun in its candidate-specific discussion: <https://pmc.ncbi.nlm.nih.gov/articles/PMC6512998/>.

NextSSL's generic adapter already uses an oversized scratch buffer and comments that some upstreams may write a full internal state. That is a public mitigation signal, so this note does **not** claim first disclosure. Its contribution is to isolate the exact shared line in both candidates, measure the 4/16-byte overwrite with a two-canary harness, and provide the minimal source fix.
