# Dynamic SHA family: truncated-output write defect

## Defensive finding

The historical NIST SHA-3 round-1 reference implementations of **Dynamic SHA** and **Dynamic SHA2** derive the final copy length from the compression block size rather than the requested digest size. As a result, callers that reserve exactly the documented output length for the truncated 224- or 384-bit variants can have adjacent storage overwritten.

| requested digest | documented output | implementation copy | excess |
|---:|---:|---:|---:|
| 224 bits | 28 bytes | 32 bytes | 4 bytes |
| 256 bits | 32 bytes | 32 bytes | 0 |
| 384 bits | 48 bytes | 64 bytes | 16 bytes |
| 512 bits | 64 bytes | 64 bytes | 0 |

This concerns two withdrawn competition candidates. It is **not** about standardized SHA-2 or SHA-3, and it is not a cryptanalytic break of either design.

## Root cause

Both reference headers serialize the complete chaining value and then use the compression block size to select the copy length:

```c
t = state->blocksize / 16;
```

That selects the full 256- or 512-bit state even for a truncated variant. The copy length must instead be derived from the requested output size.

## Remediation

For the four supported byte-aligned lengths, use:

```c
t = (state->hashbitlen + 7) / 8;
```

The supplied `reference_fix.patch` applies this minimal change to both reference headers. The intended output prefix is unchanged.

Existing integrations should also:

1. inventory any direct use of the original `Final` or one-shot `Hash` API;
2. ensure output storage is sized from the implementation's actual write contract until the implementation is patched;
3. prefer a patched implementation and retain bounds instrumentation in regression testing;
4. avoid treating an oversized scratch buffer as a substitute for correcting the upstream copy length.

The included `verify_copy_extent.py` is a non-executing static checker for the affected source formula and the resulting length table. It does not invoke the vulnerable implementation.

## Sources and scope

Pinned sources:

- Dynamic SHA proposal: <https://eprint.iacr.org/2007/476.pdf>
- Dynamic SHA2 proposal: <https://ehash.isec.tugraz.at/uploads/5/5b/DyamicSHA2.pdf>
- NIST SHA-3 C API profile: <https://csrc.nist.gov/CSRC/media/Projects/Hash-Functions/documents/SHA3-C-API.pdf>
- Dynamic SHA reference mirror: <https://github.com/QudsLab/NextSSL/blob/60654bf63498464964f67973ea9669767ddf2790/algos/hash/dynamicsha-sha3r1/dynamicsha-384-sha3r1/upstream/DynamicSHA/Reference%20Implementation/dsha_ref.h>
- Dynamic SHA2 reference mirror: <https://github.com/QudsLab/NextSSL/blob/60654bf63498464964f67973ea9669767ddf2790/algos/hash/dynamicsha2-sha3r1/dynamicsha2-384-sha3r1/upstream/DynamicSHA_2/Reference%20Implementation/dsha2_Ref.h>

Both design documents specify truncation for the 224- and 384-bit variants. The NIST API defines `hashbitlen` as the desired result length and `hashval` as storage for that result.

## Impact boundary

The defect can corrupt caller-adjacent state when an exact-size output allocation is used. The excess bytes are from the untruncated final chaining value. No claim of remote exploitability is made.

## Prior-art boundary

Mouha et al., *Finding Bugs in Cryptographic Hash Function Implementations* (2019), reports that Dynamic SHA and Dynamic SHA2 fail bit-exclusion/summary tests, but does not identify this copy-length defect in its candidate-specific discussion: <https://pmc.ncbi.nlm.nih.gov/articles/PMC6512998/>.

NextSSL's generic adapter uses an oversized scratch buffer and comments that some upstreams may write a full internal state. That is a public mitigation signal, so this note does **not** claim first disclosure. Its contribution is to isolate the exact shared copy-length error in both candidates and provide a minimal repair.
