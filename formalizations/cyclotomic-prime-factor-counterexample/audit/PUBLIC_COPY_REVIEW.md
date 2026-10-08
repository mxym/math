# Public-copy gate review, 2026-10-08

**Result: PASS.** The public source/evidence projection preserves the mathematical content and the full static audit of the original CGF Conjecture 48 verification record. No reduced proof scope or evidence gap was found.

This reviewer ran the public default checker, independently compared the staged files with the original verification archive, reconstructed both complete graph files, and tested the reproduction wrapper in preparation-only mode. **No Lean installation, Lean invocation, source compilation, or kernel replay was performed by this reviewer.** The recorded machine execution remains the designated independent verification operator's 2026-10-08 run, 10:53:35–10:56:55 UTC.

## Reviewed input

The mathematical source checkpoint is fixed at commit `616877a1f3ac57ddc23737901581e666b0aabdd1`. The original verification archive is 18,311,823 bytes with SHA-256 `c2bcb597d513f9929eadd8bc749737a966ef9f919ee8040781609e02dac878d9`.

The input public inventory had SHA-256 `d0731c344ba34b8fb2b0fc05482fa5a33afaf0876b53e694b05936e1b7e7aa07`. At that checkpoint, the formalization directory contained 118 files, totaling 3,510,261 bytes. The separate accompanying verification note contained 2,471 bytes, for a combined 119 files and 3,512,732 bytes. These input counts precede this report's insertion and the small Python-version documentation correction. Use `CURRENT_PUBLIC_MANIFEST.json` and `SHA256SUMS` for the final published inventory; rerun the gate after inserting this report and rebuilding those inventories.

## Original-to-public mapping

Every one of the original archive's 112 files was accounted for. This reviewer independently checked the recorded original sizes and SHA-256 values against the actual original bytes, rather than relying solely on the publication mapping's assertions.

- All 86 exact-copy entries match their original bytes, including the historical manifests under their clearly labeled public names.
- Both large graph files decode from the ordered gzip/base64 parts to the complete original bytes. Their encoded fingerprints, reconstructed sizes and original SHA-256 values match. The public unpacker was also run into an external temporary directory, and its output was compared byte for byte with the original graphs.
- All 22 deliberately omitted `.olean`/`.ilean` entries match the actual original output sizes and hashes. They are absent from the public payload, and the public checker correctly describes their fingerprints as historical records rather than verified available binary bytes.
- The two original environment configurations agree with the single public projection after removing exactly the two documented administrative fields. Every retained parameter was compared directly with the original configuration. This review did not merely accept the packaging-time equivalence flag or fingerprint.

All 11 author Lean sources and all retained compile, replay, and negative-control logs remain byte-identical. The frozen mathematical certificate also remains byte-identical, with SHA-256 `64b10e5427ecaaaf9076e5d8b592831393db9fcb2b412c5894fd928d5fd4dfad`. No internal identifiers or Library recovery references were found in the public files or reconstructed graph bytes.

## Full audit retained

The portable public checker was read and compared with the original static audit. Its checks retain the full declaration inventory and complete graph, rather than a root-only, named-only, signature-only, or finite-coefficient substitute.

The actual default-check result confirms:

- 112 owned declarations: 73 named and 39 generated/private, with all author audit reports present exactly once.
- 29,737 nodes in the all-owned closure; every exported node is reachable from the owned declarations.
- 304,413 type-reference edges, 513,368 value-reference edges and 30,502 structural-reference edges, all closed within that graph.
- Root closure counts 29,681; 29,661; 29,581; and 29,553, with an exact union of 29,717.
- Every owned declaration's axiom set independently recomputed from the graph. The only closure axioms are `propext`, `Classical.choice`, and `Quot.sound`; no owned axiom or unsafe/partial mathematical declaration occurs.
- All 217 coefficients and 109 weights agree with the frozen certificate and the independent exact-integer arithmetic cross-check.
- The source/control hashes, generated checker text, original 73-entry fresh-run manifest, environment pins, recorded command ordering, imported-interface record, replay summary and expected negative-control error remain consistent.

The default public check and all 117 input checksum entries passed. The reviewer enumerated every file and directory, including hidden/cache locations, and found no unlisted files, unexpected directories or symlinks. Nothing in the source evidence tree changed as a side effect of running the gate.

## Preparation-only reproduction tests

The wrapper prepares a new workspace from the preserved verifier/checker sources and the full public environment profile. It uses the delivered author source directory; it does not depend on the omitted compiled outputs. The underlying verifier creates fresh output directories and compiles all 11 source modules before the all-owned replay and negative control.

The pinned execution remains Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`, and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, with the other eight package revisions in the supplied profile. Existing matching dependencies and their compiled libraries are required. The public Python entry points require Python 3.9 or later.

The reviewer used temporary placeholder assets to exercise preparation only. Prepared configuration and verification parameters matched the public profile except for the explicitly relocated toolchain, package and source paths. Copied verifier/control bytes matched exactly. A sentinel would have recorded any attempt to execute Lean; none occurred, and no task build was started. **This test establishes wrapper preparation behavior, not successful doctor checks, source compilation or end-to-end execution of `--run`.**

The following negative tests were run on temporary copies and behaved as required:

- Existing unpack or reproduction output directory: rejected without overwriting it.
- Unpack or reproduction destination inside the evidence snapshot: rejected without creating it.
- Missing required preparation assets: rejected without creating a workspace.
- Extra `__pycache__/extra.pyc` or `.lake/extra.lean` file: default check rejected the unlisted file.
- A changed author source byte or encoded graph byte: default check rejected the mismatch.
- Restoring the fixture to its original state restored a passing default check.

## Interpretation and finalization

The mathematical conclusion remains the complete refutation of the published basic/unimodal Conjecture 48, with genuine cyclotomic polynomials, all-natural-index unimodality, universal prime-index nondivisibility, and the nonzero-denominator-cleared q-integer identity. It does not establish minimum degree, global priority, external human peer review, or a separate formal rational-function division theorem.

Historical pending and mechanical-only status fields remain unchanged and are explained in the new overview. The author `verify.sh` was not run end to end by the recorded operator. The newly supplied `reproduce_lean.py --run` path was not executed during publication preparation or this review. No GitHub CI pass is asserted.

After this report is copied into the public tree, rebuild the complete public inventory and checksums and rerun both the default checker and the independent mapping/inventory gate. The final gate receipt should bind the resulting manifest, rather than modifying this historical input-snapshot identification.
