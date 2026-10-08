# Independent final-copy review: C17 public evidence

Date: 2026-10-08 (UTC).

## Verdict

**PASS.** The projected public copy preserves the complete C17 mathematical proof and recorded verification coverage. The original delivered public archive was available to this reviewer, and every one of its 75 file members was directly compared with the proposed public copy. The path redactions are exactly the documented mechanical substitutions. No mathematical source, proof term, declaration graph, coefficient certificate, or verification result was removed or weakened.

This review executed Python static checks, exact integer reconstruction, and preparation-only positive/negative controls. **It did not execute the Lean compiler or kernel.** The earlier recorded Lean run and the separate source-level semantic review remain distinct evidence.

## 1. Reviewed snapshot and complete inventory

The initial frozen snapshot reviewed here had:

- 97 payload files under the formalization directory;
- `CURRENT_PUBLIC_MANIFEST.json` and `SHA256SUMS`, bringing that directory to 99 files;
- one separate additive note under the existing mathematical notes directory.

Its manifest SHA256 was `658bb671d85e7eeb48e319d1fa116afc7796b79a806afe79b1482c8848322094`; its checksum-file SHA256 was `e2c66924bf8982b95493df47c484f8d94d2a63eae4df7d1f75a81802059b673a`.

Every actual file was compared with the inventory, without ignoring cache directories or unexpected files. Every payload's byte count, SHA256, and Git blob hash matched. The checksum file covered every payload plus the current manifest, excluding only itself. The repository staging tree contained exactly this formalization and the one separately checked note.

Adding this review and its result requires regenerating the outer current manifest and checksum file. The hashes above intentionally identify the tested pre-review-addition snapshot; they are not presented as the checksums of the later augmented copy. Use the delivered current manifest for that copy.

## 2. Direct archive-to-public byte mapping

Historical input archive identity:

- Name: `chromatic_c17_lean_evidence_20261008_public.tar.gz`
- Size: 1,417,848 bytes
- SHA256: `3abea26096508a6a12a87eea65785bb37e7656fd13d496d6900e2f2d7c699617`

All 75 regular-file archive members are accounted for exactly once, with distinct public destinations:

- **62 files remain byte-identical.** This count includes the three historically labeled manifest/profile renames.
- **13 evidence files contain only machine-root substitutions.** They concern result/source locations, the interface-print command, dependency-path logs, recorded commands, environment/configuration data, input/search-path data, and run status.

For every projected file, the reviewer derived the five original root roles from the retained input configuration and run data, applied the documented substitutions in order, and compared the full resulting bytes with the public file. The five replacement tokens are `<LEAN_TOOLCHAIN>`, `<PROJECT_ROOT>`, `<PACKAGES_ROOT>`, `<CACHE_ROOT>`, and `<VERIFIER_ROOT>`. No undisclosed text edit is needed to reproduce the public bytes. Original and public lengths and hashes match `PUBLICATION_MAPPING.json` throughout.

The historical independent `AUDIT_REPORT.md` remains byte-identical. Its recorded JSON result contains only the same mechanical verifier-root substitution. The portable auditor's other changes were separately reviewed: relative input locations, bundled pinned kernel sources, explicitly historical checks for unavailable original assets, current/historical manifest handling, protected output locations, and an explicit rejection of Python optimization mode. Its proof-source, declaration-closure, axiom, command-consistency, and exact-arithmetic tests remain present.

The archive itself is not distributed. Its hash is accurately labeled as the identity of the historical input, rather than a checksum of a current downloadable asset. The two original checksum manifests and original profile are clearly renamed as historical. The main README expressly discloses that historical command and path records have been projected. The current outer inventory binds the bytes actually delivered.

The distinct, earlier unmodified execution archive was not provided to this reviewer. No claim of comparing that separate archive is made. This review completes the comparison against the original **delivered public archive**, which was available.

## 3. Mathematical and machine-evidence coverage is preserved

The three mathematical source modules, their three fresh-run source copies, all six compiled outputs, complete declaration inventory and dependency graph, root-closure data, mathematical proof, and exact certificates are byte-identical to the independently reviewed input.

The current portable check was actually rerun and re-established:

- 41 explicit plus 57 generated/auxiliary declarations, totaling **98**;
- **10,964** nodes reachable from all owned declarations and **10,929** in the five-root union;
- individual root closure counts of **8,828; 8,355; 7,831; 10,601; 6,947**, in the recorded root order;
- all type/value/structural edges closed inside the graph;
- no owned axioms, no unsafe or partial nodes, and exactly the three standard closure axioms `propext`, `Classical.choice`, and `Quot.sound`;
- all 98 per-declaration axiom reports matching the graph;
- source/checker bindings, all eight successful historical command records, the trust-zero empty-kernel replay summary, and the specific invalid-proof type-mismatch control;
- the independent reconstruction of all 18 C17 coefficients from 131,072 edge subsets and all four complete iteration rows, including **−28,272,276,537,344** at the third iterate's degree index 2.

These checks preserve the earlier semantic conclusion: the genuine cycle graph leads through all-natural-q proper-coloring counts and chromatic-polynomial uniqueness to actual absolute coefficients and the negative iterate. The public copy does not reduce that conclusion to checking a detached integer list.

## 4. Executed publication and preparation controls

The following passed on the frozen public snapshot or temporary copies:

1. Default `check_public.py` and the complete packaged `test_publication.py` suite.
2. Rejection of changed Lean source, truncated closure data, duplicate manifest entries, and an unexpected file.
3. Additional independent rejection of unlisted files inside `__pycache__`, a nested hidden cache directory, and a nested build-cache directory. Thus the full-inventory claim does not rely on silently excluding cache paths.
4. Rejection of an unexpected symbolic link.
5. Explicit failure of all four new public Python entrypoints under `-O`, with the assertion-required diagnostic.
6. Preparation-only operation with paths containing spaces. A synthetic executable designed to leave a marker if invoked was **never invoked**.
7. Independent confirmation that the prepared workspace receives the unchanged verifier driver and both checker sources, keeps the pinned configuration and case scope, and receives no archived owned `.olean` or `.ilean` files.
8. Rejection of an existing output directory, output inside the snapshot, missing toolchain assets, and audit-result output inside the snapshot.

Every original public-tree file remained byte-identical after testing. A byte scan of every staged file, including binary outputs, found none of the original machine-specific absolute-root prefixes. No encoding or hidden replacement archive was used to preserve those strings.

Preparation-only tests do not authenticate an installed Lean toolchain and do not establish a new Lean build. A user-requested fresh run must still execute the preserved driver's pin checks, compilation, full replay, and negative control in an existing appropriately prepared environment.

## 5. Scope and trust limits

The formalized result remains **C17 under endpoint-retaining zero extension**. C12, all larger cycles, the complete cycle classification, endpoint-deleting variants, novelty, and priority are not added to the Lean claim.

The earlier report's trust boundaries remain intact: the historical cache-stability check measures path/size/mtime metadata; the dependency/toolchain supply chain was not rebuilt by the independent reviewer; and static inspection of execution records is not a second kernel execution. The final-copy gate found no blocking defect in the proposed projected publication.
