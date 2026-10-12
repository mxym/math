# Source provenance and public derivatives

This release distinguishes the exact audited input, the source files consumed by Lean, historical evidence, independent checks, and public-only metadata redactions. Hash records establish byte identity or an explicitly recorded derivation; they are not signatures, authorship assignments, or substitutes for proof checking.

## Exact input

The independent audit inspected `entry005-actual-truncation-sharpness-20261007.zip`, dated 2026-10-07:

- archive length: **835,939 bytes**;
- regular source/archive members: **290 files**;
- SHA-256: `85f444c30899ea9a5b76b7cb912ca10165f5c2302714d5ee199e033a69fd8074`.

The input identity is recorded in [INPUT_ARCHIVE.json](provenance/INPUT_ARCHIVE.json). [ORIGINAL_SOURCE_SHA256.json](provenance/ORIGINAL_SOURCE_SHA256.json) records the original source identities. These are the received-input anchors, not a claim that every public derivative has the same hash as its original.

All **125 mathematical modules** in `project/` remain byte-identical to that input. No theorem, definition, proof body, import, target quantifier, centroid, exponent, or mathematical assumption is edited by this release preparation.

Of the 290 original input members, 288 remain byte-identical. Two nonmathematical provenance records, `project/sources/delivery-lineage.json` and `project/sources/pyramid-provenance.json`, have public-copy redactions of private delivery identifiers. Selected independent evidence also redacts private identifiers and machine-specific absolute paths. [PUBLIC_DERIVATIVE_LEDGER.json](provenance/PUBLIC_DERIVATIVE_LEDGER.json) records the affected originals and public derivatives with their hashes. These edits are disclosure cleanup, not new proof evidence. The public release should be checked against its own `SOURCE_MANIFEST.json` and required-payload records; a public derivative must not be presented as byte-identical to its original.

The source's original reports and logs remain historical submitted evidence. Fresh independent checks are kept separately under [audit/](audit/).

## Public target identity

The independently retrieved public definition source is

- repository: `mxym/math`;
- commit: `3c6f6a1a53b0d524af50bd940c3f73f400b41516`;
- path: [`lean/Entry005/Targets.lean`](https://github.com/mxym/math/blob/3c6f6a1a53b0d524af50bd940c3f73f400b41516/lean/Entry005/Targets.lean);
- length: **4,644 bytes**;
- SHA-256: `8bc873bff65384b67b05d3d4fd405bdf9c728e0befb0e6ac355373fa3ded7c94`.

The complete source, not only selected names or statement excerpts, matches [project/formal/Entry005/Targets.lean](project/formal/Entry005/Targets.lean). The original halfspace-defined projection body, actual pyramid, actual volumes, global maximum predicate, own-centroid dilation, `sInf`, and exponent are preserved. Its introductory no-inhabitant and unproved-threshold comments are historical; see [THEOREM.md](THEOREM.md) for the current proved/open distinction.

The preserved mathematical paper snapshots and their source hashes are recorded in `project/sources/provenance.json`. Having those manuscripts in the package does not mean the entire manuscripts have been formalized.

## Inherited pyramid checkpoint

The predecessor is `entry005-actual-pyramid-20261007.zip`:

- length: **526,968 bytes**;
- members: **216 files**;
- SHA-256: `7cb50eb59e03ac286d9758aebd0a8b988e968e208c80d99e6f59f47711900bbd`.

All **102** inherited mathematical modules are byte-identical to this independently audited checkpoint. Its audit covered **714** public proof declarations and **1,499** module-owned declarations, with **54,678** recursive declarations replayed from an empty trust-level-zero kernel environment. The earlier checkpoint proves the actual finite-pyramid/B and same-body bridge. Its historical exclusions correctly say that it did not close the later literal truncation sharpness theorem.

The present increment adds **23** mathematical modules and **136** public exports, bringing the totals to **125** and **850**. Eight of the 136 exports are exact upstream simplex-volume proof reuse; the other 128 are new public proof bodies in this increment. These counts include supporting lemmas and do not certify novelty or priority. The present independent replay covers the entire current owned closure, including the inherited modules; it does not merely inherit the earlier audit's pass status.

Further inherited identity/reuse records remain under `project/sources/`, including the frozen affine source hashes, whole owner-module hashes, and narrow iid-helper provenance. The public packaging does not relabel inherited bodies as newly authored proofs.

## Selected OpenAI math reuse

The upstream revision is [`openai/math` at `adc7f1241b42e322a6451854ab7e4b4c146bf78a`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a).

For the current increment, the independently retrieved source is [`lean/OAI/Geometry/ProjectionBody/SimplexVolume.lean`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/ProjectionBody/SimplexVolume.lean). Its complete preserved copy has **8,604 bytes** and SHA-256 `1f920adc4ba0b89e411c2a31d862856901dc831b72097703c2073189bb38b674`.

[TruncationSimplexVolume.lean](project/formal/Entry005/TruncationSimplexVolume.lean) reuses an exact **6,404-byte prefix**, containing eight selected proof bodies:

- prefix SHA-256: `1f46e7403100ac3275e390508fbcb43a84f0792fa493cb96dad2e41d5f4d713f`;
- the remaining owned-file text only closes namespaces;
- the preserved complete upstream file and the reused prefix were both independently compared with the pinned source.

The inherited source also preserves its OpenAI/math `Model`, `Basic`, and `Brightness` reuse and documented affine adaptations. `Model` narrows the upstream umbrella import while retaining its declarations; the exact-body/whole-source and adaptation notices remain applicable. See `project/sources/PYRAMID_UPSTREAM_REUSE.md`, `project/sources/UPSTREAM_NOTICE.md`, and the preserved upstream sources. Neither these identity comparisons nor the selected closure replay audits the complete OpenAI/math repository.

## Compiler and dependency pins

- Lean **4.34.1**, official release commit `5045d0056413266e57c625dcd7c365b10e377c52`.
- Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- All nine dependency revisions and source URLs: [project/formal/lake-manifest.json](project/formal/lake-manifest.json).
- Declared compiler: [project/formal/lean-toolchain](project/formal/lean-toolchain).
- Recorded executable/toolchain identities: [TOOLCHAIN_FILES_SHA256.json](provenance/TOOLCHAIN_FILES_SHA256.json).

The audit compared actual dependency Git revisions and tracked source cleanliness with the lockfile. It used the official pinned compiled dependency cache and independently rebuilt missing official dependency modules from the earlier audit. It did not rebuild all mathlib or bootstrap the Lean compiler. The public replay creates fresh owned outputs and does not accept an old owned-module cache as a substitute.

## Three distinct manifest roles

1. **Current public payload:** `SOURCE_MANIFEST.json`, the public seal, [REQUIRED_PAYLOAD_SHA256.json](provenance/REQUIRED_PAYLOAD_SHA256.json), and the public derivative ledger describe the actual distributed files. Use `scripts/verify_integrity.py` for this release.
2. **Original 290-file truncation input:** the preserved `project/BUNDLE_MANIFEST.json` has **289** records, all of which matched the original input before the declared public metadata redactions. It remains an original-input record and is not the current public-copy manifest.
3. **Historical pyramid checkpoint:** `project/SOURCE_FILES_SHA256.json` has **215** records. Seven differ in the later truncation input: `README.md`, `TECHNICAL_REPORT.md`, `coverage.json`, `formal/lakefile.toml`, `formal/scripts/mathlib-modules.txt`, `scripts/bootstrap.sh`, and `sources/provenance.json`. This manifest was not designed for the current truncation snapshot and has not been regenerated to conceal that fact.

The old `project/scripts/replay_text_bundle.py` and `project/scripts/package_pyramid.py` consume the historical 215-record manifest. They are checkpoint-only tools and must not be used to validate or package this release. The original `bootstrap.sh → verify_truncation.py` path does not consume that old manifest; it checks dedicated mathematical source-hash tables and writes build logs inside its working copy. The public `scripts/bootstrap.py` therefore runs it in a disposable copy and then invokes the independent replay, leaving the sealed source payload unchanged.

## Attribution and rights

Existing source headers, upstream acknowledgments, copyright notices, and license texts are retained. This release adds no author name, new copyright assertion, or blanket license. See [LICENSE_NOTICE.md](LICENSE_NOTICE.md). A verification result is not a license grant, an external human endorsement, or a full-paper certification.

## Exact public-only metadata changes

The two original-input derivatives change only these values:

- `project/sources/delivery-lineage.json`: `base_library_file_id`.
- `project/sources/pyramid-provenance.json`: `owner_source_page`, `owner_frozen533_library_id`, and `frozen147_library_id`.

Private Library identifiers and the private Space link are replaced with explanatory placeholders; public repository commits, proof identity hashes, and the meaning of the source references remain. The independent technical/semantic/predecessor reports, independent summary, and two intended-failure logs likewise replace delivery IDs or absolute machine paths. Their original and public byte digests are explicitly linked in `PUBLIC_DERIVATIVE_LEDGER.json`. The borrowed dependency-license inventory is separately adapted to `project/formal/lake-manifest.json` and its exact hash; license bytes remain unchanged.

The independent audit's complete external artifact identities are compactly retained in `provenance/EXTERNAL_ARTIFACTS_REFERENCE.json.gz`: 4,620 non-owned modules, linked to their exact pinned source hashes. The public verifier accepts cached artifact families only when all retained artifact hashes match this reference. A missing or mismatched non-toolchain family is rebuilt from the pinned source into the fresh external overlay. Official toolchain files must match the complete toolchain inventory. No prior owned artifact directory appears on the public runner's Lean search path. These checks preserve the distinction between trusted pinned runtime inputs, source provenance, fresh owned compilation, and actual empty-kernel replay.

All retained `project/scripts/` are original or historical tools. In particular, `freeze_truncation.py`, `make_truncation_coverage.py`, and the old replay/package commands must not be run inside the sealed public tree. Only the public outer `scripts/` entry points below implement this derivative's integrity contract.
