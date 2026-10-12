# Source attribution and license scope

Maintained in mxym/math; developed with AI assistance. No personal author attribution is assigned by this release preparation.

## Mathematical source lineage

The 46 mathematical Lean source files come byte-for-byte from `geometric-lean-first-chain.zip`, version 3, dated 2026-10-07, 1,657,406 bytes, SHA-256:

`747386b02dbd12ae6f7b763d79fdb1e9bd70ca1e195e1b84d943cb0bcff82cb5`.

The original target has not been weakened. `ContinuumGeometric/Target.lean` has SHA-256 `5ac9c8a13941c709116fca8cc31a56ae9c1a5c85de9eabdd4d868d3a5358af55`, matching the original version 1 as independently checked. All 16 modules in the earlier reviewed 102-theorem version were retained byte-for-byte in the complete submitted proof. The public release includes the complete current proof, not the historical bundles.

The earlier arrangement proof contributed `SignFiberCount.lean`, `LineSignBound.lean`, `Planar.lean`, and the original common `Interfaces.lean`. The source archive records the transferred arrangement patch as 52,693 bytes with SHA-256 `720875184f31f945b6c6d701e0f620d513263f16939bf184606c35281c2945a6`. Its 40 public arrangement lemmas are retained unchanged. No separate named-person authorship or new license grant for that contributed proof is asserted here. The source-level attribution and mathematical names remain intact.

The remaining proof construction, its development history, and the independent AI/model audit are not presented as external professional-human peer review. Public explanatory documentation and portable reproduction wrappers were prepared after the independent audit. `CHANGE_LEDGER.md` separates immutable mathematical source from these new reporting files.

## Dependency and repository notices

The repository's existing provenance policy is reproduced and linked in [NOTICE.md](NOTICE.md). Upstream OpenAI/math material remains subject to its retained Apache-2.0 notice. This does not imply that every new or separate item has that license.

Lean 4.34.1 and the nine exact locked packages retain their own licenses, contributor copyrights and additional notices. [DEPENDENCIES.md](DEPENDENCIES.md) and [DEPENDENCY_PROVENANCE.json](DEPENDENCY_PROVENANCE.json) identify every official repository and revision. The project includes their unmodified applicable license texts, Lean's distribution `LICENSES` bundle, and importGraph's additional HTML-template notice in [third_party_licenses/](third_party_licenses/). Dependency source headers remain in the exact upstream repositories; dependency sources and binaries are not bundled here.

This release does not select a new license or add a blanket grant for separately authored proof, audit, documentation or wrapper material. Public availability and the licenses of dependencies should not be mistaken for such a grant.
