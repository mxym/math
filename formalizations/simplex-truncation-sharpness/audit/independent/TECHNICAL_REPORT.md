# Independent audit result: literal truncation sharpness

**PASS for the literal `Entry005.truncationSharpness : truncationSharpnessGoal`. The full prescribed stability upper-bound Main remains open.**

## Exact artifact and source identity

- Library: `[private artifact identity omitted; see archive SHA-256]`, version 0.
- Backing file: `[private backing-file identity omitted]`.
- Filename: `entry005-actual-truncation-sharpness-20261007.zip`.
- Archive: 835939 bytes; 290 files; SHA-256 `85f444c30899ea9a5b76b7cb912ca10165f5c2302714d5ee199e033a69fd8074`.
- All 289 current `BUNDLE_MANIFEST.json` records match delivered file bytes and hashes. Every archive member also matches its extracted file.
- All 102 inherited mathematical modules are byte-identical to the earlier 714-public-proof pyramid bundle. Its 23 new modules bring this package to 125 mathematical modules.
- The 850 source-derived public proof names match exactly the inherited 714 plus 136 new exports. Eight of the new exports reuse exact upstream OpenAI simplex-volume proof bodies; these counts include supporting lemmas, not 850 new research results.
- The public `Targets.lean` was independently fetched from mxym/math at commit `3c6f6a1a53b0d524af50bd940c3f73f400b41516` and matches delivered bytes, SHA-256 `8bc873bff65384b67b05d3d4fd405bdf9c728e0befb0e6ac355373fa3ded7c94`.
- OpenAI/math `lean/OAI/Geometry/ProjectionBody/SimplexVolume.lean` was independently fetched at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The whole embedded upstream source matches. The copied 6404-byte prefix is exact, SHA-256 `1f46e7403100ac3275e390508fbcb43a84f0792fa493cb96dad2e41d5f4d713f`; the owned file only appends namespace closers.

## Independent build and runtime audit

Compiler: Lean 4.34.1, official release commit `5045d0056413266e57c625dcd7c365b10e377c52`. All nine dependency checkout revisions match the delivered lockfile and their tracked sources are clean. Mathlib is pinned to `d13f23b723b8a846827a245b89c10fc7d3f11612`.

The complete source import closure contains 4745 modules. All 125 owned mathematical modules were independently compiled from source into a fresh audit-owned output directory, with `autoImplicit=false`, zero warnings and zero failures. No package-supplied owned .olean files were used. Source and output SHA-256 values are recorded per module. All owned imports were already compiled as local regular files before their dependent module was built; this was independently checked against the exact source-derived topological import graph.

Dependencies use a sparse read-only overlay over the canonical official pinned cache, plus the earlier audit's independently rebuilt missing official dependency modules. No full mathlib copy was made, no canonical package was changed, and no cleared private generated cache was used. There were zero additional missing external dependencies for this increment. The 125-module source compilation took approximately 370 seconds.

The independent statement audit checks all 850 public proofs and their actual recursive axiom sets. The environment inventory identifies ownership by actual declaring module, not only namespace prefixes: all 1849 owned declarations, including private and generated declarations, were covered. All expected public names have the correct declaring module and are theorems. No owned declaration is unsafe, partial, an axiom, or an opaque constant. Only propext, Classical.choice and Quot.sound occur as logical axioms, or subsets thereof.

**Actual empty-environment kernel replay:** all 1849 owned declaration roots and the recursive dependency closure of **55163 declarations** replay successfully into `mkEmptyEnvironment 0`. No unsafe or partial node is accepted; no root is skipped. All replayed root types and universe parameters equal their original counterparts. The replay is not merely an import check. Its log is:

```
REPLAY_BEGIN roots=1849 closure=55163 skipped=[] trust=0 empty=true
ALL_SAFE_OWNED_EMPTY_KERNEL_REPLAY_PASS roots=1849 closure=55163
```

The final checker uses a sanitized search path with prior owned-cache fallbacks removed. The build had those older directories as lower-priority fallback search paths, but `fresh-output-resolution.json` proves every owned import resolved to its previously fresh-built local predecessor. Thus no inherited owned proof was skipped. The empty replay independently rechecks the complete proof closure irrespective of cached elaboration provenance.

A one-time audit-parser failure came from enabling `pp.universes true`, which prints `Classical.choice.{u}` and `Quot.sound.{u}`. The parser was corrected to normalize only printed universe suffixes; the exact API-based ownership axiom inventory already reported the standard names. No Lean source or proof was altered, and all successful original signature/ownership logs were retained. Final output is `INDEPENDENT_LITERAL_TRUNCATION_AUDIT_PASS`.

## Boundary and negative controls

1. Literal positive controls compile the exact expanded existential target and an arbitrary competitor T's volume comparison. This exercises the true global maximum quantifier.
2. Assigning `truncationSharpness` to `sharpMainGoal` fails with the expected type mismatch. The upper bound was not silently substituted.
3. Attempting to use the conditional sharpness assembly without its actual-defect formula premise fails with the expected type mismatch.
4. A deliberately malformed proof of True whose proof term is Nat.zero is rejected during trust-level-zero kernel replay. The negative-control harness itself then succeeds.
5. Independent exact rational checks at d=2,3,4,5,6 and t=1/10,1/2,9/10 verify all distinct horizontal/lifted facet minors, the actual rational formula, positivity, all finite-vertex maximum determinants, and the centroid lower witness. Deliberately reversing the bottom support sign and inserting an extra ordered-factorial factor both fail in every test. These 15 finite tests are corroboration only; the Lean proof supplies arbitrary dimensions and arbitrary inscribed competitors.

No mathematical counterexample was found. The semantic review separately checks the actual carrier, actual intrinsic areas/volumes/projections, the interior translation needed for positive support heights, ordered determinant sums, geometric-to-rational equality, arbitrary-point global maximality, same-original-centroid sInf, and the original real-power asymptotics.

## Packaging clarification required before public release

The root `SOURCE_FILES_SHA256.json` is inherited historical material from the 714-proof checkpoint: it has 215 records, with seven current mismatches (README, TECHNICAL_REPORT, coverage, formal/lakefile.toml, formal/scripts/mathlib-modules.txt, scripts/bootstrap.sh, sources/provenance.json). It is not the current archive manifest. The current `BUNDLE_MANIFEST.json` has 289 records and matches all files.

The documented reproduction path is `scripts/bootstrap.sh` → `scripts/verify_truncation.py`. It does **not** read the old manifest. It verifies four dedicated mathematical source-hash tables, the literal Targets hash, fresh source builds, expected public signatures/axioms, and actual module ownership. All 71 direct Mathlib imports used by owned modules are listed in the bootstrap's cache module list. Bootstrap shell syntax and verifier Python syntax were checked. The official download/bootstrap transaction itself was not repeated; the already verified pinned toolchain and canonical package cache were used.

Only the old `scripts/replay_text_bundle.py` and historical `scripts/package_pyramid.py` refer to `SOURCE_FILES_SHA256.json`. Consequently this is a current documentation/legacy-tool-scope clarification, not a mathematical defect or a failure of the documented proof verification path. Minimum future release fix: explicitly label `BUNDLE_MANIFEST.json` as authoritative for this release; mark/move the old manifest and old text-replay/package scripts as historical checkpoint-only. Do not regenerate the old manifest as though it described the new release, and do not edit immutable mathematical sources for this clarification. This audit did not modify the frozen bundle.

## Trust limits and non-claims

The selected proof closure was kernel-replayed from empty at trust level zero. We did not rebuild every file in mathlib or every file of OpenAI/math. Trust remains in the pinned Lean kernel implementation/runtime and the three standard logical axioms, together with the correspondence of the literal formal definitions to the intended mathematics, which was separately reviewed.

The certified sharpness statement chooses one genuine globally maximal simplex as an obstruction. It does not claim the formula for every maximizing simplex, a classification of all maxima, a best-maximum infimum, optimal upper constants, Banach–Mazur estimates, Rogers–Shephard estimates, or the full upper-bound Main. No push, merge, publication, file-sharing change, or mutation of the input source occurred.

## Evidence index

- `checks/FINAL_PASS.json`: final independent status.
- `checks/independent-verification.json`: artifact, count and trust summary.
- `checks/build.json`, `checks/fresh-output-resolution.json`: all 125 source compiles and exact import/output provenance.
- `checks/import-closure.json`, `checks/independent-pins.json`: 4745-module source closure and locked compiler/dependencies.
- `checks/owned-declarations.json`, `checks/public850-axioms.json`, `checks/ownership-summary.json`: complete API-based declaration inventory, types, owners and axioms.
- `logs/IndependentPublicAudit.log`, `logs/OwnedInventory.log`, `logs/ReplayAllSafeOwned.log`: direct compiler/kernel evidence.
- `checks/empty-kernel-replay.json`: exact 1849/55163 replay result.
- `checks/targets-upstream-fetch.json`, `checks/openai-upstream-fetch.json`, `checks/inherited-byte-identity.json`: source identity/reuse checks.
- `checks/manifest-provenance.json`: precise historical/current manifest distinction.
- `checks/exact-rational-controls.json`: independent finite rational corroboration.
- `SEMANTIC_REVIEW.md`: detailed semantic proof-chain review with source references.
