# Frozen Lean101 guard, source, inventory, and publicity review

**Verdict: PASS. No actionable defect found in this review's scope.**

Reviewed on 2026-10-07. The frozen stage was read-only throughout. Evidence and isolated negative fixtures were written only inside this guard-review directory. Build/replay and mathematical-semantic review are separate audit workstreams; this report does not claim to have independently rebuilt the project.

## Verification performed

- 51 independent consistency checks passed, recorded in `guard-audit-results.json` and reproducible with `audit_guards.py`.
- 218 independent axiom-checker executions passed: 2 positive baselines and 216 negative cases in ordinary and optimized Python. Each of the 101 theorem-output lines was independently omitted in each mode. Duplicate output, unexpected output, garbage/error output, duplicate inventory, `sorryAx`, a custom axiom, and `Lean.ofReduceBool` were also rejected. Fixtures are outside the frozen project. See `axiom-negative-controls.json`.
- The real frozen `check_pins.py`, `check_baseline.py`, and `check_previous_declarations.py` passed in both Python modes. These scripts are read-only; `GIT_OPTIONAL_LOCKS=0` prevented Git index refresh writes. See `pins-*.log`, `baseline-*.log`, and `prior-declarations-*.log`.
- Compiler/dependency record consistency was checked against all three frozen log sets: current, verification-normal, and verification-optimized. This is recorded-data validation, complementary to the parent audit's fresh compilation.

## Inherited guards and pins

Direct comparison used actual local Git objects from public68 commit `72d04aba5744ad940702e88a58073eb126229b6c`, not merely the delivered historical files.

`scripts/check_pins.py` and `scripts/bootstrap.sh` are byte-identical to public68. The compiler commit, fixed toolchain, complete nine-package allowlist, official origins, direct/transitive locked revisions, actual checkout origins, actual checkout revisions, tracked and untracked source cleanliness, and pinned bootstrap hash checks are retained. Actual pin checks passed.

The inherited source guard adds Entry005, `opaque`, `extern`, and `debug.skipKernelTC` rejection. Strict axiom-output parsing adds rejection of nonempty malformed or extraneous lines and requires exactly 101 distinct expected exports. Fresh signature and fresh axiom equality guards remain, and coverage generation adds a stale stored-inventory equality check. Compiler checks and complete stored-body traversal are added to the top-level verifier. Existing semantic and adverse-hypothesis controls remain, including the protected-theorem inventory sentinel. See `public68-guard-diff.txt`.

No active check is fixed to an obsolete total of 75. The `75-independent-declaration-inventory.json` filename correctly identifies historical 168-declaration evidence; 68 and 33 counts refer to preserved and additive subsets. The 158 original compiler declarations were separately compared field-by-field with the actual public68 compiler log (`prior-inventory-git-anchor.json`). Current checks preserve all 168 prior declarations and all 68 original theorem signatures/axioms/source paths.

## Public exports, compiler records, and goals

The exact same 101 names occur in the source export inventory, current coverage, current axiom report, and compiler-derived public source theorem inventory. There are 261 distinct owned compiler declarations: 207 theorem declarations and 54 definitions. Private helpers and compiler-generated equations explain the larger compiler theorem count; they are not presented as extra public source theorems.

All compiler-recorded axiom sets are standard. Every one of the 260 safe logical roots is represented exactly once in the dependency report; recursive body axioms agree with `collectAxioms`, with no unsafe, partial, or missing dependencies. The sole partial declaration is the inherited compiler-generated internal evaluator `Mxym.BalancedRecursion.dimension._unsafe_rec` (compiler flags: `unsafe=false`, `partial=true`); it is excluded as a logical root and unreachable from safe logical roots.

The five named target goals are compiler-recorded definitions of type `Prop`, absent from all 101 proved exports. `target-status.json`, README, completeness matrix, verification record, and provenance label them unproved. The threshold gate and small-positive-defect sharpness correction are not reported as proofs. Actual projection-deficit, simplex-volume, cone/Cauchy/Minkowski, integrated-witness, normalization, same-centroid, assembly, and truncation gaps remain explicit.

## Complete payload and source provenance

The release payload has 452 non-cache files. MANIFEST covers 450, excluding only itself and CHECKSUMS; CHECKSUMS covers the other 451 files including MANIFEST. Every manifest digest, length, and mode matches, and every original public68 path remains present. All 26 protected files agree both with their pinned hashes and the actual public68 Git blobs. All active proof sources are manifested, and the release excludes caches and compiled/binary proof artifacts.

The original six source snapshots and the two stochastic source snapshots were verified byte-for-byte against actual pinned Git objects. Exact received/integrated module hashes match the received checkpoint, with Targets.lean correctly recorded as the only target-corrected source.

Projection-cap source provenance is sufficient even without a dedicated `references/projection-cap/SOURCES.json`: PROVENANCE identifies the repository, exact commit, path and SHA256; geometry coverage names the exact commit/path; MANIFEST/CHECKSUMS pin the included bytes. Read-only GitHub fetch independently confirmed:

- `mxym/math` commit `3a1dbb9bab7ef72db726e8221deec925e0938c8d`
- `notes/sharp-simplex-stability/proof.tex`
- 22,992 bytes, SHA256 `9361999cfa4337500041da4b3fc824cd3676a07a22ffad0274e38346bf301b98`
- Exact byte agreement with `references/projection-cap/public-proof.tex`

See `projection-public-github-pin.json`. The local Git mirror lacks this later commit, so this one source was verified through the GitHub connector instead. This is an evidence-location limitation, not a source defect.

## Privacy, attribution, and publication scope

All 452 payload text files were scanned for machine-specific absolute paths, email addresses, common credential-token forms and private-key markers: no matches. Cache/config directories and compiled proof artifacts are excluded from the manifested public payload. Public text uses normalized paths. No private research originals, credentials or private communication were identified in the included payload.

OpenAI/math source attribution and Apache-2.0 license are preserved and protected. No new license is assigned to the authored work. Current documentation makes no novelty or whole-paper-formalization claim. The publication flag is false; this review performs no publication.

Official Lean/standard-library and pinned dependency binary caches remain disclosed trust dependencies. No Lean/mathlib source rebuild or external independent kernel-checker claim is made.

## Disposition

PASS within guard/source/inventory/publicity scope. No frozen-source correction requested. Final release disposition remains conditional on the independent fresh build/replay and mathematical scope workstreams.
