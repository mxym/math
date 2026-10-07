# Final independent audit of the frozen Lean101 checkpoint

## Verdict

**PASS for the exact additive 101-export checkpoint. No release-blocking fix found.**

The frozen payload was not changed. Nothing was published. This pass concerns the 68 preserved finite/scalar exports, seven finite stochastic-matrix exports, and 26 Entry005 geometric/constant exports. It is not a certificate for the full sharp simplex theorem or avoidance main theorem. The separately developed actual-simplex-volume bridge is not present in this checkpoint and is not credited here.

## Independent reproduction

- Repeated two clean builds of all 21 active owned modules, under normal and optimized Python. Both succeeded using Lean 4.34.1, compiler 5045d0056413266e57c625dcd7c365b10e377c52, Lake 5.0.0-src+5045d00 and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
- All nine actual dependency checkouts match the reviewed official origins, exact locked revisions and clean-source checks. Dependency artifacts were copied to an isolated private cache before building; the frozen sources and shared dependency cache were not used as writable build destinations.
- All six freshly generated logical reports equal the frozen reports in both modes: 101 export/coverage/axiom records, 261 compiler declarations, 260 safe logical roots and five unproved Prop targets.
- All original 68 exact signatures, axiom sets and protected source/pin/reference/vendor bytes remain identical; all original 158 and prior stochastic ten compiler records retain exact types/kinds/axioms/flags.
- Independently repeated all supplied controls: 160 negative and 18 positive executions passed. The separate guard review added 216 negative and two positive checker executions plus 51 independent consistency checks.
- Every safe logical root passed recursive stored-type/body dependency traversal, with axiom sets contained in Classical.choice, Quot.sound and propext, and no reachable unsafe, partial or missing declaration. The sole excluded inherited compiler-generated partial evaluator is Mxym.BalancedRecursion.dimension._unsafe_rec (unsafe=false, partial=true); it is not a safe-root dependency.

## Mathematical scope and canonical volume

Source review and fresh canonical-volume checks confirm that projectedVolume uses the actual orthogonal image as a set of the target subspace, with that finite-dimensional real inner-product space's canonical Euclidean volume. It is not ambient d-dimensional volume of a hyperplane. A separate Lean example verifies canonical normalization through an orthonormal coordinate isometry, and another verifies definitional agreement with projectionVolumeSet.

The cap proof derives a closest point and supporting normal, constructs a perpendicular unit direction, proves the true hyperplane dimension d-1, gives a cap ball inside the outer projected body and disjoint from the inner body, applies actual Haar measure scaling, and proves the cube bound with canonical volume. The endpoint really proves

    d_H(K,P) <= (d-1)(M+1) eta^(1/(d-1))

for compact convex bodies with d >= 2, M >= 0, eta >= 0, B subset K subset P subset M B, and a genuine upper bound eta on every intrinsic hyperplane projection-volume deficit. Finite volumes are justified before toReal arithmetic. The independent CanonicalVolumeAudit.lean compiles a zero-deficit corollary giving equality of the actual bodies, with standard axioms only.

The seven stochastic results retain their explicit nonnegativity, column-sum and determinant premises; no geometric simplex-volume correspondence is assumed or inferred. The ten constant results establish positivity, not the threshold gate. The exact constants and main/local/sharpness definitions match the supplied public mathematical source. The corrected thresholdGateGoal and defect < epsilon clause are definitions, and the reconstructed correction patch exactly reproduces the delivered Targets.lean.

All five goals remain unproved definitions: sharpMainGoal, sharpLocalGoal, thresholdGateGoal, truncationSharpnessGoal and simplexMatrixVolumeInterfaceGoal. In particular, the entryDefect-to-projection-deficit bridge, cone law, Cauchy/Minkowski interfaces, integrated witnesses, maximum-simplex normalization, actual-simplex matrix/volume correspondence, same-centroid conversion, end-to-end assembly and truncation sharpness remain open within these frozen bytes.

## Packaging, preservation and provenance

The 452-file frozen inventory agrees exactly with the staged payload, fresh archive extraction and fresh application of the additive patch to the actual Git tree at 72d04aba5744ad940702e88a58073eb126229b6c. Hashes, lengths and file modes agree. All 109 prior file paths remain present. The Git-derived 406-change ledger equals EXACT_CHANGES.json. Both patch checking and application passed with --whitespace=error-all. Deterministic archive regeneration reproduced the original archive hash exactly.

MANIFEST covers all 450 non-self/checksum files, and CHECKSUMS covers all other 451 files. The seven unchanged imported source files and corrected Targets.lean were compared with actual received checkpoints; all received/integrated hashes and change classifications agree. The embedded target-correction string reconstructs the exact historical patch hash and applies cleanly.

The original six and stochastic two mathematical snapshots agree with actual pinned Git objects. The projection-cap public source was independently fetched at its precise GitHub commit/path and matches SHA256 9361999cfa4337500041da4b3fc824cd3676a07a22ffad0274e38346bf301b98. Its repository, commit, path and hash are present in PROVENANCE, coverage and payload inventories; no dedicated extra SOURCES.json is required to repair a missing pin.

Inherited verifier guards are preserved or strengthened, and no active 75-only total remains. Complete-payload scans found no machine-specific absolute paths, private communications, secret/token patterns, email addresses or private-key markers. No cache or compiled proof artifacts occur in the public payload. Existing OpenAI/math attribution and Apache-2.0 license remain intact; no new authored-work license is assigned. Public reporting accurately separates proved lemmas, typechecked definitions and missing interfaces.

## Exact frozen identities

- Inventory: 817feae77a2caa206b78899af35edd9478cd5046ce3fcd09d7dd8631404d70b4
- Additive patch: 04c06a67fa232d58adc1354d1c51667c8ae5a0e052e76c7ba5ffef142ac5d359
- Archive: 733cce917af25ef0e98a4c68e1396f011e0b37fcf7b48498ed76bcd7e38f7ec9

## Trust boundary and evidence

Official Lean/standard-library binaries and the pinned official dependency .olean cache remain trusted. All owned modules were rebuilt, but Lean/mathlib were not rebuilt from source, bootstrap was not rerun with fresh network downloads, and no separate external kernel checker was run. The exact frozen checkpoint was audited; this is not a review of later unrelated repository changes.

Evidence: AUDIT_SUMMARY.json, PACKAGING_VERIFICATION.json, FRESH_REPORT_EQUIVALENCE.json, RECEIVED_SOURCE_EQUIVALENCE.json, CanonicalVolumeAudit.lean, logs/reproduction-progress.log, both clean-build/verification/control logs, and guard-review/GUARD_SOURCE_SCOPE_REVIEW.md. Scripts audit_packaging.py and reproduce_build.sh reproduce the local packaging and cached-toolchain checks. The audit report is outside the frozen deliverable so its audited hashes stay unchanged.
