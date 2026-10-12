# Full affine-geometric avoidance theorem

**The original `MainTarget` is proved unconditionally in Lean.**

For every real ε with 0 < ε < 1, there is one compact set E ⊆ [0,1] with genuine Lebesgue measure strictly greater than 1 − ε such that, simultaneously for every real a ≠ 0, every real b, every real q with 0 < q < 1, and every natural N, some natural n ≥ N satisfies a qⁿ + b ∉ E.

The same E is chosen before a, b, q and N. The theorem covers all real parameters and arbitrarily late escaping terms. It is not a finite sample or a rational-parameter statement.

The closed theorem is [`ContinuumGeometric.geometric_main_target`](ContinuumGeometric/MainProof.lean), with type exactly [`ContinuumGeometric.MainTarget`](ContinuumGeometric/Target.lean). [`checks/ExactMain.lean`](checks/ExactMain.lean) independently states the whole theorem without using the target abbreviation, applies the proof in an empty context, checks definitional equality with the target, and verifies the ordinary interval normalization of Lebesgue measure.

## Read the proof

- [Self-contained proof roadmap](PROOF_ROADMAP.md): the construction, parameter order, finite probability calculation, open repair, strict measure budget and countable exhaustion
- [Theorem-to-module map](THEOREM_MAP.md): exact source lemmas and their roles
- [Independent semantic review](evidence/independent/SEMANTIC_REVIEW.txt): detailed checks of the mathematical meaning
- [Trust and scope](TRUST_AND_SCOPE.md): what verification establishes, and what it still assumes
- [Attribution and licenses](ATTRIBUTION.md): project provenance and preserved upstream notices

Some byte-preserved proof modules contain historical `OPEN` or `UNRESOLVED` comments. These describe earlier local stages. `smallCompactBlockerSpec_proved` now discharges that interface, and `geometric_main_target` has no blocker, probability, schedule or geometric premise. The current theorem and verification results determine the status.

## Reproduce

The standalone project pins Lean 4.34.1 (official commit `5045d0056413266e57c625dcd7c365b10e377c52`) and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. Every transitive dependency is locked in `lake-manifest.json`; do not run an unqualified `lake update`.

On a fresh Linux x86-64 machine with Python 3, git, tar, zstd and curl ≥ 7.81, after reading the script:

```sh
python3 scripts/reproduce.py --bootstrap --fetch-dependencies
```

This explicitly downloads the hash-verified official Lean release, materializes the supplied dependency lock and gets the selected official Mathlib caches. It requires network access to the official release/package/cache hosts. Provide ample disk space for the toolchain and dependencies; neither is bundled in this source release.

With an already installed exact toolchain and dependency project, reuse their caches read-only:

```sh
python3 scripts/reproduce.py \
  --lean-bin /path/to/lean-4.34.1-linux/bin \
  --dependency-project /path/to/pinned-project \
  --output /path/to/new-replay-evidence
```

The output directory must not exist. Use a directory outside this project, or the default top-level `replay-evidence/`; other output directories inside the frozen source tree are rejected. `--extra-mathlib /path/to/second-identical-pin/mathlib` can supply another exact-pin cache, also read-only. Every package HEAD and tracked source tree is checked. The Linux executable and all 17,750 recorded toolchain distribution files are checked against their recorded SHA-256 values. The script uses isolated outputs; it does not write into the supplied dependency project. Missing official modules are built from their pinned sources into its isolated overlay.

For ordinary interactive Lean use, this is also a conventional Lake project: with the pinned toolchain and dependency cache installed, `lake build` builds the proof library. The stronger release checks are performed by `scripts/reproduce.py`, not by `lake build` alone.

## What the release checks

1. Exact source and release hashes, forbidden proof-source escapes, and all 454 public theorem names
2. Every one of the 45 proof/specification modules plus the aggregate import, rebuilt into empty owned output
3. Literal closed `MainTarget`, fully expanded all-real statement, genuine Lebesgue measure, and boundary counterexamples
4. Actual defining-module ownership for all 1,164 owned declarations, including 25 outside the visible namespace prefix
5. Raw stored type/proof graph, printed axioms, and collected axioms agreeing for all 1,155 safe owned declarations and all 454 public roots
6. The complete 34,771-declaration main proof closure replayed into a fresh empty trust-level-zero official Lean kernel
7. The same production ownership guard rejecting an intentionally injected outside-namespace target axiom in an isolated control
8. 21 supplied positive controls, 22 failures for their intended mathematical diagnostics, and 1,176,885 exact arithmetic regression checks with identical normal/Python-`-O` results
9. Fail-closed package-integrity regressions against both production entry points under normal Python and `-O`

The original independent audit also rebuilt every owned module twice with byte-identical normal/optimized outputs and checked all 454 full graph closures in both Lean and Python. [Its public-clean evidence](evidence/independent/VERIFICATION.json) and [report](evidence/independent/AUDIT_REPORT.txt) are included. The separate public-package clean-extraction replay is documented in `evidence/release/VERIFICATION.json`. Its stored dependency graph, inventory and main-closure summary match the independent audit exactly. Compiled binaries can retain build-location metadata and are neither distributed nor claimed to be identical across different locations.

The complete proof graph is included compressed in `evidence/independent/COMPLETE_STORED_PROOF_GRAPH.json.gz`. All root closures can be reconstructed by following each node's `all_direct` edges; the main closure and concise public-root summaries are included. Redundant 454-root graph expansions are intentionally omitted.

## Scope and release identity

This verifies the original affine-geometric theorem only. The stronger power-controlled nonlinear-remainder / continuum-profile theorem remains a separate written result; it is not formalized by this release. There is no claim of novelty, priority, external professional-human peer review, practical numerical construction of E, or absolute infallibility.

All 46 mathematical Lean files and all original toolchain/Lake pins are byte-identical to the audited source archive (SHA-256 `747386b02dbd12ae6f7b763d79fdb1e9bd70ca1e195e1b84d943cb0bcff82cb5`, 1,657,406 bytes). This public package is a deliberately smaller derivative, with new public documentation and portable checks. [The change ledger](CHANGE_LEDGER.md), source hashes and evidence-derivative ledger explain every category of change. Private coordination, unrelated historical archives, dependency caches and compiled proof binaries are excluded.

`SOURCE_MANIFEST.json` hashes all distributable files except itself and `SHA256SUMS`; `SHA256SUMS` also hashes that manifest. The deterministic archive recipe is `scripts/make_archive.py`. The proposed workflow under `ci/` is a read-only CI draft; its location does not enable a GitHub Actions workflow.

## Packaging integrity revision 2

The revised build and archive commands share `scripts/release_integrity.py`. Both require `SOURCE_MANIFEST.json` and `SHA256SUMS` before running Lean, downloading dependencies or opening an output archive. An independently embedded exact file inventory covers every distributed source, check, script and report. The validator rejects missing or unlisted files, source symlinks, unsafe paths, duplicate JSON keys, changed provenance metadata, incorrect digests, and any incomplete or noncanonical checksum list. The shared validator additionally checks all 50 immutable original proof/configuration entries and the five preserved independent check-wrapper records, even if the outer manifest and checksums were regenerated. Only the documented top-level `.lake/`, `vendor/`, `replay-evidence/` and `.git/` runtime/VCS directories are excluded.

To verify the source package without installing Lean:

```sh
python3 scripts/reproduce.py --verify-release-only
python3 scripts/test_release_integrity.py --output /path/outside/project/packaging-controls.json
python3 -O scripts/test_release_integrity.py --output /path/outside/project/packaging-controls-optimized.json
```

The test harness mutates temporary copies only. Its 34 cases invoke both production entry points under ordinary Python and `-O`, including missing-manifest, omitted-and-changed target-wrapper, changed archive-identity and corrupted-checksum attacks. These are packaging checks, separate from the mathematical negative controls.

Internal unkeyed hashes establish consistency with the declared package, not independent authenticity. Verify the archive digest or repository commit through a trusted external source. A party able to rewrite every file, the validator and all metadata consistently can create a different internally consistent package. The source proof and exact theorem statements did not change in revision 2; [the packaging repair record](provenance/PACKAGING_REPAIR.json) and [regressions](provenance/PACKAGING_GUARD_CONTROLS.json) document the correction.
