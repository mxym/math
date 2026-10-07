# Focused 002v4 verification repair and independent replay

7 October 2026. The checker repair has passed independent model-assisted review and normal/optimized offline replay. Mathematical claims and scope are unchanged. This is not external peer review, proof-assistant formalization or a novelty determination.

## What changed

The original audit inspected the relevant 002v4 and 006v2 sources at public commit [87868bcb65bf0460a90d6bc2efc3324e46481230](https://github.com/mxym/math/commit/87868bcb65bf0460a90d6bc2efc3324e46481230). Those target bytes remained unchanged through this repair's parent [72d04aba5744ad940702e88a58073eb126229b6c](https://github.com/mxym/math/commit/72d04aba5744ad940702e88a58073eb126229b6c). The repair changes exactly three 002v4 checkers, one definition-range sentence in sqrt2_period.md, and the v4 manifest.

- Require genuine integer arithmetic witness fields, rejecting floating-point roots in each of the three v4 failure checkers.
- Bind labelled sqrt(2) subset failures to their actual generator lists.
- Bind the historical positive sqrt(2) input to the stated order, generators and F8 step set, and the Gaussian endpoint to the stated five generators.
- Define the squarefree-q object for every squarefree q; retain the explicit small-prime list's q < 14 restriction.
- Refresh hashes for the repaired files and the previously stale PROOF_AUDIT.md entry.

The audit found six original adversarial acceptance gaps and one stale hash among 26 checked manifest/dependency entries. All 19 corruption controls reject after the repair, in normal and optimized Python. The three valid checker outputs remain byte-identical to the original recorded results. No certificate, historical v3 checker, paper theorem or stored replay output is changed. No 006 source changes are made.

## Delivered evidence

- [Original independent corruption-control source](adversarial_controls.py), with the three exact [original checker sources](original-checkers/preprints/002-quadratic-order-moats/v4/code/) supplied for offline comparison
- [Independent multiplication-image, lifted-graph and rational-control source](independent_replay.py), which does not import the submitted checker or generator
- [19-control result](evidence/controls.normal.json) and its [optimized counterpart](evidence/controls.optimized.json)
- [Independent exact replay result](evidence/independent.normal.json) and its [optimized counterpart](evidence/independent.optimized.json)
- [Original fixed-replay identity record](evidence/fixed-replays.json)
- [Source pins and exact five-file repair hashes](SOURCE_PINS.json), [evidence manifest](PACKAGE_MANIFEST.json), and [portable read-only runner](run.py)

The independent graph evidence contains 271 negative graphs, 28,489 failure-walk steps and three positive graphs. Gaussian F8 minimal period 130 and sqrt(2) F8 minimal period 14 retain their stated finite-principal-sieve hypotheses. The larger-jump controls fail for both displayed sieves and do not extend these results to unrestricted step sets. The separate rational robust-cover controls preserve the analytic hypothesis boundaries; finite replay does not formalize the infinite 006 argument.

## Reproduce offline

Use a complete extracted repository source tree or checkout at this publication commit. Python 3 is sufficient; no package install, network connection, credential or Git history is required.

From the repository root:

    python3 verification/2026-10-07-002v4-verification-repair/run.py

The runner checks all 40 pinned relevant source files and all 26 manuscript/dependency manifest bindings, then runs the repaired valid checkers, the 19 original-versus-fixed corruption controls, and the independent graph/rational reconstruction in normal and optimized Python. It compares byte-identical recorded outputs and rechecks source/evidence hashes afterward. It writes no repository file. Use --output with a destination outside the repository if a summary file is desired.

The supplied original corruption and independent replay scripts are byte-preserved from the audited delivery. The public wrapper only resolves repository-local inputs and packages the reproducible evidence; it does not change those mathematical checks. The package manifest excludes itself to avoid self-reference. The complete repository release manifest separately binds this evidence package and the five repaired files.
