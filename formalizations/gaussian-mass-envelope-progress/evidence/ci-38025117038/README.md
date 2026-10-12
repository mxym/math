# Current-turn clean build and empty-kernel replay

Verified source commit: `46f8894ac0c2e36544a8db91c8434a560f1bd868`.
GitHub Actions run: https://github.com/mxym/math/actions/runs/38025117038
Job: `114134218003`. Artifact: `11659763816`.
Finished UTC: `2026-10-10T04:48:17.404693+00:00`.

All 9 modules freshly compiled from exact source; initially zero project objects.
The 47 named roots and their 53,046-declaration dependency closure were replayed
into an empty Lean kernel at trust level zero. The only axioms were `propext`,
`Classical.choice`, and `Quot.sound`. Both deliberate analytic mutations were
rejected. Source hashes were unchanged. See `verification.json` for per-source
and object SHA-256 hashes, pinned dependency source checks, commands and timings.
`closure.txt.gz` is a lossless copy of the actual replayed closure list.

Downloaded Actions artifact ZIP SHA-256:
`9e0023597d7840b71ce348af923e4f7a263a588bd3613f59719af9c16f6e6d96`.

This verifies the analytic hazard lemma, actual-measurable-set global upper bound,
and terminal-cell entropy bound. It does NOT verify the paper's staircase lower
construction, ordered residual entropy, or complete two-sided main theorem.
This is kernel verification, not external peer review.
