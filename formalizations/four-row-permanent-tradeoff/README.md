# Sharp four-row permanent–determinant inequality: kernel-checked main results

**Author:** Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology. Email: mxymmxym1@gmail.com.
ORCID: 0009-0000-3864-3536. No external funding; AI-assisted research.
Original new material: all rights reserved, subject to existing repository
licenses and third-party notices. This is not external peer review or a
mathematical priority assessment.

## Exact completed scope

For every actual complex 4-by-4 matrix A, including matrices with a zero row,
and every real c >= 0, this package proves

    |permanent A| + c |determinant A|
      <= max(3/2, 1+c) * product_i sqrt(sum_j |A_ij|^2).

It proves that this constant is optimal, that it is attained, and that the
supremum of the actual normalized objective is exactly `max(3/2,1+c)`.
For every real t it also proves

    sup_{A: product of row norms > 0}
        |permanent A + t determinant A| / product of row norms
      = max(3/2, 1+|t|),

with an explicit attaining matrix. The permanent and determinant are
Mathlib's `Matrix.permanent` and `Matrix.det`; the norm is the usual complex
modulus, and the row norm is the square root of the sum of squared moduli.
No finite sampling, scalar replacement model, geometric assumption package,
or unproved analytic bridge is used.

The underlying written source is [the four-row paper](../../notes/four-row-permanent-tradeoff/PAPER.md).
This proves its main sharp inequality and optimal constant in Theorem 1,
and its entire real-parameter norm assertion in Corollary 2. **The full
classification of all equality matrices, the all-n rectangular theorem,
pairwise stability, convex objectives, and tensorization are not covered
by this v1 certificate.** Attainment is not a classification of all maximizers.
See [the proof map](FORMALIZATION_MAP.md) and [the proof supplement](PROOF_SUPPLEMENT.md).

## Entry points

Import `FourRowTradeoff`. All statements below are in the namespace
`FourRowTradeoff`.

| Statement | Exact scope |
| --- | --- |
| `sharp_four_row` | The original-object inequality, with the row norm expanded |
| `matrix_bound_iff` | A real constant is a universal bound iff it is at least the sharp formula |
| `matrix_attainment` | Actual flat or identity matrix attains the formula |
| `exact_tradeoff_norm` | Supremum of the actual normalized simultaneous objective |
| `pencil_bound_iff` | Exact universal bound for every real pencil coefficient |
| `pencil_norm_isGreatest` | Greatest normalized pencil value, including attainment |
| `exact_real_pencil_norm` | The exact supremum in Corollary 2 |

## Versions and reproduction

Lean **4.34.1**, commit `5045d0056413266e57c625dcd7c365b10e377c52`.
Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`.
All transitive package revisions are pinned in `lake-manifest.json`.
Do not replace that manifest with an unpinned dependency update.

In this directory, with the specified Lean/Lake available:

```sh
lake exe cache get Mathlib.Analysis.Complex.Basic Mathlib.LinearAlgebra.Matrix.Permanent Mathlib.LinearAlgebra.Matrix.Determinant.Basic Mathlib.Tactic.Ring Mathlib.Tactic.Linarith Mathlib.Tactic.NormNum Mathlib.Tactic.FinCases
lake build
python3 reproduce.py
```

An existing pinned dependency project can be reused read-only:

```sh
python3 reproduce.py --dependency-project /path/to/pinned/project \
  --lean /path/to/lean-4.34.1/bin/lean \
  --work-dir /path/to/new-nonexistent-directory
```

The runner verifies its source manifest and every dependency commit,
records the actual toolchain binary hash, creates an empty own-build
directory, compiles every own module, and rechecks every named declaration
and its full dependency closure in a newly created Lean kernel at trust
level zero. It rejects any unexpected axiom or unsafe/partial declaration
in the proof closure, and checks that replayed types and universe parameters
are unchanged. It checks source hashes again after verification.

The meta-level dependency collector in `Replay.lean` is adapted from the
repository's Gaussian/continuum replay tooling. That collector is not a
mathematical premise and is outside the replayed proof closure. Computed
permutation enumeration uses kernel `decide`, not `native_decide`.
No compiled `.olean` files are published. A separate [clean Lake build](evidence/v1/LAKE_BUILD.json) also succeeded with all six local module roots registered.

## This run's evidence

The newly performed run in [evidence/v1/VERIFICATION.json](evidence/v1/VERIFICATION.json)
rebuilt **6 modules**, then replayed **67 named owned declarations** and
**14,151 dependency-closure declarations**. Its only axioms are `propext`,
`Classical.choice`, and `Quot.sound`. The run completed at **2026-10-09T05:21:09.126147+00:00**.
The timestamps are UTC; no older compilation or replay is relabeled as this run.

`PROOF_SOURCES.json` binds the source modules, verifier, runner, and package
configuration to their SHA256 values. The evidence includes all fresh build
logs, the empty-kernel result, every root and dependency name, and hashes of
the compiled artifacts from that run. Byte identity of `.olean` serialization
on other platforms is not a claim or a prerequisite for the theorem.
