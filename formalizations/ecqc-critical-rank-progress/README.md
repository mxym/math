# ECQC critical-rank mathematical core: partial Lean coverage

Pinned Lean 4.34.1 and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612;
the complete transitive dependency versions are in `lake-manifest.json`.

This package proves two mathematical components of the
[critical-rank equality manuscript](../../research/ecqc-critical-rank-equality/PAPER.md):

* `residue_reflection_forces_square_neg_one`: for **every prime p≥5**, an
  equivalence of the **entire actual quadratic-residue set in ZMod p**
  satisfying q+σ(q)=κ forces κ=0 and a square root of -1.
* `no_residue_reflection_mod_four_three`: such an equivalence is impossible
  for p≡3 mod4. This includes all p≥7 in that congruence class.
* `diagonal_rigidity_of_distinguished_column`: for an actual complex matrix
  F, a diagonal unitary satisfying the entrywise monomial-conjugation relation
  must be scalar if F has the specified unique first-row modulus and
  a nowhere-zero distinguished column. These hypotheses are printed explicitly
  in the Lean theorem; the actual reduced Fourier matrix is checked analytically
  in the manuscript, and that specialization is **not yet Lean-formalized**.

The all-quantum critical-rank equality theorem, Holevo equality, MUB identity,
the saturation and monomial reductions, the Born transforms and entropy statements
are **not** the output of this Lean project. The paper has a complete written
proof using published Holevo as its disclosed external input. Helper-module
verification is not described as whole-paper formalization.

## Reproduction

```bash
lake update
lake exe cache get
python3 reproduce.py
```

With an already pinned, tracked-clean dependency project:

```bash
python3 reproduce.py --dependency-project /absolute/path/to/pinned/project
```

The runner checks all dependency commits and source hashes, creates a genuinely
new build directory, recompiles **both own modules**, runs `lake build`, two
kernel-decision positive controls, a negative control, and trust-zero replay of
all eleven listed roots from an empty Lean kernel. It validates type and universe
levels and rejects unsafe/partial declarations or unexpected axioms in the proof
closure. No native-decision proof oracle is used.

The fresh October 13 record in [evidence/20261013](evidence/20261013/VERIFICATION.json)
contains 20,108 replayed declarations, two modules, eleven roots, trust level zero
and only `propext`, `Classical.choice`, `Quot.sound`. This is a current rerun,
not inherited validation of the previous ECQC packages. Its scope is exactly the
two modules and roots listed in `PROOF_SOURCES.json` and `ROOTS.txt`.

Copyright 2026 Yongxian Zhang; all rights reserved for original material.
Mathlib and imported dependencies retain their existing licenses.
AI assisted research and coding; no external funding or external peer review.
