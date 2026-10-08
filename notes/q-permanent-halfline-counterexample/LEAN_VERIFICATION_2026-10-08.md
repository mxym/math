# Lean verification supplement, 2026-10-08

The explicit four-dimensional q-permanent half-line counterexample now has a
[Lean source and evidence package](../../formalizations/q-permanent-halfline-counterexample/README.md).
The earlier written proof, source audit, exact certificate, and their manifests
are retained unchanged.

The formalization uses the full inversion-weighted permutation sum and the
genuine mathlib `Matrix.PosDef` predicate. It proves the exact values at 49
and 50, their strict decrease, and failure of the required open/closed
half-line monotonicity for every endpoint at or below -1. The open-half-line
conjecture with an existential endpoint below -1 is therefore false.

The proof producer recorded fresh compilation of 4 modules, an audit of all
26 owned declarations, and replay of the 13,134-declaration closure into an
empty trust-level-zero kernel environment, plus rejection of an invalid proof.
The separate independent review checked semantics, hashes, graph closure, all
24 permutations, and the positive quadratic factorization; it did not rerun Lean.

Dimension-four minimality, the `n ≤ 3` result, the separate construction for
every `t > 1`, and Bapat's original interval `[-1,1]` are outside this Lean
formalization. The package records the exact versions, commands, trust boundary,
public-copy projection, and reproducible static checks. It does not claim a
new priority result or a passing GitHub CI run.
