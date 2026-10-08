# Lean 4 formalization roadmap and verified partial component

## Current trust boundary

The [universal exact determinant formula](paper.md) has a complete traditional mathematical proof, but it is **not yet fully Lean-formalized**. Finite integer checkers and CI replays are not substitutes for a kernel-checked all-parameter proof.

One generic algebraic component is proved in [KernelMass.lean](../formal/KernelMass.lean): if a rational constraint matrix has a first row entirely equal to one, then every vector in its matrix kernel has total signed mass zero. This theorem imports Mathlib.Data.Matrix.Basic, contains no sorry and no custom axioms, and **compiled successfully using Lean 4.34.1** under the authorized Windows mathlib environment.

This partial lemma **does not** formalize the maximal-minor formula, the rank determinant product, or the subset cycle-index theorem.

## Precise missing formalization obligations

1. Define the two-state transfer matrix over truncated formal polynomials and prove the orbital coefficient/cycle-index identity for arbitrary finite n,k.
2. Formalize the full-rank binomial-product determinant proof using finite differences and Taylor coefficients at t=1.
3. Prove the general alternating maximal-minor kernel vector identity for rectangular matrices over a field.
4. Establish an exact sparse-support reduction for sign-constrained rational kernel vectors: any non-circuit signed dependence splits into smaller-support sign-compatible dependencies.
5. Prove the maximum-minor objective equals the complete finite-dimensional signed kernel norm optimum, including degenerate and empty-kernel cases.
6. Prove conjugacy averaging and short-cycle aggregation preserve the optimum, and that every compressed signed kernel vector yields a genuine nonnegative marginal-preserving probability perturbation.
7. Verify complement symmetry, n=1, m=0, the nonzero full-rank certificate and the rational maxima.
8. Optionally replay several small finite rational values using a formally defined executable checker, **after** the general proof.

The general mathematical statement should be expressed in Lean using Finset/Fintype-indexed matrices over rational numbers, finite probability vectors, and Mathlib's determinant and linear algebra infrastructure. The current starter imports only Mathlib.Data.Matrix.Basic to avoid an unreviewed dependency or axiom addition.

## Existing compilation

Lean compiler: 4.34.1 for Windows; project mathlib sources and partial build cache were already available under the user's authorized Windows workspace. The verified fragment was compiled with the Lake environment from the existing lean005 project. In a compatible Mathlib project, the command is:

    lake env lean KernelMass.lean

No sorry or new axiom has been used, and no claim is made that Lean has verified the entire universal theorem. External human mathematical review and literature novelty checks also remain pending.
