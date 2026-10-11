# Exact identifiability and equifinality in a two-storage rainfall–runoff model

This package formalizes the exact algebraic core of the accompanying hydrology note.
It proves both sides of a useful model-design statement:

* the output of the two-storage linear model satisfies a scalar second-order
  equation whose coefficients depend on `(a,b,c)` only through
  `S = a+b+c` and `P = ac`; and
* under constant rainfall and zero initial storage, the first three output
  derivatives recover `a`, `b`, and `c` exactly.
* the positive second-order coefficients rule out an exact power-law recession
  after the calculus substitution shown in the paper; the formalized core is
  the three-point polynomial residual check.
* two active parallel exponential reservoirs satisfy an exact order-two moment
  recurrence, and a nonzero Hankel determinant makes its sum/product
  coefficients unique from the first four moments.
* three active parallel exponential reservoirs satisfy the corresponding
  order-three recurrence, with a weighted Vandermonde-square Hankel
  determinant and cubic rate equations.
* `Hydrology/Generic.lean` proves the finite-mode theorem for arbitrary mode
  count: every polynomial annihilating all decay rates induces the same linear
  recurrence on every weighted moment sequence.
* `Hydrology/Diagnostics.lean` proves exact algebraic recovery of the power-law
  exponent from the curvature invariant and of the time shift from the local
  slope identity.
* `Hydrology/FiniteBound.lean` proves the finite-spectrum growth invariant
  (M_{j+1}\le \lambda_{\max}M_j) for nonnegative weights and rates.
* `Hydrology/Variance.lean` proves the arbitrary-finite-mode Hankel identity
  as a half weighted sum of squared pairwise rate gaps, its nonnegativity for
  nonnegative weights, and strict positivity when two positive-weight rates differ.
* `Hydrology/WeightIdentifiability.lean` uses the exact Vandermonde theorem to
  prove uniqueness of all weights from the first `k` moments when the `k` rates
  are known and pairwise distinct.

The package also verifies a physical equifinality example: `(2,2,2)` and
`(1,1,4)` have the same `(S,P)` and the same equilibrium discharge for every
rainfall level, while their storage partitions differ for nonzero rainfall.

The formalization is intentionally explicit about its scope. It does not claim
that arbitrary rainfall–runoff models are identifiable, and it does not encode
ODE existence or numerical observations. The theorem is a symbolic, exact
result about trajectories (represented by their pointwise jets) satisfying the
model equations. This makes the proof reproducible with rational arithmetic and
separates structural non-identifiability from numerical conditioning.

## Reproduce

With Lean 4.34.1 and the pinned Mathlib revision:

```bash
lake exe cache get
lake build
```

The Python checker in `checks/exact.py` independently checks the same rational
identities, the parallel-reservoir regression example, and deliberate failure
controls. The parallel result is in `Hydrology/Parallel.lean`; it recovers the
unordered rate pair as the roots of the resulting quadratic, but does not claim
identifiability for arbitrary distributed or nonlinear catchments. The
three-mode extension is in `Hydrology/Parallel3.lean` and is likewise an exact
finite-mode theorem rather than a claim about arbitrary catchments. The fully
finite theorem is in `Hydrology/Generic.lean`; it does not by itself assert
rate uniqueness or positivity for an arbitrary number of modes.
