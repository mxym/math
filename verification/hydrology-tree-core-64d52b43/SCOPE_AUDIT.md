# Theorem-scope audit for the completed real-fiber extension

This is an internal semantic audit of the checked statement scope, not an
external human peer review. It must be read with the exact source hash manifest
and the independent replay receipt for the same proof commit.

## What is quantified

The tree is `t : OrderedTree n`, with n+1 original vertices. Input, root-state
observation, and the sole leak are at vertex 0. Internal transfers are bidirected
and diagonals are built by exact compartment conservation. The theorem is for
every finite size and every such parent tree, including the singleton.

The prescribed target has `r w : Fin (n+1) -> Real`, `Function.Injective r`,
strictly positive r and w, and sum w = 1. Its actual poles are -r_i, hence negative.
This is a FULL n+1-mode normalized Stieltjes response, not every nonnegative
transfer function. The assumptions concern the target, not the competing rates.

## What is NOT a premise on a competing real solution

`RealStieltjesFiber` has only the two actual matrix polynomial equalities.
`RealResponseFiber` has only root resolvent equality on the common nonpole domain.
`RealDischargeFiber` has only equality of the actual leak-scaled root resolvent
with the specified discharge target on the common nonpole domain.

No positivity, nonnegative-rate, nonzero-rate, spectral stability, determinant
regularity, or minimal-realization premise is placed on these real vectors.
The leak is not an externally calibrated input. Strict positivity, its exact
value, and the actual nonzero coefficient Jacobian are proved consequences.

## Completeness and counting

`positiveReciprocalFiberEquiv` proves both surjectivity and injectivity of the
actual parent assembly, not merely a count of possible factor assignments.
`positiveStieltjesRecursiveEquiv` constructs the full recursive bijection.
`realResponseRecursiveEquiv` extends that bijection to ALL real competitors via
automatic positivity. The discharge equivalence preserves the actual rate vector.

The exact cardinality theorem includes a separate `Finite` proof. Thus a zero
`Nat.card` of an infinite type cannot conceal an infinite family. The factorial
quotient is justified by a preceding multiplication identity and positive hook
product. Original labels are retained: there is no automorphism quotient and
within-block pole permutations are not counted twice.

## Dependency audit

Reverse real allocation uses only monicity, divisor splitting and exact
factor matching. Normalized child-cofactor recovery uses the proved polynomial
branch-recovery theorem at a proved positive reference; no unproved inverse
or missing spectral input is introduced. Strong induction discharges all child
positivity, realization, cardinality and classification obligations.

Root-response equality recovers the actual full coefficient pair through
nonpole polynomial equality, coprimality and monic equal-degree uniqueness.
Discharge equality recovers the leak from leading coefficients. No evaluation
at a totalized matrix-inverse pole is taken as physical data.

The auditor rejects nonstandard axioms and unsafe/partial declarations in the
mathematical root dependency closure. Its separate replay metaprogram is not
imported as a mathematical axiom. Only propext, Classical.choice and Quot.sound
are allowed; all replayed root types and universes are compared.

## Explicit exclusions

The proof is not yet transported to independently presented arbitrary rooted
graph objects, or to a sole leak away from the observed root. It is not an
all-input ODE solution or controllability/observability proof. Complex parameter
fibers, fewer-mode targets, repeated target poles, distributed rainfall inputs,
nonlinear catchments and empirical forecasting superiority are not claimed.

The original root-leak matrix model's algebraic and full-real-fiber core is
closed. The overall broader research program remains partially formalized.
