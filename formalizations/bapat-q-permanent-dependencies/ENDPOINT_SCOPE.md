# Actual endpoint identities: scope and remaining work

Status: all six endpoint modules compile with Lean 4.34.1 and the pinned Mathlib project at `/workspace/tools/gaussian-lean-deps/project`.

## Actual definitions

* `Bapat.inversionCount σ` counts exactly the pairs `i < j` with `σ j < σ i` by a double finite sum.
* `Bapat.qPermanent A q` is the sum over actual `Equiv.Perm (Fin n)` of `q ^ inversionCount σ` times the actual row-to-column product of entries.
* `Bapat.minorPermanent A i j k l` sums over actual bijections between the remaining rows and remaining columns. `minorPermanent_eq_submatrix_permanent` proves equality with `Matrix.permanent` after any row/column relabeling; taking increasing labels gives the ordered deletion used in the paper. No constrained-permutation counting formula is assumed.
* `Bapat.pairDeterminant` is the actual determinant of the indicated `Fin 2` matrix, and `Bapat.endpointDefect` uses those determinants and those deleted permanents.

## Completed endpoints

`hasDerivAt_qPermanent_one` proves the actual complex derivative at one from the finite polynomial definition. `endpointDerivative_minor_formula` is equation (1) of the note. `endpointDerivative_defect_identity` is equation (2), with the exact natural-number count `n * (n - 1) / 2`. `hasDerivAt_qPermanent_defect` combines them into an actual derivative statement. These hold for every complex matrix, and cover `n=0,1` without any excluded case.

`inversionCount_inverse` and `star_permutationWeight` are actual permutation/conjugation identities. `star_qPermanent_real` proves the actual polynomial takes real values on real parameters for a Hermitian matrix.

The only local hypotheses are the relevant finiteness, distinctness or order needed for each subsidiary two-row bijection and Hermitian symmetry for the reality statement. The final algebraic endpoint identity has no matrix positivity, rank, determinant, derivative or counting identity hypothesis.

## Reproduction

From this directory run `python compile.py` with these arguments in order:

```
QDefinitions.lean QPermanent.lean MinorPermanent.lean EndpointIdentity.lean EndpointDefect.lean HermitianReality.lean
```

The parent agent will independently rebuild a frozen public bundle and replay all owned theorem dependencies in an empty kernel environment. A successful compile here is not a claim of that additional replay or a full Bapat counterexample formalization.

## Not yet completed in this package

The complete rank-two Bargmann correspondence, exact polynomial recurrence semantics and closed n=200 integer certificate remain separate obligations. Positive-definite perturbation and explicit real q-interval bounds are being built by the parent agent. None of these missing obligations is asserted by the six endpoint modules.

Work in progress `ColorFibers.lean` and `ColorExpansion.lean` already proves the actual colored-bijection factorial multiplicity and finite cross-Gram/color expansion. It is not yet connected to the full coefficient-norm identity and must not be described as the complete Bargmann bridge.
