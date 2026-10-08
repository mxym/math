# Actual splitting descent and ray-generator interface

`Entry002/ArithmeticSplittingTower.lean` is an original, mathlib-only proof
module. It uses the same exact Lean 4.34.1 and official mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` pins as the main library. Source
and imported foundation hashes are in
`logs/arithmetic-splitting-tower-source-provenance.json`.

The module proves complete splitting descent from a number-field overfield
to a base number field, relative complete splitting above each base prime,
and a height-one version with the exact body of the independently audited
`ClassFieldTheory.FinitePrimeSplitsCompletely` predicate.

The principal integration endpoint is
`arithmeticSupply_exists_normal_overfield_prime_package K L N p hp hsplitN`.
It constructs an actual `v : HeightOneSpectrum (NumberField.RingOfIntegers K)`
and proves all of:

- `v.asIdeal.LiesOver (Ideal.span {(p : ℤ)})`;
- `v.asIdeal.ramificationIdx ℤ = 1`;
- `v.asIdeal.inertiaDeg ℤ = 1`;
- `Ideal.absNorm v.asIdeal = p`;
- every actual height-one prime `w` of `L` above `v` has
  `w.asIdeal.ramificationIdx (𝓞 K) = 1` and
  `w.asIdeal.inertiaDeg (𝓞 K) = 1`.

The only prime-specific inputs are actual primality of `p` and actual
`RationalPrimeSplitsCompletely N p`. Existence of `v`, splitting descent,
relative splitting, and residue degree one are all proved. No Galois or
normality premise is needed for local descent; the overfield is intended to
be a genuine normal closure when used with the density route.

For a constructed ray-class extension `L/K`, take the actual field
`N := IntermediateField.normalClosure ℚ L (AlgebraicClosure L)`.
`arithmeticSupply_normal_closure_numberField L` proves that this field is a
number field. `arithmeticSupply_normal_closure_isGalois L` proves it is
Galois over `ℚ`. The actual embedding `L →ₐ[ℚ] N` is supplied by the already
compiled `arithmeticSupply_finite_normal_closure L`, not by an assumed
normal-closure certificate. Its chosen embedding can be installed as the
actual `Algebra L N`; composing with `K → L` supplies `Algebra K N` where
needed. The final height-one `forall` above is the genuine class-field
splitting predicate by unfolding its definition, so it can feed the audited
ray splitting/generator theorem directly.

The local descent proof constructs a prime above a given prime using
Mathlib's actual `Ideal.primesOver` lying-over instance. It then applies:

```lean
Ideal.ramificationIdx_tower
Ideal.inertiaDeg_tower
```

to factor the actual indices in the tower `ℤ → 𝓞 K → 𝓞 L`. Since their
product equals one, each relevant natural-number factor is one. The first
theorem requires flatness of the extension of integer rings; the instance
is discharged by existing mathlib algebra/Dedekind-domain mathematics,
rather than assumed as a theorem field.

The normal-closure endpoints use the genuine finite normal closure from
Mathlib and characteristic-zero separability (`IsGalois` consists of
actual normality and separability). There are no conductor or infinite-unit
restrictions: this module applies unchanged to real quadratic fields and
all finite ray-class extensions selected later for positive conductors.

The number-field prime-ideal theorem remains the open analytic foundation
for supplying positive natural density on `N`. This module proves no
density theorem and does not add that foundation as an axiom.
