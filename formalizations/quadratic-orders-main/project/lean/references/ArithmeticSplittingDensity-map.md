# Actual splitting-count route and remaining analytic foundation

These four new modules are supporting proofs. They do **not** prove the
unconditional natural density of completely splitting rational primes, the
prime supply target, the finite-sieve target, or MainTarget.

The sources compile with Lean `leanprover/lean4:v4.34.1` and official mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Exact owned and standard-source
hashes are in `logs/arithmetic-splitting-source-provenance.json`.

## Compiled mathematical chain

1. `ArithmeticPrimeIdealCounting.lean` uses actual ideals of `NumberField.RingOfIntegers K`,
   actual `Ideal.absNorm` (quotient cardinality), actual `Ideal.inertiaDeg`,
   actual `Ideal.ramificationIdx`, and actual determinant `Algebra.norm`.
   A prime ideal has norm `p` iff it lies over `(p)` and has inertia degree one.
   Its integral principal generator has determinant norm of absolute value `p`.
   For an unramified `p` in any Galois number field, existence of a norm-`p`
   prime ideal is equivalent to every prime above `p` having `e=f=1`.
   Each completely splitting prime contributes exactly `[K:Q]` prime ideals.
   The exact cumulative degree-one ideal count is degree times the actual
   unramified completely splitting rational-prime count.

2. `ArithmeticPrimeIdealRemainder.lean` proves that all actual nonzero prime
   ideals of nonprime norm at most `n` lie over rational primes at most
   `Nat.sqrt n`. Their cardinality is at most `[K:Q] * (Nat.sqrt n + 1)`.
   This includes ramified primes and uses the genuine Galois fundamental
   identity to bound the number of primes in each fiber.

3. `ArithmeticSplittingCount.lean` bounds ramified prime-norm prime ideals
   by the fixed finite number of ideals of norm at most `natAbs(discr K)`.
   It proves the disjoint exact decomposition of all nonzero prime ideals
   with norm at most `n` into the degree-one unramified, degree-one ramified,
   and nonprime-norm parts. The first part is exactly degree times the
   actual completely splitting rational-prime count.

4. `ArithmeticSplittingAsymptotics.lean` proves that the latter two actual
   error counts divided by `x/log x` tend to zero, including the real
   endpoint/floor comparison. Its conditional reduction takes the following
   explicit **open** premise:

   ```lean
   Tendsto (fun x : ℝ =>
     ((nonzeroPrimeIdealsUpTo K ⌊x⌋₊).card : ℝ) / (x / Real.log x))
       atTop (nhds 1)
   ```

   From that prime-ideal theorem it proves the actual completely splitting
   rational-prime count asymptotic with coefficient `1/[K:Q]`. An additional
   explicit rational PNT premise gives relative natural density with respect
   to actual `Nat.primeCounting`; the rational premise has a separate audited
   proof in `references/upstream/arithmetic-audit/ArithmeticSupplyPNT.lean`.
   The final supporting reduction produces the literal inclusive dyadic A5
   count and its positive coefficient, using the already compiled endpoint
   correction in `GenericCumulativeDyadicDensity.lean`.

All these statements quantify over arbitrary number fields (with Galois
required for the splitting/counting chain). They impose no quadratic
signature, finite-unit, maximal-order-only, or conductor restriction. The
ray/conductor generator steps are separate and can use the degree-one
generator norm theorem; no class-field-density fact is hidden in a typeclass.

## Standard imported mathematics

- `Ideal.pow_inertiaDeg`, in mathlib
  `RingTheory/RamificationInertia/Inertia.lean`, identifies the actual prime
  ideal norm with the prime power given by its inertia degree.
- `Ideal.absNorm_span_singleton` and
  `Ideal.exists_prime_and_absNorm_eq_pow`, in
  `RingTheory/Ideal/Norm/AbsNorm.lean`, provide actual generator norms and
  finite-field prime-power norms. Its finite bounded-norm ideal set is used
  to construct every owned finite count.
- `Ideal.inertiaDeg_eq_of_isGaloisGroup`,
  `Ideal.ramificationIdxIn_eq_ramificationIdx`,
  `Ideal.inertiaDegIn_eq_inertiaDeg`, and
  `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`, in
  `NumberTheory/RamificationInertia/Galois.lean`, provide the actual Galois
  prime-fiber fundamental identity. `IsGalois.card_aut_eq_finrank`, in
  `FieldTheory/Galois/Basic.lean`, identifies its group cardinality with degree.
- `NumberField.not_dvd_discr_iff_isUnramifiedIn`, in
  `NumberTheory/NumberField/Discriminant/Different.lean`, and
  `NumberField.discr_ne_zero`, in
  `NumberTheory/NumberField/Discriminant/Defs.lean`, control actual
  ramified prime exceptions.
- `isLittleO_log_rpow_atTop`, in
  `Analysis/SpecialFunctions/Pow/Asymptotics.lean`, proves the square-root
  error negligible. Rational prime counts use the official definition from
  `NumberTheory/PrimeCounting.lean`.

## Missing analytic theorem: exact inspection result

At the pinned snapshot, `NumberTheory/NumberField/DedekindZeta.lean` defines
the actual ideal-coefficient Dedekind zeta series, its positive residue, and
`tendsto_sub_one_mul_dedekindZeta_nhdsGT`, a real-axis residue limit obtained
from **all-ideal** counting. `NumberField/Ideal/Asymptotics.lean` proves
all-ideal counting asymptotics; it does not provide a prime-ideal theorem or
a power-saving remainder yielding continuation across the line `Re(s)=1`.
`NumberField/DirichletDensity.lean` supplies the definition and basic bounds
for Dirichlet density, with no complete-splitting or natural-density theorem.
`LSeries/Nonvanishing.lean` proves nonvanishing for Dirichlet-character
L-functions and Riemann zeta, not arbitrary Dedekind zeta functions.

The separately audited four-module PNT source provides the genuine
`WienerIkeharaTheorem'`, but it still requires a nonnegative coefficient
sequence, summability for every `Re(s)>1`, a Chebyshev bound, and a continuous
boundary function `G` agreeing with `LSeries f s - A/(s-1)` on `Re(s)>1`.
Applying it to a number field requires proving the actual prime-ideal
von-Mangoldt/logarithmic-derivative formula, a genuine coefficient/Chebyshev
bound, and the required Dedekind-zeta analytic continuation and nonvanishing
on the boundary. Those foundations are absent from the inspected pinned
mathlib and 999 audited external source files. They have not been added as
axioms or as hidden assumptions.

The natural splitting-density theorem therefore remains open, although the
actual finite counting and negligible-error route from a number-field
prime-ideal theorem is now compiled.
