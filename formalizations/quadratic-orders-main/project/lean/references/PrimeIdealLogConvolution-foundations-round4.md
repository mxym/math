# Actual ideal coefficients and the logarithmic convolution identity

Read-only foundations audit, 2026-10-07. Source pin: Lean 4.34.1 and mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.
No new Lean theorem, hypothesis, axiom, or `Entry002` module was added for this audit.
The existing definitions and coefficient bound were not changed.

## Exact target and the coefficient at zero

For every number field `K`, write `N(I) := Ideal.absNorm I` and

```
aK n := (Nat.card {I : Ideal (𝓞 K) // N(I) = n} : ℝ)
ΛK n := Entry002.primeIdealVonMangoldt K n
```

The desired finite identity is

```
aK n * Real.log (n : ℝ) = LSeries.convolution aK ΛK n.
```

This is a mathematical target, not a theorem currently proved in this project.
It is valid for all `n`, including `0` and `1`, and requires no Galois assumption.

The precise mathlib zeta coefficient includes the zero ideal: in
`Mathlib/NumberTheory/NumberField/DedekindZeta.lean:49`, `dedekindZeta K` is
`LSeries (fun n ↦ Nat.card {I : Ideal (𝓞 K) // absNorm I = n})`.
Consequently the raw coefficient has `aK 0 = 1`, not `0`.
The same file explicitly uses that cardinality equality at line 86.
`Ideal.absNorm_eq_zero_iff` identifies its unique element with `⊥`.
For `n ≠ 0`, the raw fiber is equivalent to the fiber of nonzero ideals,
because an ideal of positive norm cannot be `⊥`.

The raw sequence therefore cannot be directly packaged as an
`ArithmeticFunction`. Use the existing unbundled `LSeries.convolution`, which
applies `toArithmeticFunction` to both sequences and sets index `0` to zero
internally. Alternatively package `toArithmeticFunction aK` explicitly.
`LSeries.convolution_map_zero` and `Real.log_zero` settle the target at `0`.
The zeta function is unaffected by the correction, by `LSeries_congr`, whose
hypothesis only concerns indices `n ≠ 0`.

## Existing, genuine foundations

Paths below are relative to the pinned mathlib package root
`.lake/packages/mathlib/`. They were inspected in the checked-out source.

| Role | Available API and source |
| --- | --- |
| Norm multiplicativity | `Ideal.absNorm : Ideal S →*₀ ℕ`, `Mathlib/RingTheory/Ideal/Norm/AbsNorm.lean:258`; use `map_mul`, `map_pow`, and `map_multiset_prod`. |
| Nonzero norm | `Ideal.absNorm_eq_zero_iff`, same file:410. |
| Finite norm fibers | `Ideal.finite_setOfPred_absNorm_eq`, same file:509; bounded fibers at:502. |
| Ideal multiplication cancellation | `Ideal.isCancelMulZero`, `Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean:384`; generic `mul_left_cancel₀` applies when the multiplier is nonzero. |
| Ideal divisibility | `Ideal.dvd_iff_le`, same file:395; a divisor is an ideal containing the dividend. The divisibility witness directly supplies an integral quotient ideal. |
| Nonzero prime ideals as prime monoid elements | `Ideal.prime_of_isPrime`, `Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean:109`. |
| Exact factorization | `Ideal.prod_normalizedFactors_eq_self`, same file:387. Unlike a general UFM, ideal association does not introduce an unresolved unit. |
| Identify prime factors | `Ideal.mem_normalizedFactors_iff`, same file:144, and `UniqueFactorizationMonoid.prime_of_normalized_factor`. |
| Power divisibility | `pow_dvd_iff_le_emultiplicity`, `Mathlib/RingTheory/Multiplicity.lean:261`. |
| Convert multiplicity to a natural number | `UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors`, `Mathlib/RingTheory/UniqueFactorizationDomain/Multiplicity.lean:93`; `normalize_eq` removes ideal normalization. |
| Finite ideal divisors, if desired | `UniqueFactorizationMonoid.fintypeSubtypeDvd`, `Mathlib/RingTheory/UniqueFactorizationDomain/Finite.lean:31`, for a nonzero ideal and finite units. This route is optional; the norm-fiber route below avoids constructing ideal divisor finsets. |
| Log of a factor product | `Real.log_multiset_prod`, `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:401`. |
| Collect repeated factors | `Finset.sum_multiset_map_count`, used in `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:1094`. |
| Regroup finite counts | `Finset.sum_card_fiberwise_eq_card_filter` and `Finset.card_eq_sum_card_fiberwise`, same file:972 and:993; `Nat.card_congr` transports the equivalences below. |
| Sequence convolution | `toArithmeticFunction`, `LSeries.convolution_def`, and `LSeries.convolution_map_zero`, `Mathlib/NumberTheory/LSeries/Convolution.lean:40`, :82, :89. |
| Positive divisor pairs | `Nat.mem_divisorsAntidiagonal` and `Nat.ne_zero_of_mem_divisorsAntidiagonal`, `Mathlib/NumberTheory/Divisors.lean:124` and :197. |
| Exact actual prime-power sum | Already proved project theorem `Entry002.primeIdealVonMangoldt_eq_bounded_prime_power_sum`, `Entry002/PrimeIdealPowerSummation.lean:78`. |
| Unique and bounded norm-power exponents | Already proved `Entry002.primeIdeal_norm_power_exponent_unique` and `primeIdeal_norm_power_exponent_le`, `Entry002/PrimeIdealAnalyticDefs.lean:86`, :91. |

No pre-existing theorem tying number-field ideal counts to the actual
prime-ideal von Mangoldt coefficient was found in these sources.

## Constructive proof route and exact missing lemmas

All formulas in this section describe lemmas still to be implemented.
They are not assumptions that may be substituted for the target identity.

### 1. The logarithm of an individual nonzero ideal norm

For `I ≠ ⊥`, let `c(P,I) := (normalizedFactors I).count P`. Prove

```
Real.log (N(I) : ℝ) =
  ∑ P ∈ (normalizedFactors I).toFinset,
    (c(P,I) : ℝ) * Real.log (N(P) : ℝ).
```

Apply the multiplicative norm to
`Ideal.prod_normalizedFactors_eq_self`, cast the resulting multiset product
to `ℝ`, and apply `Real.log_multiset_prod`.
Every factor has nonzero norm because it is a nonzero prime monoid element.
`Finset.sum_multiset_map_count` collects its repeated appearances.
This part needs only finite factorization and nonzero norms.

### 2. Count the prime-ideal powers dividing an individual ideal

For `P.IsPrime`, `P ≠ ⊥`, and `I ≠ ⊥`, prove the natural-number statement

```
P ^ k ∣ I ↔ k ≤ c(P,I).
```

Use `Ideal.prime_of_isPrime`, its irreducibility, the multiplicity/count
identity, `normalize_eq`, and `pow_dvd_iff_le_emultiplicity`.
This avoids defining a quotient operation on ideals.

For a fixed positive `n` and `N(I) = n`, steps 1 and 2 give

```
Real.log (n : ℝ) =
  ∑ P ∈ nonzeroPrimeIdealsUpTo K n,
    ∑ k ∈ Finset.Icc 1 n,
      if P ^ k ∣ I then Real.log (N(P) : ℝ) else 0.
```

The cutoff loses no term: `P^k ∣ I` implies `N(P)^k ∣ n` by the norm
homomorphism, hence `N(P)^k ≤ n` since `n > 0`.
`N(P) ≥ 2` then bounds `k ≤ n` using the existing exponent bound.
Likewise any contributing `P` belongs to the actual bounded prime-ideal
finset. The inner sum has exactly `c(P,I)` copies of the logarithm.

### 3. Count norm-fiber ideals divisible by a fixed ideal

For `n > 0`, `A ≠ ⊥`, and `N(A) ∣ n`, construct an equivalence

```
{J : Ideal (𝓞 K) // N(J) = n / N(A)} ≃
{I : Ideal (𝓞 K) // N(I) = n ∧ A ∣ I}.
```

The forward map is `J ↦ A * J`.
Norm multiplicativity and the divisibility of `n` prove that its norm is `n`.
Surjectivity uses the witness `I = A * J` in `A ∣ I`.
Cancellation by the nonzero ideal `A` proves injectivity and uniqueness of
the quotient ideal. The norm of that quotient is forced by the positive
natural number `N(A)` and the equality `N(A) * N(J) = n`.

`Nat.card_congr` then identifies the divisible-ideal count with
`aK (n / N(A))`. For `N(A) ∤ n`, the divisible-ideal fiber is empty by
`map_dvd`; this case must retain a guard, because the raw value `aK 0 = 1`
does not represent an empty fiber. In particular, replacing a guarded term
by an unguarded `aK (n / N(A))` would be wrong.

For the application take `A = P^k`. Its norm is `N(P)^k`, and it is nonzero.

### 4. Expand, count, and regroup the convolution

For `n > 0`, expand `LSeries.convolution_def` and replace each `ΛK(d)`
with the already proved bounded double sum using the common cutoff `n`.
Each `d` in a divisor pair is positive and at most `n`, so the theorem's
cutoff hypothesis holds. Swap the finite sums.

Selecting `d = N(P)^k` gives exactly

```
∑ P ∈ nonzeroPrimeIdealsUpTo K n,
  ∑ k ∈ Finset.Icc 1 n,
    if N(P)^k ∣ n then
      aK (n / N(P)^k) * Real.log (N(P) : ℝ)
    else 0.
```

Step 3 interprets each guarded coefficient as the cardinality of ideals
of norm `n` divisible by `P^k`. Finite fiberwise summation now turns this
into a sum over all actual ideals `I` of norm `n` of the expression in
step 2. Each such ideal contributes `Real.log n`. Since the norm fiber is
finite, that sum equals its cardinality times `Real.log n`.
The `n = 0` case is independent and already handled by the generic
convolution/logarithm zero rules; `n = 1` is included in the positive proof.

The main implementation burden is thus two finite sum transformations:
the norm-fiber multiplication equivalence in step 3, and the weighted
regrouping of the triples `(I,P,k)` in step 4. The underlying algebraic
factorization, multiplicity, finiteness, norm, and cancellation facts are
already present in the pinned library.

## What this would unlock, and what it would not prove

After the finite identity is proved, cast it to `ℂ`, using the compatibility
of the complex logarithm of a natural number with the real logarithm.
`LSeries_convolution'` and `LSeries_deriv` then give, in a common half-plane
of absolute convergence,

```
dedekindZeta K s * LSeries (fun n ↦ (ΛK n : ℂ)) s =
  -deriv (dedekindZeta K) s.
```

The project's new coefficient bound and Chebyshev module already provide
the prime-ideal series convergence for `Re(s) > 1`. The zeta-coefficient
series convergence and derivative-domain hypothesis must also be supplied
from actual ideal-count bounds.
Dividing by `dedekindZeta K s` separately requires its nonvanishing at `s`.
The finite identity alone proves neither continuation/nonvanishing on the
line `Re(s)=1` nor the natural prime-ideal PNT target. These remain distinct
analytic obligations and are not hidden in any lemma above.

## Audit outcome

The logarithmic convolution identity is not formally completed in round 4.
There is a concrete all-number-fields finite proof route with no missing
algebraic axiom. The missing deliverable is the Lean construction and
weighted sum transport of the actual norm/divisibility fibers, followed by
their factor-count evaluation. No new unfinished proof file was left in
`Entry002`, and no new compilation or build-control changes were performed
for this read-only follow-up.
