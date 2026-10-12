import Entry002.PrimeIdealAnalyticDefs
import Mathlib.RingTheory.RamificationInertia.Basic

namespace Entry002

open NumberField Ideal
open scoped NumberField Classical

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- The inertia degrees of any finite collection of primes over a rational
prime sum to at most the degree of the number field. This uses the full
ramification/inertia identity and does not assume the extension is Galois. -/
theorem primeIdeal_sum_inertiaDeg_le_degree (p : ℕ) (hp : p.Prime)
    (s : Finset (Ideal (𝓞 K)))
    (hs : ∀ P ∈ s, P.IsPrime ∧ P.LiesOver (Ideal.span {(p : ℤ)})) :
    (∑ P ∈ s, P.inertiaDeg ℤ) ≤ Module.finrank ℚ K := by
  let : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)
  let t := Algebra.QuasiFinite.finite_primesOver (S := 𝓞 K) (Ideal.span {(p : ℤ)})
  let : Fintype ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) := t.fintype
  let f := t.toFinset
  have hsub : s ⊆ f := by
    intro P hP
    change P ∈ t.toFinset
    rw [Set.Finite.mem_toFinset]
    exact hs P hP
  calc
    ∑ P ∈ s, P.inertiaDeg ℤ ≤ ∑ P ∈ s, P.ramificationIdx ℤ * P.inertiaDeg ℤ := by
      apply Finset.sum_le_sum
      intro P hP
      let : P.IsPrime := (hs P hP).1
      exact Nat.le_mul_of_pos_left _ (P.ramificationIdx_pos ℤ)
    _ ≤ ∑ P ∈ f, P.ramificationIdx ℤ * P.inertiaDeg ℤ :=
      Finset.sum_le_sum_of_subset hsub
    _ = ∑ P : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K),
        P.1.ramificationIdx ℤ * P.1.inertiaDeg ℤ := by
      exact Finset.sum_subtype f (by simp [f]) _
    _ = Module.finrank ℚ K := by
      rw [Ideal.sum_ramification_inertia_eq_finrank, RingOfIntegers.rank]

/-- If an actual prime-ideal norm power is a power of the rational prime
`p`, the ideal lies over `p`. -/
theorem primeIdealPowerSupport_liesOver_of_eq_prime_pow (n p r : ℕ)
    (hp : p.Prime) (hn : n = p ^ r) (P : Ideal (𝓞 K))
    (hP : P ∈ primeIdealPowerSupport K n) :
    P.LiesOver (Ideal.span {(p : ℤ)}) := by
  obtain ⟨_, hprime, hne, k, hk, hpow⟩ := (mem_primeIdealPowerSupport K n P).mp hP
  let : P.IsMaximal := hprime.isMaximal hne
  obtain ⟨q, m, hm, hmem, hq, hnorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
  have hdiv : q ∣ p ^ r := by
    rw [← hn, ← hpow, hnorm]
    exact dvd_pow (dvd_pow_self q hm.ne') hk.ne'
  have hqp : q = p := Nat.prime_eq_prime_of_dvd_pow hq hp hdiv
  subst q
  exact (Ideal.liesOver_span_iff hprime.ne_top (Nat.prime_iff_prime_int.mp hp)).mpr
    (by simpa using hmem)

/-- At a rational-prime power, the actual coefficient is bounded by the
degree times the logarithm of that rational prime. -/
theorem primeIdealVonMangoldt_prime_pow_le (p r : ℕ) (hp : p.Prime) :
    primeIdealVonMangoldt K (p ^ r) ≤ (Module.finrank ℚ K : ℝ) * Real.log p := by
  have hs : ∀ P ∈ primeIdealPowerSupport K (p ^ r),
      P.IsPrime ∧ P.LiesOver (Ideal.span {(p : ℤ)}) := by
    intro P hP
    exact ⟨((mem_primeIdealPowerSupport K (p ^ r) P).mp hP).2.1,
      primeIdealPowerSupport_liesOver_of_eq_prime_pow K (p ^ r) p r hp rfl P hP⟩
  have heq : primeIdealVonMangoldt K (p ^ r) =
      (∑ P ∈ primeIdealPowerSupport K (p ^ r), (P.inertiaDeg ℤ : ℝ)) * Real.log p := by
    rw [primeIdealVonMangoldt, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro P hP
    let : P.IsPrime := (hs P hP).1
    let : P.LiesOver (Ideal.span {(p : ℤ)}) := (hs P hP).2
    rw [← Ideal.pow_inertiaDeg p P, Nat.cast_pow, Real.log_pow]
  rw [heq, ← Nat.cast_sum]
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast primeIdeal_sum_inertiaDeg_le_degree K p hp
      (primeIdealPowerSupport K (p ^ r)) hs
  · exact Real.log_nonneg (by exact_mod_cast hp.one_lt.le)

/-- The genuine number-field von Mangoldt coefficient is bounded by
`[K : ℚ]` times the ordinary von Mangoldt function, for every number field.
The coefficient sums actual prime ideals with positive norm powers equal to
`n`; no analytic premise or Galois assumption occurs in the bound. -/
theorem primeIdealVonMangoldt_le_degree_mul (n : ℕ) :
    primeIdealVonMangoldt K n ≤
      (Module.finrank ℚ K : ℝ) * ArithmeticFunction.vonMangoldt n := by
  by_cases hsupport : (primeIdealPowerSupport K n).Nonempty
  · obtain ⟨P, hP⟩ := hsupport
    obtain ⟨_, hprime, hne, k, hk, hpow⟩ := (mem_primeIdealPowerSupport K n P).mp hP
    let : P.IsMaximal := hprime.isMaximal hne
    obtain ⟨p, m, hm, _, hp, hnorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
    have hn : n = p ^ (m * k) := by
      rw [← hpow, hnorm, pow_mul]
    rw [hn, ArithmeticFunction.vonMangoldt_apply_pow (Nat.mul_pos hm hk).ne',
      ArithmeticFunction.vonMangoldt_apply_prime hp]
    exact primeIdealVonMangoldt_prime_pow_le K p (m * k) hp
  · have hempty : primeIdealPowerSupport K n = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsupport
    simp only [primeIdealVonMangoldt, hempty, Finset.sum_empty]
    exact mul_nonneg (Nat.cast_nonneg _) ArithmeticFunction.vonMangoldt_nonneg

end

end Entry002
