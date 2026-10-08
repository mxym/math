import Entry002.ArithmeticPrimeIdealCounting
import Mathlib.Data.Nat.Sqrt

/-! A genuine square-root bound for the number-field prime ideals whose
absolute norm is not a rational prime. This is a finite counting theorem,
not an assertion of the prime-ideal theorem. -/

namespace Entry002

open NumberField Ideal
open scoped NumberField Classical

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- The number of actual prime ideals over a rational prime is at most
the extension degree, including at ramified primes. -/
theorem arithmeticSupply_prime_fiber_card_le [IsGalois ℚ K]
    (p : ℕ) (hp : p.Prime) :
    ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)).ncard ≤ Module.finrank ℚ K := by
  have : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (Ideal.span {(p : ℤ)}) (𝓞 K) (K ≃ₐ[ℚ] K)
  rw [IsGalois.card_aut_eq_finrank] at h
  have he : 0 < (Ideal.span {(p : ℤ)}).ramificationIdxIn (𝓞 K) :=
    Nat.pos_of_ne_zero (Ideal.ramificationIdxIn_ne_zero (B := 𝓞 K) (K ≃ₐ[ℚ] K))
  have hf : 0 < (Ideal.span {(p : ℤ)}).inertiaDegIn (𝓞 K) :=
    Nat.pos_of_ne_zero (Ideal.inertiaDegIn_ne_zero (B := 𝓞 K) (K ≃ₐ[ℚ] K))
  calc
    _ ≤ ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)).ncard *
        ((Ideal.span {(p : ℤ)}).ramificationIdxIn (𝓞 K) *
          (Ideal.span {(p : ℤ)}).inertiaDegIn (𝓞 K)) :=
      Nat.le_mul_of_pos_right _ (Nat.mul_pos he hf)
    _ = _ := h

/-- Every actual nonzero prime ideal of nonprime norm and norm at most
`n` lies over a rational prime at most `sqrt n`. -/
theorem arithmeticSupply_nonprime_norm_below_sqrt (n : ℕ)
    (P : Ideal (𝓞 K)) (hprime : P.IsPrime) (hne : P ≠ ⊥)
    (hnorm : Ideal.absNorm P ≤ n) (hnotprime : ¬ (Ideal.absNorm P).Prime) :
    ∃ p : ℕ, p.Prime ∧ p ≤ Nat.sqrt n ∧
      P.LiesOver (Ideal.span {(p : ℤ)}) := by
  have : P.IsMaximal := hprime.isMaximal hne
  obtain ⟨p, k, hkpos, hmem, hp, hpow⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
  have hk : 2 ≤ k := by
    have hkne : k ≠ 1 := by
      intro hkone
      apply hnotprime
      rw [hpow, hkone, pow_one]
      exact hp
    omega
  have hp2 : p ^ 2 ≤ n :=
    (Nat.pow_le_pow_right hp.pos hk).trans (hpow ▸ hnorm)
  exact ⟨p, hp, Nat.le_sqrt'.mpr hp2,
    (Ideal.liesOver_span_iff hprime.ne_top (Nat.prime_iff_prime_int.mp hp)).mpr
      (by simpa using hmem)⟩

/-- Actual prime ideals with composite absolute norm at most `n`. -/
def higherDegreePrimeIdeals (n : ℕ) : Finset (Ideal (𝓞 K)) := by
  classical
  exact (Ideal.finite_setOfPred_absNorm_le n).toFinset.filter (fun P =>
    P.IsPrime ∧ P ≠ ⊥ ∧ ¬ (Ideal.absNorm P).Prime)

@[simp] theorem mem_higherDegreePrimeIdeals (n : ℕ) (P : Ideal (𝓞 K)) :
    P ∈ higherDegreePrimeIdeals K n ↔ Ideal.absNorm P ≤ n ∧
      P.IsPrime ∧ P ≠ ⊥ ∧ ¬ (Ideal.absNorm P).Prime := by
  classical
  simp [higherDegreePrimeIdeals]

/-- The composite-norm prime-ideal error in a Galois number field is
bounded by `[K:ℚ] * (sqrt n + 1)`, with true ideals and true norms. -/
theorem higherDegreePrimeIdeals_card_le [IsGalois ℚ K] (n : ℕ) :
    (higherDegreePrimeIdeals K n).card ≤
      Module.finrank ℚ K * (Nat.sqrt n + 1) := by
  classical
  let primes := (Finset.range (Nat.sqrt n + 1)).filter Nat.Prime
  let fibers (p : ℕ) : Finset (Ideal (𝓞 K)) :=
    (Algebra.QuasiFinite.finite_primesOver (S := 𝓞 K) (Ideal.span {(p : ℤ)})).toFinset
  have hsubset : higherDegreePrimeIdeals K n ⊆ primes.biUnion fibers := by
    intro P hP
    obtain ⟨hnorm, hprime, hne, hnotprime⟩ := (mem_higherDegreePrimeIdeals K n P).mp hP
    obtain ⟨p, hp, hpsqrt, hlies⟩ :=
      arithmeticSupply_nonprime_norm_below_sqrt K n P hprime hne hnorm hnotprime
    apply Finset.mem_biUnion.mpr
    refine ⟨p, ?_, ?_⟩
    · simp only [primes, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le hpsqrt, hp⟩
    · change P ∈ (Algebra.QuasiFinite.finite_primesOver (S := 𝓞 K)
        (Ideal.span {(p : ℤ)})).toFinset
      rw [Set.Finite.mem_toFinset]
      exact ⟨hprime, hlies⟩
  calc
    _ ≤ (primes.biUnion fibers).card := Finset.card_le_card hsubset
    _ ≤ ∑ p ∈ primes, (fibers p).card := Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ primes, Module.finrank ℚ K := by
      apply Finset.sum_le_sum
      intro p hp
      have hprime : p.Prime := (Finset.mem_filter.mp hp).2
      change (Algebra.QuasiFinite.finite_primesOver (S := 𝓞 K)
        (Ideal.span {(p : ℤ)})).toFinset.card ≤ _
      rw [← Set.ncard_eq_toFinset_card _
        (Algebra.QuasiFinite.finite_primesOver (S := 𝓞 K) (Ideal.span {(p : ℤ)}))]
      exact arithmeticSupply_prime_fiber_card_le K p hprime
    _ = primes.card * Module.finrank ℚ K := by simp
    _ ≤ (Nat.sqrt n + 1) * Module.finrank ℚ K :=
      Nat.mul_le_mul_right _ ((Finset.card_filter_le _ _).trans (by simp))
    _ = _ := Nat.mul_comm _ _

end

end Entry002
