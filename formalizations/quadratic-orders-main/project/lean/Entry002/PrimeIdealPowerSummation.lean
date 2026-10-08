import Entry002.PrimeIdealAnalyticDefs

/-! Exact finite prime-power summation formulas for the true number-field
von Mangoldt coefficients. No asymptotic premise is used. -/

namespace Entry002

open NumberField Ideal
open scoped NumberField Classical

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem primeIdeal_positive_power_at_prime_iff (P : Ideal (𝓞 K))
    (hprime : P.IsPrime) (hne : P ≠ ⊥) (p : ℕ) (hp : p.Prime) :
    (∃ k : ℕ, 0 < k ∧ Ideal.absNorm P ^ k = p) ↔ Ideal.absNorm P = p := by
  constructor
  · rintro ⟨k, hk, hpow⟩
    have hdiv : Ideal.absNorm P ∣ p := hpow ▸ dvd_pow_self _ hk.ne'
    rcases (Nat.dvd_prime hp).mp hdiv with hnormone | hnormp
    · have := primeIdeal_absNorm_two_le K P hprime hne
      omega
    · exact hnormp
  · intro hnorm
    exact ⟨1, by norm_num, by simp [hnorm]⟩

theorem primeIdeal_positive_power_sum_bounded (P : Ideal (𝓞 K))
    (hprime : P.IsPrime) (hne : P ≠ ⊥) (n N : ℕ) (hn : n ≤ N) :
    (∑ k ∈ Finset.Icc 1 N,
      if Ideal.absNorm P ^ k = n then Real.log (Ideal.absNorm P : ℝ) else 0) =
    if ∃ k : ℕ, 0 < k ∧ Ideal.absNorm P ^ k = n then
      Real.log (Ideal.absNorm P : ℝ) else 0 := by
  by_cases hex : ∃ k : ℕ, 0 < k ∧ Ideal.absNorm P ^ k = n
  · obtain ⟨k, hkpos, hpow⟩ := hex
    have hkmem : k ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr
      ⟨hkpos, (primeIdeal_norm_power_exponent_le K P hprime hne k n hpow).trans hn⟩
    rw [ite_eq_left ⟨k, hkpos, hpow⟩]
    rw [Finset.sum_eq_single_of_mem k hkmem]
    · simp [hpow]
    · intro j _ hjne
      have hjpow : Ideal.absNorm P ^ j ≠ n := by
        intro hj
        exact hjne (primeIdeal_norm_power_exponent_unique K P hprime hne j k
          (hj.trans hpow.symm))
      simp [hjpow]
  · rw [ite_eq_right hex]
    apply Finset.sum_eq_zero
    intro k hk
    have hkpow : Ideal.absNorm P ^ k ≠ n := by
      intro hpow
      exact hex ⟨k, (Finset.mem_Icc.mp hk).1, hpow⟩
    simp [hkpow]

theorem primeIdeal_positive_power_sum (P : Ideal (𝓞 K))
    (hprime : P.IsPrime) (hne : P ≠ ⊥) (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n,
      if Ideal.absNorm P ^ k = n then Real.log (Ideal.absNorm P : ℝ) else 0) =
    if ∃ k : ℕ, 0 < k ∧ Ideal.absNorm P ^ k = n then
      Real.log (Ideal.absNorm P : ℝ) else 0 :=
  primeIdeal_positive_power_sum_bounded K P hprime hne n n le_rfl

/-- The support definition is exactly the usual positive-exponent double
sum. The cutoff on the exponent loses no term, and uniqueness prevents
multiple counting of a prime ideal. -/
theorem primeIdealVonMangoldt_eq_prime_power_sum (n : ℕ) :
    primeIdealVonMangoldt K n =
    ∑ P ∈ nonzeroPrimeIdealsUpTo K n, ∑ k ∈ Finset.Icc 1 n,
      if Ideal.absNorm P ^ k = n then Real.log (Ideal.absNorm P : ℝ) else 0 := by
  rw [primeIdealVonMangoldt, primeIdealPowerSupport, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro P hP
  obtain ⟨_, hprime, hne⟩ := (mem_nonzeroPrimeIdealsUpTo K n P).mp hP
  exact (primeIdeal_positive_power_sum K P hprime hne n).symm

/-- Enlarging the finite ideal and exponent cutoffs introduces only zero
terms, because positive powers dominate their base norm. -/
theorem primeIdealVonMangoldt_eq_bounded_prime_power_sum (n N : ℕ) (hn : n ≤ N) :
    primeIdealVonMangoldt K n =
    ∑ P ∈ nonzeroPrimeIdealsUpTo K N, ∑ k ∈ Finset.Icc 1 N,
      if Ideal.absNorm P ^ k = n then Real.log (Ideal.absNorm P : ℝ) else 0 := by
  rw [primeIdealVonMangoldt, primeIdealPowerSupport, Finset.sum_filter]
  calc
    _ = ∑ P ∈ nonzeroPrimeIdealsUpTo K N,
        if ∃ k : ℕ, 0 < k ∧ Ideal.absNorm P ^ k = n then
          Real.log (Ideal.absNorm P : ℝ) else 0 := by
      apply Finset.sum_subset
      · intro P hP
        obtain ⟨hpn, hp, hne⟩ := (mem_nonzeroPrimeIdealsUpTo K n P).mp hP
        exact (mem_nonzeroPrimeIdealsUpTo K N P).mpr ⟨hpn.trans hn, hp, hne⟩
      · intro P hPN hPnot
        obtain ⟨_, hp, hne⟩ := (mem_nonzeroPrimeIdealsUpTo K N P).mp hPN
        have hnotpower : ¬ ∃ k : ℕ, 0 < k ∧ Ideal.absNorm P ^ k = n := by
          rintro ⟨k, hk, hpow⟩
          have hnormpos : 0 < Ideal.absNorm P :=
            (by omega : 0 < 2).trans_le (primeIdeal_absNorm_two_le K P hp hne)
          have hnorm : Ideal.absNorm P ≤ n := by
            simpa only [pow_one, hpow] using Nat.pow_le_pow_right hnormpos hk
          exact hPnot ((mem_nonzeroPrimeIdealsUpTo K n P).mpr ⟨hnorm, hp, hne⟩)
        simp [hnotpower]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro P hP
      obtain ⟨_, hp, hne⟩ := (mem_nonzeroPrimeIdealsUpTo K N P).mp hP
      exact (primeIdeal_positive_power_sum_bounded K P hp hne n N hn).symm

theorem primeIdeal_power_endpoint_sum (P : Ideal (𝓞 K))
    (hprime : P.IsPrime) (hne : P ≠ ⊥) (k N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N,
      if Ideal.absNorm P ^ k = n then Real.log (Ideal.absNorm P : ℝ) else 0) =
    if Ideal.absNorm P ^ k ≤ N then Real.log (Ideal.absNorm P : ℝ) else 0 := by
  have hnormpos : 0 < Ideal.absNorm P :=
    (by omega : 0 < 2).trans_le (primeIdeal_absNorm_two_le K P hprime hne)
  have hpowpos : 0 < Ideal.absNorm P ^ k := Nat.pow_pos hnormpos
  by_cases hbound : Ideal.absNorm P ^ k ≤ N
  · rw [ite_eq_left hbound]
    rw [Finset.sum_eq_single_of_mem (Ideal.absNorm P ^ k)
      (Finset.mem_Ioc.mpr ⟨hpowpos, hbound⟩)]
    · simp
    · intro n _ hnepow
      simp [Ne.symm hnepow]
  · rw [ite_eq_right hbound]
    apply Finset.sum_eq_zero
    intro n hn
    have hpown : Ideal.absNorm P ^ k ≠ n := by
      intro heq
      exact hbound (heq ▸ (Finset.mem_Ioc.mp hn).2)
    simp [hpown]

/-- Exact weighted prime-power enumeration, with genuine norms and both
inclusive endpoints. This is a finite identity, not an asymptotic input. -/
theorem primeIdealPsi_eq_prime_power_sum (x : ℝ) :
    primeIdealPsi K x =
    ∑ P ∈ nonzeroPrimeIdealsUpTo K ⌊x⌋₊, ∑ k ∈ Finset.Icc 1 ⌊x⌋₊,
      if Ideal.absNorm P ^ k ≤ ⌊x⌋₊ then Real.log (Ideal.absNorm P : ℝ) else 0 := by
  unfold primeIdealPsi
  calc
    _ = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        ∑ P ∈ nonzeroPrimeIdealsUpTo K ⌊x⌋₊, ∑ k ∈ Finset.Icc 1 ⌊x⌋₊,
          if Ideal.absNorm P ^ k = n then Real.log (Ideal.absNorm P : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      exact primeIdealVonMangoldt_eq_bounded_prime_power_sum K n ⌊x⌋₊
        (Finset.mem_Ioc.mp hn).2
    _ = ∑ P ∈ nonzeroPrimeIdealsUpTo K ⌊x⌋₊, ∑ k ∈ Finset.Icc 1 ⌊x⌋₊,
        ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
          if Ideal.absNorm P ^ k = n then Real.log (Ideal.absNorm P : ℝ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro P _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro P hP
      obtain ⟨_, hp, hne⟩ := (mem_nonzeroPrimeIdealsUpTo K ⌊x⌋₊ P).mp hP
      apply Finset.sum_congr rfl
      intro k _
      exact primeIdeal_power_endpoint_sum K P hp hne k ⌊x⌋₊

theorem primeIdealTheta_le_primeIdealPsi (x : ℝ) :
    primeIdealTheta K x ≤ primeIdealPsi K x := by
  rw [primeIdealTheta, primeIdealPsi_eq_prime_power_sum]
  apply Finset.sum_le_sum
  intro P hP
  obtain ⟨hnorm, hp, hne⟩ := (mem_nonzeroPrimeIdealsUpTo K ⌊x⌋₊ P).mp hP
  have hnormtwo := primeIdeal_absNorm_two_le K P hp hne
  have hlog : 0 ≤ Real.log (Ideal.absNorm P : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ Ideal.absNorm P by omega))
  have hmem : 1 ∈ Finset.Icc 1 ⌊x⌋₊ := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hsingle := Finset.single_le_sum (s := Finset.Icc 1 ⌊x⌋₊)
    (f := fun k => if Ideal.absNorm P ^ k ≤ ⌊x⌋₊ then
      Real.log (Ideal.absNorm P : ℝ) else 0)
    (fun k _ => by split_ifs <;> positivity) hmem
  simpa only [pow_one, ite_eq_left hnorm] using hsingle

end

end Entry002
