import Entry002.IdealNormCoefficient
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-! Finite factorization identities for the logarithm of an ideal norm. -/

namespace Entry002

open NumberField Ideal UniqueFactorizationMonoid
open scoped NumberField Classical

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem ideal_prime_pow_dvd_iff_count (P : Ideal (𝓞 K))
    (hp : P.IsPrime) (hP : P ≠ ⊥) (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (k : ℕ) :
    P ^ k ∣ I ↔ k ≤ (normalizedFactors I).count P := by
  rw [pow_dvd_iff_le_emultiplicity,
    UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors
      (Ideal.prime_of_isPrime hP hp).irreducible hI, normalize_eq]
  norm_cast

theorem ideal_log_norm_eq_factor_sum (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    Real.log (Ideal.absNorm I : ℝ) =
      ∑ P ∈ (normalizedFactors I).toFinset,
        ((normalizedFactors I).count P : ℝ) * Real.log (Ideal.absNorm P : ℝ) := by
  let f : Ideal (𝓞 K) →* ℝ :=
    (Nat.castRingHom ℝ).toMonoidHom.comp Ideal.absNorm.toMonoidHom
  have hprod : ((normalizedFactors I).map f).prod = (Ideal.absNorm I : ℝ) := by
    rw [← map_multiset_prod, Ideal.prod_normalizedFactors_eq_self hI]
    rfl
  have hnz : ∀ x ∈ (normalizedFactors I).map f, x ≠ 0 := by
    intro x hx
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hx
    have hPne : P ≠ ⊥ :=
      (UniqueFactorizationMonoid.prime_of_normalized_factor P hP).ne_zero
    change (Ideal.absNorm P : ℝ) ≠ 0
    exact_mod_cast (mt Ideal.absNorm_eq_zero_iff.mp hPne)
  rw [← hprod, Real.log_multiset_prod hnz, Multiset.map_map]
  change ((normalizedFactors I).map
    (fun P => Real.log (Ideal.absNorm P : ℝ))).sum = _
  simpa only [nsmul_eq_mul] using
    (Finset.sum_multiset_map_count (normalizedFactors I)
      (fun P => Real.log (Ideal.absNorm P : ℝ)))

theorem ideal_prime_power_divisor_exponent_le (P : Ideal (𝓞 K))
    (hp : P.IsPrime) (hP : P ≠ ⊥) (I : Ideal (𝓞 K)) (k n : ℕ)
    (hn : 0 < n) (hnorm : Ideal.absNorm I = n) (hdiv : P ^ k ∣ I) : k ≤ n := by
  have hnormdiv : Ideal.absNorm P ^ k ∣ n := by
    have hd : Ideal.absNorm (P ^ k) ∣ Ideal.absNorm I := Ideal.absNorm.map_dvd hdiv
    simpa only [map_pow, hnorm] using hd
  exact (primeIdeal_norm_power_exponent_le K P hp hP k
    (Ideal.absNorm P ^ k) rfl).trans (Nat.le_of_dvd hn hnormdiv)

private theorem sum_Icc_ite_le (c n : ℕ) (hcn : c ≤ n) (w : ℝ) :
    (∑ k ∈ Finset.Icc 1 n, if k ≤ c then w else 0) = (c : ℝ) * w := by
  have hfilter : (Finset.Icc 1 n).filter (fun k => k ≤ c) = Finset.Icc 1 c := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [← Finset.sum_filter, hfilter]
  simp

theorem ideal_log_norm_eq_prime_power_divisor_sum (I : Ideal (𝓞 K)) (n : ℕ)
    (hn : 0 < n) (hnorm : Ideal.absNorm I = n) :
    Real.log (n : ℝ) =
      ∑ P ∈ nonzeroPrimeIdealsUpTo K n, ∑ k ∈ Finset.Icc 1 n,
        if P ^ k ∣ I then Real.log (Ideal.absNorm P : ℝ) else 0 := by
  have hI : I ≠ ⊥ := by
    intro heq
    have : n = 0 := by simpa only [heq, Ideal.absNorm_bot] using hnorm.symm
    omega
  have hsubset : (normalizedFactors I).toFinset ⊆ nonzeroPrimeIdealsUpTo K n := by
    intro P hP
    have hPm : P ∈ normalizedFactors I := Multiset.mem_toFinset.mp hP
    have hprime := UniqueFactorizationMonoid.prime_of_normalized_factor P hPm
    obtain ⟨hp, hle⟩ := (Ideal.mem_normalizedFactors_iff hI).mp hPm
    have hnormdiv : Ideal.absNorm P ∣ n := by
      rw [← hnorm]
      exact Ideal.absNorm.map_dvd (Ideal.dvd_iff_le.mpr hle)
    exact (mem_nonzeroPrimeIdealsUpTo K n P).mpr
      ⟨Nat.le_of_dvd hn hnormdiv, hp, hprime.ne_zero⟩
  calc
    Real.log (n : ℝ) = ∑ P ∈ (normalizedFactors I).toFinset,
        ((normalizedFactors I).count P : ℝ) * Real.log (Ideal.absNorm P : ℝ) := by
      rw [← hnorm]
      exact ideal_log_norm_eq_factor_sum K I hI
    _ = ∑ P ∈ nonzeroPrimeIdealsUpTo K n,
        ((normalizedFactors I).count P : ℝ) * Real.log (Ideal.absNorm P : ℝ) := by
      apply Finset.sum_subset hsubset
      intro P _ hnot
      have hc : (normalizedFactors I).count P = 0 :=
        Multiset.count_eq_zero.mpr (fun hP => hnot (Multiset.mem_toFinset.mpr hP))
      simp [hc]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro P hP
      obtain ⟨_, hp, hPne⟩ := (mem_nonzeroPrimeIdealsUpTo K n P).mp hP
      have hcount : (normalizedFactors I).count P ≤ n :=
        ideal_prime_power_divisor_exponent_le K P hp hPne I _ n hn hnorm
          ((ideal_prime_pow_dvd_iff_count K P hp hPne I hI _).mpr le_rfl)
      simp_rw [ideal_prime_pow_dvd_iff_count K P hp hPne I hI]
      exact (sum_Icc_ite_le _ n hcount _).symm

end

end Entry002
