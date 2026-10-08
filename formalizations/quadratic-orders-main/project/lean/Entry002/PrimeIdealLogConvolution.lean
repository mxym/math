import Entry002.IdealNormDivisibility
import Entry002.IdealFactorLogarithm

/-! The actual ideal-count / prime-ideal logarithmic convolution. -/

namespace Entry002

open NumberField Ideal
open scoped NumberField Classical

noncomputable section

/-- Selecting the second member of a positive divisor pair retains its genuine
divisibility guard. In particular no count at index zero is substituted. -/
theorem divisorsAntidiagonal_snd_select (u : ℕ → ℝ) (n a : ℕ)
    (hn : 0 < n) (c : ℝ) :
    (∑ z ∈ n.divisorsAntidiagonal, u z.1 * (if a = z.2 then c else 0)) =
      if a ∣ n then u (n / a) * c else 0 := by
  by_cases hdiv : a ∣ n
  · have ha : 0 < a := Nat.pos_of_dvd_of_pos hdiv hn
    have hmem : (n / a, a) ∈ n.divisorsAntidiagonal :=
      Nat.mem_divisorsAntidiagonal.mpr ⟨Nat.div_mul_cancel hdiv, hn.ne'⟩
    rw [ite_eq_left hdiv, Finset.sum_eq_single_of_mem (n / a, a) hmem]
    · simp
    · intro z hz hne
      have hneq : a ≠ z.2 := by
        intro hsame
        have hmul : z.1 * a = n := by
          simpa [hsame] using (Nat.mem_divisorsAntidiagonal.mp hz).1
        have hfst : z.1 = n / a := Nat.eq_div_of_mul_eq_left ha.ne' hmul
        exact hne (Prod.ext hfst hsame.symm)
      simp [hneq]
  · rw [ite_eq_right hdiv]
    apply Finset.sum_eq_zero
    intro z hz
    have hneq : a ≠ z.2 := by
      intro hsame
      apply hdiv
      exact hsame ▸ Nat.dvd_of_mem_divisors
        (Nat.snd_mem_divisors_of_mem_antidiagonal hz)
    simp [hneq]

variable (K : Type*) [Field K] [NumberField K]

/-- Finite expansion of the convolution into actual prime ideals and positive
powers. The norm-divisibility guard is essential for the raw zeta coefficient. -/
theorem idealNormCoefficient_convolution_primeIdealVonMangoldt_expand
    (n : ℕ) (hn : 0 < n) :
    LSeries.convolution (idealNormCoefficient K) (primeIdealVonMangoldt K) n =
      ∑ P ∈ nonzeroPrimeIdealsUpTo K n, ∑ k ∈ Finset.Icc 1 n,
        if Ideal.absNorm P ^ k ∣ n then
          idealNormCoefficient K (n / Ideal.absNorm P ^ k) *
            Real.log (Ideal.absNorm P : ℝ)
        else 0 := by
  rw [LSeries.convolution_def]
  calc
    _ = ∑ z ∈ n.divisorsAntidiagonal,
        ∑ P ∈ nonzeroPrimeIdealsUpTo K n, ∑ k ∈ Finset.Icc 1 n,
          idealNormCoefficient K z.1 *
            (if Ideal.absNorm P ^ k = z.2 then Real.log (Ideal.absNorm P : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro z hz
      have hzn : z.2 ≤ n := Nat.divisor_le
        (Nat.snd_mem_divisors_of_mem_antidiagonal hz)
      rw [primeIdealVonMangoldt_eq_bounded_prime_power_sum K z.2 n hzn]
      simp only [Finset.mul_sum]
    _ = ∑ P ∈ nonzeroPrimeIdealsUpTo K n, ∑ k ∈ Finset.Icc 1 n,
        ∑ z ∈ n.divisorsAntidiagonal,
          idealNormCoefficient K z.1 *
            (if Ideal.absNorm P ^ k = z.2 then Real.log (Ideal.absNorm P : ℝ) else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro P _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro P _
      apply Finset.sum_congr rfl
      intro k _
      simpa only [ite_mul, zero_mul] using
        divisorsAntidiagonal_snd_select (idealNormCoefficient K) n
          (Ideal.absNorm P ^ k) hn (Real.log (Ideal.absNorm P : ℝ))

/-- The genuine logarithmic convolution identity for the actual Dedekind-zeta
coefficients and genuine prime-ideal von Mangoldt coefficients. All number
fields and all indices are included; no analytic hypothesis is used. -/
theorem idealNormCoefficient_log_eq_convolution (n : ℕ) :
    idealNormCoefficient K n * Real.log (n : ℝ) =
      LSeries.convolution (idealNormCoefficient K) (primeIdealVonMangoldt K) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [idealNormCoefficient_convolution_primeIdealVonMangoldt_expand K n hn]
    calc
      _ = ∑ I ∈ idealNormFiber K n, Real.log (n : ℝ) := by
        simp [idealNormCoefficient, ← idealNormFiber_card K n, nsmul_eq_mul]
      _ = ∑ I ∈ idealNormFiber K n,
          ∑ P ∈ nonzeroPrimeIdealsUpTo K n, ∑ k ∈ Finset.Icc 1 n,
            if P ^ k ∣ I then Real.log (Ideal.absNorm P : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro I hI
        exact ideal_log_norm_eq_prime_power_divisor_sum K I n hn
          ((mem_idealNormFiber K n I).mp hI)
      _ = ∑ P ∈ nonzeroPrimeIdealsUpTo K n, ∑ k ∈ Finset.Icc 1 n,
          ∑ I ∈ idealNormFiber K n,
            if P ^ k ∣ I then Real.log (Ideal.absNorm P : ℝ) else 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro P _
        exact Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro P hP
        obtain ⟨_, _, hPne⟩ := (mem_nonzeroPrimeIdealsUpTo K n P).mp hP
        apply Finset.sum_congr rfl
        intro k _
        simpa only [map_pow, ite_mul, zero_mul] using
          idealNormFiber_sum_divisible K hn (P ^ k) (pow_ne_zero k hPne)
            (Real.log (Ideal.absNorm P : ℝ))

end

end Entry002
