import ChromaticCyclesAllN.CycleSequenceAlgebra
import Mathlib.Algebra.Polynomial.Coeff

namespace ChromaticCycleAll

open Polynomial

/-- The familiar candidate chromatic polynomial of the n-cycle. -/
noncomputable def cycleFormulaPolynomial (n : ℕ) : ℤ[X] :=
  (X - 1) ^ n + C ((-1 : ℤ)^n) * (X - 1)

/-- Absolute signed-polynomial coefficients, embedded in rational arithmetic. -/
noncomputable def cycleAbsCoeff (n k : ℕ) : ℚ :=
  ((|((cycleFormulaPolynomial n).coeff k)| : ℤ) : ℚ)

theorem coefficient_formula (n k : ℕ) :
    (cycleFormulaPolynomial n).coeff k =
      (-1 : ℤ)^(n-k) * (Nat.choose n k : ℤ)
      + (-1 : ℤ)^n * (if k=1 then 1 else if k=0 then -1 else 0) := by
  have he : (X - 1 : ℤ[X]) = X + C (-1) := by simp [sub_eq_add_neg]
  have hpow : ((X-1 : ℤ[X])^n).coeff k =
      (-1 : ℤ)^(n-k) * (Nat.choose n k : ℤ) := by
    rw [he]
    exact coeff_X_add_C_pow (-1) n k
  have hlinear : (X-1 : ℤ[X]).coeff k =
      (if k=1 then 1 else if k=0 then -1 else 0) := by
    by_cases hk1 : k = 1
    · subst k
      norm_num [coeff_sub, coeff_X, coeff_one]
    · by_cases hk0 : k = 0
      · subst k
        norm_num
      · simp [coeff_sub, coeff_X, coeff_one, hk1, hk0, eq_comm]
  simp only [cycleFormulaPolynomial, coeff_add, coeff_C_mul]
  rw [hpow, hlinear]

theorem cycleAbsCoeff_binomial (n : ℕ) (hn : 1 ≤ n) (k : ℕ) :
    cycleAbsCoeff n k = binomialBase n k := by
  have hcases : k = 0 ∨ k = 1 ∨ 2 ≤ k := by omega
  rcases hcases with h0 | h1 | h2
  · subst k
    have hz : (cycleFormulaPolynomial n).coeff 0 = 0 := by
      rw [coefficient_formula]
      norm_num
    simp [cycleAbsCoeff, binomialBase, hz]
  · subst k
    have hns : n = (n-1)+1 := by omega
    have hn1 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast (show 1 ≤ n by omega)
    have hsign : (-1 : ℤ)^n = -(-1 : ℤ)^(n-1) := by
      conv_lhs => rw [hns, pow_succ]
      ring
    have hone : (cycleFormulaPolynomial n).coeff 1 =
        (-1 : ℤ)^(n-1) * ((n : ℤ)-1) := by
      rw [coefficient_formula]
      simp only [Nat.choose_one_right, if_true, ite_true]
      rw [hsign]
      ring
    have hnorm : |(cycleFormulaPolynomial n).coeff 1| = ((n : ℤ) - 1) := by
      rw [hone, abs_mul]
      have hh : |(-1 : ℤ)^(n-1)| = 1 := by simp
      rw [hh, one_mul, abs_of_nonneg (sub_nonneg.mpr hn1)]
    simp only [cycleAbsCoeff, binomialBase, hnorm, ite_true]
    norm_num
  · have hk0 : k ≠ 0 := by omega
    have hk1 : k ≠ 1 := by omega
    have he : (cycleFormulaPolynomial n).coeff k =
        (-1 : ℤ)^(n-k) * (Nat.choose n k : ℤ) := by
      rw [coefficient_formula]
      simp [hk0, hk1]
    have hc : (0 : ℤ) ≤ (Nat.choose n k : ℤ) := by exact_mod_cast (Nat.zero_le _)
    have habs : |(cycleFormulaPolynomial n).coeff k| = (Nat.choose n k : ℤ) := by
      rw [he, abs_mul]
      have hh : |(-1 : ℤ)^(n-k)| = 1 := by simp
      rw [hh, one_mul, abs_of_nonneg hc]
    simp [cycleAbsCoeff, binomialBase, hk0, hk1, habs]

theorem cycleFormula_all_large_negative (n : ℕ) (hn : 17 ≤ n) :
    LC (LC (LC (cycleAbsCoeff n))) 2 < 0 := by
  have h : ∀ i, i ≤ 5 → cycleAbsCoeff n i = binomialBase n i :=
    fun i hi => cycleAbsCoeff_binomial n (by omega) i
  rw [triple_LC_agrees (cycleAbsCoeff n) (binomialBase n) h]
  exact all_large_cycle_binomial_sequences_fail n hn

theorem cycleAbsCoeff_eq_binomialBase (n : ℕ) (hn : 1 ≤ n) :
    cycleAbsCoeff n = binomialBase n := by
  funext k
  exact cycleAbsCoeff_binomial n hn k

end ChromaticCycleAll
