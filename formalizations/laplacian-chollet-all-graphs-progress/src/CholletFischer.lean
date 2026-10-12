import BapatMvFischer
import Mathlib.Algebra.MvPolynomial.PDeriv

set_option autoImplicit false
open scoped BigOperators
open MvPolynomial BapatFiniteRank

namespace Chollet

variable {C : Type*} [Fintype C] [DecidableEq C]

noncomputable section

theorem multiFactorial_pos (α : C →₀ ℕ) : 0 < multiFactorial α := by
  exact Finset.prod_pos fun c _ => Nat.factorial_pos (α c)

theorem multiFactorial_add_single (α : C →₀ ℕ) (i : C) :
    multiFactorial (α + Finsupp.single i 1) = multiFactorial α * (α i + 1) := by
  classical
  calc
    _ = ∏ c, (α c).factorial * (if c = i then α i + 1 else 1) := by
      apply Finset.prod_congr rfl
      intro c hc
      by_cases h : c = i
      · subst c
        simp [Nat.factorial_succ, mul_comm]
      · simp [Finsupp.single_apply, h, Ne.symm h]
    _ = _ := by rw [Finset.prod_mul_distrib]; simp [multiFactorial]

@[simp] theorem pair_zero_left (q : MvPolynomial C ℝ) : fischerPair 0 q = 0 := by
  simp [fischerPair]

@[simp] theorem pair_zero_right (p : MvPolynomial C ℝ) : fischerPair p 0 = 0 := by
  simp [fischerPair]

theorem pair_monomials (α β : C →₀ ℕ) (a b : ℝ) :
    fischerPair (monomial α a) (monomial β b) =
      if α = β then (multiFactorial α : ℝ) * a * b else 0 := by
  rw [fischerPair_monomial_left, coeff_monomial]
  split_ifs <;> simp_all

theorem pair_comm (p q : MvPolynomial C ℝ) : fischerPair p q = fischerPair q p := by
  conv_lhs => rw [MvPolynomial.as_sum p, MvPolynomial.as_sum q]
  conv_rhs => rw [MvPolynomial.as_sum q, MvPolynomial.as_sum p]
  simp only [fischerPair_sum_left, fischerPair_sum_right, pair_monomials]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro β hβ
  apply Finset.sum_congr rfl
  intro α hα
  by_cases h : α = β
  · subst β
    simp [mul_comm, mul_left_comm]
  · simp [h, Ne.symm h]

theorem pair_self_nonneg (p : MvPolynomial C ℝ) : 0 ≤ fischerPair p p := by
  unfold fischerPair
  rw [MvPolynomial.sum_def]
  apply Finset.sum_nonneg
  intro α hα
  have h : 0 ≤ (multiFactorial α : ℝ) := Nat.cast_nonneg _
  nlinarith [sq_nonneg (p.coeff α)]

theorem pair_X_mul (i : C) (p q : MvPolynomial C ℝ) :
    fischerPair (X i * p) q = fischerPair p (pderiv i q) := by
  conv_lhs => rw [MvPolynomial.as_sum p]
  conv_rhs => rw [MvPolynomial.as_sum p]
  simp only [Finset.mul_sum, fischerPair_sum_left]
  apply Finset.sum_congr rfl
  intro α hα
  rw [X, monomial_mul_monomial, one_mul, fischerPair_monomial_left,
    fischerPair_monomial_left, coeff_pderiv, add_comm (Finsupp.single i 1) α,
    multiFactorial_add_single]
  push_cast
  ring

theorem pair_pderiv (i : C) (p q : MvPolynomial C ℝ) :
    fischerPair (pderiv i p) q = fischerPair p (X i * q) := by
  rw [pair_comm, ← pair_X_mul, pair_comm]

/-- Creation-annihilation identity, including all mixed terms. -/
theorem pair_X_mul_X_mul (i j : C) (p q : MvPolynomial C ℝ) :
    fischerPair (X i * p) (X j * q) =
      (if i = j then fischerPair p q else 0) +
        fischerPair (pderiv j p) (pderiv i q) := by
  rw [pair_X_mul, pderiv_mul, fischerPair_add_right, ← pair_pderiv]
  by_cases h : i = j
  · subst j
    simp
  · simp [h, Ne.symm h]

theorem pair_mul_X_self (i : C) (p : MvPolynomial C ℝ) :
    fischerPair (X i * p) (X i * p) =
      fischerPair p p + fischerPair (pderiv i p) (pderiv i p) := by
  simpa using pair_X_mul_X_mul i i p p

theorem pair_le_pair_mul_X_self (i : C) (p : MvPolynomial C ℝ) :
    fischerPair p p ≤ fischerPair (X i * p) (X i * p) := by
  rw [pair_mul_X_self]
  exact le_add_of_nonneg_right (pair_self_nonneg _)

end
end Chollet
