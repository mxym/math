import HydrologyTree.LeadingCoefficients
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination

/-! Global, not merely local, uniqueness of the branch numerator decomposition
for prescribed pairwise coprime child denominators. This proves the algebraic
recovery step used by constructive tree realizations. -/
open Polynomial
noncomputable section
namespace HydrologyTree

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The actual polynomial sum of each numerator times all other denominators. -/
def branchNumeratorSum (P R : I → ℝ[X]) : ℝ[X] :=
  ∑ i : I, R i * ∏ j ∈ Finset.univ.erase i, P j

/-- Unique exact numerator decomposition, valid over every finite branch family.
The degree conditions are actual polynomial degree bounds, not sample tests. -/
theorem coprime_branch_numerators_unique (P R S : I → ℝ[X])
    (hP : ∀ i j, i ≠ j → IsCoprime (P i) (P j))
    (hR : ∀ i, (R i).degree < (P i).degree)
    (hS : ∀ i, (S i).degree < (P i).degree)
    (h : branchNumeratorSum P R = branchNumeratorSum P S) : R = S := by
  have hz : (∑ i : I, (R i-S i) * ∏ j ∈ Finset.univ.erase i, P j) = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr h
  funext i
  have hd : P i ∣ ∑ j ∈ Finset.univ.erase i,
      (R j-S j) * ∏ k ∈ Finset.univ.erase j, P k := by
    apply Finset.dvd_sum
    intro j hj
    apply dvd_mul_of_dvd_right
    exact Finset.dvd_prod_of_mem P (by simp [Ne.symm (Finset.mem_erase.mp hj).1])
  have he := Finset.sum_erase_add Finset.univ
    (fun j : I => (R j-S j) * ∏ k ∈ Finset.univ.erase j, P k) (Finset.mem_univ i)
  rw [hz] at he
  have hterm : (R i-S i) * (∏ j ∈ Finset.univ.erase i, P j) =
      -(∑ j ∈ Finset.univ.erase i, (R j-S j) * ∏ k ∈ Finset.univ.erase j, P k) := by
    linear_combination he
  have hdiv : P i ∣ (R i-S i) * (∏ j ∈ Finset.univ.erase i, P j) := by
    rw [hterm]
    exact dvd_neg.mpr hd
  have hc : IsCoprime (P i) (∏ j ∈ Finset.univ.erase i, P j) := by
    apply IsCoprime.prod_right
    intro j hj
    exact hP i j (Ne.symm (Finset.mem_erase.mp hj).1)
  have hdiff : (R i-S i).degree < (P i).degree :=
    (Polynomial.degree_sub_le _ _).trans_lt (max_lt (hR i) (hS i))
  exact sub_eq_zero.mp (Polynomial.eq_zero_of_dvd_of_degree_lt
    (hc.dvd_of_dvd_mul_right hdiv) hdiff)

/-- Uniqueness also holds modulo the full denominator product. This is the
form needed when the unknown root diagonal contributes a multiple of that product. -/
theorem coprime_branch_numerators_unique_mod_product (P R S : I → ℝ[X])
    (hP : ∀ i j, i ≠ j → IsCoprime (P i) (P j))
    (hR : ∀ i, (R i).degree < (P i).degree)
    (hS : ∀ i, (S i).degree < (P i).degree)
    (h : (∏ i : I, P i) ∣ branchNumeratorSum P R - branchNumeratorSum P S) : R = S := by
  have hsum : (∑ i : I, (R i-S i) * ∏ j ∈ Finset.univ.erase i, P j) =
      branchNumeratorSum P R - branchNumeratorSum P S := by
    simp only [sub_mul, Finset.sum_sub_distrib, branchNumeratorSum]
  funext i
  have hall : P i ∣ ∑ j : I, (R j-S j) * ∏ k ∈ Finset.univ.erase j, P k := by
    rw [hsum]
    exact (Finset.dvd_prod_of_mem P (Finset.mem_univ i)).trans h
  have hd : P i ∣ ∑ j ∈ Finset.univ.erase i,
      (R j-S j) * ∏ k ∈ Finset.univ.erase j, P k := by
    apply Finset.dvd_sum
    intro j hj
    apply dvd_mul_of_dvd_right
    exact Finset.dvd_prod_of_mem P (by simp [Ne.symm (Finset.mem_erase.mp hj).1])
  have he := Finset.sum_erase_add Finset.univ
    (fun j : I => (R j-S j) * ∏ k ∈ Finset.univ.erase j, P k) (Finset.mem_univ i)
  rw [← he] at hall
  have hdiv : P i ∣ (R i-S i) * (∏ j ∈ Finset.univ.erase i, P j) := by
    simpa only [add_sub_cancel_left] using dvd_sub hall hd
  have hc : IsCoprime (P i) (∏ j ∈ Finset.univ.erase i, P j) := by
    apply IsCoprime.prod_right
    intro j hj
    exact hP i j (Ne.symm (Finset.mem_erase.mp hj).1)
  have hdiff : (R i-S i).degree < (P i).degree :=
    (Polynomial.degree_sub_le _ _).trans_lt (max_lt (hR i) (hS i))
  exact sub_eq_zero.mp (Polynomial.eq_zero_of_dvd_of_degree_lt
    (hc.dvd_of_dvd_mul_right hdiv) hdiff)

/-- A monic polynomial times a nonzero scalar is recovered completely, including
its scale, from its actual coefficients. -/
theorem scalar_monic_polynomial_unique (P Q : ℝ[X]) (hP : P.Monic) (hQ : Q.Monic)
    (a b : ℝ) (ha : a ≠ 0) (h : C a * P = C b * Q) : a = b ∧ P = Q := by
  have hb : b ≠ 0 := by
    intro hb
    rw [hb, map_zero, zero_mul] at h
    exact (mul_ne_zero (Polynomial.C_ne_zero.mpr ha) hP.ne_zero) h
  have hc := congrArg Polynomial.leadingCoeff h
  simp only [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hP.leadingCoeff,
    hQ.leadingCoeff, mul_one] at hc
  refine ⟨hc,?_⟩
  rw [← hc] at h
  exact mul_left_cancel₀ (Polynomial.C_ne_zero.mpr ha) h

end HydrologyTree
