import Entry002.WeakSupplyDyadicSeries
import Mathlib.Algebra.BigOperators.Intervals

/-! The finite split of actual prime batches into fixed-density good bins. -/

namespace Entry002

open scoped BigOperators Classical

theorem supply_dyadic_bad_ratio_le (P : Set ℕ) (δ : ℝ) (j : ℕ)
    (hbad : ¬ δ * (2 : ℝ) ^ j / Real.log ((2 : ℝ) ^ (j + 1)) ≤
      (dyadicPrimeBatch P j).card) :
    ((dyadicPrimeBatch P j).card : ℝ) / (2 : ℝ) ^ j ≤
      (δ / Real.log 2) / ((j : ℝ) + 1) := by
  have hbad' := lt_of_not_ge hbad
  have hdiv := div_le_div_of_nonneg_right hbad'.le
    (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ j)
  refine hdiv.trans_eq ?_
  rw [Real.log_pow, Nat.cast_add, Nat.cast_one]
  field_simp

theorem supply_dyadic_ratio_good_bad_le (P : Set ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (δ : ℝ) (hδ : 0 ≤ δ) (j : ℕ) :
    ((dyadicPrimeBatch P j).card : ℝ) / (2 : ℝ) ^ j ≤
      (δ / Real.log 2) / ((j : ℝ) + 1) +
        if δ * (2 : ℝ) ^ j / Real.log ((2 : ℝ) ^ (j + 1)) ≤
          (dyadicPrimeBatch P j).card then 8 / ((j : ℝ) + 1) else 0 := by
  by_cases hg : δ * (2 : ℝ) ^ j / Real.log ((2 : ℝ) ^ (j + 1)) ≤
    (dyadicPrimeBatch P j).card
  · rw [ite_eq_left hg]
    exact (supply_dyadicPrimeBatch_ratio_le P hP j).trans
      (le_add_of_nonneg_left (by positivity))
  · rw [ite_eq_right hg, add_zero]
    exact supply_dyadic_bad_ratio_le P δ j hg

theorem supply_dyadic_Icc_ratio_good_bad_le (P : Set ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (δ : ℝ) (hδ : 0 ≤ δ) (J : ℕ) :
    (∑ j ∈ Finset.Icc 2 J, ((dyadicPrimeBatch P j).card : ℝ) / (2 : ℝ) ^ j) ≤
      (δ / Real.log 2) * (∑ j ∈ Finset.Icc 2 J, 1 / ((j : ℝ) + 1)) +
        8 * (∑ j ∈ goodDyadicBins P δ J, 1 / ((j : ℝ) + 1)) := by
  calc
    _ ≤ ∑ j ∈ Finset.Icc 2 J,
        ((δ / Real.log 2) / ((j : ℝ) + 1) +
          if δ * (2 : ℝ) ^ j / Real.log ((2 : ℝ) ^ (j + 1)) ≤
            (dyadicPrimeBatch P j).card then 8 / ((j : ℝ) + 1) else 0) :=
      Finset.sum_le_sum (fun j _ => supply_dyadic_ratio_good_bad_le P hP δ hδ j)
    _ = _ := by
      simp [Finset.sum_add_distrib, goodDyadicBins, Finset.sum_filter,
        Finset.mul_sum, mul_ite, div_eq_mul_inv]

theorem supply_dyadic_prefix_good_bad_le (P : Set ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (δ : ℝ) (hδ : 0 ≤ δ) {ε : ℝ}
    (hε : 0 < ε) (J : ℕ) (hJ : 2 ≤ J) :
    (∑ j ∈ Finset.range (J + 1), ((dyadicPrimeBatch P j).card / (2 : ℝ) ^ j) *
      ((2 : ℝ) ^ (-ε)) ^ j) ≤
      16 + (δ / Real.log 2) * (∑ j ∈ Finset.Icc 2 J, 1 / ((j : ℝ) + 1)) +
        8 * (∑ j ∈ goodDyadicBins P δ J, 1 / ((j : ℝ) + 1)) := by
  have hsmall : (∑ j ∈ Finset.range 2,
      ((dyadicPrimeBatch P j).card : ℝ) / (2 : ℝ) ^ j) ≤ 16 := by
    calc
      _ ≤ ∑ _j ∈ Finset.range 2, (8 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        refine (supply_dyadicPrimeBatch_ratio_le P hP j).trans ?_
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) + 1)).mpr
        nlinarith [show (0 : ℝ) ≤ (j : ℝ) by positivity]
      _ = _ := by norm_num
  calc
    _ ≤ ∑ j ∈ Finset.range (J + 1), ((dyadicPrimeBatch P j).card : ℝ) / (2 : ℝ) ^ j := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_of_le_one_right (by positivity)
        (pow_le_one₀ supply_dyadic_discount_nonneg (supply_dyadic_discount_lt_one hε).le)
    _ = (∑ j ∈ Finset.range 2, ((dyadicPrimeBatch P j).card : ℝ) / (2 : ℝ) ^ j) +
        ∑ j ∈ Finset.Icc 2 J, ((dyadicPrimeBatch P j).card : ℝ) / (2 : ℝ) ^ j := by
      rw [← Finset.Ico_add_one_right_eq_Icc]
      exact (Finset.sum_range_add_sum_Ico _ (by omega : 2 ≤ J + 1)).symm
    _ ≤ _ := by
      have hlarge := supply_dyadic_Icc_ratio_good_bad_le P hP δ hδ J
      linarith

end Entry002
