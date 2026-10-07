import Mxym
open scoped BigOperators Classical
open Mxym.Rademacher

-- These are semantic controls, checked as ordinary proof terms.
-- The empty family and all-zero cases are inside the main theorem's scope.
example : mean (fun _ : Fin 0 => (0 : ℝ)) = 0 := by
  exact mean_zero
example : mean (fun _ : Fin 4 => (0 : ℝ)) = 0 := by
  exact mean_zero

-- Three positive coordinates can attain equality with no half-mass coordinate.
example : mean ![(1 / 3 : ℝ), 1 / 3, 1 / 3] = 1 / 2 := by
  have h := mean_three_nonneg (1 / 3) (1 / 3) (1 / 3)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

-- The strictness witness has four positive coordinates below half mass.
example : mean (fun _ : Fin 4 => (1 / 4 : ℝ)) < 1 / 2 := by
  rw [mean_four_quarters]
  norm_num

-- Removing balance makes the asserted half-mass inequality false.
example : ¬ mean (fun _ : Fin 1 => (1 : ℝ)) ≤ 1 / 2 := by
  norm_num [mean, signedSum, sum_signs_succ, Fin.sum_univ_succ, sign, Fin.default_eq_zero]

-- Removing weight nonnegativity makes weighted Jensen false.
example : ¬ |∑ _ : Fin 1, (-1 : ℝ) * 1| ≤ ∑ _ : Fin 1, (-1 : ℝ) * |1| := by
  norm_num

-- Removing the endpoint order makes signed_square false.
example : ¬ ((-1 : ℝ) - 1) ^ 2 ≤ 2 * ((-1 : ℝ) * |-1| - 1 * |1|) := by
  norm_num

