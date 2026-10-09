import CofactorIndicator
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The nested-indicator and Cauchy--Schwarz part of the sharp spectral bound. -/
set_option autoImplicit false
open scoped BigOperators
namespace CofactorSpectral
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
noncomputable section

def sqrtIncrement (j : ℕ) : ℝ := Real.sqrt (j+1) - Real.sqrt j
def binaryNormConstant (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, sqrtIncrement j ^ 2

theorem abel_zero_endpoint (x : ℕ → ℝ) (u : ℕ → E) (n : ℕ) (hx : x n = 0) :
    (∑ j ∈ Finset.range n, x j • u j) =
      ∑ j ∈ Finset.range n, (x j - x (j+1)) • (∑ i ∈ Finset.range (j+1), u i) := by
  cases n with
  | zero => simp
  | succ n =>
    rw [Finset.sum_range_by_parts, Nat.add_sub_cancel]
    conv_rhs => rw [Finset.sum_range_succ]
    have hd : ∀ j, (x j - x (j+1)) • (∑ i ∈ Finset.range (j+1), u i) =
        -((x (j+1) - x j) • (∑ i ∈ Finset.range (j+1), u i)) := by
      intro j
      rw [← neg_smul, neg_sub]
    simp only [hx, sub_zero]
    conv_rhs => arg 1; rw [Finset.sum_congr rfl (fun j _ => hd j), Finset.sum_neg_distrib]
    abel

theorem sum_sqrtIncrement (n : ℕ) :
    (∑ j ∈ Finset.range n, sqrtIncrement j) = Real.sqrt n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [sqrtIncrement, Nat.cast_add, Nat.cast_one]
    ring

theorem weighted_sqrt_abel (x : ℕ → ℝ) (n : ℕ) (hx : x n = 0) :
    (∑ j ∈ Finset.range n, (x j - x (j+1)) * Real.sqrt (j+1)) =
      ∑ j ∈ Finset.range n, x j * sqrtIncrement j := by
  have h := abel_zero_endpoint x sqrtIncrement n hx
  simp only [smul_eq_mul, sum_sqrtIncrement] at h
  simpa only [Nat.cast_add, Nat.cast_one] using h.symm

theorem sorted_binary_norm_bound (u : ℕ → E) (x : ℕ → ℝ) (n : ℕ)
    (hx : x n = 0) (hd : ∀ j < n, 0 ≤ x j - x (j+1))
    (hu : ∀ j < n, ‖∑ i ∈ Finset.range (j+1), u i‖ ≤ Real.sqrt (j+1)) :
    ‖∑ j ∈ Finset.range n, x j • u j‖ ^ 2 ≤
      binaryNormConstant n * ∑ j ∈ Finset.range n, x j ^ 2 := by
  have hnorm : ‖∑ j ∈ Finset.range n, x j • u j‖ ≤
      ∑ j ∈ Finset.range n, x j * sqrtIncrement j := by
    rw [abel_zero_endpoint x u n hx, ← weighted_sqrt_abel x n hx]
    calc
      _ ≤ ∑ j ∈ Finset.range n,
          ‖(x j-x (j+1)) • (∑ i ∈ Finset.range (j+1), u i)‖ := norm_sum_le _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        have hjn := Finset.mem_range.mp hj
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hd j hjn)]
        exact mul_le_mul_of_nonneg_left (hu j hjn) (hd j hjn)
  have hp : 0 ≤ ∑ j ∈ Finset.range n, x j * sqrtIncrement j :=
    (norm_nonneg _).trans hnorm
  calc
    _ ≤ (∑ j ∈ Finset.range n, x j * sqrtIncrement j) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hp).mpr hnorm
    _ ≤ (∑ j ∈ Finset.range n, x j ^ 2) *
        (∑ j ∈ Finset.range n, sqrtIncrement j ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = _ := mul_comm _ _

end
end CofactorSpectral
