import CofactorBinaryNorm
import Mathlib.NumberTheory.Harmonic.Bounds

/-! The exact harmonic estimate for the binary-vector norm constant. -/
set_option autoImplicit false
open scoped BigOperators
namespace CofactorSpectral
noncomputable section

theorem sqrtIncrement_nonneg (j : ℕ) : 0 ≤ sqrtIncrement j := by
  unfold sqrtIncrement
  exact sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))

theorem sqrtIncrement_mul_sum (j : ℕ) :
    sqrtIncrement j * (Real.sqrt (j+1) + Real.sqrt j) = 1 := by
  have h0 := Real.sq_sqrt (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
  have h1 := Real.sq_sqrt (show (0 : ℝ) ≤ (j : ℝ)+1 by positivity)
  unfold sqrtIncrement
  nlinarith

theorem sqrtIncrement_sq_le (j : ℕ) (hj : 0 < j) :
    sqrtIncrement j ^ 2 ≤ 1 / (4 * (j : ℝ)) := by
  have h0 := Real.sq_sqrt (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
  have hm : Real.sqrt j ≤ Real.sqrt (j+1) := Real.sqrt_le_sqrt (by linarith)
  have hd : 4 * (j : ℝ) ≤ (Real.sqrt (j+1) + Real.sqrt j)^2 := by
    nlinarith [Real.sqrt_nonneg (j : ℝ), Real.sqrt_nonneg ((j : ℝ)+1)]
  have hp : sqrtIncrement j ^ 2 * (Real.sqrt (j+1) + Real.sqrt j)^2 = 1 := by
    calc
      _ = (sqrtIncrement j * (Real.sqrt (j+1) + Real.sqrt j))^2 := by ring
      _ = 1 := by rw [sqrtIncrement_mul_sum]; norm_num
  have hmul : sqrtIncrement j ^ 2 * (4 * (j : ℝ)) ≤ 1 := by
    calc
      _ ≤ sqrtIncrement j ^ 2 * (Real.sqrt (j+1) + Real.sqrt j)^2 :=
        mul_le_mul_of_nonneg_left hd (sq_nonneg _)
      _ = _ := hp
  exact (le_div_iff₀ (by positivity)).mpr hmul

theorem binaryNormConstant_le_harmonic (n : ℕ) :
    binaryNormConstant n ≤ 1 + (harmonic (n-1) : ℝ) / 4 := by
  cases n with
  | zero => simp [binaryNormConstant]
  | succ n =>
    have ht : (∑ j ∈ Finset.range n, sqrtIncrement (j+1)^2) ≤ (harmonic n : ℝ)/4 := by
      calc
        _ ≤ ∑ j ∈ Finset.range n, 1 / (4 * ((j+1 : ℕ) : ℝ)) := by
          apply Finset.sum_le_sum
          intro j _
          exact sqrtIncrement_sq_le (j+1) (Nat.succ_pos _)
        _ = _ := by
          simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Finset.sum_div]
          apply Finset.sum_congr rfl
          intro j _
          simp only [one_div, mul_inv_rev, div_eq_mul_inv]
          ring
    unfold binaryNormConstant
    rw [Finset.sum_range_succ']
    simpa [sqrtIncrement, add_comm] using add_le_add_left ht 1

end
end CofactorSpectral
