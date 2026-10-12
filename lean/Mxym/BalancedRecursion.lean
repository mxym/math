import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Entry005 v5, Section 2. These are unconditional proofs about the explicitly
defined scalar recurrences. Connecting them to actual convex bodies requires
the geometric product and join identities, which this project does not prove. -/
namespace Mxym.BalancedRecursion

def dimension (t p : ℕ) : ℕ → ℕ
  | 0 => p
  | j + 1 => t ^ 2 * dimension t p j + t - 1

noncomputable def invariant (t p : ℕ) : ℕ → ℝ
  | 0 => 1 / (p + 1 : ℝ)
  | j + 1 => invariant t p j / t

 theorem shifted_dimension (t p j : ℕ) (ht : 2 ≤ t) :
    (dimension t p j : ℝ) + 1 / (t + 1 : ℝ) =
      ((p : ℝ) + 1 / (t + 1 : ℝ)) * ((t : ℝ) ^ 2) ^ j := by
  have hden : (t : ℝ) + 1 ≠ 0 := by positivity
  induction j with
  | zero => simp [dimension]
  | succ j ih =>
    have hn : 1 ≤ t ^ 2 * dimension t p j + t := by omega
    calc
      (dimension t p (j + 1) : ℝ) + 1 / (t + 1 : ℝ) =
          (t : ℝ) ^ 2 * (dimension t p j : ℝ) + t - 1 + 1 / (t + 1 : ℝ) := by
        rw [dimension, Nat.cast_sub hn]
        push_cast
        ring
      _ = (t : ℝ) ^ 2 * ((dimension t p j : ℝ) + 1 / (t + 1 : ℝ)) := by
        field_simp
        ring
      _ = (t : ℝ) ^ 2 * (((p : ℝ) + 1 / (t + 1 : ℝ)) * ((t : ℝ) ^ 2) ^ j) := by rw [ih]
      _ = ((p : ℝ) + 1 / (t + 1 : ℝ)) * ((t : ℝ) ^ 2) ^ (j + 1) := by
        rw [pow_succ]
        ring

 theorem invariant_closed_form (t p j : ℕ) :
    invariant t p j = 1 / ((p + 1 : ℝ) * (t : ℝ) ^ j) := by
  induction j with
  | zero => simp [invariant]
  | succ j ih =>
    rw [invariant, ih, div_div, pow_succ]
    ring

 theorem dimension_binary (p j : ℕ) :
    3 * dimension 2 p j + 1 = (3 * p + 1) * 4 ^ j := by
  induction j with
  | zero => simp [dimension]
  | succ j ih =>
    have hs : dimension 2 p (j + 1) = 4 * dimension 2 p j + 1 := by
      simp only [dimension]
      omega
    rw [hs, pow_succ]
    nlinarith [ih]

 theorem winning_dimension_level_six : dimension 2 5 6 = 21845 := by
  norm_num [dimension]

 theorem winning_invariant_level_six : invariant 2 5 6 = 1 / 384 := by
  rw [invariant_closed_form]
  norm_num

end Mxym.BalancedRecursion
