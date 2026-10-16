import SpectralProtocol.IntegerBell
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring

namespace SpectralProtocol

/-- The exact integer budget formula agrees with the real-logarithm floor in
the paper, including all integer boundary cases. -/
theorem integerBellYield_eq_real_floor (k r : ℕ) (hr : 0 < r) (hrdim : r ≤ 4^k) :
    integerBellYield k r = ⌊(k:ℝ) - Real.log (r:ℝ) / Real.log 4⌋₊ := by
  let h := integerBellYield k r
  have hbudget : r*4^h ≤ 4^k := (integerBellYield_iff k r h hr hrdim).mp le_rfl
  have hnext : 4^k < r*4^(h+1) := by
    by_contra hle
    have hy := (integerBellYield_iff k r (h+1) hr hrdim).mpr (le_of_not_gt hle)
    change h+1 ≤ h at hy
    omega
  have hrpos : 0 < (r:ℝ) := by exact_mod_cast hr
  have hfour : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hleft := Real.log_le_log (mul_pos hrpos (by positivity))
    (show (r:ℝ)*(4:ℝ)^h ≤ (4:ℝ)^k by exact_mod_cast hbudget)
  have hright := Real.log_lt_log (by positivity : 0 < (4:ℝ)^k)
    (show (4:ℝ)^k < (r:ℝ)*(4:ℝ)^(h+1) by exact_mod_cast hnext)
  rw [Real.log_mul hrpos.ne' (by positivity), Real.log_pow, Real.log_pow] at hleft
  rw [Real.log_mul hrpos.ne' (by positivity), Real.log_pow, Real.log_pow] at hright
  have hdiv : Real.log (r:ℝ)/Real.log 4 ≤ (k:ℝ)-h :=
    (div_le_iff₀ hfour).mpr (by nlinarith [hleft])
  have hdiv' : (k:ℝ)-h-1 < Real.log (r:ℝ)/Real.log 4 :=
    (lt_div_iff₀ hfour).mpr (by push_cast at hright; nlinarith [hright])
  have hlow : (h:ℝ) ≤ (k:ℝ)-Real.log (r:ℝ)/Real.log 4 := by linarith
  have hhigh : (k:ℝ)-Real.log (r:ℝ)/Real.log 4 < (h:ℝ)+1 := by linarith
  exact ((Nat.floor_eq_iff (le_trans (Nat.cast_nonneg h) hlow)).mpr ⟨hlow,hhigh⟩).symm

/-- Equivalently, the expression uses one half of the base-two logarithm. -/
theorem integerBellYield_eq_paper_floor (k r : ℕ) (hr : 0 < r) (hrdim : r ≤ 4^k) :
    integerBellYield k r = ⌊(k:ℝ) - (1/2:ℝ)*(Real.log (r:ℝ)/Real.log 2)⌋₊ := by
  rw [integerBellYield_eq_real_floor k r hr hrdim]
  have hlog : Real.log 4 = 2 * Real.log 2 := by
    simpa only [show (2:ℝ)^2=4 by norm_num, Nat.cast_ofNat] using Real.log_pow (2:ℝ) 2
  rw [hlog]
  congr 1
  ring

end SpectralProtocol