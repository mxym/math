import BapatN200Matrix
import DefinitionBridge

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open scoped BigOperators ComplexOrder

namespace BapatExplicit
open BapatRankTwo BapatRankTwo.Exact BapatRankTwo.N200

theorem toComplex_norm_sq (z : GI) :
    ‖toComplex z‖ ^ 2 = ((z.re * z.re + z.im * z.im : ℤ) : ℝ) := by
  simp [Complex.sq_norm, Complex.normSq_apply, toComplex, Zsqrtd.lift_apply_apply]

/-- A finite kernel-checked bound on the actual ordered published data. -/
theorem integer_coordinate_norm_bounds : ∀ i : Fin 200,
    let z := vectorAt vectors i.val
    z.1.re * z.1.re + z.1.im * z.1.im ≤ (800 : ℤ) ∧
    z.2.re * z.2.re + z.2.im * z.2.im ≤ (800 : ℤ) := by
  decide +kernel

theorem vector_norm_sq_bounds (i : Fin 200) : ‖a i‖ ^ 2 ≤ (800 : ℝ) ∧
    ‖b i‖ ^ 2 ≤ (800 : ℝ) := by
  have hi := integer_coordinate_norm_bounds i
  constructor
  · rw [a, toComplex_norm_sq]
    exact_mod_cast hi.1
  · rw [b, toComplex_norm_sq]
    exact_mod_cast hi.2

theorem matrix_entry_norm_bound (i j : Fin 200) : ‖matrix i j‖ ≤ (1600 : ℝ) := by
  have hi := vector_norm_sq_bounds i
  have hj := vector_norm_sq_bounds j
  have ha : ‖a i‖ * ‖a j‖ ≤ (800 : ℝ) := by
    nlinarith [sq_nonneg (‖a i‖ - ‖a j‖)]
  have hb : ‖b i‖ * ‖b j‖ ≤ (800 : ℝ) := by
    nlinarith [sq_nonneg (‖b i‖ - ‖b j‖)]
  calc
    ‖matrix i j‖ ≤ ‖a i * star (a j)‖ + ‖b i * star (b j)‖ := norm_add_le _ _
    _ = ‖a i‖ * ‖a j‖ + ‖b i‖ * ‖b j‖ := by simp
    _ ≤ 1600 := by linarith

end BapatExplicit
