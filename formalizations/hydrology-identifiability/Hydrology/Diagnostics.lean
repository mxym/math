import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace HydrologyIdentifiability

/-! Exact local diagnostics for a shifted power-law recession.

The analytic substitution producing these identities is described in the
accompanying note. This file formalizes the algebraic recovery step once the
three observed jets have been supplied.
-/

/-- A positive power-law exponent has curvature invariant strictly above one. -/
theorem powerLaw_invariant_gt_one {α : ℝ} (hα : 0 < α) :
    1 < (α + 1) / α := by
  field_simp [ne_of_gt hα]
  linarith

/-- The exponent is uniquely recovered from the curvature invariant
`K = Q Q''/(Q')^2 = (α+1)/α`. -/
theorem powerLaw_alpha_recovery
    (K α : ℝ) (hα : α ≠ 0)
    (hshape : K = (α + 1) / α) :
    α = 1 / (K - 1) := by
  have hshape' : K * α = α + 1 := by
    field_simp [hα] at hshape
    linarith
  have hK : K - 1 ≠ 0 := by
    intro hzero
    have : K = 1 := by linarith
    rw [this] at hshape'
    linarith
  field_simp [hK]
  linarith

/-- Once the exponent is known, the local slope recovers the shifted time:
`Q' (τ+t) = -α Q` implies `τ = -α Q/Q' - t`. -/
theorem powerLaw_shift_recovery
    (q q₁ α τ t : ℝ) (hq₁ : q₁ ≠ 0)
    (hslope : q₁ * (τ + t) = -α * q) :
    τ = -α * q / q₁ - t := by
  field_simp [hq₁]
  linarith

end HydrologyIdentifiability
