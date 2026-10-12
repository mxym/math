import BapatN200Data
import BapatOriginalStatement

set_option autoImplicit false

open scoped ComplexOrder

namespace BapatRankTwo.N200

noncomputable def a (i : Fin 200) : ℂ := Exact.toComplex (Exact.vectorAt vectors i.val).1
noncomputable def b (i : Fin 200) : ℂ := Exact.toComplex (Exact.vectorAt vectors i.val).2
noncomputable def matrix : Matrix (Fin 200) (Fin 200) ℂ := gram a b

theorem matrix_posSemidef : matrix.PosSemidef := gram_posSemidef a b

/-- The first off-diagonal entry of the actual published ordered matrix. -/
theorem matrix_zero_one : matrix 0 1 = 398 - Complex.I := by
  change Exact.toComplex ⟨13, -5⟩ * star (Exact.toComplex ⟨12, -6⟩) +
    Exact.toComplex ⟨-6, -13⟩ * star (Exact.toComplex ⟨-5, -14⟩) = _
  apply Complex.ext <;>
    norm_num [Exact.toComplex, Zsqrtd.lift_apply_apply, Complex.mul_re, Complex.mul_im]

theorem matrix_not_isDiag : ¬ matrix.IsDiag := by
  intro hd
  have hz := hd (by decide : (0 : Fin 200) ≠ 1)
  change matrix 0 1 = 0 at hz
  rw [matrix_zero_one] at hz
  have hi := congrArg Complex.im hz
  norm_num at hi

theorem perturb_matrix_posDef {δ : ℝ} (hδ : 0 < δ) : (perturb matrix δ).PosDef :=
  perturb_posDef matrix_posSemidef hδ

theorem perturb_matrix_not_isDiag (δ : ℝ) : ¬ (perturb matrix δ).IsDiag :=
  perturb_not_isDiag matrix_not_isDiag δ

end BapatRankTwo.N200
