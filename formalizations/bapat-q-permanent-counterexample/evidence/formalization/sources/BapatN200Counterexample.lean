import BapatN200Trace
import BapatN200Matrix
import BapatExactStateBridge

set_option autoImplicit false
set_option maxRecDepth 100000

open scoped ComplexOrder
open Set

namespace BapatRankTwo.N200

theorem matrix_derivative_negative : (realQPolynomial matrix).derivative.eval 1 < 0 := by
  apply Exact.derivative_negative_of_gap (Exact.vectorAt vectors) 200
  rw [state_eq_200]
  change 0 < wedgeNorm - 19900 * permanentNorm
  exact sub_pos.mpr norm_gap_positive

/-- A full counterexample to the original conjecture, in dimension 200.
The small positive shift and two interior real points are existential; this
theorem does not claim the paper's particular epsilon or q0 bounds. -/
theorem explicit_counterexample :
    ∃ δ : ℝ, 0 < δ ∧ (perturb matrix δ).PosDef ∧ ¬ (perturb matrix δ).IsDiag ∧
      ∃ q₁ ∈ Ioo (-1 : ℝ) 1, ∃ q₂ ∈ Ioo (-1 : ℝ) 1,
        q₁ < q₂ ∧ (qPermanent (perturb matrix δ) (q₂ : ℂ)).re <
          (qPermanent (perturb matrix δ) (q₁ : ℂ)).re := by
  obtain ⟨δ, hδ, hp, q₁, h₁, q₂, h₂, hlt, hdec⟩ :=
    exists_posDef_interior_counterexample_of_psd_derivative_neg
      matrix_posSemidef matrix_derivative_negative
  exact ⟨δ, hδ, hp, perturb_matrix_not_isDiag δ, q₁, h₁, q₂, h₂, hlt, hdec⟩

theorem originalBapatConjecture_false : ¬ OriginalBapatConjecture :=
  originalBapatConjecture_false_of_psd_derivative_neg
    matrix_posSemidef matrix_not_isDiag matrix_derivative_negative

theorem bapatConjecture_false : ¬ BapatConjecture :=
  bapatConjecture_false_of_psd_derivative_neg matrix_posSemidef matrix_derivative_negative

end BapatRankTwo.N200
