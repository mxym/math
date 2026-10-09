import CofactorFixedParameterLower
import CofactorSharpParameters

/-! The four sharp lower bounds, with all construction parameters fixed before dimension tends to infinity. -/
set_option autoImplicit false
namespace CofactorSpectral
noncomputable section

theorem four_extrema_eventual_sharp_log_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N ≥ N0,
      1-ε ≤ complexExtremum N/Real.log (N : ℝ) ∧
      1/2-ε ≤ realExtremum N/Real.log (N : ℝ) ∧
      1-ε ≤ rankTwoComplexExtremum N/Real.log (N : ℝ) ∧
      1/2-ε ≤ rankTwoRealExtremum N/Real.log (N : ℝ) := by
  have he : 0 < ε/2 := by linarith
  obtain ⟨C,b,δ,η,hC,hb,hδ0,hδ1,hη,hθ,hval⟩ := exists_sharp_lower_parameters (ε/2) he
  obtain ⟨N0,hN0⟩ := four_extrema_eventual_fixed_log_lower C b δ η (ε/2) hC hb hδ0 hδ1 hη he hθ
  refine ⟨N0,?_⟩
  intro N hN
  obtain ⟨hc,hr,hc2,hr2⟩ := hN0 N hN
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

end
end CofactorSpectral
