import CofactorDegreeSequence
import CofactorExtremaUpper

/-! Actual rank-two witnesses give lower bounds for the four actual variational extrema. -/
set_option autoImplicit false
open scoped ComplexOrder
namespace CofactorSpectral
noncomputable section

theorem rankTwo_witness_extrema_lower {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : rankTwoCorrelationAdmissible A) (z : Fin N → ℂ) (x : Fin N → ℝ)
    (hz : 0 < vectorNormSq z) (hx : 0 < vectorNormSq (fun i => (x i : ℂ)))
    (Lc Lr : ℝ) (hc : Lc ≤ cofactorRayleighRatio A z)
    (hr : Lr ≤ cofactorRayleighRatio A (fun i => (x i : ℂ))) :
    Lc ≤ complexExtremum N ∧ Lr ≤ realExtremum N ∧
      Lc ≤ rankTwoComplexExtremum N ∧ Lr ≤ rankTwoRealExtremum N := by
  have hcp : cofactorRayleighRatio A z ∈ complexRayleighValues N psdAdmissible :=
    ⟨A,hA.1,z,hz,rfl⟩
  have hrp : cofactorRayleighRatio A (fun i => (x i : ℂ)) ∈ realRayleighValues N psdAdmissible :=
    ⟨A,hA.1,x,hx,rfl⟩
  have hc2 : cofactorRayleighRatio A z ∈ complexRayleighValues N rankTwoCorrelationAdmissible :=
    ⟨A,hA,z,hz,rfl⟩
  have hr2 : cofactorRayleighRatio A (fun i => (x i : ℂ)) ∈ realRayleighValues N rankTwoCorrelationAdmissible :=
    ⟨A,hA,x,hx,rfl⟩
  exact ⟨hc.trans (le_csSup (complexRayleighValues_bddAbove N _ (fun _ h => h)) hcp),
    hr.trans (le_csSup (realRayleighValues_bddAbove N _ (fun _ h => h)) hrp),
    hc.trans (le_csSup (complexRayleighValues_bddAbove N _ (fun _ h => h.1)) hc2),
    hr.trans (le_csSup (realRayleighValues_bddAbove N _ (fun _ h => h.1)) hr2)⟩

end
end CofactorSpectral
