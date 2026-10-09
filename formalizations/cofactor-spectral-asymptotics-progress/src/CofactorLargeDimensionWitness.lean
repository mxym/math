import CofactorDegreeFits
import CofactorWitnessExtrema

/-! Actual lower witnesses in every sufficiently large dimension, not merely a subsequence. -/
set_option autoImplicit false
open scoped BigOperators ComplexOrder
namespace CofactorSpectral
noncomputable section

theorem eventually_actual_ring_lower_witness (C b δ η : ℝ) (hC : 0 < C) (hb : 1 < b)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hη : 0 < η)
    (hθ : entropyConstant b/(C*Real.exp 1*(1-δ)) < 1) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ N0 : ℕ, ∀ N ≥ N0,
      ∃ z : Fin N → ℂ,
        rankTwoCorrelationAdmissible (normalizedBinaryGram z) ∧
        0 < vectorNormSq z ∧ 0 < vectorNormSq (fun i => ((z i).im : ℂ)) ∧
        (degreeCount b m δ N : ℝ)/(C*(1+η)) ≤ cofactorRayleighRatio (normalizedBinaryGram z) z ∧
        (degreeCount b m δ N : ℝ)/(2*C*(1+η)) ≤
          cofactorRayleighRatio (normalizedBinaryGram z) (fun i => ((z i).im : ℂ)) := by
  obtain ⟨m,hm,hThreshold⟩ := exists_ring_lower_threshold C b δ η hC hb hδ1 hη hθ
  have hmp : 0 < m := by omega
  obtain ⟨N0,hFits⟩ := eventually_degreeCount_fits b hb m hmp δ hδ0 hδ1
  refine ⟨m,hm,N0,?_⟩
  intro N hN
  obtain ⟨hK,hr,hsize,hfrac,hlog⟩ := hFits N hN
  cases N with
  | zero => simp only [Nat.cast_zero,Real.log_zero] at hlog; linarith
  | succ n =>
    exact hThreshold n _ _ _ hr hK
      (fun k => ringDegreeSequence_min b hb m hmp k.val)
      (fun i j hij => ringDegreeSequence_separation b hb m hmp i.val j.val hij)
      hsize (by simpa only [Nat.cast_succ] using hfrac)

theorem eventually_four_extrema_degree_lower (C b δ η : ℝ) (hC : 0 < C) (hb : 1 < b)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hη : 0 < η)
    (hθ : entropyConstant b/(C*Real.exp 1*(1-δ)) < 1) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ N0 : ℕ, ∀ N ≥ N0,
      (degreeCount b m δ N : ℝ)/(C*(1+η)) ≤ complexExtremum N ∧
      (degreeCount b m δ N : ℝ)/(2*C*(1+η)) ≤ realExtremum N ∧
      (degreeCount b m δ N : ℝ)/(C*(1+η)) ≤ rankTwoComplexExtremum N ∧
      (degreeCount b m δ N : ℝ)/(2*C*(1+η)) ≤ rankTwoRealExtremum N := by
  obtain ⟨m,hm,N0,hN0⟩ := eventually_actual_ring_lower_witness C b δ η hC hb hδ0 hδ1 hη hθ
  refine ⟨m,hm,N0,?_⟩
  intro N hN
  obtain ⟨z,hA,hz,hi,hc,hr⟩ := hN0 N hN
  exact rankTwo_witness_extrema_lower (normalizedBinaryGram z) hA z (fun i => (z i).im)
    hz hi _ _ hc hr

end
end CofactorSpectral
