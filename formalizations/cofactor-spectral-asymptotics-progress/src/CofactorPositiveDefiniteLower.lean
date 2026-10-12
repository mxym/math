import CofactorPositiveDefinitePerturbation
import CofactorSharpMain

/-! The same sharp lower bounds hold for positive definite correlation matrices.
The perturbation has no exact-rank-two requirement. -/
set_option autoImplicit false
open scoped ComplexOrder Topology
open Filter
namespace CofactorSpectral
noncomputable section

theorem psdCorrelation_complex_ratio_le_pdExtremum {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℂ) (hA : psdAdmissible A) (hd : ∀ i, A i i = 1)
    (w : Fin N → ℂ) (hw : 0 < vectorNormSq w) :
    cofactorRayleighRatio A w ≤ pdComplexExtremum N := by
  apply le_of_forall_lt
  intro c hc
  obtain ⟨B,hB,hcB⟩ := exists_pd_correlation_above_ratio A hA hd w hw c hc
  have hb : cofactorRayleighRatio B w ∈ complexRayleighValues N pdCorrelationAdmissible :=
    ⟨B,hB,w,hw,rfl⟩
  exact hcB.trans_le (le_csSup (complexRayleighValues_bddAbove N _
    (fun _ h => ⟨h.1.posSemidef,h.2.1⟩)) hb)

theorem psdCorrelation_real_ratio_le_pdExtremum {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℂ) (hA : psdAdmissible A) (hd : ∀ i, A i i = 1)
    (w : Fin N → ℝ) (hw : 0 < vectorNormSq (fun i => (w i : ℂ))) :
    cofactorRayleighRatio A (fun i => (w i : ℂ)) ≤ pdRealExtremum N := by
  apply le_of_forall_lt
  intro c hc
  obtain ⟨B,hB,hcB⟩ := exists_pd_correlation_above_ratio A hA hd (fun i => (w i : ℂ)) hw c hc
  have hb : cofactorRayleighRatio B (fun i => (w i : ℂ)) ∈ realRayleighValues N pdCorrelationAdmissible :=
    ⟨B,hB,w,hw,rfl⟩
  exact hcB.trans_le (le_csSup (realRayleighValues_bddAbove N _
    (fun _ h => ⟨h.1.posSemidef,h.2.1⟩)) hb)

theorem eventually_pd_extrema_degree_lower (C b δ η : ℝ) (hC : 0 < C) (hb : 1 < b)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hη : 0 < η)
    (hθ : entropyConstant b/(C*Real.exp 1*(1-δ)) < 1) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ N0 : ℕ, ∀ N ≥ N0,
      (degreeCount b m δ N : ℝ)/(C*(1+η)) ≤ pdComplexExtremum N ∧
      (degreeCount b m δ N : ℝ)/(2*C*(1+η)) ≤ pdRealExtremum N := by
  obtain ⟨m,hm,N0,hN0⟩ := eventually_actual_ring_lower_witness C b δ η hC hb hδ0 hδ1 hη hθ
  refine ⟨m,hm,N0,?_⟩
  intro N hN
  obtain ⟨z,hA,hz,hi,hc,hr⟩ := hN0 N hN
  exact ⟨hc.trans (psdCorrelation_complex_ratio_le_pdExtremum _ hA.1 hA.2.1 z hz),
    hr.trans (psdCorrelation_real_ratio_le_pdExtremum _ hA.1 hA.2.1 (fun i => (z i).im) hi)⟩

theorem pd_extrema_eventual_fixed_log_lower (C b δ η ε : ℝ) (hC : 0 < C) (hb : 1 < b)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hη : 0 < η) (hε : 0 < ε)
    (hθ : entropyConstant b/(C*Real.exp 1*(1-δ)) < 1) :
    ∃ N0 : ℕ, ∀ N ≥ N0,
      1/(C*(1+η)*Real.log b)-ε ≤ pdComplexExtremum N/Real.log (N : ℝ) ∧
      (1/(C*(1+η)*Real.log b)-ε)/2 ≤ pdRealExtremum N/Real.log (N : ℝ) := by
  obtain ⟨m,hm,N0,hN0⟩ := eventually_pd_extrema_degree_lower C b δ η hC hb hδ0 hδ1 hη hθ
  have hD : 0 < C*(1+η) := mul_pos hC (by linarith)
  obtain ⟨N1,hN1⟩ := degreeCount_eventual_log_lower b hb m δ (C*(1+η)) ε hD hε
  refine ⟨max N0 N1,?_⟩
  intro N hN
  obtain ⟨hc,hr⟩ := hN0 N ((le_max_left _ _).trans hN)
  obtain ⟨hd,hlog⟩ := hN1 N ((le_max_right _ _).trans hN)
  have he : ((degreeCount b m δ N : ℝ)/(2*C*(1+η)))/Real.log (N : ℝ) =
      (((degreeCount b m δ N : ℝ)/(C*(1+η)))/Real.log (N : ℝ))/2 := by
    have hT : 1+η ≠ 0 := by linarith
    field_simp [hC.ne',hlog.ne',hT]
    <;> ring
  have hrn := div_le_div_of_nonneg_right hr hlog.le
  rw [he] at hrn
  exact ⟨hd.trans (div_le_div_of_nonneg_right hc hlog.le),
    (div_le_div_of_nonneg_right hd (by norm_num : (0 : ℝ) ≤ 2)).trans hrn⟩

theorem pd_extrema_eventual_sharp_log_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N ≥ N0,
      1-ε ≤ pdComplexExtremum N/Real.log (N : ℝ) ∧
      1/2-ε ≤ pdRealExtremum N/Real.log (N : ℝ) := by
  have he : 0 < ε/2 := by linarith
  obtain ⟨C,b,δ,η,hC,hb,hδ0,hδ1,hη,hθ,hval⟩ := exists_sharp_lower_parameters (ε/2) he
  obtain ⟨N0,hN0⟩ := pd_extrema_eventual_fixed_log_lower C b δ η (ε/2) hC hb hδ0 hδ1 hη he hθ
  refine ⟨N0,?_⟩
  intro N hN
  obtain ⟨hc,hr⟩ := hN0 N hN
  exact ⟨by linarith,by linarith⟩

theorem pdComplexExtremum_log_tendsto :
    Tendsto (fun N : ℕ => pdComplexExtremum N/Real.log (N : ℝ)) atTop (𝓝 1) := by
  apply tendsto_of_eventual_two_sided_bounds
  · intro ε hε
    obtain ⟨N,hN⟩ := pd_extrema_eventual_sharp_log_lower ε hε
    exact ⟨N,fun n hn => (hN n hn).1⟩
  · exact pdComplexExtremum_eventual_log_upper

theorem pdRealExtremum_log_tendsto :
    Tendsto (fun N : ℕ => pdRealExtremum N/Real.log (N : ℝ)) atTop (𝓝 (1/2)) := by
  apply tendsto_of_eventual_two_sided_bounds
  · intro ε hε
    obtain ⟨N,hN⟩ := pd_extrema_eventual_sharp_log_lower ε hε
    exact ⟨N,fun n hn => (hN n hn).2⟩
  · exact pdRealExtremum_eventual_log_upper

end
end CofactorSpectral
