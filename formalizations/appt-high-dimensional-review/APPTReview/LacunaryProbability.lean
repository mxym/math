import APPTReview.LacunaryEnergy

open scoped BigOperators NNReal
open MeasureTheory
namespace APPTReview

/-- The limiting-measure energy inequality, for arbitrary probability measures.
No finite-support assumption or independently optimized level measure is used. -/
theorem lacunary_probability_energy (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (ds : List ℝ) (hds : LacunaryScales ds) (e : ℝ → ℝ) (B : ℝ)
    (hB : 0≤B) (he : ∀ d∈ds,0≤e d) (heB : ∀ d∈ds,e d≤B) :
    (∑ d∈ds.toFinset,Real.sqrt (e d*((μ.prod μ).real (scaleLine d)/2))) ≤
      Real.sqrt (∑ d∈ds.toFinset,e d)/2+Real.sqrt (B/2) := by
  classical
  have hq : (∑ d∈ds.toFinset,(μ.prod μ).real (scaleOff d)/2)≤1/4 := by
    rw [← Finset.sum_div]
    linarith [lacunary_off_mass μ ds hds.2]
  have hl := scale_center_mass μ ds.toFinset
    (fun d hd => (hds.1 d (List.mem_toFinset.mp hd)).le)
  have hb := lacunary_energy_budget ds.toFinset e
    (fun d => (μ.prod μ).real (scaleOff d)/2)
    (fun d => μ.real {scaleCenter d}) B hB
    (fun d hd => he d (List.mem_toFinset.mp hd))
    (fun d hd => heB d (List.mem_toFinset.mp hd))
    (fun _ _ => div_nonneg measureReal_nonneg (by norm_num))
    (fun _ _ => measureReal_nonneg) hq hl
  convert hb using 1
  apply Finset.sum_congr rfl
  intro d hd
  rw [scaleLine_measure_split μ d (hds.1 d (List.mem_toFinset.mp hd)).le]
  congr 2
  ring

end APPTReview

namespace APPTReview

/-- Rayleigh-scale form with all factors of two retained. -/
theorem lacunary_probability_energy_doubled (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (ds : List ℝ) (hds : LacunaryScales ds) (e : ℝ → ℝ) (B : ℝ)
    (hB : 0≤B) (he : ∀ d∈ds,0≤e d) (heB : ∀ d∈ds,e d≤B) :
    2*(∑ d∈ds.toFinset,Real.sqrt (e d*((μ.prod μ).real (scaleLine d)/2))) ≤
      Real.sqrt (∑ d∈ds.toFinset,e d)+Real.sqrt (2*B) := by
  have h := lacunary_probability_energy μ ds hds e B hB he heB
  have hs : 2*Real.sqrt (B/2)=Real.sqrt (2*B) := by
    have h1 := Real.sq_sqrt (div_nonneg hB (by norm_num : (0:ℝ)≤2))
    have h2 := Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ)≤2) hB)
    have hp := Real.sqrt_nonneg (B/2)
    have hq := Real.sqrt_nonneg (2*B)
    nlinarith
  linarith

end APPTReview
