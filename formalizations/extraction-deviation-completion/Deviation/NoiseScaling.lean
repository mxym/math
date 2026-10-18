import Deviation.SincKernel

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter

namespace ExtractionDeviation
noncomputable section

def scaledNoise (μ : Measure ℝ) (R : ℝ) : Measure ℝ := μ.map (fun y => y/R)

instance scaledNoise_isProbabilityMeasure (μ : Measure ℝ) [IsProbabilityMeasure μ] (R : ℝ) :
    IsProbabilityMeasure (scaledNoise μ R) := by
  constructor
  rw [scaledNoise,Measure.map_apply (by fun_prop) MeasurableSet.univ]
  simp

theorem scaledNoise_firstMoment_integrable (μ : Measure ℝ)
    (habs : Integrable (fun y : ℝ => |y|) μ) (R : ℝ) :
    Integrable (fun y : ℝ => |y|) (scaledNoise μ R) := by
  rw [scaledNoise,integrable_map_measure continuous_abs.aestronglyMeasurable (by fun_prop)]
  change Integrable (fun y : ℝ => |y/R|) μ
  simp_rw [abs_div]
  exact habs.div_const |R|

theorem scaledNoise_firstMoment (μ : Measure ℝ) (R : ℝ) (hR : 0<R) :
    (∫ y,|y| ∂scaledNoise μ R)=(∫ y,|y| ∂μ)/R := by
  rw [scaledNoise,integral_map (by fun_prop) continuous_abs.aestronglyMeasurable]
  simp_rw [abs_div,abs_of_pos hR]
  exact integral_div _ _

/-- An actual scaled-noise smoothing estimate. All tail probabilities are
derived from the original noise's finite first moment. -/
theorem cdfSupError_scaled_noise_smoothing (F G : ℝ → ℝ) (hF : Monotone F)
    (hF01 : ∀ x,0≤F x ∧ F x≤1) (hG01 : ∀ x,0≤G x ∧ G x≤1)
    (M : ℝ≥0) (hG : LipschitzWith M G)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (habs : Integrable (fun y : ℝ => |y|) μ)
    (R δ : ℝ) (hR : 0<R)
    (hsm : ∀ z,|smoothedCDFDifference F G (scaledNoise μ R) z|≤δ) :
    cdfSupError F G≤2*δ+(2*(M:ℝ)*(5*(∫ y,|y| ∂μ)+1))/R := by
  let m := ∫ y,|y| ∂μ
  have hm : 0≤m := integral_nonneg (fun _ => abs_nonneg _)
  let a := (4*m+1)/R
  have ha : 0<a := div_pos (by positivity) hR
  have hmom : 4*(∫ y,|y| ∂scaledNoise μ R)≤a := by
    rw [scaledNoise_firstMoment μ R hR]
    dsimp [a,m]
    rw [← mul_div_assoc]
    apply (div_le_div_iff_of_pos_right hR).mpr
    linarith
  have h := cdfSupError_firstMoment_smoothing F G hF hF01 hG01 M hG
    (scaledNoise μ R) (scaledNoise_firstMoment_integrable μ habs R) a δ ha hmom hsm
  rw [scaledNoise_firstMoment μ R hR] at h
  apply h.trans_eq
  dsimp [a,m]
  ring

def sincNoiseMoment : ℝ := ∫ y,|y| ∂sincKernelMeasure

theorem sincNoiseMoment_nonneg : 0≤sincNoiseMoment := integral_nonneg (fun _ => abs_nonneg _)

theorem sinc_noise_gaussian_smoothing (F : ℝ → ℝ) (hF : Monotone F)
    (hF01 : ∀ x,0≤F x ∧ F x≤1) (R δ : ℝ) (hR : 0<R)
    (hsm : ∀ z,|smoothedCDFDifference F (gaussianCDF 1)
      (scaledNoise sincKernelMeasure R) z|≤δ) :
    cdfSupError F (gaussianCDF 1)≤2*δ+(2*gaussianPeak*(5*sincNoiseMoment+1))/R := by
  have hG01 : ∀ x,0≤gaussianCDF 1 x ∧ gaussianCDF 1 x≤1 :=
    fun _ => ⟨measureReal_nonneg,measureReal_le_one⟩
  have h := cdfSupError_scaled_noise_smoothing F (gaussianCDF 1) hF hF01 hG01
    gaussianPeak.toNNReal gaussianCDF_lipschitz sincKernelMeasure
    sincKernelMeasure_firstMoment_integrable R δ hR hsm
  simpa only [Real.coe_toNNReal _ gaussianPeak_pos.le,sincNoiseMoment] using h

end
end ExtractionDeviation
