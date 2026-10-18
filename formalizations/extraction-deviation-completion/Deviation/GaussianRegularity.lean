import Deviation.Gaussian

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Set

namespace ExtractionDeviation
noncomputable section

def gaussianPeak : ℝ := (Real.sqrt (2*Real.pi))⁻¹

theorem gaussianPeak_pos : 0 < gaussianPeak := by unfold gaussianPeak; positivity

theorem standardGaussianPDF_le_peak (x : ℝ) : gaussianPDFReal 0 1 x ≤ gaussianPeak := by
  unfold gaussianPDFReal gaussianPeak
  simp only [NNReal.coe_one,mul_one,sub_zero]
  calc
    _ ≤ (Real.sqrt (2*Real.pi))⁻¹*1 := mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (sq_nonneg x)) (by norm_num))) (by positivity)
    _ = _ := mul_one _

theorem gaussianCDF_sub_le_peak (x y : ℝ) (hxy : x ≤ y) :
    gaussianCDF 1 y-gaussianCDF 1 x ≤ gaussianPeak*(y-x) := by
  have hdiff : gaussianCDF 1 y-gaussianCDF 1 x = (gaussianReal 0 1).real (Ioc x y) := by
    rw [← Iic_sdiff_Iic,measureReal_sdiff (Iic_subset_Iic.mpr hxy) measurableSet_Iic]
    rfl
  rw [hdiff]
  have heq : (gaussianReal 0 1).real (Ioc x y) = ∫ z in Ioc x y, gaussianPDFReal 0 1 z := by
    rw [measureReal_def,gaussianReal_apply_eq_integral 0 one_ne_zero,ENNReal.toReal_ofReal]
    exact integral_nonneg (fun z => gaussianPDFReal_nonneg 0 1 z)
  rw [heq]
  letI : IsFiniteMeasure (volume.restrict (Ioc x y)) :=
    ⟨by simp only [Measure.restrict_apply_univ,Real.volume_Ioc]; finiteness⟩
  calc
    _ ≤ ∫ _z in Ioc x y, gaussianPeak := integral_mono
      (integrable_gaussianPDFReal 0 1).integrableOn (integrable_const _)
      standardGaussianPDF_le_peak
    _ = gaussianPeak*(y-x) := by
      rw [integral_const]
      simp only [measureReal_def,Measure.restrict_apply_univ,Real.volume_Ioc,ENNReal.toReal_ofReal (sub_nonneg.mpr hxy),
        smul_eq_mul]
      ring

theorem gaussianCDF_lipschitz : LipschitzWith gaussianPeak.toNNReal (gaussianCDF 1) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,Real.dist_eq]
  rw [Real.coe_toNNReal _ gaussianPeak_pos.le]
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr (gaussianCDF_mono 1 hxy)),
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    have h := gaussianCDF_sub_le_peak x y hxy
    simpa only [neg_sub] using h
  · rw [abs_of_nonneg (sub_nonneg.mpr (gaussianCDF_mono 1 hyx)),
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact gaussianCDF_sub_le_peak y x hyx

end
end ExtractionDeviation
