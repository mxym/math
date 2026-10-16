import Deviation.KernelPrimitive

open scoped NNReal ENNReal Topology MeasureTheory
open MeasureTheory ProbabilityTheory Filter Set

namespace ExtractionDeviation
noncomputable section

theorem sincKernelMeasure_real (E : Set ℝ) (hE : MeasurableSet E) :
    sincKernelMeasure.real E=∫ x in E,sincKernelPDF x := by
  rw [measureReal_def,sincKernelMeasure,withDensity_apply _ hE,
    ← ofReal_integral_eq_lintegral_ofReal sincKernelPDF_integrable.integrableOn
      (ae_of_all _ sincKernelPDF_nonneg),ENNReal.toReal_ofReal]
  exact integral_nonneg sincKernelPDF_nonneg

def sincNoiseCDF (x : ℝ) : ℝ := sincKernelMeasure.real (Iic x)

theorem sincNoiseCDF_sub (x y : ℝ) (hxy : x≤y) :
    sincNoiseCDF y-sincNoiseCDF x=∫ z in x..y,sincKernelPDF z := by
  have hdiff : sincNoiseCDF y-sincNoiseCDF x=sincKernelMeasure.real (Ioc x y) := by
    rw [← Iic_sdiff_Iic,measureReal_sdiff (Iic_subset_Iic.mpr hxy) measurableSet_Iic]
    rfl
  rw [hdiff,sincKernelMeasure_real _ measurableSet_Ioc,
    intervalIntegral.integral_of_le hxy]

/-- An exact identity for the actual noise CDF, valid on either side of zero.
No CDF/Fourier inversion identity is a caller assumption. -/
theorem sincNoiseCDF_primitive (u : ℝ) :
    sincNoiseCDF u-sincNoiseCDF 0=sincKernelPrimitive u/sincKernelIntegral := by
  have heq : (∫ z in (0:ℝ)..u,sincKernelPDF z)=
      sincKernelPrimitive u/sincKernelIntegral := by
    change (∫ z in (0:ℝ)..u,sincKernel z/sincKernelIntegral)=_
    exact intervalIntegral.integral_div _ _
  rw [← heq]
  rcases le_total (0:ℝ) u with hu|hu
  · exact sincNoiseCDF_sub 0 u hu
  · have h := sincNoiseCDF_sub u 0 hu
    rw [intervalIntegral.integral_symm] at h
    linarith

theorem sincNoiseCDF_compact_representation (u : ℝ) :
    ((sincNoiseCDF u-sincNoiseCDF 0:ℝ):ℂ)=
      (∫ t,exponentialPrimitive t u ∂compactFrequency)/(sincKernelIntegral:ℂ) := by
  rw [sincNoiseCDF_primitive,Complex.ofReal_div,sincKernelPrimitive_representation]

end
end ExtractionDeviation
