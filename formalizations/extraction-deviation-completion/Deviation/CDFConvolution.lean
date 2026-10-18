import Deviation.KernelCDF
import Deviation.NoiseScaling

open scoped NNReal ENNReal Topology MeasureTheory
open MeasureTheory ProbabilityTheory Filter Set

namespace ExtractionDeviation
noncomputable section

def measureCDF (μ : Measure ℝ) (x : ℝ) : ℝ := μ.real (Iic x)

theorem measureCDF_mono (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Monotone (measureCDF μ) := by
  intro x y hxy
  exact measureReal_mono (Iic_subset_Iic.mpr hxy)

theorem measureCDF_mem_unitInterval (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    0≤measureCDF μ x ∧ measureCDF μ x≤1 := ⟨measureReal_nonneg,measureReal_le_one⟩

theorem measureCDF_shift_integrable (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (x : ℝ) : Integrable (fun y => measureCDF μ (x-y)) ν := by
  apply (integrable_const (1:ℝ)).mono'
    (((measureCDF_mono μ).measurable.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
  apply ae_of_all
  intro y
  change ‖measureCDF μ (x-y)‖≤1
  rw [Real.norm_eq_abs,abs_of_nonneg (measureCDF_mem_unitInterval μ _).1]
  exact (measureCDF_mem_unitInterval μ _).2

theorem measureCDF_conv (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (x : ℝ) :
    measureCDF (μ ∗ ν) x=∫ y,measureCDF μ (x-y) ∂ν := by
  rw [Measure.conv_comm μ ν]
  have hi : Integrable ((Iic x).indicator (fun _ : ℝ => (1:ℝ))) (ν ∗ μ) :=
    (integrable_const _).indicator measurableSet_Iic
  have hc := integral_conv hi
  have hleft : (∫ z,(Iic x).indicator (fun _ : ℝ => (1:ℝ)) z ∂(ν ∗ μ))=
      measureCDF (ν ∗ μ) x := by
    rw [integral_indicator_const _ measurableSet_Iic,smul_eq_mul,mul_one]
    rfl
  rw [hleft] at hc
  rw [hc]
  apply integral_congr_ae
  apply ae_of_all
  intro y
  have heq : (fun z : ℝ => (Iic x).indicator (fun _ : ℝ => (1:ℝ)) (y+z))=
      (Iic (x-y)).indicator (fun _ : ℝ => (1:ℝ)) := by
    ext z
    simp only [indicator,mem_Iic,
      show y+z≤x ↔ z≤x-y by constructor <;> intro h <;> linarith]
  change (∫ z,(Iic x).indicator (fun _ : ℝ => (1:ℝ)) (y+z) ∂μ)=measureCDF μ (x-y)
  rw [heq,integral_indicator_const _ measurableSet_Iic,smul_eq_mul,mul_one]
  rfl

/-- The smoothed actual CDF discrepancy is the difference of expectations of
the noise CDF. This connects the real-space smoothing definition to the kernel
primitive without any probabilistic approximation assumption. -/
theorem smoothed_measureCDF_difference (μ ν noise : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure noise] (x : ℝ) :
    smoothedCDFDifference (measureCDF μ) (measureCDF ν) noise x=
      (∫ z,measureCDF noise (x-z) ∂μ)-(∫ z,measureCDF noise (x-z) ∂ν) := by
  rw [smoothedCDFDifference,integral_sub (measureCDF_shift_integrable μ noise x)
    (measureCDF_shift_integrable ν noise x),← measureCDF_conv,← measureCDF_conv,
    Measure.conv_comm μ noise,Measure.conv_comm ν noise,measureCDF_conv,measureCDF_conv]

end
end ExtractionDeviation
