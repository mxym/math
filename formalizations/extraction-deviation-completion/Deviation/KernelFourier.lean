import Deviation.KernelExpectation

open scoped NNReal ENNReal Topology MeasureTheory
open MeasureTheory ProbabilityTheory Filter Set

namespace ExtractionDeviation
noncomputable section

def primitiveFrequencyIntegrand (μ : Measure ℝ) (x t : ℝ) : ℂ :=
  (Complex.exp (((t*x:ℝ):ℂ)*Complex.I)*charFun μ (-t)-1)/((t:ℂ)*Complex.I)

theorem primitiveFrequencyIntegrand_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (habs : Integrable (fun z : ℝ => |z|) μ) (x : ℝ) :
    Integrable (primitiveFrequencyIntegrand μ x) compactFrequency := by
  have hi : Integrable (fun t : ℝ => ∫ z,exponentialPrimitive t (x-z) ∂μ) compactFrequency :=
    (exponentialPrimitive_product_integrable μ habs x).integral_prod_left
  apply hi.congr
  filter_upwards [compactFrequency_ae_ne_zero] with t ht
  exact exponentialPrimitive_expectation μ t x ht

theorem sincNoiseCDF_expectation (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    (∫ z,sincNoiseCDF (x-z) ∂μ)-sincNoiseCDF 0=
      (∫ z,sincKernelPrimitive (x-z) ∂μ)/sincKernelIntegral := by
  have hi : Integrable (fun z => sincNoiseCDF (x-z)) μ :=
    measureCDF_shift_integrable sincKernelMeasure μ x
  calc
    _ = ∫ z,sincNoiseCDF (x-z)-sincNoiseCDF 0 ∂μ := by
      rw [integral_sub hi (integrable_const _)]
      simp
    _ = _ := by
      simp_rw [sincNoiseCDF_primitive]
      exact integral_div _ _

theorem smoothed_sinc_primitive_difference (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (x : ℝ) :
    smoothedCDFDifference (measureCDF μ) (measureCDF ν) sincKernelMeasure x=
      ((∫ z,sincKernelPrimitive (x-z) ∂μ)-(∫ z,sincKernelPrimitive (x-z) ∂ν))/sincKernelIntegral := by
  rw [smoothed_measureCDF_difference]
  have hμ := sincNoiseCDF_expectation μ x
  have hν := sincNoiseCDF_expectation ν x
  change (∫ z,sincNoiseCDF (x-z) ∂μ)-(∫ z,sincNoiseCDF (x-z) ∂ν)=_
  calc
    _ = ((∫ z,sincNoiseCDF (x-z) ∂μ)-sincNoiseCDF 0)-
        ((∫ z,sincNoiseCDF (x-z) ∂ν)-sincNoiseCDF 0) := by ring
    _ = _ := by rw [hμ,hν]; ring

/-- Exact Fourier representation of the discrepancy between two actual CDFs
after convolution with the constructed sinc noise. All probability and Fourier
bridges are proved; only finite first moments are assumed for the inputs. -/
theorem smoothed_sinc_fourier_difference (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun z : ℝ => |z|) μ) (hν : Integrable (fun z : ℝ => |z|) ν) (x : ℝ) :
    ((smoothedCDFDifference (measureCDF μ) (measureCDF ν) sincKernelMeasure x:ℝ):ℂ)=
      (∫ t,Complex.exp (((t*x:ℝ):ℂ)*Complex.I)*(charFun μ (-t)-charFun ν (-t))/
        ((t:ℂ)*Complex.I) ∂compactFrequency)/(sincKernelIntegral:ℂ) := by
  rw [smoothed_sinc_primitive_difference,Complex.ofReal_div,Complex.ofReal_sub,
    ← integral_complex_ofReal,← integral_complex_ofReal,
    sincKernelPrimitive_expectation μ hμ x,sincKernelPrimitive_expectation ν hν x]
  change ((∫ t,primitiveFrequencyIntegrand μ x t ∂compactFrequency)-
    (∫ t,primitiveFrequencyIntegrand ν x t ∂compactFrequency))/(sincKernelIntegral:ℂ)=_
  rw [← integral_sub (primitiveFrequencyIntegrand_integrable μ hμ x)
    (primitiveFrequencyIntegrand_integrable ν hν x)]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun t => by unfold primitiveFrequencyIntegrand; ring)

end
end ExtractionDeviation
