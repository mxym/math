import Deviation.KernelFourier

open scoped NNReal ENNReal Topology MeasureTheory
open MeasureTheory ProbabilityTheory Filter Set

namespace ExtractionDeviation
noncomputable section

def dilatedLaw (μ : Measure ℝ) (R : ℝ) : Measure ℝ := μ.map (fun z => R*z)

instance dilatedLaw_isProbabilityMeasure (μ : Measure ℝ) [IsProbabilityMeasure μ] (R : ℝ) :
    IsProbabilityMeasure (dilatedLaw μ R) := by
  constructor
  rw [dilatedLaw,Measure.map_apply (by fun_prop) MeasurableSet.univ]
  simp

theorem dilatedLaw_firstMoment_integrable (μ : Measure ℝ)
    (habs : Integrable (fun z : ℝ => |z|) μ) (R : ℝ) :
    Integrable (fun z : ℝ => |z|) (dilatedLaw μ R) := by
  rw [dilatedLaw,integrable_map_measure continuous_abs.aestronglyMeasurable (by fun_prop)]
  change Integrable (fun z : ℝ => |R*z|) μ
  simp_rw [abs_mul]
  exact habs.const_mul |R|

theorem measureCDF_dilatedLaw (μ : Measure ℝ) (R : ℝ) (hR : 0<R) (u : ℝ) :
    measureCDF (dilatedLaw μ R) u=measureCDF μ (u/R) := by
  unfold measureCDF dilatedLaw Measure.real
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
  congr 2
  ext z
  simp only [mem_preimage,mem_Iic]
  constructor
  · intro h
    apply (le_div_iff₀ hR).mpr
    simpa only [mul_comm] using h
  · intro h
    have hh := (le_div_iff₀ hR).mp h
    simpa only [mul_comm] using hh

theorem smoothed_dilatedLaw_difference (μ ν noise : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure noise]
    (R : ℝ) (hR : 0<R) (x : ℝ) :
    smoothedCDFDifference (measureCDF μ) (measureCDF ν) (scaledNoise noise R) x=
      smoothedCDFDifference (measureCDF (dilatedLaw μ R)) (measureCDF (dilatedLaw ν R)) noise (R*x) := by
  rw [smoothedCDFDifference,scaledNoise,integral_map (by fun_prop) (by
    exact (((measureCDF_mono μ).measurable.comp (measurable_const.sub measurable_id)).sub
      ((measureCDF_mono ν).measurable.comp (measurable_const.sub measurable_id))).aestronglyMeasurable)]
  unfold smoothedCDFDifference
  simp_rw [measureCDF_dilatedLaw _ R hR]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by
    change measureCDF μ (x-y/R)-measureCDF ν (x-y/R)=
      measureCDF μ ((R*x-y)/R)-measureCDF ν ((R*x-y)/R)
    rw [show (R*x-y)/R=x-y/R by field_simp])

/-- The exact scaled Fourier smoothing formula, with the same concrete compact
frequency measure constructed from four uniform intervals. -/
theorem smoothed_scaled_sinc_fourier_difference (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun z : ℝ => |z|) μ) (hν : Integrable (fun z : ℝ => |z|) ν)
    (R : ℝ) (hR : 0<R) (x : ℝ) :
    ((smoothedCDFDifference (measureCDF μ) (measureCDF ν) (scaledNoise sincKernelMeasure R) x:ℝ):ℂ)=
      (∫ t,Complex.exp (((t*(R*x):ℝ):ℂ)*Complex.I)*
        (charFun μ (R*(-t))-charFun ν (R*(-t)))/((t:ℂ)*Complex.I)
          ∂compactFrequency)/(sincKernelIntegral:ℂ) := by
  rw [smoothed_dilatedLaw_difference μ ν sincKernelMeasure R hR x,
    smoothed_sinc_fourier_difference _ _ (dilatedLaw_firstMoment_integrable μ hμ R)
      (dilatedLaw_firstMoment_integrable ν hν R)]
  simp only [dilatedLaw,charFun_map_mul]

end
end ExtractionDeviation
