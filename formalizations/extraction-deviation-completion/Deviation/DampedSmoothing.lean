import Deviation.LawScaling
import Deviation.FourierIntegral

open scoped NNReal ENNReal Topology MeasureTheory
open MeasureTheory ProbabilityTheory Filter Set

namespace ExtractionDeviation
noncomputable section

def scaledFourierMajorant (β R t : ℝ) : ℝ :=
  (5*β*R)*((R*t)^2*Real.exp (-(R*t)^2/8))

theorem scaledFourierMajorant_nonneg (β R t : ℝ) (hβ : 0≤β) (hR : 0<R) :
    0≤scaledFourierMajorant β R t := by unfold scaledFourierMajorant; positivity

theorem scaledFourierMajorant_integrable (β R : ℝ) (hR : 0<R) :
    Integrable (scaledFourierMajorant β R) :=
  (fourierGaussianMoment_integrable.comp_mul_left' (ne_of_gt hR)).const_mul _

theorem scaledFourierMajorant_integral (β R : ℝ) (hR : 0<R) :
    (∫ t : ℝ,scaledFourierMajorant β R t)=5*β*fourierGaussianMoment := by
  change (∫ t : ℝ,(5*β*R)*((R*t)^2*Real.exp (-(R*t)^2/8)))=_
  rw [integral_const_mul,
    Measure.integral_comp_mul_left (fun u : ℝ => u^2*Real.exp (-u^2/8)) R,
    abs_of_pos (inv_pos.mpr hR),smul_eq_mul]
  unfold fourierGaussianMoment
  field_simp

theorem scaledFourierMajorant_compact_integral (β R : ℝ) (hβ : 0≤β) (hR : 0<R) :
    (∫ t,scaledFourierMajorant β R t ∂compactFrequency)≤(5*β*fourierGaussianMoment)/2 := by
  have hi := (scaledFourierMajorant_integrable β R hR).smul_measure
    (show (2:ℝ≥0∞)⁻¹≠⊤ by norm_num)
  have h := integral_mono_measure compactFrequency_le_volume
    (ae_of_all _ (fun t => scaledFourierMajorant_nonneg β R t hβ hR)) hi
  rw [integral_smul_measure,scaledFourierMajorant_integral β R hR] at h
  norm_num at h
  linarith

theorem scaled_fourier_integrand_bound (μ ν : Measure ℝ) (β R x t : ℝ)
    (hβ : 0≤β) (hR : 0<R) (hwindow : 64*β*R≤1) (ht : |t|≤4)
    (hdamp : ∀ u : ℝ,16*β*|u|≤1 → ‖charFun μ u-charFun ν u‖≤
      5*β*|u|^3*Real.exp (-u^2/8)) :
    ‖Complex.exp (((t*(R*x):ℝ):ℂ)*Complex.I)*
      (charFun μ (R*(-t))-charFun ν (R*(-t)))/((t:ℂ)*Complex.I)‖≤
        scaledFourierMajorant β R t := by
  by_cases ht0 : t=0
  · simp only [ht0,Complex.ofReal_zero,zero_mul,div_zero,norm_zero]
    exact scaledFourierMajorant_nonneg β R 0 hβ hR
  have hfreq : 16*β*|R*(-t)|≤1 := by
    rw [abs_mul,abs_of_pos hR,abs_neg]
    nlinarith [mul_le_mul_of_nonneg_left ht (mul_nonneg hβ hR.le)]
  have h := hdamp (R*(-t)) hfreq
  rw [norm_div,norm_mul,Complex.norm_exp_ofReal_mul_I,norm_mul,Complex.norm_I,
    Complex.norm_real,Real.norm_eq_abs,one_mul,mul_one]
  apply (div_le_iff₀ (abs_pos.mpr ht0)).mpr
  apply h.trans_eq
  unfold scaledFourierMajorant
  simp only [abs_mul,abs_of_pos hR,abs_neg,mul_neg,neg_sq,mul_pow]
  rw [show |t|^3=t^2*|t| by rw [pow_succ,sq_abs]]
  ring

/-- The actual scaled sinc convolution discrepancy has a finite, explicit
linear bound once the quantitative local characteristic-function estimate has
been established. The CDF-to-Fourier bridge is internal to this theorem. -/
theorem smoothedCDFDifference_damped_bound (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun z : ℝ => |z|) μ) (hν : Integrable (fun z : ℝ => |z|) ν)
    (β R : ℝ) (hβ : 0≤β) (hR : 0<R) (hwindow : 64*β*R≤1)
    (hdamp : ∀ u : ℝ,16*β*|u|≤1 → ‖charFun μ u-charFun ν u‖≤
      5*β*|u|^3*Real.exp (-u^2/8)) (x : ℝ) :
    |smoothedCDFDifference (measureCDF μ) (measureCDF ν)
      (scaledNoise sincKernelMeasure R) x|≤(5*β*fourierGaussianMoment)/(2*sincKernelIntegral) := by
  have hiVol := (scaledFourierMajorant_integrable β R hR).smul_measure
    (show (2:ℝ≥0∞)⁻¹≠⊤ by norm_num)
  have hi := hiVol.mono_measure compactFrequency_le_volume
  have hbound : ∀ᵐ t ∂compactFrequency, ‖Complex.exp (((t*(R*x):ℝ):ℂ)*Complex.I)*
      (charFun μ (R*(-t))-charFun ν (R*(-t)))/((t:ℂ)*Complex.I)‖≤
        scaledFourierMajorant β R t := by
    filter_upwards [compactFrequency_support] with t ht
    exact scaled_fourier_integrand_bound μ ν β R x t hβ hR hwindow ht hdamp
  have hnorm := norm_integral_le_of_norm_le hi hbound
  have hrepr := smoothed_scaled_sinc_fourier_difference μ ν hμ hν R hR x
  have hn := congrArg norm hrepr
  rw [Complex.norm_real,Real.norm_eq_abs,norm_div,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos sincKernelIntegral_pos] at hn
  rw [hn]
  calc
    _ ≤ (∫ t,scaledFourierMajorant β R t ∂compactFrequency)/sincKernelIntegral :=
      div_le_div_of_nonneg_right hnorm sincKernelIntegral_pos.le
    _ ≤ ((5*β*fourierGaussianMoment)/2)/sincKernelIntegral :=
      div_le_div_of_nonneg_right (scaledFourierMajorant_compact_integral β R hβ hR)
        sincKernelIntegral_pos.le
    _ = _ := by ring

end
end ExtractionDeviation
