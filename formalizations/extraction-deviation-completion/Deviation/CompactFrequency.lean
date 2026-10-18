import Deviation.SincKernel
import Mathlib.MeasureTheory.Measure.IntegralCharFun

open scoped NNReal ENNReal Topology MeasureTheory
open MeasureTheory ProbabilityTheory Filter Set

namespace ExtractionDeviation
noncomputable section

def boxFrequency : Measure ℝ := (2:ℝ≥0∞)⁻¹ • volume.restrict (Icc (-1) 1)

instance boxFrequency_isProbabilityMeasure : IsProbabilityMeasure boxFrequency := by
  constructor
  norm_num [boxFrequency,Measure.smul_apply,Measure.restrict_apply,Real.volume_Icc]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

theorem charFun_boxFrequency (t : ℝ) : charFun boxFrequency t=(Real.sinc t:ℂ) := by
  rw [charFun_apply_real,boxFrequency,integral_smul_measure]
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ)≤1)]
  have hi : (∫ x in (-1:ℝ)..1,Complex.exp (((t*x:ℝ):ℂ)*Complex.I))=
      2*(Real.sinc t:ℂ) := by
    by_cases ht : t=0
    · norm_num [ht]
    have h := intervalIntegral.integral_comp_mul_left
      (fun x : ℝ => Complex.exp ((x:ℂ)*Complex.I)) (a:=(-1:ℝ)) (b:=1) ht
    simp only [mul_one,mul_neg_one] at h
    rw [integral_exp_mul_I_eq_sinc] at h
    rw [h]
    simp only [Complex.real_smul,Complex.ofReal_inv]
    have htC : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ht
    field_simp
  have hi' : (∫ x in (-1:ℝ)..1,Complex.exp ((t:ℂ)*(x:ℂ)*Complex.I))=
      2*(Real.sinc t:ℂ) := by simpa only [Complex.ofReal_mul] using hi
  rw [hi']
  norm_num
  ring

theorem boxFrequency_support : ∀ᵐ x ∂boxFrequency,|x|≤1 := by
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact abs_le.mpr hx

theorem convolution_abs_support (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (a b : ℝ)
    (ha : ∀ᵐ x ∂μ,|x|≤a) (hb : ∀ᵐ y ∂ν,|y|≤b) :
    ∀ᵐ z ∂(μ ∗ ν),|z|≤a+b := by
  rw [Measure.conv,ae_map_iff (by fun_prop) (by measurability)]
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  filter_upwards [ha] with x hx
  filter_upwards [hb] with y hy
  exact (abs_add_le x y).trans (add_le_add hx hy)

def compactFrequency : Measure ℝ := (boxFrequency ∗ boxFrequency) ∗ (boxFrequency ∗ boxFrequency)

instance compactFrequency_isProbabilityMeasure : IsProbabilityMeasure compactFrequency := by
  unfold compactFrequency
  infer_instance

/-- A compactly supported genuine probability measure whose characteristic
function is exactly the fourth-power sinc kernel. This is proved by actual
uniform-interval integration and convolution, not a Fourier-support premise. -/
theorem charFun_compactFrequency (t : ℝ) : charFun compactFrequency t=(sincKernel t:ℂ) := by
  simp only [compactFrequency,charFun_conv,charFun_boxFrequency,sincKernel,Complex.ofReal_pow]
  ring

theorem compactFrequency_support : ∀ᵐ x ∂compactFrequency,|x|≤4 := by
  have h2 := convolution_abs_support boxFrequency boxFrequency 1 1
    boxFrequency_support boxFrequency_support
  have h4 := convolution_abs_support (boxFrequency ∗ boxFrequency) (boxFrequency ∗ boxFrequency)
    (1+1) (1+1) h2 h2
  norm_num at h4
  exact h4

theorem convolution_boxFrequency_le_volume (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    ν ∗ boxFrequency≤(2:ℝ≥0∞)⁻¹ • volume := by
  apply Measure.le_iff.mpr
  intro E hE
  rw [Measure.conv,Measure.map_apply (by fun_prop) hE,Measure.prod_apply (by measurability)]
  calc
    _ ≤ ∫⁻ _x : ℝ,(2:ℝ≥0∞)⁻¹*volume E ∂ν := by
      apply lintegral_mono
      intro x
      change boxFrequency ((fun y : ℝ => x+y) ⁻¹' E)≤(2:ℝ≥0∞)⁻¹*volume E
      rw [boxFrequency,Measure.smul_apply,smul_eq_mul]
      rw [← measure_preimage_add volume x E]
      gcongr
      exact Measure.restrict_le_self
    _ = _ := by simp [Measure.smul_apply,smul_eq_mul]

/-- The compact frequency measure has an internally proved bounded density
in measure-order form. No externally supplied regularity of a kernel occurs. -/
theorem compactFrequency_le_volume : compactFrequency≤(2:ℝ≥0∞)⁻¹ • volume := by
  unfold compactFrequency
  rw [← Measure.conv_assoc]
  exact convolution_boxFrequency_le_volume _

/-- The kernel has an exact integral representation using frequencies in a
fixed compact interval. Later Fourier inversion must still connect this
representation to a bound on the smoothed CDF discrepancy. -/
theorem sincKernel_compact_representation (x : ℝ) :
    (sincKernel x:ℂ)=∫ t,Complex.exp (((t*x:ℝ):ℂ)*Complex.I) ∂compactFrequency := by
  rw [← charFun_compactFrequency,charFun_apply_real]
  congr 1
  ext t
  push_cast
  rw [mul_comm (t:ℂ) (x:ℂ)]

end
end ExtractionDeviation
