import Deviation.NoiseSmoothing
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter

namespace ExtractionDeviation
noncomputable section

/-- The nonnegative fourth-power sinc kernel used in the Esseen construction.
This file proves its probability normalization and first moment. The compact
Fourier support and inversion argument are not asserted here. -/
def sincKernel (x : ℝ) : ℝ := (Real.sinc x)^4

theorem sincKernel_nonneg (x : ℝ) : 0≤sincKernel x := by unfold sincKernel; positivity

theorem sincKernel_continuous : Continuous sincKernel := Real.continuous_sinc.pow 4

theorem sincKernel_weighted_bound (x : ℝ) :
    (1+|x|)*sincKernel x≤4*(1+x^2)⁻¹ := by
  let r := |x|
  let u := |Real.sinc x|
  have hr : 0≤r := abs_nonneg _
  have hu : 0≤u := abs_nonneg _
  have hu1 : u≤1 := Real.abs_sinc_le_one x
  have hu4 : u^4=sincKernel x := by
    dsimp [u,sincKernel]
    rw [show (4:ℕ)=2*2 by norm_num,pow_mul,pow_mul,sq_abs]
  have hr2 : r^2=x^2 := sq_abs _
  have hpos : 0<1+x^2 := by positivity
  rw [← hu4,← hr2]
  apply (le_mul_inv_iff₀ (show 0<1+r^2 by positivity)).mpr
  by_cases hr1 : r≤1
  · have hp : (1+r)*(1+r^2)≤4 := by
      have h1 : 1+r≤2 := by linarith
      have h2 : 1+r^2≤2 := by nlinarith
      nlinarith [mul_le_mul h1 h2 (by positivity : 0≤1+r^2) (by norm_num : (0:ℝ)≤2)]
    have hu4le : u^4≤1 := by simpa using pow_le_one₀ hu hu1 (n:=4)
    have hmul := mul_le_mul hp hu4le (pow_nonneg hu 4) (by norm_num : (0:ℝ)≤4)
    nlinarith
  · have hr1' : 1≤r := (lt_of_not_ge hr1).le
    have hrpos : 0<r := by linarith
    have hx : x≠0 := by intro hx; simp [r,hx] at hrpos
    have hur : r*u≤1 := by
      have hs : u≤1/r := by
        dsimp [u]
        rw [Real.sinc_of_ne_zero hx,abs_div]
        exact div_le_div_of_nonneg_right (Real.abs_sin_le_one x) hr
      have h := (le_div_iff₀ hrpos).mp hs
      nlinarith
    have hpoly : (1+r)*(1+r^2)≤4*r^4 := by
      have h2 : 1≤r^2 := by nlinarith
      have h3 : r^3≤r^4 := by
        have h := mul_nonneg (sub_nonneg.mpr hr1') (pow_nonneg hr 3)
        nlinarith
      calc
        _ ≤ (2*r)*(2*r^2) := mul_le_mul (by linarith) (by linarith)
          (by positivity) (by positivity)
        _ = 4*r^3 := by ring
        _ ≤ _ := by linarith
    have hru4 : r^4*u^4≤1 := by
      have h := pow_le_one₀ (mul_nonneg hr hu) hur (n:=4)
      simpa only [mul_pow] using h
    have hmul := mul_le_mul_of_nonneg_right hpoly (pow_nonneg hu 4)
    nlinarith

theorem sincKernel_integrable : Integrable sincKernel := by
  apply (integrable_inv_one_add_sq.const_mul 4).mono' sincKernel_continuous.aestronglyMeasurable
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (sincKernel_nonneg x)]
  have h := sincKernel_weighted_bound x
  have hnn := mul_nonneg (abs_nonneg x) (sincKernel_nonneg x)
  linarith

theorem sincKernel_firstMoment_integrable : Integrable (fun x : ℝ => |x| * sincKernel x) := by
  apply (integrable_inv_one_add_sq.const_mul 4).mono'
    (continuous_abs.mul sincKernel_continuous).aestronglyMeasurable
  apply ae_of_all
  intro x
  change ‖|x| * sincKernel x‖≤4*(1+x^2)⁻¹
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (abs_nonneg _) (sincKernel_nonneg _))]
  have h := sincKernel_weighted_bound x
  linarith [sincKernel_nonneg x]

def sincKernelIntegral : ℝ := ∫ x : ℝ,sincKernel x

theorem sincKernelIntegral_pos : 0<sincKernelIntegral := by
  apply integral_pos_of_integrable_nonneg_nonzero sincKernel_continuous sincKernel_integrable
    sincKernel_nonneg (x:=0)
  simp [sincKernel]

def sincKernelPDF (x : ℝ) : ℝ := sincKernel x/sincKernelIntegral

theorem sincKernelPDF_nonneg (x : ℝ) : 0≤sincKernelPDF x :=
  div_nonneg (sincKernel_nonneg _) sincKernelIntegral_pos.le

theorem sincKernelPDF_continuous : Continuous sincKernelPDF :=
  sincKernel_continuous.div_const _

theorem sincKernelPDF_integrable : Integrable sincKernelPDF := sincKernel_integrable.div_const _

theorem sincKernelPDF_integral : (∫ x : ℝ,sincKernelPDF x)=1 := by
  change (∫ x : ℝ,sincKernel x/sincKernelIntegral)=1
  rw [integral_div]
  exact div_self (ne_of_gt sincKernelIntegral_pos)

def sincKernelMeasure : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (sincKernelPDF x))

instance sincKernelMeasure_isProbabilityMeasure : IsProbabilityMeasure sincKernelMeasure := by
  constructor
  rw [sincKernelMeasure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal sincKernelPDF_integrable
      (ae_of_all _ sincKernelPDF_nonneg),sincKernelPDF_integral,ENNReal.ofReal_one]

theorem sincKernelMeasure_firstMoment_integrable :
    Integrable (fun x : ℝ => |x|) sincKernelMeasure := by
  rw [sincKernelMeasure,integrable_withDensity_iff]
  · simp_rw [ENNReal.toReal_ofReal (sincKernelPDF_nonneg _)]
    change Integrable (fun x : ℝ => |x| * (sincKernel x/sincKernelIntegral))
    convert sincKernel_firstMoment_integrable.div_const sincKernelIntegral using 1
    ext x
    ring
  · exact sincKernelPDF_continuous.measurable.ennreal_ofReal
  · exact ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)

theorem sincKernelMeasure_firstMoment :
    (∫ x,|x| ∂sincKernelMeasure)=(∫ x : ℝ,|x| * sincKernel x)/sincKernelIntegral := by
  rw [sincKernelMeasure,integral_withDensity_eq_integral_toReal_smul
    sincKernelPDF_continuous.measurable.ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  change (∫ x : ℝ,(ENNReal.ofReal (sincKernelPDF x)).toReal*|x|)=_
  simp_rw [ENNReal.toReal_ofReal (sincKernelPDF_nonneg _)]
  calc
    _ = ∫ x : ℝ,|x| * sincKernel x/sincKernelIntegral := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by unfold sincKernelPDF; ring)
    _ = _ := integral_div _ _

end
end ExtractionDeviation
