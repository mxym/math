import BapatGaussianSphereTransfer

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology

namespace BapatRealExistence
noncomputable section

def realSwap01 : RealSpace4 ≃ₗᵢ[ℝ] RealSpace4 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0:Fin 4) 1)

@[simp] theorem realSwap01_apply_zero (x : RealSpace4) : realSwap01 x 0 = x 1 := rfl
@[simp] theorem realSwap01_apply_one (x : RealSpace4) : realSwap01 x 1 = x 0 := rfl

theorem log_midpoint_le {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    Real.log a + Real.log b ≤ 2*Real.log ((a+b)/2) := by
  have hp : a*b ≤ ((a+b)/2)^2 := by nlinarith [sq_nonneg (a-b)]
  have h := Real.log_le_log (mul_pos ha hb) hp
  simpa only [Real.log_mul ha.ne' hb.ne',Real.log_pow,Nat.cast_ofNat] using h

theorem log_midpoint_lt {a b : ℝ} (ha : 0<a) (hb : 0<b) (hab : a≠b) :
    Real.log a + Real.log b < 2*Real.log ((a+b)/2) := by
  have hp : a*b < ((a+b)/2)^2 := by nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hab)]
  have h := Real.log_lt_log (mul_pos ha hb) hp
  simpa only [Real.log_mul ha.ne' hb.ne',Real.log_pow,Nat.cast_ofNat] using h

def gaussianLogPotential (t : ℝ) : ℝ :=
  ∫ x : RealSpace4, Real.log (canonicalQuadratic t x)*Real.exp (-‖x‖^2)

def gaussianBalanceGap (t : ℝ) (x : RealSpace4) : ℝ :=
  (2*Real.log (canonicalQuadratic (1/2) x) - Real.log (canonicalQuadratic t x) -
    Real.log (canonicalQuadratic t (realSwap01 x))) * Real.exp (-‖x‖^2)

theorem canonicalQuadratic_swap_mean (t : ℝ) (x : RealSpace4) :
    (canonicalQuadratic t x + canonicalQuadratic t (realSwap01 x))/2 =
      canonicalQuadratic (1/2) x := by
  simp only [canonicalQuadratic,realSwap01_apply_zero,realSwap01_apply_one]
  ring

theorem gaussianBalanceGap_nonneg {t : ℝ} (ht : 0<t) (ht' : t ≤ 1)
    (x : RealSpace4) (h0 : x 0≠0) (h1 : x 1≠0) : 0 ≤ gaussianBalanceGap t x := by
  have hq := (canonicalQuadratic_bounds ht ht' x h0).1
  have hq' := (canonicalQuadratic_bounds ht ht' (realSwap01 x) (by simpa using h1)).1
  have h := log_midpoint_le hq hq'
  rw [canonicalQuadratic_swap_mean] at h
  exact mul_nonneg (by linarith) (Real.exp_pos _).le

theorem gaussianBalanceGap_integrable {t : ℝ} (ht : 0<t) (ht' : t ≤ 1) :
    Integrable (gaussianBalanceGap t) := by
  have hhalf := integrable_realGaussian_log_quadratic (by norm_num : (0:ℝ)<1/2)
    (by norm_num : (1/2:ℝ)≤1)
  have htint := integrable_realGaussian_log_quadratic ht ht'
  have hswap : Integrable (fun x : RealSpace4 =>
      Real.log (canonicalQuadratic t (realSwap01 x))*Real.exp (-‖x‖^2)) := by
    have h := realSwap01.measurePreserving.integrable_comp_of_integrable htint
    simpa only [Function.comp_def,realSwap01.norm_map] using h
  convert ((hhalf.const_mul 2).sub htint).sub hswap using 1
  ext x
  simp only [gaussianBalanceGap,Pi.sub_apply]
  ring

theorem gaussianBalanceGap_integral (t : ℝ) (ht : 0<t) (ht' : t≤1) :
    (∫ x, gaussianBalanceGap t x) = 2*(gaussianLogPotential (1/2)-gaussianLogPotential t) := by
  have hhalf := integrable_realGaussian_log_quadratic (by norm_num : (0:ℝ)<1/2)
    (by norm_num : (1/2:ℝ)≤1)
  have hi := integrable_realGaussian_log_quadratic ht ht'
  have hswap : Integrable (fun x : RealSpace4 =>
      Real.log (canonicalQuadratic t (realSwap01 x))*Real.exp (-‖x‖^2)) := by
    have h := realSwap01.measurePreserving.integrable_comp_of_integrable hi
    simpa only [Function.comp_def,realSwap01.norm_map] using h
  have hsi : (∫ x : RealSpace4, Real.log (canonicalQuadratic t (realSwap01 x))*Real.exp (-‖x‖^2)) =
      gaussianLogPotential t := by
    have h := realSwap01.measurePreserving.integral_comp realSwap01.toHomeomorph.measurableEmbedding
      (fun x : RealSpace4 => Real.log (canonicalQuadratic t x)*Real.exp (-‖x‖^2))
    simpa only [realSwap01.norm_map,gaussianLogPotential] using h
  have he : gaussianBalanceGap t = fun x : RealSpace4 =>
      (2*(Real.log (canonicalQuadratic (1/2) x)*Real.exp (-‖x‖^2)) -
       Real.log (canonicalQuadratic t x)*Real.exp (-‖x‖^2)) -
       Real.log (canonicalQuadratic t (realSwap01 x))*Real.exp (-‖x‖^2) := by
    funext x
    unfold gaussianBalanceGap
    ring
  have hsub := integral_sub ((hhalf.const_mul 2).sub hi) hswap
  simp only [Pi.sub_apply] at hsub
  rw [he,hsub,integral_sub (hhalf.const_mul 2) hi,integral_const_mul,hsi]
  unfold gaussianLogPotential
  ring

/-- Strict maximality holds for the genuine Gaussian potential, including t=1. -/
theorem gaussianLogPotential_strict_balanced {t : ℝ} (ht : 1/2<t) (ht' : t≤1) :
    gaussianLogPotential t < gaussianLogPotential (1/2) := by
  have ht0 : 0<t := by linarith
  let w : RealSpace4 := WithLp.toLp 2 ![1,2,0,0]
  have hw0 : w 0≠0 := by norm_num [w]
  have hw1 : w 1≠0 := by norm_num [w]
  have ha := (canonicalQuadratic_bounds ht0 ht' w hw0).1
  have hb := (canonicalQuadratic_bounds ht0 ht' (realSwap01 w) (by simpa using hw1)).1
  have hab : canonicalQuadratic t w ≠ canonicalQuadratic t (realSwap01 w) := by
    simp only [canonicalQuadratic,realSwap01_apply_zero,realSwap01_apply_one]
    norm_num [w]
    linarith
  have hlog := log_midpoint_lt ha hb hab
  rw [canonicalQuadratic_swap_mean] at hlog
  have hpos : 0 < gaussianBalanceGap t w := mul_pos (by linarith) (Real.exp_pos _)
  have hc : ContinuousAt (gaussianBalanceGap t) w := by
    have hqa : Continuous (canonicalQuadratic t) := by unfold canonicalQuadratic; fun_prop
    have hqh : Continuous (canonicalQuadratic (1/2)) := by unfold canonicalQuadratic; fun_prop
    have hhalf := (canonicalQuadratic_bounds (by norm_num : (0:ℝ)<1/2)
      (by norm_num : (1/2:ℝ)≤1) w hw0).1
    exact (((hqh.continuousAt.log hhalf.ne').const_mul 2).sub
      (hqa.continuousAt.log ha.ne') |>.sub
      ((hqa.continuousAt.comp realSwap01.continuous.continuousAt).log hb.ne')).mul
        (by fun_prop)
  have hn : 0 ≤ᵐ[volume] gaussianBalanceGap t := by
    filter_upwards [real_euclidean_coordinate_ne_zero_ae (0:Fin 4),
      real_euclidean_coordinate_ne_zero_ae (1:Fin 4)] with x h0 h1
    exact gaussianBalanceGap_nonneg ht0 ht' x h0 h1
  have hs : Function.support (gaussianBalanceGap t) ∈ 𝓝 w := by
    exact Filter.mem_of_superset (hc.eventually (lt_mem_nhds hpos)) (by intro x hx; exact ne_of_gt hx)
  have hi : 0 < ∫ x, gaussianBalanceGap t x :=
    (integral_pos_iff_support_of_nonneg_ae hn (gaussianBalanceGap_integrable ht0 ht')).mpr
      (Measure.measure_pos_of_mem_nhds volume hs)
  rw [gaussianBalanceGap_integral t ht0 ht'] at hi
  linarith

end
end BapatRealExistence
