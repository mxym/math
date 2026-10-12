import BapatRatioIntegrability
import BapatEmpiricalPairs

set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology

namespace BapatRealExistence
noncomputable section

def ratioNumerator (t : ℝ) (v : RealSpace4) : ℝ :=
  (realComplexLinear v transverseComplex4 * star (realComplexLinear v (canonicalComplex4 t))).re

def ratioDenominator (t : ℝ) (v : RealSpace4) : ℝ := ‖realComplexLinear v (canonicalComplex4 t)‖^2

theorem realRowRatio_eq (t : ℝ) (v : RealSpace4) :
    realRowRatio t v = ratioNumerator t v / ratioDenominator t v := by
  simp only [realRowRatio,complexRowRatio,Complex.div_re,ratioNumerator,ratioDenominator,
    Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im,← Complex.normSq_eq_norm_sq]
  ring

theorem ratioNumerator_zero_of_denominator {t : ℝ} {v : RealSpace4} (h : ratioDenominator t v=0) :
    ratioNumerator t v=0 := by
  have hz : realComplexLinear v (canonicalComplex4 t)=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp h)
  simp [ratioNumerator,hz]

@[fun_prop] theorem ratioNumerator_continuous : Continuous (fun p : ℝ × RealSpace4 => ratioNumerator p.1 p.2) := by
  unfold ratioNumerator canonicalComplex4
  fun_prop

@[fun_prop] theorem ratioDenominator_continuous : Continuous (fun p : ℝ × RealSpace4 => ratioDenominator p.1 p.2) := by
  unfold ratioDenominator canonicalComplex4
  fun_prop

def ratioLowerApprox (k : ℕ) (t : ℝ) (x y : RealSpace4) : ℝ :=
  |ratioNumerator t x*ratioDenominator t y-ratioNumerator t y*ratioDenominator t x| /
    max (ratioDenominator t x*ratioDenominator t y) (Real.exp (-(k:ℝ)))

@[fun_prop] theorem ratioLowerApprox_continuous (k : ℕ) :
    Continuous (fun p : (RealSpace4 × RealSpace4) × ℝ => ratioLowerApprox k p.2 p.1.1 p.1.2) := by
  unfold ratioLowerApprox
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro p
    exact ne_of_gt ((Real.exp_pos _).trans_le (le_max_right _ _))

theorem ratioLowerApprox_nonneg (k : ℕ) (t : ℝ) (x y : RealSpace4) : 0≤ratioLowerApprox k t x y := by
  unfold ratioLowerApprox
  exact div_nonneg (abs_nonneg _) ((Real.exp_pos _).le.trans (le_max_right _ _))

theorem ratio_difference_cross {t : ℝ} {x y : RealSpace4}
    (hx : ratioDenominator t x≠0) (hy : ratioDenominator t y≠0) :
    |realRowRatio t x-realRowRatio t y| =
      |ratioNumerator t x*ratioDenominator t y-ratioNumerator t y*ratioDenominator t x| /
        (ratioDenominator t x*ratioDenominator t y) := by
  rw [realRowRatio_eq,realRowRatio_eq,div_sub_div _ _ hx hy,abs_div,
    abs_of_nonneg (show 0≤ratioDenominator t x*ratioDenominator t y from
      mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  congr 2
  ring

theorem ratioLowerApprox_le (k : ℕ) (t : ℝ) (x y : RealSpace4) :
    ratioLowerApprox k t x y ≤ |realRowRatio t x-realRowRatio t y| := by
  by_cases hx : ratioDenominator t x=0
  · simp [ratioLowerApprox,hx,ratioNumerator_zero_of_denominator hx,abs_nonneg]
  by_cases hy : ratioDenominator t y=0
  · simp [ratioLowerApprox,hy,ratioNumerator_zero_of_denominator hy,abs_nonneg]
  rw [ratio_difference_cross hx hy]
  apply div_le_div_of_nonneg_left (abs_nonneg _) _ (le_max_left _ _)
  exact mul_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm hx))
    (lt_of_le_of_ne (sq_nonneg _) (Ne.symm hy))

theorem ratioLowerApprox_tendsto {t : ℝ} {x y : RealSpace4}
    (hx : ratioDenominator t x≠0) (hy : ratioDenominator t y≠0) :
    Tendsto (fun k : ℕ => ratioLowerApprox k t x y) atTop (𝓝 |realRowRatio t x-realRowRatio t y|) := by
  have hp : 0<ratioDenominator t x*ratioDenominator t y :=
    mul_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm hx)) (lt_of_le_of_ne (sq_nonneg _) (Ne.symm hy))
  have he : Tendsto (fun k : ℕ => Real.exp (-(k:ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  apply tendsto_const_nhds.congr'
  filter_upwards [(tendsto_order.mp he).2 _ hp] with k hk
  rw [ratioLowerApprox,max_eq_left hk.le,ratio_difference_cross hx hy]

theorem ratioLowerApprox_integral_tendsto :
    Tendsto (fun k : ℕ => ∫ p : RealUnitSphere4 × RealUnitSphere4, ratioLowerApprox k (1/2) p.1 p.2
      ∂(normalizedSphere (volume : Measure RealSpace4)).prod
        (normalizedSphere (volume : Measure RealSpace4))) atTop (𝓝 (Real.pi/2)) := by
  rw [← sphere_balancedRealRatio_prod_gini]
  apply tendsto_integral_of_dominated_convergence
    (fun p : RealUnitSphere4 × RealUnitSphere4 => |balancedRealRatio p.1-balancedRealRatio p.2|)
  · intro k
    exact ((ratioLowerApprox_continuous k).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
        |>.prodMk continuous_const)).aestronglyMeasurable
  · exact balancedRealRatio_pair_sphere_integrable
  · intro k
    apply Filter.Eventually.of_forall
    intro p
    simpa only [Real.norm_eq_abs,abs_of_nonneg (ratioLowerApprox_nonneg _ _ _ _),realRowRatio_balanced]
      using ratioLowerApprox_le k (1/2) p.1 p.2
  · have h : ∀ᵐ v : RealUnitSphere4 ∂normalizedSphere (volume : Measure RealSpace4),
        ratioDenominator (1/2) v≠0 := by
      filter_upwards [canonical_linear_ne_zero_ae (by norm_num : (0:ℝ)<1/2) (by norm_num)] with v hv
      exact pow_ne_zero _ (norm_ne_zero_iff.mpr hv)
    filter_upwards [quasiMeasurePreserving_fst.ae h,quasiMeasurePreserving_snd.ae h] with p hx hy
    simpa only [realRowRatio_balanced] using ratioLowerApprox_tendsto hx hy

end
end BapatRealExistence
