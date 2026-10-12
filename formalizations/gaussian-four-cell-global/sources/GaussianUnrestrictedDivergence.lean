import GaussianDensityMeasure
import GaussianSmoothTestProduct

/-! Product rules and whole-space Gaussian divergence integration for arbitrary
smooth compact fields. Normalization is performed explicitly, so no unit-norm
assumption is imposed on the fields in the integration theorem. -/
open MeasureTheory ProbabilityTheory Module Set
open scoped Topology ENNReal ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

lemma gaussianDivergence_product_function (ρ : Space d → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (X : Space d → Space d) (hX : ContDiff ℝ ∞ X) (x : Space d) :
    gaussianDivergence (fun y => ρ y • X y) x =
      ρ x*gaussianDivergence X x+fderiv ℝ ρ x (X x) := by
  have hdρ : Differentiable ℝ ρ := hρ.differentiable (by simp)
  have hdX : Differentiable ℝ X := hX.differentiable (by simp)
  have hf := fderiv_fun_smul (hdρ x) (hdX x)
  have hs : (∑ i : Fin d,(fderiv ℝ ρ x) (EuclideanSpace.basisFun (Fin d) ℝ i)*X x i) =
      fderiv ℝ ρ x (X x) := by
    have he := congrArg (fderiv ℝ ρ x) ((EuclideanSpace.basisFun (Fin d) ℝ).sum_repr' (X x))
    simpa only [map_sum,map_smul,EuclideanSpace.basisFun_inner,smul_eq_mul,mul_comm] using he
  unfold gaussianDivergence
  rw [hf]
  simp only [add_apply,ContinuousLinearMap.smulRight_apply,
    smul_apply,inner_add_right,real_inner_smul_right,PiLp.smul_apply,smul_eq_mul,
    EuclideanSpace.basisFun_inner,Finset.sum_add_distrib,← Finset.mul_sum]
  rw [hs]
  ring

lemma gaussianDivergence_const_smul_function (a : ℝ)
    (X : Space d → Space d) (hX : ContDiff ℝ ∞ X) (x : Space d) :
    gaussianDivergence (fun y => a • X y) x = a*gaussianDivergence X x := by
  simpa only [fderiv_const_apply,zero_apply,add_zero] using
    gaussianDivergence_product_function (fun _ => a) contDiff_const X hX x

noncomputable def normalizeGaussianField (X : Space d → Space d)
    (hX : ContDiff ℝ ∞ X) (hc : HasCompactSupport X)
    (C : ℝ) (hC : 0 < C) (hb : ∀ x,‖X x‖ ≤ C) : GaussianTestField d :=
  { toFun := fun x => C⁻¹ • X x
    smooth := ContDiff.const_smul C⁻¹ hX
    compact := hc.smul_left (f := fun _ => C⁻¹)
    norm_le := fun x => by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hC)]
      calc
        C⁻¹*‖X x‖ ≤ C⁻¹*C := mul_le_mul_of_nonneg_left (hb x) (inv_nonneg.mpr hC.le)
        _ = 1 := inv_mul_cancel₀ hC.ne' }

theorem gaussianDivergence_integral_zero_function (X : Space d → Space d)
    (hX : ContDiff ℝ ∞ X) (hc : HasCompactSupport X) :
    (∫ x,gaussianDivergence X x ∂gaussian d) = 0 := by
  obtain ⟨M,hM⟩ := hc.exists_bound_of_continuous hX.continuous
  let C := max M 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right M 1)
  have hb : ∀ x,‖X x‖ ≤ C := fun x => (hM x).trans (le_max_left M 1)
  have hz := gaussianDivergence_integral_zero (normalizeGaussianField X hX hc C hC hb)
  change (∫ x,gaussianDivergence (fun y => C⁻¹ • X y) x ∂gaussian d) = 0 at hz
  simp_rw [gaussianDivergence_const_smul_function C⁻¹ X hX] at hz
  rw [integral_const_mul] at hz
  exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero hC.ne')

theorem gaussianBV_bound_field (S : Set (Space d)) (X : Space d → Space d)
    (hX : ContDiff ℝ ∞ X) (hc : HasCompactSupport X)
    (C : ℝ) (hC : 0 < C) (hb : ∀ x,‖X x‖ ≤ C)
    (P : ℝ) (hP : 0 ≤ P) (hBV : gaussianBVPerimeter S ≤ ENNReal.ofReal P) :
    (∫ x in S,gaussianDivergence X x ∂gaussian d) ≤ C*P := by
  have h := (gaussianBVPerimeter_ge_test S
    (normalizeGaussianField X hX hc C hC hb)).trans hBV
  change ENNReal.ofReal (∫ x in S,
    gaussianDivergence (fun y => C⁻¹ • X y) x ∂gaussian d) ≤ ENNReal.ofReal P at h
  simp_rw [gaussianDivergence_const_smul_function C⁻¹ X hX] at h
  rw [integral_const_mul,ENNReal.ofReal_le_ofReal_iff hP] at h
  have he : C*(C⁻¹*(∫ x in S,gaussianDivergence X x ∂gaussian d)) =
      ∫ x in S,gaussianDivergence X x ∂gaussian d := by
    rw [← mul_assoc,mul_inv_cancel₀ hC.ne',one_mul]
  rw [← he]
  exact mul_le_mul_of_nonneg_left h hC.le

end GaussianMeasureBridge
