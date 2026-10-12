import GaussianDivergenceStein
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! A genuine scalar-test product rule and its integrated Gaussian identity.
Smooth approximants need not have compact support: the actual vector test
supplies compact support to the product. -/
open MeasureTheory ProbabilityTheory Module Set
open scoped Topology ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

noncomputable def multiplyGaussianTest (ρ : Space d → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hb : ∀ x,0 ≤ ρ x ∧ ρ x ≤ 1) (X : GaussianTestField d) : GaussianTestField d :=
  { toFun := fun x => ρ x • X x
    smooth := hρ.smul X.smooth
    compact := X.compact.smul_left (f := ρ)
    norm_le := fun x => by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hb x).1]
      exact (mul_le_mul_of_nonneg_left (X.norm_le x) (hb x).1).trans (by simpa using (hb x).2) }

lemma gaussianDivergence_product (ρ : Space d → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hb : ∀ x,0 ≤ ρ x ∧ ρ x ≤ 1) (X : GaussianTestField d) (x : Space d) :
    gaussianDivergence (multiplyGaussianTest ρ hρ hb X) x =
      ρ x*gaussianDivergence X x+fderiv ℝ ρ x (X x) := by
  have hdρ : Differentiable ℝ ρ := hρ.differentiable (by simp)
  have hdX : Differentiable ℝ X := X.smooth.differentiable (by simp)
  have hf := fderiv_fun_smul (hdρ x) (hdX x)
  have hs : (∑ i : Fin d,(fderiv ℝ ρ x) (EuclideanSpace.basisFun (Fin d) ℝ i)*X x i) =
      fderiv ℝ ρ x (X x) := by
    have he := congrArg (fderiv ℝ ρ x) ((EuclideanSpace.basisFun (Fin d) ℝ).sum_repr' (X x))
    simpa only [map_sum,map_smul,EuclideanSpace.basisFun_inner,smul_eq_mul,mul_comm] using he
  unfold gaussianDivergence
  change (∑ i : Fin d,⟪EuclideanSpace.basisFun (Fin d) ℝ i,
    fderiv ℝ (fun z => ρ z • X z) x (EuclideanSpace.basisFun (Fin d) ℝ i)⟫)-⟪x,ρ x • X x⟫ = _
  rw [hf]
  simp only [add_apply,ContinuousLinearMap.smulRight_apply,
    smul_apply,inner_add_right,real_inner_smul_right,PiLp.smul_apply,smul_eq_mul,
    EuclideanSpace.basisFun_inner,Finset.sum_add_distrib,← Finset.mul_sum]
  rw [hs]
  ring

lemma scalar_test_divergence_integrable (ρ : Space d → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (X : GaussianTestField d) : Integrable (fun x => ρ x*gaussianDivergence X x) (gaussian d) := by
  have hc := hρ.continuous.mul (gaussianDivergence_continuous X)
  exact hc.integrable_of_hasCompactSupport (gaussianDivergence_hasCompactSupport X).mul_left

lemma scalar_test_directional_integrable (ρ : Space d → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (X : GaussianTestField d) : Integrable (fun x => fderiv ℝ ρ x (X x)) (gaussian d) := by
  have hd := hρ.continuous_fderiv (by simp)
  have hc := X.smooth.continuous
  have hcont : Continuous (fun x => fderiv ℝ ρ x (X x)) := by fun_prop
  have hs : HasCompactSupport (fun x => fderiv ℝ ρ x (X x)) := by
    apply X.compact.mono'
    intro x hx
    by_contra he
    have hz : X x=0 := Function.notMem_support.mp (fun h => he (subset_tsupport _ h))
    apply hx
    change fderiv ℝ ρ x (X x)=0
    rw [hz,map_zero]
  exact hcont.integrable_of_hasCompactSupport hs

theorem gaussian_smooth_test_integral (ρ : Space d → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hb : ∀ x,0 ≤ ρ x ∧ ρ x ≤ 1) (X : GaussianTestField d) :
    (∫ x,ρ x*gaussianDivergence X x ∂gaussian d) =
      -(∫ x,fderiv ℝ ρ x (X x) ∂gaussian d) := by
  have hz := gaussianDivergence_integral_zero (multiplyGaussianTest ρ hρ hb X)
  simp_rw [gaussianDivergence_product ρ hρ hb X] at hz
  rw [integral_add (scalar_test_divergence_integrable ρ hρ X)
    (scalar_test_directional_integrable ρ hρ X)] at hz
  linarith

end GaussianMeasureBridge
