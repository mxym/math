import GaussianUnrestrictedDivergence

/-! Ordinary Euclidean divergence and its exact density transformation.
The Lebesgue whole-space identity is derived from the already proved Gaussian
Stein theorem by dividing a compact field by the positive Gaussian density. -/
open MeasureTheory ProbabilityTheory Module Set
open scoped Topology ENNReal ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

noncomputable def euclideanDivergence (X : Space d → Space d) (x : Space d) : ℝ :=
  gaussianDivergence X x+⟪x,X x⟫

lemma euclideanDivergence_coordinate_sum (X : Space d → Space d) (x : Space d) :
    euclideanDivergence X x = ∑ i : Fin d,⟪EuclideanSpace.basisFun (Fin d) ℝ i,
      fderiv ℝ X x (EuclideanSpace.basisFun (Fin d) ℝ i)⟫ := by
  unfold euclideanDivergence gaussianDivergence
  ring

lemma euclideanDivergence_product (ρ : Space d → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (X : Space d → Space d) (hX : ContDiff ℝ ∞ X) (x : Space d) :
    euclideanDivergence (fun y => ρ y • X y) x =
      ρ x*euclideanDivergence X x+fderiv ℝ ρ x (X x) := by
  simp only [euclideanDivergence,gaussianDivergence_product_function ρ hρ X hX,
    real_inner_smul_right]
  ring

lemma euclideanDivergence_density_product (X : Space d → Space d)
    (hX : ContDiff ℝ ∞ X) (x : Space d) :
    euclideanDivergence (fun y => gaussianLebesgueDensity d y • X y) x =
      gaussianLebesgueDensity d x*gaussianDivergence X x := by
  rw [euclideanDivergence_product _ (gaussianLebesgueDensity_contDiff d) X hX,
    gaussianLebesgueDensity_fderiv]
  simp only [smul_apply,smul_eq_mul,innerSL_apply_apply,euclideanDivergence]
  ring

lemma gaussianDensity_inverse_contDiff (d : ℕ) :
    ContDiff ℝ ∞ (fun x : Space d => (gaussianLebesgueDensity d x)⁻¹) :=
  (gaussianLebesgueDensity_contDiff d).inv (fun x => (gaussianLebesgueDensity_pos x).ne')

lemma euclideanDivergence_density_inverse (X : Space d → Space d)
    (hX : ContDiff ℝ ∞ X) (x : Space d) :
    euclideanDivergence X x = gaussianLebesgueDensity d x*
      gaussianDivergence (fun y => (gaussianLebesgueDensity d y)⁻¹ • X y) x := by
  have hh := euclideanDivergence_density_product
    (fun y => (gaussianLebesgueDensity d y)⁻¹ • X y)
    ((gaussianDensity_inverse_contDiff d).smul hX) x
  have he : (fun y => gaussianLebesgueDensity d y •
      ((gaussianLebesgueDensity d y)⁻¹ • X y)) = X := by
    funext y
    rw [smul_smul,mul_inv_cancel₀ (gaussianLebesgueDensity_pos y).ne',one_smul]
  rwa [he] at hh

theorem euclideanDivergence_integral_zero (X : Space d → Space d)
    (hX : ContDiff ℝ ∞ X) (hc : HasCompactSupport X) :
    (∫ x,euclideanDivergence X x) = 0 := by
  have hz := gaussianDivergence_integral_zero_function
    (fun y => (gaussianLebesgueDensity d y)⁻¹ • X y)
    ((gaussianDensity_inverse_contDiff d).smul hX)
    (hc.smul_left (f := fun y => (gaussianLebesgueDensity d y)⁻¹))
  rw [gaussian_integral_density] at hz
  simpa only [smul_eq_mul,← euclideanDivergence_density_inverse X hX] using hz

lemma euclideanDivergence_continuous (X : Space d → Space d) (hX : ContDiff ℝ ∞ X) :
    Continuous (euclideanDivergence X) := by
  have hd := hX.continuous_fderiv (by simp)
  unfold euclideanDivergence gaussianDivergence
  fun_prop

lemma euclideanDivergence_compact (X : Space d → Space d) (hc : HasCompactSupport X) :
    HasCompactSupport (euclideanDivergence X) := by
  apply hc.mono'
  intro x hx
  by_contra he
  apply hx
  simp only [euclideanDivergence_coordinate_sum,fderiv_of_notMem_tsupport ℝ he,
    zero_apply,inner_zero_right,Finset.sum_const_zero]

theorem euclideanDivergence_integrable (X : Space d → Space d)
    (hX : ContDiff ℝ ∞ X) (hc : HasCompactSupport X) :
    Integrable (euclideanDivergence X) :=
  (euclideanDivergence_continuous X hX).integrable_of_hasCompactSupport
    (euclideanDivergence_compact X hc)

end GaussianMeasureBridge
