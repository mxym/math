import GaussianHalflineFlux
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Independence.Integration

/-! Actual vector-valued Gaussian flux for a halfspace with unit inward normal.
The proof uses Gaussian orthogonal independence and the proved half-line flux. -/
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

namespace GaussianMeasureBridge
variable {d : ℕ}

lemma gaussian_inner_covariance (u v : Space d) :
    cov[fun x => ⟪u, x⟫, fun x => ⟪v, x⟫; gaussian d] = ⟪u, v⟫ := by
  rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    gaussian, covarianceBilin_stdGaussian]
  rfl

lemma gaussian_orthogonal_indep (u v : Space d) (huv : ⟪u, v⟫ = 0) :
    IndepFun (fun x : Space d => ⟪u, x⟫) (fun x => ⟪v, x⟫) (gaussian d) := by
  have h := (IsGaussian.hasGaussianLaw_id (μ := gaussian d)).map
    ((innerSL ℝ u).prod (innerSL ℝ v))
  apply HasGaussianLaw.indepFun_of_covariance_eq_zero h
  change cov[fun x => ⟪u, x⟫, fun x => ⟪v, x⟫; gaussian d] = 0
  rw [gaussian_inner_covariance, huv]

lemma gaussian_unit_inner_law (u : Space d) (hu : ‖u‖ = 1) :
    (gaussian d).map (fun x => ⟪u, x⟫) = gaussianReal 0 1 := by
  change (gaussian d).map (innerSL ℝ u) = _
  rw [IsGaussian.map_eq_gaussianReal, gaussian, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, innerSL_apply_norm, hu]
  norm_num

lemma integrable_gaussian_inner (u : Space d) :
    Integrable (fun x : Space d => ⟪u, x⟫) (gaussian d) := by
  exact (innerSL ℝ u).integrable_comp IsGaussian.integrable_id

lemma integral_gaussian_inner (u : Space d) :
    (∫ x : Space d, ⟪u, x⟫ ∂gaussian d) = 0 := by
  change (∫ x, (innerSL ℝ u) x ∂gaussian d) = _
  rw [gaussian, integral_strongDual_stdGaussian]

lemma gaussian_halfspace_orthogonal_integral (u v : Space d) (huv : ⟪u, v⟫ = 0) (a : ℝ) :
    (∫ x in {x : Space d | a < ⟪v, x⟫}, ⟪u, x⟫ ∂gaussian d) = 0 := by
  let f : ℝ → ℝ := (Ioi a).indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator measurableSet_Ioi
  have h := (gaussian_orthogonal_indep u v huv).comp measurable_id hf
  have hi := h.integral_fun_mul_eq_mul_integral
    (by fun_prop) (hf.comp (by fun_prop)).aestronglyMeasurable
  have he : (fun x : Space d => ⟪u, x⟫ * f ⟪v, x⟫) =
      {x : Space d | a < ⟪v, x⟫}.indicator (fun x => ⟪u, x⟫) := by
    ext x
    by_cases hx : a < ⟪v, x⟫ <;> simp [f, hx]
  change (∫ x, ⟪u, x⟫ * f ⟪v, x⟫ ∂gaussian d) =
    (∫ x, ⟪u, x⟫ ∂gaussian d) * (∫ x, f ⟪v, x⟫ ∂gaussian d) at hi
  rw [he, integral_indicator (measurableSet_lt measurable_const (by fun_prop)),
    integral_gaussian_inner, zero_mul] at hi
  exact hi

lemma gaussian_unit_halfspace_scalar_flux (u : Space d) (hu : ‖u‖ = 1) (a : ℝ) :
    (∫ x in {x : Space d | a < ⟪u, x⟫}, ⟪u, x⟫ ∂gaussian d) = standardDensity a := by
  have h := gaussianReal_halfline_firstMoment a
  rw [← integral_indicator measurableSet_Ioi, ← gaussian_unit_inner_law u hu] at h
  have hm : AEStronglyMeasurable ((Ioi a).indicator (fun x : ℝ => x))
      ((gaussian d).map (fun x => ⟪u, x⟫)) :=
    (measurable_id.indicator measurableSet_Ioi).aestronglyMeasurable
  rw [integral_map (by fun_prop) hm] at h
  have he : (fun x : Space d => (Ioi a).indicator (fun t => t) ⟪u, x⟫) =
      {x : Space d | a < ⟪u, x⟫}.indicator (fun x => ⟪u, x⟫) := by
    ext x
    by_cases hx : a < ⟪u, x⟫ <;> simp [hx]
  rw [he, integral_indicator (measurableSet_lt measurable_const (by fun_prop))] at h
  exact h

/-- Gaussian flux with the inward unit normal, at any offset and in any finite
dimension. All quantities are actual Bochner integrals and Gaussian density. -/
theorem gaussian_unit_halfspace_flux (u : Space d) (hu : ‖u‖ = 1) (a : ℝ) :
    (∫ x in {x : Space d | a < ⟪u, x⟫}, x ∂gaussian d) = standardDensity a • u := by
  apply ext_inner_left ℝ
  intro v
  let r := v - ⟪v, u⟫ • u
  have hru : ⟪r, u⟫ = 0 := by
    simp [r, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hu]
  have hzero := gaussian_halfspace_orthogonal_integral r u hru a
  have hscalar := gaussian_unit_halfspace_scalar_flux u hu a
  have hid : ∀ x : Space d, ⟪v, x⟫ = ⟪r, x⟫ + ⟪v, u⟫ * ⟪u, x⟫ := by
    intro x
    simp [r, inner_sub_left, real_inner_smul_left]
  have hvector := (innerSL ℝ v).integral_comp_comm
    ((IsGaussian.integrable_id (μ := gaussian d)).integrableOn
      (s := {x : Space d | a < ⟪u, x⟫}))
  change (∫ x in {x : Space d | a < ⟪u, x⟫}, ⟪v, x⟫ ∂gaussian d) =
    ⟪v, ∫ x in {x : Space d | a < ⟪u, x⟫}, x ∂gaussian d⟫ at hvector
  rw [← hvector]
  rw [integral_congr_ae (ae_of_all ((gaussian d).restrict {x | a < ⟪u, x⟫}) hid)]
  rw [integral_add (integrable_gaussian_inner r).integrableOn
    ((integrable_gaussian_inner u).const_mul ⟪v, u⟫).integrableOn,
    integral_const_mul, hzero, hscalar]
  simp [real_inner_smul_right, mul_comm]

end GaussianMeasureBridge
