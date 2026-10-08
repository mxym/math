import GaussianUnrestrictedDivergence
import GaussianScaledCutoffGradient
import GaussianUnitHalfspacePerimeter
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# First-moment calibration for actual Gaussian BV perimeter

For every (not necessarily polyhedral) measurable set S, the genuine
variational Gaussian perimeter bounds the Euclidean norm of the Bochner
Gaussian first moment.  The bound is sharp for every halfspace.

This elementary statement is *not* the sharp equal-mass multi-bubble
perimeter inequality: it does not establish the all-k Gaussian theorem.
-/

open MeasureTheory ProbabilityTheory Module Set Filter
open scoped Topology ENNReal ContDiff RealInnerProductSpace

namespace GaussianMeasureBridge
variable {d : ℕ}

noncomputable def directionalCutoffTest (N : ℕ) (u : Space d) (hu : ‖u‖ ≤ 1) :
    GaussianTestField d :=
  { toFun := fun x => scaledGaussianCutoff d N x • (-u)
    smooth := (scaledGaussianCutoff_contDiff N).smul contDiff_const
    compact := (scaledGaussianCutoff_compact N).smul_right (f' := fun _ => -u)
    norm_le := fun x => by
      rw [norm_smul, norm_neg, Real.norm_eq_abs,
        abs_of_nonneg (scaledGaussianCutoff_bounds N x).1]
      calc
        scaledGaussianCutoff d N x * ‖u‖ ≤ 1 * ‖u‖ :=
          mul_le_mul_of_nonneg_right (scaledGaussianCutoff_bounds N x).2 (norm_nonneg u)
        _ ≤ 1 := by simpa using hu }

lemma gaussianDivergence_const_negative (u : Space d) (x : Space d) :
    gaussianDivergence (fun _ : Space d => -u) x = ⟪x,u⟫ := by
  simp [gaussianDivergence]

lemma directionalCutoffTest_divergence (N : ℕ) (u : Space d)
    (hu : ‖u‖ ≤ 1) (x : Space d) :
    gaussianDivergence (directionalCutoffTest N u hu) x =
      -(fderiv ℝ (scaledGaussianCutoff d N) x u) +
      scaledGaussianCutoff d N x * ⟪x,u⟫ := by
  have h := gaussianDivergence_product_function
    (scaledGaussianCutoff d N) (scaledGaussianCutoff_contDiff N)
    (fun _ : Space d => -u) contDiff_const x
  change gaussianDivergence (directionalCutoffTest N u hu) x =
    scaledGaussianCutoff d N x *
      gaussianDivergence (fun _ : Space d => -u) x +
    fderiv ℝ (scaledGaussianCutoff d N) x (-u) at h
  rw [gaussianDivergence_const_negative u x, map_neg] at h
  simpa only [add_comm] using h

lemma directionalCutoffTest_divergence_tendsto (u : Space d)
    (hu : ‖u‖ ≤ 1) (x : Space d) :
    Tendsto (fun N => gaussianDivergence (directionalCutoffTest N u hu) x)
      atTop (𝓝 ⟪u,x⟫) := by
  simp_rw [directionalCutoffTest_divergence]
  have h := (scaledGaussianCutoff_directional_tendsto x u).neg.add
    ((scaledGaussianCutoff_tendsto x).mul_const ⟪x,u⟫)
  simpa only [neg_zero, zero_add, one_mul, real_inner_comm x u] using h

lemma directionalCutoffTest_divergence_bound (u : Space d)
    (hu : ‖u‖ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N (x : Space d),
      ‖gaussianDivergence (directionalCutoffTest N u hu) x‖ ≤
        C * ‖u‖ + ‖⟪u,x⟫‖ := by
  obtain ⟨C,hC0,hC⟩ := scaledGaussianCutoff_uniform_gradient_bound (d := d)
  refine ⟨C,hC0,fun N x => ?_⟩
  rw [directionalCutoffTest_divergence]
  have hd := ((fderiv ℝ (scaledGaussianCutoff d N) x).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (hC N x) (norm_nonneg u))
  have hb : ‖scaledGaussianCutoff d N x * ⟪x,u⟫‖ ≤ ‖⟪u,x⟫‖ := by
    calc
      _ = scaledGaussianCutoff d N x * ‖⟪u,x⟫‖ := by
        rw [norm_mul,Real.norm_eq_abs,
          abs_of_nonneg (scaledGaussianCutoff_bounds N x).1,
          real_inner_comm x u]
      _ ≤ 1 * ‖⟪u,x⟫‖ :=
        mul_le_mul_of_nonneg_right (scaledGaussianCutoff_bounds N x).2 (norm_nonneg _)
      _ = _ := one_mul _
  calc
    ‖-fderiv ℝ (scaledGaussianCutoff d N) x u +
        scaledGaussianCutoff d N x * ⟪x,u⟫‖ ≤
      ‖-fderiv ℝ (scaledGaussianCutoff d N) x u‖ +
        ‖scaledGaussianCutoff d N x * ⟪x,u⟫‖ := norm_add_le _ _
    _ ≤ C * ‖u‖ + ‖⟪u,x⟫‖ :=
      add_le_add (by simpa only [norm_neg] using hd) hb

/-- A sharp, unconditional lower calibration for the actual variational
Gaussian BV perimeter, applied to any real directional first moment. -/
theorem gaussianBVPerimeter_ge_directional_moment
    (S : Set (Space d)) (u : Space d) (hu : ‖u‖ ≤ 1) :
    ENNReal.ofReal (∫ x in S, ⟪u,x⟫ ∂gaussian d) ≤ gaussianBVPerimeter S := by
  let X : ℕ → GaussianTestField d := fun N => directionalCutoffTest N u hu
  obtain ⟨C,hC0,hbound⟩ := directionalCutoffTest_divergence_bound u hu
  have hdom : Integrable (fun x : Space d => C * ‖u‖ + ‖⟪u,x⟫‖) (gaussian d) :=
    (integrable_const _).add (integrable_gaussian_inner u).norm
  have hlim : Tendsto
      (fun N => ∫ x in S,gaussianDivergence (X N) x ∂gaussian d) atTop
      (𝓝 (∫ x in S,⟪u,x⟫ ∂gaussian d)) := by
    have h := tendsto_integral_of_dominated_convergence
      (μ := (gaussian d).restrict S)
      (F := fun N x => gaussianDivergence (X N) x)
      (f := fun x => ⟪u,x⟫)
      (fun x => C * ‖u‖ + ‖⟪u,x⟫‖)
      (fun N => (gaussianDivergence_continuous (X N)).aestronglyMeasurable)
      hdom.integrableOn
      (fun N => ae_of_all _ fun x => by simpa only [X] using hbound N x)
      (ae_of_all _ fun x => by
        simpa only [X] using directionalCutoffTest_divergence_tendsto u hu x)
    exact h
  have hen := (ENNReal.continuous_ofReal.tendsto _).comp hlim
  apply le_of_tendsto hen
  exact Eventually.of_forall fun N => gaussianBVPerimeter_ge_test S (X N)

/-- The actual Bochner Gaussian first-moment norm is bounded by the
conventional Gaussian BV perimeter, in every finite dimension. -/
theorem gaussianBVPerimeter_ge_moment_norm (S : Set (Space d)) :
    ENNReal.ofReal ‖∫ x in S,x ∂gaussian d‖ ≤ gaussianBVPerimeter S := by
  let m : Space d := ∫ x in S,x ∂gaussian d
  by_cases hm : m = 0
  · change ENNReal.ofReal ‖m‖ ≤ gaussianBVPerimeter S
    rw [hm, norm_zero, ENNReal.ofReal_zero]
    exact bot_le
  · have hp : 0 < ‖m‖ := norm_pos_iff.mpr hm
    let u : Space d := ‖m‖⁻¹ • m
    have hu : ‖u‖ = 1 := by
      rw [show u = ‖m‖⁻¹ • m from rfl, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hp.le)]
      exact inv_mul_cancel₀ hp.ne'
    have hinner : ⟪u,m⟫ = ‖m‖ := by
      rw [show u = ‖m‖⁻¹ • m from rfl,
        real_inner_smul_left, real_inner_self_eq_norm_sq]
      calc
        ‖m‖⁻¹ * ‖m‖ ^ 2 = (‖m‖⁻¹ * ‖m‖) * ‖m‖ := by ring
        _ = ‖m‖ := by rw [inv_mul_cancel₀ hp.ne',one_mul]
    have hcomm : (∫ x in S, ⟪u,x⟫ ∂gaussian d) = ⟪u,m⟫ := by
      have h := (innerSL ℝ u).integral_comp_comm
        ((IsGaussian.integrable_id (μ := gaussian d)).integrableOn (s := S))
      change (∫ x in S,⟪u,x⟫ ∂gaussian d) =
        ⟪u,∫ x in S,x ∂gaussian d⟫ at h
      exact h
    have h := gaussianBVPerimeter_ge_directional_moment S u hu.le
    rw [hcomm, hinner] at h
    exact h

/-- For every true Gaussian halfspace, the first-moment calibration is an
equality (not merely an asymptotic claim). -/
theorem gaussianBVPerimeter_halfspace_eq_moment_norm
    (u : Space (d+1)) (hu : ‖u‖ = 1) (a : ℝ) :
    gaussianBVPerimeter {x | a < ⟪u,x⟫} =
      ENNReal.ofReal ‖∫ x in {x | a < ⟪u,x⟫},x ∂gaussian (d+1)‖ := by
  rw [gaussianBVPerimeter_unit_halfspace u hu a,
    gaussian_unit_halfspace_flux u hu a, norm_smul, hu, mul_one,
    Real.norm_eq_abs,abs_of_pos (standardDensity_pos a)]

#print axioms gaussianBVPerimeter_ge_directional_moment
#print axioms gaussianBVPerimeter_ge_moment_norm
#print axioms gaussianBVPerimeter_halfspace_eq_moment_norm

end GaussianMeasureBridge

