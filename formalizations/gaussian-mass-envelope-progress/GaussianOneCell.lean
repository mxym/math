import GaussianQuantile
import GaussianHalfspaceFlux

/-!
The exact one-cell Gaussian upper bound on actual Bochner first moments.
The labels may be fractional and have no geometric regularity assumptions.
-/
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

namespace GaussianMeasureBridge

lemma gaussian_unit_halfspace_mass {d : ℕ} (u : Space d) (hu : ‖u‖ = 1) (a : ℝ) :
    ((gaussian d) {x | a < ⟪u, x⟫}).toReal = gaussianTail a := by
  rw [gaussianTail_eq_probability, ← gaussian_unit_inner_law u hu,
    Measure.map_apply (by fun_prop) measurableSet_Ioi]
  rfl

namespace FractionalPartition
variable {d k : ℕ} [NeZero k] (F : FractionalPartition d k)

/-- The threshold rearrangement inequality, including its mass correction. -/
theorem one_cell_threshold_bound (i : Fin k) (u : Space d) (hu : ‖u‖ = 1) (a : ℝ) :
    ⟪u, F.moment i⟫ - F.mass i * a ≤ standardDensity a - gaussianTail a * a := by
  let H : Set (Space d) := {x | a < ⟪u, x⟫}
  have hH : MeasurableSet H := measurableSet_lt measurable_const (by fun_prop)
  have hi := (integrable_score u a).indicator hH
  have hle : ∀ᵐ x ∂gaussian d, F.labels i x * (⟪u, x⟫ - a) ≤
      H.indicator (fun x => ⟪u, x⟫ - a) x := by
    filter_upwards [F.nonneg i, F.le_one i] with x hx0 hx1
    by_cases hx : a < ⟪u, x⟫
    · rw [indicator_of_mem (show x ∈ H from hx)]
      nlinarith
    · rw [indicator_of_notMem (show x ∉ H from hx)]
      exact mul_nonpos_of_nonneg_of_nonpos hx0 (sub_nonpos.mpr (le_of_not_gt hx))
  have h := integral_mono_ae (F.integrable_weighted_score i u a) hi hle
  rw [F.integral_weighted_score, integral_indicator hH,
    integral_sub (integrable_gaussian_inner u).integrableOn
      (integrable_const a).integrableOn] at h
  have hc : (∫ x in H, a ∂gaussian d) = gaussianTail a * a := by
    rw [integral_const]
    change (((gaussian d).restrict H) univ).toReal * a = gaussianTail a * a
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    rw [gaussian_unit_halfspace_mass u hu a]
  rw [hc, gaussian_unit_halfspace_scalar_flux u hu a] at h
  exact h

/-- Arbitrary measurable fractional cells of mass equal to the actual tail at a
have first moment norm at most the density at a. -/
theorem one_cell_norm_bound (i : Fin k) (a : ℝ) (ha : F.mass i = gaussianTail a) :
    ‖F.moment i‖ ≤ standardDensity a := by
  by_cases hm : F.moment i = 0
  · simpa [hm] using (standardDensity_pos a).le
  · let u : Space d := ‖F.moment i‖⁻¹ • F.moment i
    have hn : ‖F.moment i‖ ≠ 0 := norm_ne_zero_iff.mpr hm
    have hu : ‖u‖ = 1 := by
      simp only [u, norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ hn
    have hi : ⟪u, F.moment i⟫ = ‖F.moment i‖ := by
      simp only [u, real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp [hn]
    have h := F.one_cell_threshold_bound i u hu a
    rw [ha, hi] at h
    linarith

/-- The exact single-cell Gaussian profile in the paper's mass parameter. -/
theorem one_cell_profile_bound (i : Fin k) (hp : 0 < F.mass i) (hp1 : F.mass i < 1) :
    ‖F.moment i‖ ≤ standardDensity (upperQuantile (F.mass i)) :=
  F.one_cell_norm_bound i _ (gaussianTail_upperQuantile hp hp1).symm

/-- The global upper half of the mass-envelope theorem for arbitrary fractional partitions. -/
theorem sum_moment_sq_le_profile
    (hp : ∀ i, 0 < F.mass i) (hp1 : ∀ i, F.mass i < 1) :
    ∑ i, ‖F.moment i‖ ^ 2 ≤ ∑ i, standardDensity (upperQuantile (F.mass i)) ^ 2 := by
  apply Finset.sum_le_sum
  intro i _
  have h := F.one_cell_profile_bound i (hp i) (hp1 i)
  have hn := norm_nonneg (F.moment i)
  have hs := (standardDensity_pos (upperQuantile (F.mass i))).le
  nlinarith

end FractionalPartition
end GaussianMeasureBridge
