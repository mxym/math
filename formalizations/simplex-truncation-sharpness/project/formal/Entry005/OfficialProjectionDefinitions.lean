import OAI.Geometry.ProjectionVolume.Brightness
import Entry005.Targets

noncomputable section
open Metric MeasureTheory Module
open scoped RealInnerProductSpace Pointwise

namespace Entry005

theorem official_normal_hyperplane_eq {d : ℕ} (u : Space d) :
    OAI.Paper092.normalHyperplane u = (ℝ ∙ u)ᗮ := rfl

theorem official_projection_volume_eq {d : ℕ} (K : Set (Space d)) (u : Space d) :
    OAI.Paper092.projectionVolume K u =
      volume ((ℝ ∙ u)ᗮ.orthogonalProjectionOnto '' K) := rfl

theorem official_projection_volume_real_eq {d : ℕ} (K : Set (Space d)) (u : Space d) :
    (OAI.Paper092.projectionVolume K u).toReal = projectionVolumeSet K u := rfl

theorem official_brightness_eq_norm_mul {d : ℕ} (K : Set (Space d)) (u : Space d) :
    OAI.Paper092.brightness K u = ‖u‖ * projectionVolumeSet K u := rfl

theorem official_unit_brightness_eq {d : ℕ} (K : Set (Space d)) (u : Space d) (hu : ‖u‖ = 1) :
    OAI.Paper092.brightness K u = projectionVolumeSet K u := by
  rw [official_brightness_eq_norm_mul, hu, one_mul]

/-- All-direction official brightness halfspaces and the original target's
unit-direction projection halfspaces define the same actual set. -/
theorem official_projection_body_eq {d : ℕ} (K : Set (Space d)) :
    OAI.Paper092.projectionBody K = projectionBodySet K := by
  ext x
  constructor
  · intro hx u hu
    simpa only [official_unit_brightness_eq K u hu] using hx u
  · intro hx u
    by_cases hu : u = 0
    · simp [hu, OAI.Paper092.brightness]
    have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
    let v : Space d := ‖u‖⁻¹ • u
    have hv : ‖v‖ = 1 := by
      dsimp [v]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnu), inv_mul_cancel₀ hnu.ne']
    have hbright : OAI.Paper092.brightness K v = ‖u‖⁻¹ * OAI.Paper092.brightness K u := by
      dsimp [v]
      rw [OAI.Paper092.brightness_smul, abs_of_pos (inv_pos.mpr hnu)]
    have hf : inner ℝ v x ≤ OAI.Paper092.brightness K v := by
      rw [official_unit_brightness_eq K v hv]
      exact hx v hv
    rw [hbright] at hf
    change inner ℝ (‖u‖⁻¹ • u) x ≤ _ at hf
    rw [real_inner_smul_left] at hf
    exact (mul_le_mul_iff_right₀ (inv_pos.mpr hnu)).mp (by simpa only [mul_comm] using hf)

theorem official_normalized_projection_volume_eq {d : ℕ} (K : Set (Space d)) :
    OAI.Paper092.normalizedProjectionVolume K = projectionRatio K := by
  unfold OAI.Paper092.normalizedProjectionVolume
  rw [official_projection_body_eq]
  simp only [projectionRatio, finrank_euclideanSpace_fin]

/-- The checked official theorem strengthens compactness to every target set,
without a supplied radius or geometric representation premise. -/
theorem actual_projection_body_compact_via_official {d : ℕ} (K : Set (Space d)) :
    IsCompact (projectionBodySet K) := by
  rw [← official_projection_body_eq]
  exact OAI.Paper092.projectionBody_isCompact K

end Entry005
