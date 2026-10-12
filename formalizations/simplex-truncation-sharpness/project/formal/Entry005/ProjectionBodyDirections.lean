import Entry005.Targets

noncomputable section
open Metric MeasureTheory
open scoped RealInnerProductSpace
namespace Entry005

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Homogeneous brightness from the actual intrinsic projected Haar volume. -/
def projectionBrightness (K : Set E) (u : E) : ℝ := ‖u‖ * projectionVolumeSet K u

/-- Rescaling a nonzero normal does not change its actual orthogonal subspace or volume. -/
theorem projectionVolumeSet_smul_normal (K : Set E) (u : E) (c : ℝ) (hc : c ≠ 0) :
    projectionVolumeSet K (c • u) = projectionVolumeSet K u := by
  let F : Submodule ℝ E → ℝ := fun U =>
    (volume (U.orthogonalProjectionOnto '' K)).toReal
  change F (ℝ ∙ c • u)ᗮ = F (ℝ ∙ u)ᗮ
  exact congrArg (fun U : Submodule ℝ E => F Uᗮ)
    (Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc) u)

/-- The canonical unit-direction halfspace intersection equals its homogeneous
all-direction description; no abstract projection body is substituted. -/
theorem mem_projectionBodySet_iff_brightness (K : Set E) (y : E) :
    y ∈ projectionBodySet K ↔ ∀ u : E, inner ℝ u y ≤ projectionBrightness K u := by
  constructor
  · intro hy u
    by_cases hu : u = 0
    · simp [hu, projectionBrightness]
    have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hnunit : ‖‖u‖⁻¹ • u‖ = 1 := by simp [norm_smul, hu]
    have h := hy (‖u‖⁻¹ • u) hnunit
    rw [real_inner_smul_left,
      projectionVolumeSet_smul_normal K u _ (inv_ne_zero hnorm.ne')] at h
    change inner ℝ u y ≤ ‖u‖ * projectionVolumeSet K u
    have hh := mul_le_mul_of_nonneg_left h hnorm.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hnorm.ne', one_mul] using hh
  · intro hy u hu
    simpa only [projectionBrightness, hu, one_mul] using hy u

/-- Actual intrinsic projection volumes are translation invariant for every set. -/
theorem projectionVolumeSet_translate (K : Set E) (b u : E) :
    projectionVolumeSet ((fun x : E => x + b) '' K) u = projectionVolumeSet K u := by
  let U := (ℝ ∙ u)ᗮ
  have himage : U.orthogonalProjectionOnto '' ((fun x : E => x + b) '' K) =
      (fun z : U => z + -U.orthogonalProjectionOnto b) ⁻¹'
        (U.orthogonalProjectionOnto '' K) := by
    rw [Set.image_image]
    ext z
    constructor
    · rintro ⟨x, hx, he⟩
      refine ⟨x, hx, ?_⟩
      change U.orthogonalProjectionOnto x = z + -U.orthogonalProjectionOnto b
      rw [← sub_eq_add_neg]
      apply eq_sub_iff_add_eq.mpr
      simpa only [Function.comp_apply, map_add] using he
    · rintro ⟨x, hx, he⟩
      refine ⟨x, hx, ?_⟩
      change U.orthogonalProjectionOnto (x + b) = z
      rw [map_add, he]
      simp
  unfold projectionVolumeSet
  change (volume (U.orthogonalProjectionOnto '' ((fun x : E => x + b) '' K))).toReal = _
  rw [himage, measure_preimage_add_right]

/-- Translation invariance of the actual canonical projection-body carrier. -/
theorem projectionBodySet_translate (K : Set E) (b : E) :
    projectionBodySet ((fun x : E => x + b) '' K) = projectionBodySet K := by
  ext y
  simp only [projectionBodySet, Set.mem_ofPred_eq, projectionVolumeSet_translate]

/-- Translation invariance of the actual canonical projection-volume ratio. -/
theorem projectionRatio_translate (K : Set E) (b : E) :
    projectionRatio ((fun x : E => x + b) '' K) = projectionRatio K := by
  have himage : (fun x : E => x + b) '' K = (fun x : E => x + -b) ⁻¹' K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨x + -b, hx, by simp⟩
  unfold projectionRatio
  rw [projectionBodySet_translate, himage, measure_preimage_add_right]

end Entry005
