import Entry005.PyramidLiftCoordinates

noncomputable section
open MeasureTheory Module
open scoped BigOperators RealInnerProductSpace Pointwise
namespace Entry005
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem finite_zonotope_option (g : Option ι → E) :
    finiteZonotope g = symmetricSegmentExtrusion (finiteZonotope (fun i => g (some i))) (g none) := by
  classical
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨∑ i, t (some i) • g (some i), ⟨fun i => t (some i), fun i => ht (some i), rfl⟩,
      t none, ht none, ?_⟩
    change (∑ i, t i • g i) = _
    rw [Fintype.sum_option]
    exact add_comm _ _
  · rintro ⟨x, ⟨t, ht, rfl⟩, r, hr, rfl⟩
    refine ⟨(fun i => match i with | none => r | some j => t j), ?_, ?_⟩
    · intro i
      cases i with
      | none => exact hr
      | some i => exact ht i
    · change (∑ i, (match i with | none => r | some j => t j) • g i) = _
      rw [Fintype.sum_option]
      exact add_comm _ _

theorem finite_zonotope_scalar_image (g : ι → E) (c : ℝ) :
    finiteZonotope (fun i => c • g i) = c • finiteZonotope g := by
  have hm := finite_zonotope_linear_image g (c • LinearMap.id)
  simpa only [LinearMap.smul_apply, LinearMap.id_apply, Set.image_smul] using hm.symm

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem finite_zonotope_option_volume (g : Option ι → E) :
    volume (finiteZonotope g) = volume (finiteZonotope (fun i => g (some i))) +
      ENNReal.ofReal (2 * ‖g none‖) *
        volume ((ℝ ∙ g none)ᗮ.orthogonalProjectionOnto '' finiteZonotope (fun i => g (some i))) := by
  rw [finite_zonotope_option, symmetric_segment_extrusion_eq_preimage,
    measure_preimage_add, compact_convex_extrusion_volume
      (finite_zonotope_compact _) (finite_zonotope_convex _) (g none) 2 (by norm_num)]

/-- Actual side-generated segment sum of the lifted pyramid. -/
def pyramidSideZonotope (n : ι → E) (h : ι → ℝ) : Set (WithLp 2 (E × ℝ)) :=
  finiteZonotope (fun i => (finiteHalfspaceFacetArea n h i / (2 * Module.finrank ℝ E : ℝ)) •
    WithLp.toLp 2 (n i, h i))

end Entry005
