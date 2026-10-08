import Entry005.PyramidFacetAreas
import Entry005.PyramidSideFrame

noncomputable section
open MeasureTheory Module
open scoped RealInnerProductSpace Pointwise
namespace Entry005
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def pyramidSideChartApex (n : E) (h : ℝ) : (ℝ ∙ pyramidSideNormal n h)ᗮ :=
  (ℝ ∙ pyramidSideNormal n h)ᗮ.orthogonalProjectionOnto pyramidApex

theorem pyramid_side_chart_offset (n : E) (h : ℝ) (hn : ‖n‖ = 1) :
    (h / pyramidSlope h) • pyramidSideNormal n h +
      (pyramidSideChartApex n h : WithLp 2 (E × ℝ)) = pyramidApex := by
  have hd := unit_normal_projection_decomposition (pyramidSideNormal n h) pyramidApex
    (pyramidSideNormal_unit n h hn)
  have hi : inner ℝ (pyramidSideNormal n h) pyramidApex = h / pyramidSlope h := by
    rw [pyramidApex, inner_pyramidSideNormal]
    simp
  rw [hi] at hd
  simpa only [pyramidSideChartApex, add_comm] using hd.symm

/-- Actual side coordinates from a literal radial cone over the original facet chart. -/
theorem pyramid_side_radial_coordinates (n : E) (h : ℝ) (hn : ‖n‖ = 1)
    (q : (ℝ ∙ n)ᗮ) (r : ℝ) :
    pyramidApex + (pyramidSideFrame n h hn (WithLp.toLp 2 (r • q, r * pyramidSlope h)) :
        WithLp 2 (E × ℝ)) =
      WithLp.toLp 2 (r • (h • n + (q : E)), 1 - r) := by
  rw [pyramidSideFrame_val, pyramidApex, ← WithLp.toLp_add]
  apply WithLp.ofLp_injective
  apply Prod.ext
  · change 0 + (r • (q : E) + (r * pyramidSlope h / pyramidSlope h * h) • n) = _
    rw [mul_div_cancel_right₀ _ (pyramidSlope_pos h).ne', zero_add]
    module
  · change 1 + -(r * pyramidSlope h) / pyramidSlope h = 1 - r
    field_simp [(pyramidSlope_pos h).ne']
    ring

variable {ι : Type*} [Fintype ι] [Nontrivial E]

omit [Fintype ι] in
theorem pyramid_side_facet_chart (n : ι → E) (h : ι → ℝ) (i : ι)
    (hn : ‖n i‖ = 1) (hh : ∀ i, 0 < h i) (hc : IsCompact (finiteHalfspaceSet n h)) :
    finiteHalfspaceFacetChart (pyramidHalfspaceNormal n h) (pyramidHalfspaceHeight h) (some i) =
      (fun y => pyramidSideChartApex (n i) (h i) + y) ''
        (pyramidSideFrame (n i) (h i) hn ''
          (WithLp.toLp 2 '' radialCone (finiteHalfspaceFacetChart n h i) (pyramidSlope (h i)))) ∪
      {pyramidSideChartApex (n i) (h i)} := by
  let a := pyramidSideChartApex (n i) (h i)
  let v := pyramidSideNormal (n i) (h i)
  let b := h i / pyramidSlope (h i)
  have hoff : b • v + (a : WithLp 2 (E × ℝ)) = pyramidApex :=
    pyramid_side_chart_offset (n i) (h i) hn
  have hconv := finite_halfspace_convex n h
  change ({y : (ℝ ∙ v)ᗮ | b • v + (y : WithLp 2 (E × ℝ)) ∈
      finiteHalfspaceSet (pyramidHalfspaceNormal n h) (pyramidHalfspaceHeight h)} : Set (ℝ ∙ v)ᗮ) =
    (fun y : (ℝ ∙ v)ᗮ => a + y) ''
      (pyramidSideFrame (n i) (h i) hn ''
        (WithLp.toLp 2 '' radialCone (finiteHalfspaceFacetChart n h i) (pyramidSlope (h i)))) ∪ {a}
  ext y
  change b • v + (y : WithLp 2 (E × ℝ)) ∈
      finiteHalfspaceSet (pyramidHalfspaceNormal n h) (pyramidHalfspaceHeight h) ↔ _
  constructor
  · intro hy
    have hp : b • v + (y : WithLp 2 (E × ℝ)) ∈ pyramidSet (finiteHalfspaceSet n h) := by
      rwa [pyramidSet_finite_halfspace n h hh hc]
    have hi : inner ℝ v (b • v + (y : WithLp 2 (E × ℝ))) = b := by
      rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq,
        pyramidSideNormal_unit (n i) (h i) hn,
        Submodule.mem_orthogonal_singleton_iff_inner_right.mp y.property]
      simp
    rcases (mem_pyramidSet_iff hconv _).mp hp with hp | ⟨r, hr, z, hz, hp⟩
    · apply Set.mem_union_right
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      exact add_left_cancel (hp.trans hoff.symm)
    · by_cases hr0 : r = 0
      · apply Set.mem_union_right
        apply Set.mem_singleton_iff.mpr
        apply Subtype.ext
        have hp' : b • v + (y : WithLp 2 (E × ℝ)) = pyramidApex := by
          simpa [hr0, pyramidApex] using hp
        exact add_left_cancel (hp'.trans hoff.symm)
      · have hzi : inner ℝ (n i) z = h i := by
          rw [hp] at hi
          change inner ℝ (pyramidSideNormal (n i) (h i)) (WithLp.toLp 2 (r • z, 1 - r)) =
            h i / pyramidSlope (h i) at hi
          rw [inner_pyramidSideNormal, inner_smul_right] at hi
          have he := (div_left_inj' (pyramidSlope_pos (h i)).ne').mp hi
          have hm : r * (inner ℝ (n i) z - h i) = 0 := by nlinarith
          exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hr0)
        let q := (ℝ ∙ n i)ᗮ.orthogonalProjectionOnto z
        have hq : q ∈ finiteHalfspaceFacetChart n h i := by
          rw [← finite_halfspace_facet_chart_projection_image n h i hn]
          exact ⟨z, ⟨hz, hzi⟩, rfl⟩
        have hzq : h i • n i + (q : E) = z := by
          have hd := unit_normal_projection_decomposition (n i) z hn
          rw [hzi] at hd
          simpa only [q, add_comm] using hd.symm
        apply Set.mem_union_left
        refine ⟨pyramidSideFrame (n i) (h i) hn
          (WithLp.toLp 2 (r • q, r * pyramidSlope (h i))), ?_, ?_⟩
        · refine ⟨WithLp.toLp 2 (r • q, r * pyramidSlope (h i)), ?_, rfl⟩
          exact ⟨(r • q, r * pyramidSlope (h i)), ⟨r, hr, q, hq, rfl⟩, rfl⟩
        · apply Subtype.ext
          apply (add_left_cancel (a := b • v))
          rw [Submodule.coe_add, ← add_assoc, hoff, pyramid_side_radial_coordinates, hzq]
          exact hp.symm
  · rintro (⟨s, ⟨p, ⟨z, ⟨r, hr, q, hq, rfl⟩, rfl⟩, rfl⟩, rfl⟩ | hy)
    · rw [Submodule.coe_add, ← add_assoc, hoff, pyramid_side_radial_coordinates]
      rw [← pyramidSet_finite_halfspace n h hh hc]
      exact (mem_pyramidSet_iff hconv _).mpr (Or.inr ⟨r, hr, h i • n i + (q : E), hq, rfl⟩)
    · rcases Set.mem_singleton_iff.mp hy with rfl
      rw [hoff, ← pyramidSet_finite_halfspace n h hh hc]
      exact (mem_pyramidSet_iff hconv _).mpr (Or.inl rfl)

omit [Fintype ι] in
theorem pyramid_side_facet_of_empty (n : ι → E) (h : ι → ℝ) (i : ι)
    (hn : ‖n i‖ = 1) (hh : ∀ i, 0 < h i) (hc : IsCompact (finiteHalfspaceSet n h))
    (he : finiteHalfspaceFacet n h i = ∅) :
    finiteHalfspaceFacet (pyramidHalfspaceNormal n h) (pyramidHalfspaceHeight h) (some i) =
      {pyramidApex} := by
  have hchart : finiteHalfspaceFacetChart n h i = ∅ := by
    rw [← finite_halfspace_facet_chart_projection_image n h i hn, he, Set.image_empty]
  have hr : radialCone (∅ : Set (ℝ ∙ n i)ᗮ) (pyramidSlope (h i)) = ∅ := by
    ext p
    simp [radialCone]
  rw [← finite_halfspace_facet_chart_image (pyramidHalfspaceNormal n h)
    (pyramidHalfspaceHeight h) (some i) (pyramidSideNormal_unit (n i) (h i) hn),
    pyramid_side_facet_chart n h i hn hh hc, hchart]
  simp only [hr, Set.image_empty, Set.empty_union]
  change (fun z : (ℝ ∙ pyramidSideNormal (n i) (h i))ᗮ =>
    (h i / pyramidSlope (h i)) • pyramidSideNormal (n i) (h i) +
    (z : WithLp 2 (E × ℝ))) '' {pyramidSideChartApex (n i) (h i)} = _
  rw [Set.image_singleton, pyramid_side_chart_offset (n i) (h i) hn]

section Volume
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [Fintype ι] in
/-- Actual side area, with no assumed pyramid, Jacobian or facet-area identity. -/
theorem pyramid_side_facet_area (n : ι → E) (h : ι → ℝ) (i : ι)
    (hn : ‖n i‖ = 1) (hh : ∀ i, 0 < h i) (hc : IsCompact (finiteHalfspaceSet n h)) :
    finiteHalfspaceFacetArea (pyramidHalfspaceNormal n h) (pyramidHalfspaceHeight h) (some i) =
      finiteHalfspaceFacetArea n h i * pyramidSlope (h i) / (Module.finrank ℝ E : ℝ) := by
  let J := pyramidSideFrame (n i) (h i) hn
  let a := pyramidSideChartApex (n i) (h i)
  let C := WithLp.toLp 2 '' radialCone (finiteHalfspaceFacetChart n h i) (pyramidSlope (h i))
  have hF := finite_halfspace_facet_chart_compact n h i hn hc
  have hz : volume ({a} : Set (ℝ ∙ pyramidSideNormal (n i) (h i))ᗮ) = 0 := by
    calc
      volume {a} = volume (J '' {J.symm a}) := by simp
      _ = volume {J.symm a} := IntrinsicLinearImageReuse.isometry_volume_image J _
      _ = 0 := by simp
  have hu : volume ((fun y => a + y) '' (J '' C) ∪ {a}) =
      volume ((fun y => a + y) '' (J '' C)) := by
    apply le_antisymm
    · simpa [hz] using measure_union_le (μ := volume) ((fun y => a + y) '' (J '' C)) {a}
    · exact measure_mono Set.subset_union_left
  have hn0 : n i ≠ 0 := by intro he; rw [he, norm_zero] at hn; norm_num at hn
  have hd : Module.finrank ℝ (ℝ ∙ n i)ᗮ + 1 = Module.finrank ℝ E := by
    have hdim := (ℝ ∙ n i).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton hn0] at hdim
    omega
  unfold finiteHalfspaceFacetArea
  rw [pyramid_side_facet_chart n h i hn hh hc]
  change (volume ((fun y => a + y) '' (J '' C) ∪ {a})).toReal = _
  rw [hu, IntrinsicLinearImageReuse.translation_volume_image,
    IntrinsicLinearImageReuse.isometry_volume_image]
  change (volume (WithLp.toLp 2 '' radialCone (finiteHalfspaceFacetChart n h i)
    (pyramidSlope (h i)))).toReal = _
  rw [radial_cone_lp_volume hF (pyramidSlope_pos _)]
  have hdR : (Module.finrank ℝ (ℝ ∙ n i)ᗮ : ℝ) + 1 = (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast hd
  rw [hdR]
  ring

end Volume
end Entry005
