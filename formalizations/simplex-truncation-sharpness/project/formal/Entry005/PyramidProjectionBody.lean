import Entry005.PyramidSideArea

noncomputable section
open MeasureTheory Module
open scoped RealInnerProductSpace Pointwise
namespace Entry005

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

def pyramidProjectionGenerator (n : ι → E) (h : ι → ℝ) : Option ι → WithLp 2 (E × ℝ)
  | none => ((volume (finiteHalfspaceSet n h)).toReal / 2) • pyramidBaseNormal
  | some i => (finiteHalfspaceFacetArea n h i / (2 * Module.finrank ℝ E : ℝ)) •
      WithLp.toLp 2 (n i, h i)

omit [Fintype ι] in
theorem pyramid_projection_generator_eq (n : ι → E) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hh : ∀ i, 0 < h i) (hc : IsCompact (finiteHalfspaceSet n h))
    (i : Option ι) :
    (finiteHalfspaceFacetArea (pyramidHalfspaceNormal n h) (pyramidHalfspaceHeight h) i / 2) •
      pyramidHalfspaceNormal n h i = pyramidProjectionGenerator n h i := by
  cases i with
  | none => rw [pyramid_base_facet_area]; rfl
  | some i =>
    rw [pyramid_side_facet_area n h i (hn i) hh hc]
    change (finiteHalfspaceFacetArea n h i * pyramidSlope (h i) / (Module.finrank ℝ E : ℝ) / 2) •
      ((pyramidSlope (h i))⁻¹ • WithLp.toLp 2 (n i, h i)) = _
    rw [smul_smul]
    congr 1
    field_simp [(pyramidSlope_pos (h i)).ne']

/-- Actual projection body of the canonical pyramid, derived from its actual
finite-halfspace facets and intrinsic areas. No Cauchy identity is assumed. -/
theorem pyramid_projection_body_eq_zonotope (n : ι → E) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hh : ∀ i, 0 < h i) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n h)) :
    projectionBodySet (pyramidSet (finiteHalfspaceSet n h)) =
      finiteZonotope (pyramidProjectionGenerator n h) := by
  have hp := pyramidSet_compact hc (finite_halfspace_convex n h)
  rw [pyramidSet_finite_halfspace n h hh hc] at hp ⊢
  rw [finite_halfspace_projection_body_eq_zonotope _ _
    (pyramidHalfspaceNormal_unit n h hn) (pyramidHalfspaceNormal_injective n h hn hinj) hp]
  congr 1
  funext i
  exact pyramid_projection_generator_eq n h hn hh hc i

omit [Fintype ι] [Nontrivial E] in
theorem pyramid_finite_halfspace_volume (n : ι → E) (h : ι → ℝ)
    (hc : IsCompact (finiteHalfspaceSet n h)) :
    (volume (pyramidSet (finiteHalfspaceSet n h))).toReal =
      (volume (finiteHalfspaceSet n h)).toReal / (Module.finrank ℝ E + 1 : ℝ) :=
  pyramidSet_volume hc (finite_halfspace_convex n h)

omit [Fintype ι] [Nontrivial E] in
theorem finite_halfspace_facet_area_of_empty (n : ι → E) (h : ι → ℝ) (i : ι)
    (hn : ‖n i‖ = 1) (he : finiteHalfspaceFacet n h i = ∅) :
    finiteHalfspaceFacetArea n h i = 0 := by
  unfold finiteHalfspaceFacetArea
  rw [← finite_halfspace_facet_chart_projection_image n h i hn, he, Set.image_empty]
  simp

omit [Fintype ι] in
theorem pyramid_side_facet_area_of_empty (n : ι → E) (h : ι → ℝ) (i : ι)
    (hn : ‖n i‖ = 1) (hh : ∀ i, 0 < h i) (hc : IsCompact (finiteHalfspaceSet n h))
    (he : finiteHalfspaceFacet n h i = ∅) :
    finiteHalfspaceFacetArea (pyramidHalfspaceNormal n h) (pyramidHalfspaceHeight h) (some i) = 0 := by
  rw [pyramid_side_facet_area n h i hn hh hc, finite_halfspace_facet_area_of_empty n h i hn he]
  simp

end Entry005
