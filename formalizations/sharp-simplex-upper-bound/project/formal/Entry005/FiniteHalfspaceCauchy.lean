import Entry005.FiniteHalfspaceFacets
import Entry005.Targets

noncomputable section
open Metric MeasureTheory Module Function
open scoped BigOperators RealInnerProductSpace

namespace Entry005

section ScalarAreaSums

variable {ι : Type*} [Fintype ι]

theorem finite_abs_area_split (a b : ι → ℝ) :
    (∑ i, |b i| * a i) =
      (∑ i ∈ Finset.univ.filter (fun i => 0 < b i), b i * a i) +
      (∑ i ∈ Finset.univ.filter (fun i => b i < 0), (-b i) * a i) := by
  classical
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hp : 0 < b i
  · simp [hp, not_lt.mpr hp.le, abs_of_pos hp]
  · by_cases hm : b i < 0
    · simp [hp, hm, abs_of_neg hm]
    · have hz : b i = 0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hm)
      simp [hz]

theorem finite_signed_area_split (a b : ι → ℝ) :
    (∑ i, b i * a i) =
      (∑ i ∈ Finset.univ.filter (fun i => 0 < b i), b i * a i) -
      (∑ i ∈ Finset.univ.filter (fun i => b i < 0), (-b i) * a i) := by
  classical
  simp only [Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hp : 0 < b i
  · simp [hp, not_lt.mpr hp.le]
  · by_cases hm : b i < 0
    · simp [hp, hm]
    · have hz : b i = 0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hm)
      simp [hz]

end ScalarAreaSums

section FiniteCauchy

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def finiteHalfspaceFacetArea (n : ι → E) (h : ι → ℝ) (i : ι) : ℝ :=
  (volume (finiteHalfspaceFacetChart n h i)).toReal

omit [Fintype ι] in
theorem finite_halfspace_facet_projection_volume (n : ι → E) (h : ι → ℝ) (i : ι)
    (hn : ‖n i‖ = 1) (u : E) (hu : ‖u‖ = 1) :
    volume ((ℝ ∙ u)ᗮ.orthogonalProjectionOnto '' finiteHalfspaceFacet n h i) =
      ENNReal.ofReal |inner ℝ (n i) u| * volume (finiteHalfspaceFacetChart n h i) := by
  rw [← finite_halfspace_facet_chart_image n h i hn,
    affine_hyperplane_projection_volume (n i) u hn hu]
  rw [real_inner_comm u (n i)]

omit [Fintype ι] in
theorem finite_halfspace_facet_projection_volume_real (n : ι → E) (h : ι → ℝ) (i : ι)
    (hn : ‖n i‖ = 1) (u : E) (hu : ‖u‖ = 1) :
    (volume ((ℝ ∙ u)ᗮ.orthogonalProjectionOnto '' finiteHalfspaceFacet n h i)).toReal =
      |inner ℝ (n i) u| * finiteHalfspaceFacetArea n h i := by
  rw [finite_halfspace_facet_projection_volume n h i hn u hu,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
  rfl

/-- Upper-facing projected facets exactly cover the actual projected body,
and their intrinsic projected volumes add because overlaps have measure zero. -/
theorem finite_halfspace_upper_area_sum (n : ι → E) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n h)) (u : E) (hu : ‖u‖ = 1) :
    projectionVolumeSet (finiteHalfspaceSet n h) u =
      ∑ i ∈ Finset.univ.filter (fun i => 0 < inner ℝ (n i) u),
        inner ℝ (n i) u * finiteHalfspaceFacetArea n h i := by
  classical
  let Q := (ℝ ∙ u)ᗮ.orthogonalProjectionOnto
  let s := Finset.univ.filter (fun i => 0 < inner ℝ (n i) u)
  let F : ι → Set (ℝ ∙ u)ᗮ := fun i => Q '' finiteHalfspaceFacet n h i
  have hcover : Q '' finiteHalfspaceSet n h = ⋃ i ∈ s, F i := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, hi, hyi⟩ := finite_halfspace_upper_projection_cover n h hc u hu y hy
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ i, hi⟩, hyi⟩⟩
    · intro hy
      obtain ⟨i, _, x, hx, hxy⟩ := Set.mem_iUnion.mp hy |>.imp fun i => Set.mem_iUnion.mp
      exact ⟨x, hx.1, hxy⟩
  have hFcompact : ∀ i, IsCompact (F i) := fun i =>
    (finite_halfspace_facet_compact n h i hc).image Q.continuous
  have hdisj : Set.Pairwise (s : Set ι) (AEDisjoint volume on F) := by
    intro i hi j hj hij
    exact upper_projected_facets_inter_volume_zero n h hn i j (hinj.ne hij) u hu
      (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  have hsum := measureReal_biUnion_finset₀ hdisj
    (fun i _ => (hFcompact i).measurableSet.nullMeasurableSet)
    (fun i _ => (hFcompact i).measure_ne_top)
  change (volume (Q '' finiteHalfspaceSet n h)).toReal = _
  rw [hcover]
  change volume.real (⋃ i ∈ s, F i) = _
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i hi
  change (volume (Q '' finiteHalfspaceFacet n h i)).toReal = _
  rw [finite_halfspace_facet_projection_volume_real n h i (hn i) u hu,
    abs_of_pos (Finset.mem_filter.mp hi).2]

theorem finite_halfspace_lower_area_sum (n : ι → E) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n h)) (u : E) (hu : ‖u‖ = 1) :
    projectionVolumeSet (finiteHalfspaceSet n h) u =
      ∑ i ∈ Finset.univ.filter (fun i => inner ℝ (n i) u < 0),
        (-inner ℝ (n i) u) * finiteHalfspaceFacetArea n h i := by
  classical
  let Q := (ℝ ∙ u)ᗮ.orthogonalProjectionOnto
  let s := Finset.univ.filter (fun i => inner ℝ (n i) u < 0)
  let F : ι → Set (ℝ ∙ u)ᗮ := fun i => Q '' finiteHalfspaceFacet n h i
  have hcover : Q '' finiteHalfspaceSet n h = ⋃ i ∈ s, F i := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, hi, hyi⟩ := finite_halfspace_lower_projection_cover n h hc u hu y hy
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ i, hi⟩, hyi⟩⟩
    · intro hy
      obtain ⟨i, _, x, hx, hxy⟩ := Set.mem_iUnion.mp hy |>.imp fun i => Set.mem_iUnion.mp
      exact ⟨x, hx.1, hxy⟩
  have hFcompact : ∀ i, IsCompact (F i) := fun i =>
    (finite_halfspace_facet_compact n h i hc).image Q.continuous
  have hdisj : Set.Pairwise (s : Set ι) (AEDisjoint volume on F) := by
    intro i hi j hj hij
    exact lower_projected_facets_inter_volume_zero n h hn i j (hinj.ne hij) u hu
      (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  have hsum := measureReal_biUnion_finset₀ hdisj
    (fun i _ => (hFcompact i).measurableSet.nullMeasurableSet)
    (fun i _ => (hFcompact i).measure_ne_top)
  change (volume (Q '' finiteHalfspaceSet n h)).toReal = _
  rw [hcover]
  change volume.real (⋃ i ∈ s, F i) = _
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i hi
  change (volume (Q '' finiteHalfspaceFacet n h i)).toReal = _
  rw [finite_halfspace_facet_projection_volume_real n h i (hn i) u hu,
    abs_of_neg (Finset.mem_filter.mp hi).2]

/-- Cauchy's projection formula for the actual compact finite halfspace body,
with actual intrinsic facet areas. No surface or Cauchy identity is a premise. -/
theorem finite_halfspace_cauchy (n : ι → E) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n h)) (u : E) (hu : ‖u‖ = 1) :
    projectionVolumeSet (finiteHalfspaceSet n h) u =
      (1 / 2 : ℝ) * ∑ i, |inner ℝ (n i) u| * finiteHalfspaceFacetArea n h i := by
  have hs := finite_abs_area_split (finiteHalfspaceFacetArea n h) (fun i => inner ℝ (n i) u)
  rw [← finite_halfspace_upper_area_sum n h hn hinj hc u hu,
    ← finite_halfspace_lower_area_sum n h hn hinj hc u hu] at hs
  linarith

theorem finite_halfspace_directional_balance (n : ι → E) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n h)) (u : E) (hu : ‖u‖ = 1) :
    ∑ i, inner ℝ (n i) u * finiteHalfspaceFacetArea n h i = 0 := by
  have hs := finite_signed_area_split (finiteHalfspaceFacetArea n h) (fun i => inner ℝ (n i) u)
  rw [← finite_halfspace_upper_area_sum n h hn hinj hc u hu,
    ← finite_halfspace_lower_area_sum n h hn hinj hc u hu] at hs
  exact hs.trans (sub_self _)

/-- The intrinsic areas of the actual facets have balanced normals. This is
derived from the two actual fiber partitions, without a divergence theorem. -/
theorem finite_halfspace_normal_balance (n : ι → E) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n h)) :
    ∑ i, finiteHalfspaceFacetArea n h i • n i = 0 := by
  classical
  let z : E := ∑ i, finiteHalfspaceFacetArea n h i • n i
  change z = 0
  by_contra hz
  have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let u : E := ‖z‖⁻¹ • z
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnz),
      inv_mul_cancel₀ (ne_of_gt hnz)]
  have hs := finite_halfspace_directional_balance n h hn hinj hc u hu
  have hzu0 : inner ℝ z u = 0 := by
    change inner ℝ (∑ i, finiteHalfspaceFacetArea n h i • n i) u = 0
    rw [sum_inner]
    simpa only [real_inner_smul_left, mul_comm] using hs
  have hzu : inner ℝ z u = ‖z‖ := by
    dsimp [u]
    rw [inner_smul_right, real_inner_self_eq_norm_sq, pow_two, ← mul_assoc,
      inv_mul_cancel₀ (ne_of_gt hnz), one_mul]
  rw [hzu] at hzu0
  linarith

omit [Fintype ι] in
theorem finite_halfspace_facet_area_nonneg (n : ι → E) (h : ι → ℝ) (i : ι) :
    0 ≤ finiteHalfspaceFacetArea n h i := ENNReal.toReal_nonneg

/-- The actual projection body of the finite halfspace body is the actual
zonotope generated by half of each intrinsic facet area times its unit normal. -/
theorem finite_halfspace_projection_body_eq_zonotope (n : ι → E) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n h)) :
    projectionBodySet (finiteHalfspaceSet n h) =
      finiteZonotope (fun i => (finiteHalfspaceFacetArea n h i / 2) • n i) := by
  apply projection_body_eq_finite_zonotope_of_projection_volume
  intro u hu
  rw [finite_halfspace_cauchy n h hn hinj hc u hu, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_smul_right, abs_mul,
    abs_of_nonneg (div_nonneg (finite_halfspace_facet_area_nonneg n h i) (by norm_num)),
    real_inner_comm u (n i)]
  ring

end FiniteCauchy
end Entry005
