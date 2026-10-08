import Entry005.FiniteHalfspaceCauchy
import Entry005.RadialConeVolume

noncomputable section
open Metric MeasureTheory Module Function
open scoped BigOperators RealInnerProductSpace

namespace Entry005

section ActualRadialCones

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An actual cone from the origin to one actual finite-halfspace facet. -/
def finiteHalfspaceFacetCone (n : ι → E) (h : ι → ℝ) (i : ι) : Set E :=
  {x | ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ q ∈ finiteHalfspaceFacet n h i, x = t • q}

theorem finite_halfspace_facet_cone_compact (n : ι → E) (h : ι → ℝ) (i : ι)
    (hc : IsCompact (finiteHalfspaceSet n h)) : IsCompact (finiteHalfspaceFacetCone n h i) := by
  have heq : finiteHalfspaceFacetCone n h i =
      (fun p : ℝ × E => p.1 • p.2) '' (Set.Icc (0 : ℝ) 1 ×ˢ finiteHalfspaceFacet n h i) := by
    ext x
    constructor
    · rintro ⟨t, ht, q, hq, rfl⟩
      exact ⟨(t, q), ⟨ht, hq⟩, rfl⟩
    · rintro ⟨⟨t, q⟩, ⟨ht, hq⟩, rfl⟩
      exact ⟨t, ht, q, hq, rfl⟩
  rw [heq]
  exact (isCompact_Icc.prod (finite_halfspace_facet_compact n h i hc)).image
    (continuous_fst.smul continuous_snd)

theorem finite_halfspace_facet_cone_subset (n : ι → E) (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i)
    (i : ι) : finiteHalfspaceFacetCone n h i ⊆ finiteHalfspaceSet n h := by
  rintro x ⟨t, ht, q, hq, rfl⟩ j
  rw [inner_smul_right]
  have hfirst := mul_le_mul_of_nonneg_left (hq.1 j) ht.1
  have hsecond := mul_le_mul_of_nonneg_right ht.2 (hh j)
  simpa only [one_mul] using hfirst.trans hsecond

end ActualRadialCones

section RadialCoverage

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Every nonzero point of the actual body lies in a cone over an actual
facet. The endpoint is constructed by maximization on the actual radial line. -/
theorem finite_halfspace_nonzero_radial_cover (n : ι → E) (h : ι → ℝ)
    (hc : IsCompact (finiteHalfspaceSet n h)) (x : E) (hx : x ∈ finiteHalfspaceSet n h)
    (hx0 : x ≠ 0) : ∃ i, x ∈ finiteHalfspaceFacetCone n h i := by
  let F : Set E := finiteHalfspaceSet n h ∩ (ℝ ∙ x)
  have hFc : IsCompact F := hc.inter_right (Submodule.closed_of_finiteDimensional (ℝ ∙ x))
  have hFne : F.Nonempty := ⟨x, hx, Submodule.mem_span_singleton_self x⟩
  obtain ⟨q, hq, hmax⟩ := hFc.exists_isMaxOn hFne
    (show Continuous (fun z : E => inner ℝ x z) from continuous_const.inner continuous_id).continuousOn
  obtain ⟨t, htq⟩ := Submodule.mem_span_singleton.mp hq.2
  have hxx : 0 < inner ℝ x x := by
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hx0)
  have ht : 1 ≤ t := by
    have hm := hmax (show x ∈ F from ⟨hx, Submodule.mem_span_singleton_self x⟩)
    change inner ℝ x x ≤ inner ℝ x q at hm
    rw [← htq, inner_smul_right] at hm
    nlinarith
  have hstop : ∀ s : ℝ, 0 < s → q + s • x ∉ finiteHalfspaceSet n h := by
    intro s hs hnew
    have hnewF : q + s • x ∈ F := ⟨hnew, (ℝ ∙ x).add_mem hq.2
      ((ℝ ∙ x).smul_mem s (Submodule.mem_span_singleton_self x))⟩
    have hm := hmax hnewF
    change inner ℝ x (q + s • x) ≤ inner ℝ x q at hm
    rw [inner_add_right, inner_smul_right] at hm
    nlinarith
  obtain ⟨i, _, hqi⟩ := finite_halfspace_upper_active n h q x hq.1 hstop
  refine ⟨i, t⁻¹, ⟨inv_nonneg.mpr (by linarith), inv_le_one₀ (by linarith) |>.mpr ht⟩,
    q, hqi, ?_⟩
  rw [← htq, smul_smul, inv_mul_cancel₀ (by linarith : t ≠ 0), one_smul]

omit [FiniteDimensional ℝ E] in
theorem finite_halfspace_radial_cover_ae (n : ι → E) (h : ι → ℝ)
    (hc : IsCompact (finiteHalfspaceSet n h)) :
    finiteHalfspaceSet n h \ {0} ⊆ ⋃ i, finiteHalfspaceFacetCone n h i := by
  rintro x ⟨hx, hx0⟩
  obtain ⟨i, hxi⟩ := finite_halfspace_nonzero_radial_cover n h hc x hx
    (by simpa only [Set.mem_singleton_iff] using hx0)
  exact Set.mem_iUnion.mpr ⟨i, hxi⟩

end RadialCoverage

section ConeCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem unit_normal_coordinates_orthogonal (u : E) (hu : ‖u‖ = 1) (z : (ℝ ∙ u)ᗮ) :
    unitNormalCoordinates u hu (z : E) = (z, 0) := by
  simp [unitNormalCoordinates, unitNormalLpCoordinates]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem unit_normal_coordinates_affine (u : E) (hu : ‖u‖ = 1) (h : ℝ) (z : (ℝ ∙ u)ᗮ) :
    unitNormalCoordinates u hu (h • u + (z : E)) = (z, h) := by
  rw [map_add, map_smul, unit_normal_coordinates_self, unit_normal_coordinates_orthogonal]
  simp

omit [MeasurableSpace E] [BorelSpace E] in
theorem unit_normal_hyperplane_finrank_add_one (u : E) (hu : ‖u‖ = 1) :
    finrank ℝ (ℝ ∙ u)ᗮ + 1 = finrank ℝ E := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hdim := (ℝ ∙ u).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hu0] at hdim
  omega

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem finite_halfspace_facet_cone_coordinates {ι : Type*} (n : ι → E) (h : ι → ℝ) (i : ι)
    (hn : ‖n i‖ = 1) :
    unitNormalCoordinates (n i) hn '' finiteHalfspaceFacetCone n h i =
      radialCone (finiteHalfspaceFacetChart n h i) (h i) := by
  ext p
  constructor
  · rintro ⟨x, ⟨t, ht, q, hq, hx⟩, hxp⟩
    have hqimage : q ∈ (fun z : (ℝ ∙ n i)ᗮ => h i • n i + (z : E)) ''
        finiteHalfspaceFacetChart n h i := by
      rw [finite_halfspace_facet_chart_image n h i hn]
      exact hq
    obtain ⟨z, hz, hqz⟩ := hqimage
    refine ⟨t, ht, z, hz, ?_⟩
    rw [← hxp, hx, ← hqz, map_smul, unit_normal_coordinates_affine]
    rfl
  · rintro ⟨t, ht, z, hz, hp⟩
    have hq : h i • n i + (z : E) ∈ finiteHalfspaceFacet n h i := by
      rw [← finite_halfspace_facet_chart_image n h i hn]
      exact Set.mem_image_of_mem _ hz
    refine ⟨t • (h i • n i + (z : E)), ⟨t, ht, _, hq, rfl⟩, ?_⟩
    rw [hp, map_smul, unit_normal_coordinates_affine]
    rfl

theorem finite_halfspace_facet_cone_volume {ι : Type*} (n : ι → E) (h : ι → ℝ) (i : ι)
    (hn : ‖n i‖ = 1) (hh : 0 < h i) (hc : IsCompact (finiteHalfspaceSet n h)) :
    (volume (finiteHalfspaceFacetCone n h i)).toReal =
      h i / (finrank ℝ E : ℝ) * finiteHalfspaceFacetArea n h i := by
  rw [unit_normal_coordinates_volume (n i) hn (finite_halfspace_facet_cone_compact n h i hc),
    finite_halfspace_facet_cone_coordinates n h i hn,
    radial_cone_product_volume (finite_halfspace_facet_chart_compact n h i hn hc) hh]
  have hdim : (finrank ℝ (ℝ ∙ n i)ᗮ : ℝ) + 1 = (finrank ℝ E : ℝ) := by
    exact_mod_cast unit_normal_hyperplane_finrank_add_one (n i) hn
  rw [hdim]
  rfl

end ConeCoordinates

section RadialNullOverlap

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Actual cones from the origin to distinct supporting facets are almost
disjoint. Positive support heights make their radial endpoints agree. -/
theorem finite_halfspace_facet_cones_inter_volume_zero (n : ι → E) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hh : ∀ i, 0 < h i)
    (i j : ι) (hij : n i ≠ n j) :
    volume (finiteHalfspaceFacetCone n h i ∩ finiteHalfspaceFacetCone n h j) = 0 := by
  let r : E := h j • n i - h i • n j
  have hrne : r ≠ 0 := by
    intro hr
    have hmul : h j • n i = h i • n j := sub_eq_zero.mp hr
    have hnorm := congrArg norm hmul
    simp only [norm_smul, Real.norm_eq_abs, hn i, hn j, abs_of_pos (hh i),
      abs_of_pos (hh j), mul_one] at hnorm
    apply hij
    apply smul_right_injective E (ne_of_gt (hh i))
    simpa only [hnorm] using hmul
  have hsub : finiteHalfspaceFacetCone n h i ∩ finiteHalfspaceFacetCone n h j ⊆
      {x : E | inner ℝ r x = 0} := by
    rintro x ⟨⟨t, ht, q, hq, hxt⟩, ⟨s, hs, z, hz, hxs⟩⟩
    have hti : t * h i ≤ s * h i := by
      calc
        t * h i = inner ℝ (n i) x := by rw [hxt, inner_smul_right, hq.2]
        _ = s * inner ℝ (n i) z := by rw [hxs, inner_smul_right]
        _ ≤ s * h i := mul_le_mul_of_nonneg_left (hz.1 i) hs.1
    have htj : s * h j ≤ t * h j := by
      calc
        s * h j = inner ℝ (n j) x := by rw [hxs, inner_smul_right, hz.2]
        _ = t * inner ℝ (n j) q := by rw [hxt, inner_smul_right]
        _ ≤ t * h j := mul_le_mul_of_nonneg_left (hq.1 j) ht.1
    have hts : t = s := by nlinarith [hh i, hh j]
    have hxi : inner ℝ (n i) x = t * h i := by rw [hxt, inner_smul_right, hq.2]
    have hxj : inner ℝ (n j) x = s * h j := by rw [hxs, inner_smul_right, hz.2]
    change inner ℝ r x = 0
    dsimp [r]
    rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, hxi, hxj, hts]
    ring
  exact measure_mono_null hsub (inner_level_volume_zero r hrne 0)

end RadialNullOverlap

section RadialVolumePartition

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- The actual body-volume is the sum of its actual radial facet-cone
volumes. Coverage omits only the origin, which has zero ambient volume. -/
theorem finite_halfspace_volume_eq_sum_cone_volumes (n : ι → E) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hh : ∀ i, 0 < h i) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n h)) :
    (volume (finiteHalfspaceSet n h)).toReal =
      ∑ i, (volume (finiteHalfspaceFacetCone n h i)).toReal := by
  classical
  let U : Set E := ⋃ i, finiteHalfspaceFacetCone n h i
  have hUP : U ⊆ finiteHalfspaceSet n h := by
    intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    exact finite_halfspace_facet_cone_subset n h (fun i => (hh i).le) i hxi
  have hPU : finiteHalfspaceSet n h ⊆ U ∪ {0} := by
    intro x hx
    by_cases hx0 : x = 0
    · exact Or.inr hx0
    · exact Or.inl (finite_halfspace_radial_cover_ae n h hc
        ⟨hx, by simpa only [Set.mem_singleton_iff] using hx0⟩)
  have hvol : volume (finiteHalfspaceSet n h) = volume U := by
    apply le_antisymm
    · calc
        volume (finiteHalfspaceSet n h) ≤ volume (U ∪ {0}) := measure_mono hPU
        _ ≤ volume U + volume ({0} : Set E) := measure_union_le U {0}
        _ = volume U := by simp
    · exact measure_mono hUP
  have hcones : ∀ i, IsCompact (finiteHalfspaceFacetCone n h i) :=
    fun i => finite_halfspace_facet_cone_compact n h i hc
  have hdisj : Pairwise (AEDisjoint volume on fun i => finiteHalfspaceFacetCone n h i) := by
    intro i j hij
    exact finite_halfspace_facet_cones_inter_volume_zero n h hn hh i j (hinj.ne hij)
  have hsum : volume U = ∑ i, volume (finiteHalfspaceFacetCone n h i) := by
    dsimp [U]
    rw [measure_iUnion₀ hdisj (fun i => (hcones i).measurableSet.nullMeasurableSet), tsum_fintype]
  rw [hvol, hsum, ENNReal.toReal_sum (fun i _ => (hcones i).measure_ne_top)]

/-- The actual geometric normalization identity: height times intrinsic
facet area sums to dimension times actual body-volume. -/
theorem finite_halfspace_facet_mass (n : ι → E) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hh : ∀ i, 0 < h i) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n h)) :
    ∑ i, finiteHalfspaceFacetArea n h i * h i =
      (finrank ℝ E : ℝ) * (volume (finiteHalfspaceSet n h)).toReal := by
  classical
  obtain ⟨z, hz⟩ := exists_ne (0 : E)
  have hdim : 1 ≤ finrank ℝ E := by
    have hspan : finrank ℝ (ℝ ∙ z) = 1 := finrank_span_singleton hz
    calc
      1 = finrank ℝ (ℝ ∙ z) := hspan.symm
      _ ≤ finrank ℝ E := Submodule.finrank_le _
  have hdne : (finrank ℝ E : ℝ) ≠ 0 := by exact_mod_cast (by omega : finrank ℝ E ≠ 0)
  rw [finite_halfspace_volume_eq_sum_cone_volumes n h hn hh hinj hc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [finite_halfspace_facet_cone_volume n h i (hn i) (hh i) hc]
  field_simp [hdne]

end RadialVolumePartition

section BodyVolumePositivity

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem finite_halfspace_interior_nonempty_of_positive_heights (n : ι → E) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hh : ∀ i, 0 < h i) :
    (interior (finiteHalfspaceSet n h)).Nonempty := by
  obtain ⟨ε, hε, hbound⟩ := finite_uniform_positive h hh
  have hb : ball (0 : E) ε ⊆ finiteHalfspaceSet n h := by
    intro x hx i
    have hnorm : ‖x‖ < ε := by simpa only [mem_ball, dist_zero_right] using hx
    calc
      inner ℝ (n i) x ≤ ‖n i‖ * ‖x‖ := real_inner_le_norm _ _
      _ = ‖x‖ := by rw [hn i, one_mul]
      _ ≤ h i := hnorm.le.trans (hbound i)
  exact ⟨0, (interior_mono hb) (by rw [isOpen_ball.interior_eq]; simpa using hε)⟩

theorem finite_halfspace_volume_pos (n : ι → E) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hh : ∀ i, 0 < h i)
    (hc : IsCompact (finiteHalfspaceSet n h)) :
    0 < (volume (finiteHalfspaceSet n h)).toReal := by
  exact ENNReal.toReal_pos
    (Measure.measure_pos_of_nonempty_interior volume
      (finite_halfspace_interior_nonempty_of_positive_heights n h hn hh)).ne'
    hc.measure_ne_top

variable [Nontrivial E]

theorem finite_halfspace_normalization_pos (n : ι → E) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hh : ∀ i, 0 < h i)
    (hc : IsCompact (finiteHalfspaceSet n h)) :
    0 < (finrank ℝ E : ℝ) * (volume (finiteHalfspaceSet n h)).toReal := by
  apply mul_pos
  · exact_mod_cast (finrank_pos_iff.mpr inferInstance : 0 < finrank ℝ E)
  · exact finite_halfspace_volume_pos n h hn hh hc

end BodyVolumePositivity
end Entry005
