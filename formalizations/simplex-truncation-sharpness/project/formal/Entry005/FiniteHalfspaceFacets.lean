import Entry005.HyperplaneProjectionJacobian
import Mathlib.Topology.Order.Compact

noncomputable section
open Metric MeasureTheory Module
open scoped BigOperators RealInnerProductSpace

namespace Entry005

section Halfspaces

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def finiteHalfspaceSet (n : ι → E) (h : ι → ℝ) : Set E :=
  {x | ∀ i, inner ℝ (n i) x ≤ h i}

def finiteHalfspaceFacet (n : ι → E) (h : ι → ℝ) (i : ι) : Set E :=
  finiteHalfspaceSet n h ∩ {x | inner ℝ (n i) x = h i}

theorem finite_uniform_positive (q : ι → ℝ) (hq : ∀ i, 0 < q i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ q i := by
  classical
  have hfin : ∀ s : Finset ι, ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ s, ε ≤ q i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨ε, hε, hsmall⟩ := ih
      refine ⟨min ε (q i), lt_min hε (hq i), ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hsmall j hj)
  obtain ⟨ε, hε, hsmall⟩ := hfin Finset.univ
  exact ⟨ε, hε, fun i => hsmall i (Finset.mem_univ i)⟩

/-- A point that cannot move positively along `u` has an actual active facet
whose normal has positive component along `u`. Finiteness proves the common
small displacement; no supporting-facet existence assumption is supplied. -/
theorem finite_halfspace_upper_active (n : ι → E) (h : ι → ℝ) (q u : E)
    (hq : q ∈ finiteHalfspaceSet n h)
    (hstop : ∀ t : ℝ, 0 < t → q + t • u ∉ finiteHalfspaceSet n h) :
    ∃ i, 0 < inner ℝ (n i) u ∧ q ∈ finiteHalfspaceFacet n h i := by
  classical
  by_contra hnot
  have hslack : ∀ i, 0 < inner ℝ (n i) u → inner ℝ (n i) q < h i := by
    intro i hi
    have hneq : inner ℝ (n i) q ≠ h i := by
      intro heq
      exact hnot ⟨i, hi, hq, heq⟩
    exact lt_of_le_of_ne (hq i) hneq
  let bound : ι → ℝ := fun i =>
    if 0 < inner ℝ (n i) u then (h i - inner ℝ (n i) q) / inner ℝ (n i) u else 1
  have hb : ∀ i, 0 < bound i := by
    intro i
    dsimp [bound]
    split_ifs with hi
    · exact div_pos (sub_pos.mpr (hslack i hi)) hi
    · norm_num
  obtain ⟨ε, hε, hsmall⟩ := finite_uniform_positive bound hb
  apply hstop ε hε
  intro i
  rw [inner_add_right, inner_smul_right]
  by_cases hi : 0 < inner ℝ (n i) u
  · have hb' := hsmall i
    dsimp [bound] at hb'
    rw [ite_eq_left hi] at hb'
    have hm := (le_div_iff₀ hi).mp hb'
    nlinarith
  · have hm : ε * inner ℝ (n i) u ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hε.le (le_of_not_gt hi)
    linarith [hq i]

end Halfspaces

section Coverage

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Every actual projected point has a preimage on an upper-facing facet.
The endpoint is produced by maximizing along its compact projection fiber. -/
theorem finite_halfspace_upper_projection_cover (n : ι → E) (h : ι → ℝ)
    (hcompact : IsCompact (finiteHalfspaceSet n h)) (u : E) (hu : ‖u‖ = 1)
    (y : (ℝ ∙ u)ᗮ) (hy : y ∈ (ℝ ∙ u)ᗮ.orthogonalProjectionOnto '' finiteHalfspaceSet n h) :
    ∃ i, 0 < inner ℝ (n i) u ∧
      y ∈ (ℝ ∙ u)ᗮ.orthogonalProjectionOnto '' finiteHalfspaceFacet n h i := by
  let Q := (ℝ ∙ u)ᗮ.orthogonalProjectionOnto
  let F := finiteHalfspaceSet n h ∩ {x | Q x = y}
  have hc : IsCompact F := hcompact.inter_right
    (isClosed_eq Q.continuous continuous_const)
  have hfne : F.Nonempty := by
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨x, hx, hxy⟩
  obtain ⟨q, hq, hmax⟩ := hc.exists_isMaxOn hfne
    (show Continuous (fun x : E => inner ℝ u x) from
      continuous_const.inner continuous_id).continuousOn
  have hstop : ∀ t : ℝ, 0 < t → q + t • u ∉ finiteHalfspaceSet n h := by
    intro t ht hqt
    have hQt : Q (q + t • u) = y := by
      rw [map_add, map_smul, Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero]
      simpa using hq.2
    have hm := hmax ⟨hqt, hQt⟩
    change inner ℝ u (q + t • u) ≤ inner ℝ u q at hm
    rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hu] at hm
    norm_num at hm
    linarith
  obtain ⟨i, hi, hfacet⟩ := finite_halfspace_upper_active n h q u hq.1 hstop
  exact ⟨i, hi, q, hfacet, hq.2⟩

omit [FiniteDimensional ℝ E] in
theorem unit_normal_projection_decomposition (u x : E) (hu : ‖u‖ = 1) :
    x = ((ℝ ∙ u)ᗮ.orthogonalProjectionOnto x : E) + inner ℝ u x • u := by
  rw [orthogonal_hyperplane_projection_formula, hu]
  norm_num

omit [FiniteDimensional ℝ E] in
/-- The lower endpoint gives actual negative-facing facet coverage. -/
theorem finite_halfspace_lower_projection_cover (n : ι → E) (h : ι → ℝ)
    (hcompact : IsCompact (finiteHalfspaceSet n h)) (u : E) (hu : ‖u‖ = 1)
    (y : (ℝ ∙ u)ᗮ) (hy : y ∈ (ℝ ∙ u)ᗮ.orthogonalProjectionOnto '' finiteHalfspaceSet n h) :
    ∃ i, inner ℝ (n i) u < 0 ∧
      y ∈ (ℝ ∙ u)ᗮ.orthogonalProjectionOnto '' finiteHalfspaceFacet n h i := by
  let Q := (ℝ ∙ u)ᗮ.orthogonalProjectionOnto
  let F := finiteHalfspaceSet n h ∩ {x | Q x = y}
  have hc : IsCompact F := hcompact.inter_right
    (isClosed_eq Q.continuous continuous_const)
  have hfne : F.Nonempty := by
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨x, hx, hxy⟩
  obtain ⟨q, hq, hmax⟩ := hc.exists_isMaxOn hfne
    (show Continuous (fun x : E => inner ℝ (-u) x) from
      continuous_const.inner continuous_id).continuousOn
  have hstop : ∀ t : ℝ, 0 < t → q + t • (-u) ∉ finiteHalfspaceSet n h := by
    intro t ht hqt
    have hQt : Q (q + t • (-u)) = y := by
      rw [map_add, map_smul, map_neg,
        Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero]
      simpa using hq.2
    have hm := hmax ⟨hqt, hQt⟩
    change inner ℝ (-u) (q + t • (-u)) ≤ inner ℝ (-u) q at hm
    rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, norm_neg, hu] at hm
    norm_num at hm
    linarith
  obtain ⟨i, hi, hfacet⟩ := finite_halfspace_upper_active n h q (-u) hq.1 hstop
  rw [inner_neg_right] at hi
  exact ⟨i, by linarith, q, hfacet, hq.2⟩

/-- Actual facet coordinates in its supporting hyperplane; their volume is
the intrinsic facet area. -/
def finiteHalfspaceFacetChart (n : ι → E) (h : ι → ℝ) (i : ι) : Set (ℝ ∙ n i)ᗮ :=
  {z | h i • n i + (z : E) ∈ finiteHalfspaceSet n h}

omit [Fintype ι] [FiniteDimensional ℝ E] in
theorem finite_halfspace_facet_chart_image (n : ι → E) (h : ι → ℝ) (i : ι)
    (hn : ‖n i‖ = 1) :
    (fun z : (ℝ ∙ n i)ᗮ => h i • n i + (z : E)) '' finiteHalfspaceFacetChart n h i =
      finiteHalfspaceFacet n h i := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨hz, ?_⟩
    change inner ℝ (n i) (h i • n i + (z : E)) = h i
    rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hn,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp z.2]
    norm_num
  · rintro ⟨hx, hxeq⟩
    refine ⟨(ℝ ∙ n i)ᗮ.orthogonalProjectionOnto x, ?_, ?_⟩
    · change h i • n i + ((ℝ ∙ n i)ᗮ.orthogonalProjectionOnto x : E) ∈ finiteHalfspaceSet n h
      have hd := unit_normal_projection_decomposition (n i) x hn
      rw [hxeq] at hd
      rw [add_comm, ← hd]
      exact hx
    · have hd := unit_normal_projection_decomposition (n i) x hn
      rw [hxeq] at hd
      simpa [add_comm] using hd.symm

omit [Fintype ι] [FiniteDimensional ℝ E] in
theorem finite_halfspace_facet_compact (n : ι → E) (h : ι → ℝ) (i : ι)
    (hc : IsCompact (finiteHalfspaceSet n h)) : IsCompact (finiteHalfspaceFacet n h i) :=
  hc.inter_right (isClosed_eq (show Continuous (fun x : E => inner ℝ (n i) x) from
    continuous_const.inner continuous_id) continuous_const)

omit [Fintype ι] [FiniteDimensional ℝ E] in
theorem same_unit_projection_sub (u x y : E) (hu : ‖u‖ = 1)
    (hp : (ℝ ∙ u)ᗮ.orthogonalProjectionOnto x = (ℝ ∙ u)ᗮ.orthogonalProjectionOnto y) :
    x - y = (inner ℝ u x - inner ℝ u y) • u := by
  have hx := unit_normal_projection_decomposition u x hu
  have hy := unit_normal_projection_decomposition u y hu
  calc
    x - y = (((ℝ ∙ u)ᗮ.orthogonalProjectionOnto x : E) + inner ℝ u x • u) -
        (((ℝ ∙ u)ᗮ.orthogonalProjectionOnto y : E) + inner ℝ u y • u) := by rw [← hx, ← hy]
    _ = (inner ℝ u x - inner ℝ u y) • u := by rw [hp]; module

omit [Fintype ι] [FiniteDimensional ℝ E] in
/-- Positive-facing active facets on a common projection fiber have the same
actual endpoint. This closes the geometric overlap argument. -/
theorem upper_facets_same_fiber_eq (n : ι → E) (h : ι → ℝ) (i j : ι)
    (u : E) (hu : ‖u‖ = 1) (hi : 0 < inner ℝ (n i) u) (hj : 0 < inner ℝ (n j) u)
    (x y : E) (hx : x ∈ finiteHalfspaceFacet n h i) (hy : y ∈ finiteHalfspaceFacet n h j)
    (hp : (ℝ ∙ u)ᗮ.orthogonalProjectionOnto x = (ℝ ∙ u)ᗮ.orthogonalProjectionOnto y) :
    x = y := by
  have hd := same_unit_projection_sub u x y hu hp
  have hineqi : 0 ≤ inner ℝ (n i) (x - y) := by
    rw [inner_sub_right, hx.2]
    exact sub_nonneg.mpr (hy.1 i)
  have hineqj : inner ℝ (n j) (x - y) ≤ 0 := by
    rw [inner_sub_right, hy.2]
    exact sub_nonpos.mpr (hx.1 j)
  rw [hd, inner_smul_right] at hineqi hineqj
  have ht : inner ℝ u x = inner ℝ u y := by nlinarith
  rw [ht, sub_self, zero_smul] at hd
  exact sub_eq_zero.mp hd

omit [Fintype ι] [FiniteDimensional ℝ E] in
theorem same_sign_facets_same_fiber_eq (n : ι → E) (h : ι → ℝ) (i j : ι)
    (u : E) (hu : ‖u‖ = 1)
    (hsign : (0 < inner ℝ (n i) u ∧ 0 < inner ℝ (n j) u) ∨
      (inner ℝ (n i) u < 0 ∧ inner ℝ (n j) u < 0))
    (x y : E) (hx : x ∈ finiteHalfspaceFacet n h i) (hy : y ∈ finiteHalfspaceFacet n h j)
    (hp : (ℝ ∙ u)ᗮ.orthogonalProjectionOnto x = (ℝ ∙ u)ᗮ.orthogonalProjectionOnto y) :
    x = y := by
  rcases hsign with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · exact upper_facets_same_fiber_eq n h i j u hu hi hj x y hx hy hp
  · have hd := same_unit_projection_sub u x y hu hp
    have hineqi : 0 ≤ inner ℝ (n i) (x - y) := by
      rw [inner_sub_right, hx.2]
      exact sub_nonneg.mpr (hy.1 i)
    have hineqj : inner ℝ (n j) (x - y) ≤ 0 := by
      rw [inner_sub_right, hy.2]
      exact sub_nonpos.mpr (hx.1 j)
    rw [hd, inner_smul_right] at hineqi hineqj
    have ht : inner ℝ u x = inner ℝ u y := by nlinarith
    rw [ht, sub_self, zero_smul] at hd
    exact sub_eq_zero.mp hd

omit [Fintype ι] [FiniteDimensional ℝ E] in
theorem finite_halfspace_facet_chart_projection_image (n : ι → E) (h : ι → ℝ) (i : ι)
    (hn : ‖n i‖ = 1) :
    (ℝ ∙ n i)ᗮ.orthogonalProjectionOnto '' finiteHalfspaceFacet n h i =
      finiteHalfspaceFacetChart n h i := by
  rw [← finite_halfspace_facet_chart_image n h i hn, ← Set.image_comp]
  have heq : (fun x : E => (ℝ ∙ n i)ᗮ.orthogonalProjectionOnto x) ∘
      (fun z : (ℝ ∙ n i)ᗮ => h i • n i + (z : E)) = id := by
    funext z
    simp only [Function.comp_apply, map_add, map_smul,
      Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero,
      smul_zero, zero_add, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self, id_eq]
  rw [heq, Set.image_id]

omit [Fintype ι] [FiniteDimensional ℝ E] in
theorem finite_halfspace_facet_chart_compact (n : ι → E) (h : ι → ℝ) (i : ι)
    (hn : ‖n i‖ = 1) (hc : IsCompact (finiteHalfspaceSet n h)) :
    IsCompact (finiteHalfspaceFacetChart n h i) := by
  rw [← finite_halfspace_facet_chart_projection_image n h i hn]
  exact (finite_halfspace_facet_compact n h i hc).image
    (ℝ ∙ n i)ᗮ.orthogonalProjectionOnto.continuous

end Coverage

section NullHyperplanes

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem inner_level_volume_zero (r : E) (hr : r ≠ 0) (c : ℝ) :
    volume {x : E | inner ℝ r x = c} = 0 := by
  classical
  let K := (innerₗ E r).ker
  have hproper : K ≠ ⊤ := by
    intro heq
    have hm : r ∈ K := by rw [heq]; trivial
    have hrr : inner ℝ r r = 0 := hm
    exact hr (inner_self_eq_zero.mp hrr)
  by_cases hn : ({x : E | inner ℝ r x = c} : Set E).Nonempty
  · obtain ⟨a, ha⟩ := hn
    have hset : {x : E | inner ℝ r x = c} = (fun z : E => a + z) '' (K : Set E) := by
      ext x
      constructor
      · intro hx
        refine ⟨x - a, ?_, by abel_nf⟩
        change inner ℝ r (x - a) = 0
        rw [inner_sub_right, hx, ha, sub_self]
      · rintro ⟨z, hz, rfl⟩
        change inner ℝ r z = 0 at hz
        change inner ℝ r (a + z) = c
        rw [inner_add_right, ha, hz, add_zero]
    rw [hset, translation_volume_image]
    exact Measure.addHaar_submodule volume K hproper
  · rw [Set.not_nonempty_iff_eq_empty.mp hn, measure_empty]

end NullHyperplanes

section NullFacetOverlap

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [Fintype ι] in
/-- Actual same-facing facet projections are almost disjoint. Distinct
unit normals suffice, including redundant halfspaces and empty facets. -/
theorem same_sign_projected_facets_inter_volume_zero (n : ι → E) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (i j : ι) (hij : n i ≠ n j)
    (u : E) (hu : ‖u‖ = 1)
    (hsign : (0 < inner ℝ (n i) u ∧ 0 < inner ℝ (n j) u) ∨
      (inner ℝ (n i) u < 0 ∧ inner ℝ (n j) u < 0)) :
    volume (((ℝ ∙ u)ᗮ.orthogonalProjectionOnto '' finiteHalfspaceFacet n h i) ∩
      ((ℝ ∙ u)ᗮ.orthogonalProjectionOnto '' finiteHalfspaceFacet n h j)) = 0 := by
  let r : E := inner ℝ (n j) u • n i - inner ℝ (n i) u • n j
  have hrorth : r ∈ (ℝ ∙ u)ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    dsimp [r]
    rw [inner_sub_left, inner_smul_left, inner_smul_left]
    simp only [starRingEnd_apply, star_trivial]
    ring
  have hrne : r ≠ 0 := by
    intro heq
    have hmul : inner ℝ (n j) u • n i = inner ℝ (n i) u • n j := sub_eq_zero.mp heq
    have hnormabs := congrArg norm hmul
    simp only [norm_smul, Real.norm_eq_abs, hn i, hn j, mul_one] at hnormabs
    have hnorm : inner ℝ (n j) u = inner ℝ (n i) u := by
      rcases hsign with ⟨hi, hj⟩ | ⟨hi, hj⟩
      · simpa only [abs_of_pos hi, abs_of_pos hj] using hnormabs
      · rw [abs_of_neg hi, abs_of_neg hj] at hnormabs
        linarith
    have hine : inner ℝ (n i) u ≠ 0 := by
      rcases hsign with ⟨hi, _⟩ | ⟨hi, _⟩
      · exact ne_of_gt hi
      · exact ne_of_lt hi
    apply hij
    apply smul_right_injective E hine
    simpa only [hnorm] using hmul
  let rH : (ℝ ∙ u)ᗮ := ⟨r, hrorth⟩
  have hrHne : rH ≠ 0 := by
    intro heq
    exact hrne (congrArg Subtype.val heq)
  let c : ℝ := inner ℝ (n j) u * h i - inner ℝ (n i) u * h j
  have hsubset :
      ((ℝ ∙ u)ᗮ.orthogonalProjectionOnto '' finiteHalfspaceFacet n h i) ∩
      ((ℝ ∙ u)ᗮ.orthogonalProjectionOnto '' finiteHalfspaceFacet n h j) ⊆
      {p : (ℝ ∙ u)ᗮ | inner ℝ rH p = c} := by
    rintro p ⟨⟨x, hx, hxp⟩, ⟨y, hy, hyp⟩⟩
    have hxy := same_sign_facets_same_fiber_eq n h i j u hu hsign x y hx hy (hxp.trans hyp.symm)
    subst y
    have hxlevel : inner ℝ r x = c := by
      dsimp [r, c]
      rw [inner_sub_left, inner_smul_left, inner_smul_left, hx.2, hy.2]
      simp only [starRingEnd_apply, star_trivial]
    have hru : inner ℝ r u = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_left.mp hrorth
    have hd := unit_normal_projection_decomposition u x hu
    rw [hxp] at hd
    calc
      inner ℝ rH p = inner ℝ r (p : E) := rfl
      _ = inner ℝ r x := by rw [hd, inner_add_right, inner_smul_right, hru]; simp
      _ = c := hxlevel
  exact measure_mono_null hsubset (inner_level_volume_zero rH hrHne c)

omit [Fintype ι] in
theorem upper_projected_facets_inter_volume_zero (n : ι → E) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (i j : ι) (hij : n i ≠ n j)
    (u : E) (hu : ‖u‖ = 1) (hi : 0 < inner ℝ (n i) u) (hj : 0 < inner ℝ (n j) u) :
    volume (((ℝ ∙ u)ᗮ.orthogonalProjectionOnto '' finiteHalfspaceFacet n h i) ∩
      ((ℝ ∙ u)ᗮ.orthogonalProjectionOnto '' finiteHalfspaceFacet n h j)) = 0 :=
  same_sign_projected_facets_inter_volume_zero n h hn i j hij u hu (Or.inl ⟨hi, hj⟩)

omit [Fintype ι] in
theorem lower_projected_facets_inter_volume_zero (n : ι → E) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (i j : ι) (hij : n i ≠ n j)
    (u : E) (hu : ‖u‖ = 1) (hi : inner ℝ (n i) u < 0) (hj : inner ℝ (n j) u < 0) :
    volume (((ℝ ∙ u)ᗮ.orthogonalProjectionOnto '' finiteHalfspaceFacet n h i) ∩
      ((ℝ ∙ u)ᗮ.orthogonalProjectionOnto '' finiteHalfspaceFacet n h j)) = 0 :=
  same_sign_projected_facets_inter_volume_zero n h hn i j hij u hu (Or.inr ⟨hi, hj⟩)

end NullFacetOverlap
end Entry005
