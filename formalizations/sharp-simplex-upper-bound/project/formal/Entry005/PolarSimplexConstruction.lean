import Entry005.ActualBodyPolarBoundary
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.InnerProductSpace.Dual

noncomputable section
open Metric MeasureTheory Module
open scoped BigOperators RealInnerProductSpace

namespace Entry005

/-- The affine basis consists of exactly the supplied witness points. -/
def polarWitnessBasis {d : ℕ} (w : Fin (d + 1) → Space d)
    (ha : AffineIndependent ℝ w) : AffineBasis (Fin (d + 1)) ℝ (Space d) :=
  ⟨w, ha, (ha.affineSpan_eq_top_iff_card_eq_finrank_add_one).mpr (by simp [Space])⟩

def polarWitnessWeight {d : ℕ} (w : Fin (d + 1) → Space d)
    (ha : AffineIndependent ℝ w) (i : Fin (d + 1)) : ℝ :=
  (polarWitnessBasis w ha).coord i 0

def polarWitnessGradient {d : ℕ} (w : Fin (d + 1) → Space d)
    (ha : AffineIndependent ℝ w) (i : Fin (d + 1)) : Space d :=
  (InnerProductSpace.toDual ℝ (Space d)).symm
    (LinearMap.toContinuousLinearMap ((polarWitnessBasis w ha).coord i).linear)

def polarWitnessVertex {d : ℕ} (w : Fin (d + 1) → Space d)
    (ha : AffineIndependent ℝ w) (i : Fin (d + 1)) : Space d :=
  -(polarWitnessWeight w ha i)⁻¹ • polarWitnessGradient w ha i

theorem polar_witness_weight_pos {d : ℕ} (w : Fin (d + 1) → Space d)
    (ha : AffineIndependent ℝ w) {b : ℝ} (hb : 0 < b)
    (hball : closedBall (0 : Space d) b ⊆ convexHull ℝ (Set.range w))
    (i : Fin (d + 1)) : 0 < polarWitnessWeight w ha i := by
  have h0 : (0 : Space d) ∈ interior (convexHull ℝ (Set.range w)) :=
    mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (closedBall_mem_nhds 0 hb) hball)
  have heq := (polarWitnessBasis w ha).interior_convexHull
  change interior (convexHull ℝ (Set.range w)) = _ at heq
  rw [heq] at h0
  exact h0 i

theorem polar_witness_gradient_inner {d : ℕ} (w : Fin (d + 1) → Space d)
    (ha : AffineIndependent ℝ w) (i : Fin (d + 1)) (x : Space d) :
    inner ℝ (polarWitnessGradient w ha i) x =
      (polarWitnessBasis w ha).coord i x - polarWitnessWeight w ha i := by
  rw [polarWitnessGradient, InnerProductSpace.toDual_symm_apply]
  have hd := congrFun ((polarWitnessBasis w ha).coord i).decomp x
  change ((polarWitnessBasis w ha).coord i).linear x =
    (polarWitnessBasis w ha).coord i x - polarWitnessWeight w ha i
  change (polarWitnessBasis w ha).coord i x =
    ((polarWitnessBasis w ha).coord i).linear x + polarWitnessWeight w ha i at hd
  linarith

theorem polar_witness_vertex_inner {d : ℕ} (w : Fin (d + 1) → Space d)
    (ha : AffineIndependent ℝ w) {b : ℝ} (hb : 0 < b)
    (hball : closedBall (0 : Space d) b ⊆ convexHull ℝ (Set.range w))
    (i j : Fin (d + 1)) :
    inner ℝ (w i) (polarWitnessVertex w ha j) =
      1 - (if i = j then 1 else 0) / polarWitnessWeight w ha j := by
  classical
  have hp := polar_witness_weight_pos w ha hb hball j
  rw [polarWitnessVertex, real_inner_smul_right, real_inner_comm,
    polar_witness_gradient_inner]
  have hv : (polarWitnessBasis w ha).coord j (w i) = if j = i then 1 else 0 :=
    (polarWitnessBasis w ha).coord_apply j i
  rw [hv]
  simp only [eq_comm (a := j)]
  field_simp [hp.ne']
  ring


theorem polar_witness_vertices_affine_independent {d : ℕ}
    (w : Fin (d + 1) → Space d) (ha : AffineIndependent ℝ w)
    {b : ℝ} (hb : 0 < b)
    (hball : closedBall (0 : Space d) b ⊆ convexHull ℝ (Set.range w)) :
    AffineIndependent ℝ (polarWitnessVertex w ha) := by
  classical
  apply affineIndependent_iff.mpr
  intro s c hc hs i hi
  have hp := polar_witness_weight_pos w ha hb hball i
  have heq : inner ℝ (w i) (∑ j ∈ s, c j • polarWitnessVertex w ha j) =
      (∑ j ∈ s, c j) - c i / polarWitnessWeight w ha i := by
    rw [inner_sum]
    simp_rw [real_inner_smul_right, polar_witness_vertex_inner w ha hb hball,
      mul_sub, mul_one, ← mul_div_assoc]
    rw [Finset.sum_sub_distrib]
    congr 1
    simp [mul_ite, ite_div, hi]
  rw [hs, inner_zero_right, hc] at heq
  have hz : c i / polarWitnessWeight w ha i = 0 := by linarith
  exact (div_eq_zero_iff).mp hz |>.resolve_right hp.ne'

/-- The polar vertices form a full-dimensional affine basis. -/
def polarVertexBasis {d : ℕ} (w : Fin (d + 1) → Space d)
    (ha : AffineIndependent ℝ w) {b : ℝ} (hb : 0 < b)
    (hball : closedBall (0 : Space d) b ⊆ convexHull ℝ (Set.range w)) :
    AffineBasis (Fin (d + 1)) ℝ (Space d) :=
  polarWitnessBasis (polarWitnessVertex w ha)
    (polar_witness_vertices_affine_independent w ha hb hball)

/-- Literal barycentric coordinates for the actual polar simplex. -/
def polarVertexCoord {d : ℕ} (w : Fin (d + 1) → Space d)
    (ha : AffineIndependent ℝ w) (i : Fin (d + 1)) : Space d →ᵃ[ℝ] ℝ where
  toFun x := polarWitnessWeight w ha i * (1 - inner ℝ (w i) x)
  linear := -(polarWitnessWeight w ha i • (innerSL ℝ (w i)).toLinearMap)
  map_vadd' p v := by
    change polarWitnessWeight w ha i * (1 - inner ℝ (w i) (v + p)) =
      -(polarWitnessWeight w ha i * inner ℝ (w i) v) +
        polarWitnessWeight w ha i * (1 - inner ℝ (w i) p)
    rw [inner_add_right]
    ring

theorem polar_vertex_coord_vertex {d : ℕ} (w : Fin (d + 1) → Space d)
    (ha : AffineIndependent ℝ w) {b : ℝ} (hb : 0 < b)
    (hball : closedBall (0 : Space d) b ⊆ convexHull ℝ (Set.range w))
    (i j : Fin (d + 1)) :
    polarVertexCoord w ha i (polarWitnessVertex w ha j) = if i = j then 1 else 0 := by
  classical
  change polarWitnessWeight w ha i * (1 - inner ℝ (w i) (polarWitnessVertex w ha j)) = _
  rw [polar_witness_vertex_inner w ha hb hball]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    field_simp [(polar_witness_weight_pos w ha hb hball i).ne']
    ring
  · simp [hij]

theorem polar_vertex_coord_eq_basis_coord {d : ℕ} (w : Fin (d + 1) → Space d)
    (ha : AffineIndependent ℝ w) {b : ℝ} (hb : 0 < b)
    (hball : closedBall (0 : Space d) b ⊆ convexHull ℝ (Set.range w))
    (i : Fin (d + 1)) :
    polarVertexCoord w ha i = (polarVertexBasis w ha hb hball).coord i := by
  classical
  apply AffineMap.ext_on (polarVertexBasis w ha hb hball).tot
  rintro x ⟨j, rfl⟩
  change polarVertexCoord w ha i (polarWitnessVertex w ha j) = _
  rw [polar_vertex_coord_vertex w ha hb hball]
  exact ((polarVertexBasis w ha hb hball).coord_apply i j).symm

/-- A genuine simplex whose vertices are derived from the same normals. -/
def polarWitnessSimplex {d : ℕ} (w : Fin (d + 1) → Space d)
    (ha : AffineIndependent ℝ w) {b : ℝ} (hb : 0 < b)
    (hball : closedBall (0 : Space d) b ⊆ convexHull ℝ (Set.range w)) :
    Affine.Simplex ℝ (Space d) d :=
  ⟨polarWitnessVertex w ha, polar_witness_vertices_affine_independent w ha hb hball⟩

theorem polar_witness_simplex_halfspaces {d : ℕ} (w : Fin (d + 1) → Space d)
    (ha : AffineIndependent ℝ w) {b : ℝ} (hb : 0 < b)
    (hball : closedBall (0 : Space d) b ⊆ convexHull ℝ (Set.range w)) :
    simplexSet (polarWitnessSimplex w ha hb hball) =
      {x | ∀ i, inner ℝ (w i) x ≤ 1} := by
  have heq := (polarVertexBasis w ha hb hball).convexHull_eq_nonneg_coord
  change simplexSet (polarWitnessSimplex w ha hb hball) = _ at heq
  rw [heq]
  ext x
  simp only [Set.mem_ofPred_eq]
  apply forall_congr'
  intro i
  rw [← polar_vertex_coord_eq_basis_coord w ha hb hball i]
  change 0 ≤ polarWitnessWeight w ha i * (1 - inner ℝ (w i) x) ↔ inner ℝ (w i) x ≤ 1
  rw [mul_nonneg_iff_of_pos_left (polar_witness_weight_pos w ha hb hball i), sub_nonneg]


theorem polar_witness_simplex_compact {d : ℕ} (w : Fin (d + 1) → Space d)
    (ha : AffineIndependent ℝ w) {b : ℝ} (hb : 0 < b)
    (hball : closedBall (0 : Space d) b ⊆ convexHull ℝ (Set.range w)) :
    IsCompact (simplexSet (polarWitnessSimplex w ha hb hball)) :=
  (Set.finite_range _).isCompact_convexHull ℝ

theorem polar_witness_simplex_contains_unit_ball {d : ℕ}
    (w : Fin (d + 1) → Space d) (ha : AffineIndependent ℝ w)
    (hw : ∀ i, ‖w i‖ ≤ 1) {b : ℝ} (hb : 0 < b)
    (hball : closedBall (0 : Space d) b ⊆ convexHull ℝ (Set.range w)) :
    closedBall (0 : Space d) 1 ⊆ simplexSet (polarWitnessSimplex w ha hb hball) := by
  rw [polar_witness_simplex_halfspaces w ha hb hball]
  intro x hx i
  have hxnorm : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hx
  exact (real_inner_le_norm (w i) x).trans
    ((mul_le_mul (hw i) hxnorm (norm_nonneg x) (by norm_num)).trans (by norm_num))

theorem polar_witness_simplex_radius_bound {d : ℕ}
    (w : Fin (d + 1) → Space d) (ha : AffineIndependent ℝ w)
    {b : ℝ} (hb : 0 < b)
    (hball : closedBall (0 : Space d) b ⊆ convexHull ℝ (Set.range w)) :
    simplexSet (polarWitnessSimplex w ha hb hball) ⊆ closedBall (0 : Space d) b⁻¹ := by
  rw [polar_witness_simplex_halfspaces w ha hb hball]
  intro x hx
  have hbound : ∀ z ∈ convexHull ℝ (Set.range w), inner ℝ z x ≤ 1 := by
    have hch : convexHull ℝ (Set.range w) ⊆ {z | inner ℝ x z ≤ 1} := by
      apply convexHull_min
      · rintro z ⟨i, rfl⟩
        simpa only [Set.mem_ofPred_eq, real_inner_comm] using hx i
      · exact convex_halfSpace_le (innerSL ℝ x).toLinearMap.isLinear 1
    intro z hz
    simpa only [Set.mem_ofPred_eq, real_inner_comm] using hch hz
  change dist x 0 ≤ b⁻¹
  rw [dist_zero_right]
  by_cases hzero : x = 0
  · subst x
    simpa using (inv_pos.mpr hb).le
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hzero
  have hy : (b / ‖x‖) • x ∈ closedBall (0 : Space d) b := by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hb hn), div_mul_cancel₀ _ hn.ne']
  have hh := hbound _ (hball hy)
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq] at hh
  have hcalc : b / ‖x‖ * ‖x‖ ^ 2 = b * ‖x‖ := by field_simp
  rw [hcalc] at hh
  rw [← one_div]
  exact (le_div_iff₀ hb).mpr (by simpa only [mul_comm] using hh)

theorem polar_witness_simplex_contains_body {d : ℕ}
    (K : Set (Space d)) (hc : IsCompact K) (hne : K.Nonempty)
    (w : Fin (d + 1) → Space d) (ha : AffineIndependent ℝ w)
    {b : ℝ} (hb : 0 < b)
    (hball : closedBall (0 : Space d) b ⊆ convexHull ℝ (Set.range w))
    (hboundary : ∀ i, compactSupportHeight K (w i) = 1) :
    K ⊆ simplexSet (polarWitnessSimplex w ha hb hball) := by
  rw [polar_witness_simplex_halfspaces w ha hb hball]
  intro x hx i
  simpa only [hboundary i] using compact_support_height_bound K hc hne (w i) x hx

theorem polar_witness_weight_lt_one {d : ℕ} (hd : 1 ≤ d)
    (w : Fin (d + 1) → Space d) (ha : AffineIndependent ℝ w)
    {b : ℝ} (hb : 0 < b)
    (hball : closedBall (0 : Space d) b ⊆ convexHull ℝ (Set.range w))
    (i : Fin (d + 1)) : polarWitnessWeight w ha i < 1 := by
  classical
  have : Nontrivial (Fin (d + 1)) := Fintype.one_lt_card_iff_nontrivial.mp (by simp; omega)
  obtain ⟨j, hji⟩ := exists_ne i
  have hjpos := polar_witness_weight_pos w ha hb hball j
  have hsum : ∑ k, polarWitnessWeight w ha k = 1 :=
    (polarWitnessBasis w ha).sum_coord_apply_eq_one 0
  have heq := Finset.sum_erase_add Finset.univ (polarWitnessWeight w ha) (Finset.mem_univ i)
  have hjbound : polarWitnessWeight w ha j ≤
      ∑ k ∈ Finset.univ.erase i, polarWitnessWeight w ha k :=
    Finset.single_le_sum (fun k _ => (polar_witness_weight_pos w ha hb hball k).le)
      (by simp [hji])
  rw [hsum] at heq
  linarith

theorem polar_witness_point_ne_zero {d : ℕ} (hd : 1 ≤ d)
    (w : Fin (d + 1) → Space d) (ha : AffineIndependent ℝ w)
    {b : ℝ} (hb : 0 < b)
    (hball : closedBall (0 : Space d) b ⊆ convexHull ℝ (Set.range w))
    (i : Fin (d + 1)) : w i ≠ 0 := by
  intro hi
  have hc : (polarWitnessBasis w ha).coord i (w i) = 1 :=
    (polarWitnessBasis w ha).coord_apply_eq i
  rw [hi] at hc
  exact (ne_of_lt (polar_witness_weight_lt_one hd w ha hb hball i)) hc

theorem polar_witness_simplex_support_one {d : ℕ} (hd : 1 ≤ d)
    (w : Fin (d + 1) → Space d) (ha : AffineIndependent ℝ w)
    {b : ℝ} (hb : 0 < b)
    (hball : closedBall (0 : Space d) b ⊆ convexHull ℝ (Set.range w))
    (i : Fin (d + 1)) :
    compactSupportHeight (simplexSet (polarWitnessSimplex w ha hb hball)) (w i) = 1 := by
  classical
  have : Nontrivial (Fin (d + 1)) := Fintype.one_lt_card_iff_nontrivial.mp (by simp; omega)
  obtain ⟨j, hji⟩ := exists_ne i
  have hv : polarWitnessVertex w ha j ∈ simplexSet (polarWitnessSimplex w ha hb hball) :=
    subset_convexHull ℝ _ (Set.mem_range_self j)
  have hne : (simplexSet (polarWitnessSimplex w ha hb hball)).Nonempty := ⟨_, hv⟩
  have hc := polar_witness_simplex_compact w ha hb hball
  apply le_antisymm
  · obtain ⟨q, hq, hheight⟩ := compact_support_height_attained _ hc hne (w i)
    rw [← hheight]
    rw [polar_witness_simplex_halfspaces w ha hb hball] at hq
    exact hq i
  · have h := compact_support_height_bound _ hc hne (w i) _ hv
    rw [polar_witness_vertex_inner w ha hb hball] at h
    simpa [Ne.symm hji] using h

/-- Normalization preserves the actual supplied witness points as facet atoms. -/
def polarWitnessNormal {d : ℕ} (w : Fin (d + 1) → Space d) (i : Fin (d + 1)) : Space d :=
  ‖w i‖⁻¹ • w i

def polarWitnessHeight {d : ℕ} (w : Fin (d + 1) → Space d) (i : Fin (d + 1)) : ℝ :=
  ‖w i‖⁻¹

theorem polar_witness_normal_unit {d : ℕ} (hd : 1 ≤ d)
    (w : Fin (d + 1) → Space d) (ha : AffineIndependent ℝ w)
    {b : ℝ} (hb : 0 < b)
    (hball : closedBall (0 : Space d) b ⊆ convexHull ℝ (Set.range w))
    (i : Fin (d + 1)) : ‖polarWitnessNormal w i‖ = 1 := by
  have hp := norm_pos_iff.mpr (polar_witness_point_ne_zero hd w ha hb hball i)
  rw [polarWitnessNormal, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne']

theorem polar_witness_height_pos {d : ℕ} (hd : 1 ≤ d)
    (w : Fin (d + 1) → Space d) (ha : AffineIndependent ℝ w)
    {b : ℝ} (hb : 0 < b)
    (hball : closedBall (0 : Space d) b ⊆ convexHull ℝ (Set.range w))
    (i : Fin (d + 1)) : 0 < polarWitnessHeight w i :=
  inv_pos.mpr (norm_pos_iff.mpr (polar_witness_point_ne_zero hd w ha hb hball i))

theorem polar_witness_finite_cone_point {d : ℕ} (hd : 1 ≤ d)
    (w : Fin (d + 1) → Space d) (ha : AffineIndependent ℝ w)
    {b : ℝ} (hb : 0 < b)
    (hball : closedBall (0 : Space d) b ⊆ convexHull ℝ (Set.range w))
    (i : Fin (d + 1)) :
    finiteConePoint (fun i j => polarWitnessNormal w i j) (polarWitnessHeight w) i =
      (fun j => w i j) := by
  have hp := norm_pos_iff.mpr (polar_witness_point_ne_zero hd w ha hb hball i)
  ext j
  change (‖w i‖⁻¹ * w i j) / ‖w i‖⁻¹ = w i j
  exact mul_div_cancel_left₀ _ (inv_ne_zero hp.ne')

theorem polar_witness_simplex_normal_halfspaces {d : ℕ} (hd : 1 ≤ d)
    (w : Fin (d + 1) → Space d) (ha : AffineIndependent ℝ w)
    {b : ℝ} (hb : 0 < b)
    (hball : closedBall (0 : Space d) b ⊆ convexHull ℝ (Set.range w)) :
    simplexSet (polarWitnessSimplex w ha hb hball) =
      finiteHalfspaceSet (polarWitnessNormal w) (polarWitnessHeight w) := by
  rw [polar_witness_simplex_halfspaces w ha hb hball]
  ext x
  change (∀ i, inner ℝ (w i) x ≤ 1) ↔
    (∀ i, inner ℝ (‖w i‖⁻¹ • w i) x ≤ ‖w i‖⁻¹)
  apply forall_congr'
  intro i
  rw [real_inner_smul_left]
  have hp : 0 < ‖w i‖⁻¹ := polar_witness_height_pos hd w ha hb hball i
  simpa only [mul_one] using
    (mul_le_mul_iff_right₀ (b := inner ℝ (w i) x) (c := (1 : ℝ)) hp).symm


theorem polar_witness_normals_injective {d : ℕ} (hd : 1 ≤ d)
    (w : Fin (d + 1) → Space d) (ha : AffineIndependent ℝ w)
    {b : ℝ} (hb : 0 < b)
    (hball : closedBall (0 : Space d) b ⊆ convexHull ℝ (Set.range w)) :
    Function.Injective (polarWitnessNormal w) := by
  intro i j hij
  by_contra hne
  have hpi := polar_witness_weight_pos w ha hb hball i
  have hli := polar_witness_weight_lt_one hd w ha hb hball i
  have hquot : 1 < 1 / polarWitnessWeight w ha i :=
    (lt_div_iff₀ hpi).mpr (by simpa only [one_mul] using hli)
  have hdiag : inner ℝ (w i) (polarWitnessVertex w ha i) < 0 := by
    rw [polar_witness_vertex_inner w ha hb hball]
    simp only [ite_true]
    linarith
  have hneg : inner ℝ (polarWitnessNormal w i) (polarWitnessVertex w ha i) < 0 := by
    rw [polarWitnessNormal, real_inner_smul_left]
    exact mul_neg_of_pos_of_neg (polar_witness_height_pos hd w ha hb hball i) hdiag
  have hpos : 0 < inner ℝ (polarWitnessNormal w j) (polarWitnessVertex w ha i) := by
    rw [polarWitnessNormal, real_inner_smul_left,
      polar_witness_vertex_inner w ha hb hball]
    have hp : 0 < ‖w j‖⁻¹ := polar_witness_height_pos hd w ha hb hball j
    simpa only [ite_eq_right (Ne.symm hne), zero_div, sub_zero, mul_one] using hp
  rw [hij] at hneg
  linarith

theorem polar_witness_normal_support_height {d : ℕ} (hd : 1 ≤ d)
    (w : Fin (d + 1) → Space d) (ha : AffineIndependent ℝ w)
    {b : ℝ} (hb : 0 < b)
    (hball : closedBall (0 : Space d) b ⊆ convexHull ℝ (Set.range w))
    (i : Fin (d + 1)) :
    compactSupportHeight (simplexSet (polarWitnessSimplex w ha hb hball))
      (polarWitnessNormal w i) = polarWitnessHeight w i := by
  have hc := polar_witness_simplex_compact w ha hb hball
  have hne : (simplexSet (polarWitnessSimplex w ha hb hball)).Nonempty :=
    ⟨polarWitnessVertex w ha 0, subset_convexHull ℝ _ (Set.mem_range_self 0)⟩
  have hp : 0 < ‖w i‖⁻¹ := polar_witness_height_pos hd w ha hb hball i
  rw [polarWitnessNormal,
    compact_support_height_direction_nonnegative_smul _ hc hne ‖w i‖⁻¹ hp.le,
    polar_witness_simplex_support_one hd w ha hb hball, mul_one]
  rfl

/-- The actual convex body has exactly the constructed simplex as carrier. -/
def polarWitnessConvexBody {d : ℕ} (w : Fin (d + 1) → Space d)
    (ha : AffineIndependent ℝ w) {b : ℝ} (hb : 0 < b)
    (hball : closedBall (0 : Space d) b ⊆ convexHull ℝ (Set.range w)) :
    ConvexBody (Space d) :=
  ⟨simplexSet (polarWitnessSimplex w ha hb hball), convex_convexHull ℝ _,
    polar_witness_simplex_compact w ha hb hball,
    ⟨polarWitnessVertex w ha 0, subset_convexHull ℝ _ (Set.mem_range_self 0)⟩⟩

theorem polar_witness_convex_body_coe {d : ℕ} (w : Fin (d + 1) → Space d)
    (ha : AffineIndependent ℝ w) {b : ℝ} (hb : 0 < b)
    (hball : closedBall (0 : Space d) b ⊆ convexHull ℝ (Set.range w)) :
    (polarWitnessConvexBody w ha hb hball : Set (Space d)) =
      simplexSet (polarWitnessSimplex w ha hb hball) := rfl

/-- Construct the enclosing polar simplex from the same supplied witnesses.
Every halfspace, normalized normal, height and facet atom is literal. -/
theorem actual_polar_enclosing_simplex {d : ℕ} (hd : 1 ≤ d)
    (K : Set (Space d)) (hc : IsCompact K) (hne : K.Nonempty)
    (w : Fin (d + 1) → Space d) (ha : AffineIndependent ℝ w)
    (hw : ∀ i, ‖w i‖ ≤ 1) {b : ℝ} (hb : 0 < b)
    (hround : closedBall (0 : Space d) b ⊆ convexHull ℝ (Set.range w))
    (hboundary : ∀ i, compactSupportHeight K (w i) = 1) :
    ∃ P : Affine.Simplex ℝ (Space d) d,
      ∃ n : Fin (d + 1) → Space d, ∃ heights : Fin (d + 1) → ℝ,
        simplexSet P = {x | ∀ i, inner ℝ (w i) x ≤ 1} ∧
        K ⊆ simplexSet P ∧
        closedBall (0 : Space d) 1 ⊆ simplexSet P ∧
        simplexSet P ⊆ closedBall (0 : Space d) b⁻¹ ∧
        (∀ i, ‖n i‖ = 1) ∧ (∀ i, 0 < heights i) ∧ Function.Injective n ∧
        simplexSet P = finiteHalfspaceSet n heights ∧
        (∀ i, finiteConePoint (fun i j => n i j) heights i = (fun j => w i j)) ∧
        (∀ i, compactSupportHeight (simplexSet P) (w i) = 1) := by
  refine ⟨polarWitnessSimplex w ha hb hround, polarWitnessNormal w, polarWitnessHeight w,
    polar_witness_simplex_halfspaces w ha hb hround,
    polar_witness_simplex_contains_body K hc hne w ha hb hround hboundary,
    polar_witness_simplex_contains_unit_ball w ha hw hb hround,
    polar_witness_simplex_radius_bound w ha hb hround,
    polar_witness_normal_unit hd w ha hb hround,
    polar_witness_height_pos hd w ha hb hround,
    polar_witness_normals_injective hd w ha hb hround,
    polar_witness_simplex_normal_halfspaces hd w ha hb hround,
    polar_witness_finite_cone_point hd w ha hb hround,
    polar_witness_simplex_support_one hd w ha hb hround⟩

/-- Exact original-radius interface for the SAME raw witnesses in the actual
body's polar boundary. No facet formula or abstract polar-body input is needed. -/
theorem actual_polar_enclosing_simplex_original_radius {d : ℕ} (hd : 2 ≤ d)
    (K : ConvexBody (Space d)) (w : Fin (d + 1) → Fin d → ℝ)
    (ha : AffineIndependent ℝ (fun i => WithLp.toLp 2 (w i)))
    (hw : ∀ i, ‖WithLp.toLp 2 (w i)‖ ≤ 1)
    (hround : closedBall (0 : Space d) (b d) ⊆
      convexHull ℝ (Set.range (fun i => WithLp.toLp 2 (w i))))
    (hboundary : ∀ i, w i ∈ actualPolarBoundaryRaw (K : Set (Space d))) :
    ∃ P : Affine.Simplex ℝ (Space d) d,
      ∃ n : Fin (d + 1) → Space d, ∃ heights : Fin (d + 1) → ℝ,
        simplexSet P = {x | ∀ i, inner ℝ (WithLp.toLp 2 (w i)) x ≤ 1} ∧
        (K : Set (Space d)) ⊆ simplexSet P ∧
        closedBall (0 : Space d) 1 ⊆ simplexSet P ∧
        simplexSet P ⊆ closedBall (0 : Space d) (M d) ∧
        (∀ i, ‖n i‖ = 1) ∧ (∀ i, 0 < heights i) ∧ Function.Injective n ∧
        simplexSet P = finiteHalfspaceSet n heights ∧
        (∀ i, finiteConePoint (fun i j => n i j) heights i = w i) ∧
        (∀ i, compactSupportHeight (simplexSet P) (WithLp.toLp 2 (w i)) = 1) := by
  have hd1 : 1 ≤ d := by omega
  have hboundary' : ∀ i, compactSupportHeight (K : Set (Space d)) (WithLp.toLp 2 (w i)) = 1 :=
    hboundary
  simpa only [M, one_div] using actual_polar_enclosing_simplex hd1 (K : Set (Space d))
    K.isCompact K.nonempty (fun i => WithLp.toLp 2 (w i)) ha hw (b_pos hd1) hround hboundary'

end Entry005
