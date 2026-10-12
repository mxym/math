import Entry005.PrescribedSimplex
import Entry005.ProjectionCap

noncomputable section
open Metric MeasureTheory MeasureTheory.Measure
open scoped RealInnerProductSpace Pointwise

namespace Entry005

section Support
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The support function is the actual supremum of the linear functional on the body. -/
def geometricSupport (K : ConvexBody E) (n : E) : ℝ :=
  sSup ((fun x : E => inner ℝ n x) '' (K : Set E))

private theorem support_attained (K : ConvexBody E) (n : E) :
    ∃ x ∈ K, geometricSupport K n = inner ℝ n x ∧
      ∀ y ∈ K, inner ℝ n y ≤ inner ℝ n x := by
  obtain ⟨x, hx, hmax⟩ := K.isCompact.exists_isMaxOn (f := fun x : E => inner ℝ n x) K.nonempty
    (continuous_const.inner continuous_id).continuousOn
  refine ⟨x, hx, le_antisymm ?_ ?_, hmax⟩
  · exact csSup_le (K.nonempty.image _) (by rintro a ⟨y, hy, rfl⟩; exact hmax hy)
  · exact le_csSup ((K.isCompact.image (continuous_const.inner continuous_id)).bddAbove)
      ⟨x, hx, rfl⟩

/-- All support halfspaces are computed from the actual compact carrier. -/
theorem geometricSupport_le_iff (K : ConvexBody E) (n : E) (a : ℝ) :
    geometricSupport K n ≤ a ↔ ∀ x ∈ K, inner ℝ n x ≤ a := by
  obtain ⟨q, hq, he, hmax⟩ := support_attained K n
  rw [he]
  exact ⟨fun h x hx => (hmax x hx).trans h, fun h => h q hq⟩

/-- Genuine closed convex bodies equal their intersection of unit support halfspaces. -/
theorem mem_iff_geometricSupport (K : ConvexBody E) (x : E) :
    x ∈ K ↔ ∀ n : E, ‖n‖ = 1 → inner ℝ n x ≤ geometricSupport K n := by
  constructor
  · intro hx n _
    exact (geometricSupport_le_iff K n _).mp le_rfl x hx
  · intro h
    by_contra hx
    obtain ⟨k, hk, n, hpos, hn, hgap, hsep, _⟩ :=
      closest_support K K.convex K.isCompact.isComplete K.nonempty x hx
    have hs := (geometricSupport_le_iff K n (inner ℝ n k)).mpr hsep
    have hh := (h n hn).trans hs
    linarith

/-- Hausdorff control bounds genuine support functions; no inclusion is needed. -/
theorem geometricSupport_le_of_hausdorff (K P : ConvexBody E) (s : ℝ)
    (hhaus : hausdorffDist (K : Set E) (P : Set E) ≤ s) (n : E) :
    geometricSupport P n ≤ geometricSupport K n + ‖n‖ * s := by
  obtain ⟨q, hq, he, _⟩ := support_attained P n
  obtain ⟨k, hk, hdist⟩ := K.isCompact.exists_infDist_eq_dist K.nonempty q
  have hfinite := hausdorffEDist_ne_top_of_nonempty_of_bounded
    P.nonempty K.nonempty P.isCompact.isBounded K.isCompact.isBounded
  have hqk : ‖q - k‖ ≤ s := by
    have hh := (infDist_le_hausdorffDist_of_mem hq hfinite).trans
      ((hausdorffDist_comm (s := (P : Set E)) (t := (K : Set E))) ▸ hhaus)
    simpa only [hdist, dist_eq_norm] using hh
  have hinner := real_inner_le_norm n (q - k)
  rw [inner_sub_right] at hinner
  have hkSupport := (geometricSupport_le_iff K n _).mp le_rfl k hk
  rw [he]
  have hb := mul_le_mul_of_nonneg_left hqk (norm_nonneg n)
  linarith

/-- Unit-ball containment in the outer body alone suffices for the manuscript's shrink. -/
theorem shrink_subset_of_hausdorff (K P : ConvexBody E) (s : ℝ)
    (hball : closedBall (0 : E) 1 ⊆ P) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hhaus : hausdorffDist (K : Set E) (P : Set E) ≤ s) :
    (1 - s) • (P : Set E) ⊆ (K : Set E) := by
  rintro y ⟨p, hp, rfl⟩
  apply (mem_iff_geometricSupport K _).mpr
  intro n hn
  have hnP : n ∈ P := hball (by simp [mem_closedBall, dist_zero_right, hn])
  have hlower : 1 ≤ geometricSupport P n := by
    have hh := (geometricSupport_le_iff P n _).mp le_rfl n hnP
    simpa only [real_inner_self_eq_norm_sq, hn, one_pow] using hh
  have hpSupport := (geometricSupport_le_iff P n _).mp le_rfl p hp
  have hgap := geometricSupport_le_of_hausdorff K P s hhaus n
  rw [hn, one_mul] at hgap
  rw [inner_smul_right]
  have hscale := mul_le_mul_of_nonneg_left hpSupport (sub_nonneg.mpr hs1.le)
  have hprod : 0 ≤ s * (geometricSupport P n - 1) :=
    mul_nonneg hs0 (sub_nonneg.mpr hlower)
  nlinarith

/-- The same true support argument works about any center, including the prescribed centroid. -/
theorem shrink_subset_of_hausdorff_about (K P : ConvexBody E) (c : E) (s : ℝ)
    (hball : closedBall c 1 ⊆ P) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hhaus : hausdorffDist (K : Set E) (P : Set E) ≤ s) :
    AffineMap.homothety c (1 - s) '' (P : Set E) ⊆ (K : Set E) := by
  rintro y ⟨p, hp, rfl⟩
  apply (mem_iff_geometricSupport K _).mpr
  intro n hn
  have hnP : c + n ∈ P := hball (by simp [mem_closedBall, dist_eq_norm, hn])
  have hlower : inner ℝ n c + 1 ≤ geometricSupport P n := by
    have hh := (geometricSupport_le_iff P n _).mp le_rfl (c + n) hnP
    simpa only [inner_add_right, real_inner_self_eq_norm_sq, hn, one_pow] using hh
  have hpSupport := (geometricSupport_le_iff P n _).mp le_rfl p hp
  have hgap := geometricSupport_le_of_hausdorff K P s hhaus n
  rw [hn, one_mul] at hgap
  have hscale := mul_le_mul_of_nonneg_left
    (sub_le_sub_right hpSupport (inner ℝ n c)) (sub_nonneg.mpr hs1.le)
  have hprod : 0 ≤ s * (geometricSupport P n - inner ℝ n c - 1) :=
    mul_nonneg hs0 (by linarith)
  simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add,
    inner_add_right, inner_smul_right, inner_sub_right]
  nlinarith

end Support

/-- The genuine compact convex carrier of a full-dimensional affine simplex. -/
def simplexBody {d : ℕ} (P : Affine.Simplex ℝ (Space d) d) : ConvexBody (Space d) where
  carrier := simplexSet P
  convex' := convex_convexHull ℝ _
  isCompact' := (Set.finite_range P.points).isCompact_convexHull ℝ
  nonempty' := ⟨P.points 0, subset_convexHull ℝ _ ⟨0, rfl⟩⟩

private theorem dimension_space (d : ℕ) : Module.finrank ℝ (Space d) = d := by
  simp [Space]

private theorem vertices_bound_hull {d : ℕ} (P : Affine.Simplex ℝ (Space d) d) (M : ℝ)
    (hbound : ∀ i, ‖P.points i‖ ≤ M) : simplexSet P ⊆ closedBall 0 M := by
  apply convexHull_min
  · rintro x ⟨i, rfl⟩
    simpa only [mem_closedBall, dist_zero_right] using hbound i
  · exact convex_closedBall _ _

/-- Actual Hausdorff control now replaces the formerly assumed shrink inclusion. -/
theorem retain_maximum_simplex_of_hausdorff {d : ℕ} (hd : 1 ≤ d)
    (K : ConvexBody (Space d)) (P S : Affine.Simplex ℝ (Space d) d)
    (M s : ℝ) (hmax : maximumInscribed K S)
    (hKP : (K : Set (Space d)) ⊆ simplexSet P)
    (hbound : ∀ i, ‖P.points i‖ ≤ M) (hball : closedBall (0 : Space d) 1 ⊆ simplexSet S)
    (hs0 : 0 ≤ s) (hds : (d : ℝ) * s ≤ 1 / 8)
    (hhaus : hausdorffDist (K : Set (Space d)) (simplexSet P) ≤ s) :
    (K : Set (Space d)) ⊆ (1 + 2 * M * (d : ℝ) * s) • simplexSet S := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : s < 1 := by nlinarith
  exact retain_maximum_simplex hd K P S M s hmax hKP hbound hball hs0 hds
    (shrink_subset_of_hausdorff K (simplexBody P) s
      (fun x hx => hKP (hmax.1 (hball hx))) hs0 hs1 hhaus)

/-- Exact zero-distance endpoint, without identifying the origin with the centroid. -/
theorem maximum_simplex_zero_hausdorff {d : ℕ} (hd : 1 ≤ d)
    (K : ConvexBody (Space d)) (P S : Affine.Simplex ℝ (Space d) d)
    (M : ℝ) (hmax : maximumInscribed K S)
    (hKP : (K : Set (Space d)) ⊆ simplexSet P)
    (hbound : ∀ i, ‖P.points i‖ ≤ M) (hball : closedBall (0 : Space d) 1 ⊆ simplexSet S)
    (hhaus : hausdorffDist (K : Set (Space d)) (simplexSet P) = 0) :
    (K : Set (Space d)) = simplexSet S ∧ simplexSet P = simplexSet S := by
  have hKS := retain_maximum_simplex_of_hausdorff hd K P S M 0 hmax hKP hbound
    hball le_rfl (by norm_num) hhaus.le
  simp only [mul_zero, add_zero, one_smul] at hKS
  have hPK := shrink_subset_of_hausdorff K (simplexBody P) 0
    (fun x hx => hKP (hmax.1 (hball hx))) le_rfl zero_lt_one hhaus.le
  simp only [sub_zero, one_smul] at hPK
  exact ⟨Set.Subset.antisymm hKS hmax.1, Set.Subset.antisymm (hPK.trans hKS) (hmax.1.trans hKP)⟩

/-- Literal original-centroid excess from actual Hausdorff control and centered geometry. -/
theorem excess_of_hausdorff_at_centroid {d : ℕ} (hd : 1 ≤ d)
    (K : ConvexBody (Space d)) (P S : Affine.Simplex ℝ (Space d) d)
    (M s : ℝ) (hmax : maximumInscribed K S)
    (hKP : (K : Set (Space d)) ⊆ simplexSet P)
    (hbound : ∀ i, ‖P.points i - S.centroid‖ ≤ M)
    (hball : closedBall S.centroid 1 ⊆ simplexSet S)
    (hs0 : 0 ≤ s) (hds : (d : ℝ) * s ≤ 1 / 8)
    (hhaus : hausdorffDist (K : Set (Space d)) (simplexSet P) ≤ s) :
    excess (K : Set (Space d)) S ≤ 2 * M * (d : ℝ) * s := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : s < 1 := by nlinarith
  exact retain_maximum_simplex_excess hd K P S M s hmax hKP hbound hball hs0 hds
    (shrink_subset_of_hausdorff_about K (simplexBody P) S.centroid s
      (fun x hx => hKP (hmax.1 (hball hx))) hs0 hs1 hhaus)

/-- The literal geometric radius produced by actual intrinsic projection deficits. -/
def projectionHausdorffBound (d : ℕ) (M η : ℝ) : ℝ :=
  ((d - 1 : ℕ) : ℝ) * (M + 1) * η ^ (1 / ((d - 1 : ℕ) : ℝ))

/-- Combined projection-cap, true shrink, true maximum-volume, and stochastic matching endpoint.
The analytic input is solely the displayed bound on actual projection volumes. -/
theorem retain_maximum_simplex_of_projection_deficit {d : ℕ} (hd : 2 ≤ d)
    (K : ConvexBody (Space d)) (P S : Affine.Simplex ℝ (Space d) d)
    (M η : ℝ) (hmax : maximumInscribed K S)
    (hKP : (K : Set (Space d)) ⊆ simplexSet P)
    (hbound : ∀ i, ‖P.points i‖ ≤ M) (hball : closedBall (0 : Space d) 1 ⊆ simplexSet S)
    (hη : 0 ≤ η) (hgate : (d : ℝ) * projectionHausdorffBound d M η ≤ 1 / 8)
    (hdef : ∀ u : Space d, ‖u‖ = 1 →
      (projectedVolume (ℝ ∙ u)ᗮ (simplexBody P)).toReal -
        (projectedVolume (ℝ ∙ u)ᗮ K).toReal ≤ η) :
    (K : Set (Space d)) ⊆
      (1 + 2 * M * (d : ℝ) * projectionHausdorffBound d M η) • simplexSet S := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hbound 0)
  have hdim : 2 ≤ Module.finrank ℝ (Space d) := by simpa only [dimension_space] using hd
  have hhaus := hausdorff_from_projection_deficit hdim K (simplexBody P) M η hM hη
    (fun x hx => hmax.1 (hball hx)) hKP (vertices_bound_hull P M hbound) hdef
  simp only [dimension_space] at hhaus
  exact retain_maximum_simplex_of_hausdorff (by omega) K P S M
    (projectionHausdorffBound d M η) hmax hKP hbound hball (by unfold projectionHausdorffBound; positivity)
    hgate hhaus

end Entry005
