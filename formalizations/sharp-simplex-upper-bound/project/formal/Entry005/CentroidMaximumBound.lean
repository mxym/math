import Entry005.MaximumOuterBall

noncomputable section
open Metric MeasureTheory
open scoped BigOperators
namespace Entry005

/-- The original centroid has the actual uniform barycentric coordinates. -/
theorem simplexCoord_centroid {d : ℕ} (S : Affine.Simplex ℝ (Space d) d)
    (i : Fin (d + 1)) : simplexCoord S i S.centroid = 1 / ((d : ℝ) + 1) := by
  have h := (simplexAffineBasis S).coord_apply_centroid
    (s := Finset.univ) (i := i) (Finset.mem_univ i)
  change simplexCoord S i S.centroid = _ at h
  simpa only [Finset.card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one, one_div] using h

/-- Actual barycentric coordinates of contraction about the original centroid.
No origin or regular-simplex normalization is used. -/
theorem simplexCoord_centroid_contraction {d : ℕ}
    (S : Affine.Simplex ℝ (Space d) d) (i : Fin (d + 1)) (x : Space d) :
    simplexCoord S i (S.centroid + ((d : ℝ) + 2)⁻¹ • (x - S.centroid)) =
      (simplexCoord S i x + 1) / ((d : ℝ) + 2) := by
  have hv := (simplexCoord S i).linearMap_vsub x S.centroid
  simp only [vsub_eq_sub] at hv
  have ha := (simplexCoord S i).map_vadd S.centroid
    (((d : ℝ) + 2)⁻¹ • (x - S.centroid))
  simp only [vadd_eq_add, map_smul, smul_eq_mul] at ha
  rw [add_comm, ha, hv, simplexCoord_centroid]
  have h1 : (d : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
  have h2 : (d : ℝ) + 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

/-- Every actual prescribed maximum simplex controls the whole body about its
original centroid, with dimension-only excess parameter `d + 1`. -/
theorem maximumInscribed_centered_bound {d : ℕ} (hd : 1 ≤ d)
    (K : ConvexBody (Space d)) (S : Affine.Simplex ℝ (Space d) d)
    (hmax : maximumInscribed K S) :
    (K : Set (Space d)) ⊆ centeredDilation S ((d : ℝ) + 1) := by
  intro x hx
  let y := S.centroid + ((d : ℝ) + 2)⁻¹ • (x - S.centroid)
  have hy : y ∈ simplexSet S := by
    change y ∈ convexHull ℝ (Set.range (simplexAffineBasis S))
    rw [(simplexAffineBasis S).convexHull_eq_nonneg_coord]
    intro i
    change 0 ≤ simplexCoord S i y
    rw [show simplexCoord S i y = (simplexCoord S i x + 1) / ((d : ℝ) + 2) from
      simplexCoord_centroid_contraction S i x]
    have hcoord := (abs_le.mp (maximumInscribed_coord_abs_le_one hd K S hmax x hx i)).1
    exact div_nonneg (by linarith) (by positivity)
  refine ⟨y, hy, ?_⟩
  change S.centroid + (1 + ((d : ℝ) + 1)) •
    (S.centroid + ((d : ℝ) + 2)⁻¹ • (x - S.centroid) - S.centroid) = x
  rw [add_sub_cancel_left, show 1 + ((d : ℝ) + 1) = (d : ℝ) + 2 by ring,
    smul_smul, mul_inv_cancel₀ (ne_of_gt (show 0 < (d : ℝ) + 2 by positivity)), one_smul]
  abel

/-- The literal infimum-based excess is at most `d + 1` for every actual
prescribed maximum simplex, measured about its own original centroid. -/
theorem maximumInscribed_excess_le_dim_add_one {d : ℕ} (hd : 1 ≤ d)
    (K : ConvexBody (Space d)) (S : Affine.Simplex ℝ (Space d) d)
    (hmax : maximumInscribed K S) :
    excess (K : Set (Space d)) S ≤ (d : ℝ) + 1 := by
  unfold excess
  apply csInf_le
  · exact ⟨0, fun t ht => ht.1⟩
  · exact ⟨by positivity, maximumInscribed_centered_bound hd K S hmax⟩

end Entry005
