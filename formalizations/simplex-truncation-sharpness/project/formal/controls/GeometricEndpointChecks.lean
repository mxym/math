import Entry005.GeometricEndpoint

noncomputable section
open Entry005 Metric MeasureTheory
open scoped Pointwise
namespace GeometricEndpointChecks

private def R : Affine.Simplex ℝ (Space 2) 2 := regularSimplex 2 (by decide)
private def K : ConvexBody (Space 2) := simplexBody R
private theorem hmax : maximumInscribed K R :=
  ⟨Set.Subset.refl _, fun _ h => measure_mono h⟩

example : projectionHausdorffBound 2 2 0 = 0 := by
  norm_num [projectionHausdorffBound]

-- Actual dimension-two projection bodies with exactly zero deficit, not a scalar model.
example : (K : Set (Space 2)) ⊆ simplexSet R := by
  have h := retain_maximum_simplex_of_projection_deficit (by decide) K R R 2 0 hmax
    (Set.Subset.refl _) (fun i => (regularSimplex_vertex_norm 2 (by decide) i).le)
    (regularSimplex_unit_ball 2 (by decide)) (by norm_num)
    (by norm_num [projectionHausdorffBound]) (by intro u _; simp [K])
  have hrho : projectionHausdorffBound 2 2 0 = 0 := by norm_num [projectionHausdorffBound]
  simpa only [hrho, mul_zero, add_zero, one_smul] using h

-- Actual compact simplex and its genuine maximum satisfy the global geometric branch.
example : excess (K : Set (Space 2)) R ≤ 5 := by
  have h := maximum_simplex_excess_le_R0_sub_one (by decide) K R hmax
  norm_num [R0] at h
  exact h

-- True Hausdorff zero gives zero original-centroid excess; no centroid is stipulated.
example : excess (K : Set (Space 2)) R ≤ 0 := by
  have hc : R.centroid = 0 := regularSimplex_centroid 2 (by decide)
  have hb : closedBall R.centroid 1 ⊆ simplexSet R := by
    rw [hc]
    exact regularSimplex_unit_ball 2 (by decide)
  have h := excess_of_hausdorff_at_centroid (by decide) K R R 2 0 hmax
    (Set.Subset.refl _) (by intro i; rw [hc, sub_zero]; exact (regularSimplex_vertex_norm 2 (by decide) i).le)
    hb le_rfl (by norm_num) hausdorffDist_self_zero.le
  simpa only [mul_zero] using h

end GeometricEndpointChecks
