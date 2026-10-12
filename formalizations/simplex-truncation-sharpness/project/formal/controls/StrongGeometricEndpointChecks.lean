import Entry005.StrongGeometricEndpoint

noncomputable section
open Entry005 Metric MeasureTheory
namespace StrongGeometricEndpointChecks

private def S : Affine.Simplex ℝ (Space 2) 2 := regularSimplex 2 (by decide)
private def K : ConvexBody (Space 2) := simplexBody S
private theorem maximal : maximumInscribed K S :=
  ⟨Set.Subset.refl _, fun _ h => measure_mono h⟩
private theorem body_radius : (K : Set (Space 2)) ⊆ closedBall 0 2 := by
  apply convexHull_min ?_ (convex_closedBall _ _)
  rintro x ⟨i, rfl⟩
  simpa only [mem_closedBall, dist_zero_right, S, Nat.cast_ofNat] using
    (regularSimplex_vertex_norm 2 (by decide) i).le

-- Zero deficit involves actual intrinsic projected Haar volumes of a genuine 2D simplex.
example : excess (K : Set (Space 2)) S = 0 ∧ (K : Set (Space 2)) = simplexSet S := by
  exact excess_eq_zero_of_zero_projection_deficit (by decide) K S S 2 maximal
    (Set.Subset.refl _) (regularSimplex_centroid 2 (by decide))
    (regularSimplex_unit_ball 2 (by decide)) (by norm_num) body_radius
    (by intro u _; simp [K])

-- The non-circular endpoint receives only the actual inner radius; no outer-simplex radius.
example : excess (K : Set (Space 2)) S ≤ 0 := by
  have hs : innerProjectionRadius 2 2 0 = 0 := by norm_num [innerProjectionRadius]
  have he := excess_of_inner_radius_projection_deficit (by decide) K S S 2 0 maximal
    (Set.Subset.refl _) (regularSimplex_centroid 2 (by decide))
    (regularSimplex_unit_ball 2 (by decide)) (by norm_num) body_radius le_rfl
    (by rw [hs, mul_zero]; norm_num)
    (by intro u _; simp [K])
  simpa only [hs, mul_zero] using he

example : 0 ≤ excess (K : Set (Space 2)) S :=
  excess_nonnegative_of_maximum (by decide) K S maximal

-- The full existential conclusion derives its normalization from this actual maximum.
example : ∃ f : Space 2 ≃ᵃ[ℝ] Space 2,
    (affineSimplex f S).centroid = 0 ∧
    (affineBody f K : Set (Space 2)) ⊆ closedBall 0 (regularMaximumRadius 2) ∧
    excess (K : Set (Space 2)) S ≤ 3 := by
  obtain ⟨f, hc, _, _, _, hr, he, _⟩ :=
    maximum_simplex_strong_geometric_endpoint (by decide) K S maximal
  exact ⟨f, hc, hr, by norm_num at he; exact he⟩

end StrongGeometricEndpointChecks
