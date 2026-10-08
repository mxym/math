import Entry005.TruncationFacetVectors
import Entry005.TruncationCenteredHalfspaces

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Entry005

/-- This is the actual projection body of the actual truncated simplex. -/
theorem truncation_actual_projection_body {d : ℕ} (hd : 2 ≤ d)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    projectionBodySet (truncationSet d t) =
      finiteZonotope (fun i : TruncationFacetIndex d =>
        (1 / 2 : ℝ) • truncationRawHorizontal d t i) := by
  have hc : IsCompact (finiteHalfspaceSet (truncationFacetNormal d) (truncationFacetHeight d t)) := by
    rw [truncation_halfspace_representation (by omega) t]
    exact truncationSet_isCompact ht0 ht1
  rw [← truncation_halfspace_representation (by omega) t,
    finite_halfspace_projection_body_eq_zonotope _ _ (truncation_facet_norm (by omega))
      (truncation_facet_normal_injective hd) hc]
  congr 1
  funext i
  rw [← truncation_actual_facet_vector hd t ht0 ht1 i, smul_smul]
  congr 1
  ring

/-- Exact brightness of the literal truncated simplex, in every unit direction. -/
theorem truncation_actual_projection_volume {d : ℕ} (hd : 2 ≤ d)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (u : Space d) (hu : ‖u‖ = 1) :
    projectionVolumeSet (truncationSet d t) u =
      truncationFacetScale d / 2 *
        ((1 - t ^ (d - 1)) * (∑ i, |u i|) +
          (1 + t ^ (d - 1)) * |∑ i, u i|) := by
  classical
  have hc : IsCompact (finiteHalfspaceSet (truncationFacetNormal d) (truncationFacetHeight d t)) := by
    rw [truncation_halfspace_representation (by omega) t]
    exact truncationSet_isCompact ht0 ht1
  have he := finite_halfspace_cauchy (truncationFacetNormal d) (truncationFacetHeight d t)
    (truncation_facet_norm (by omega)) (truncation_facet_normal_injective hd) hc u hu
  rw [truncation_halfspace_representation (by omega) t] at he
  have hscale : 0 ≤ truncationFacetScale d := by unfold truncationFacetScale; positivity
  have hq : 0 ≤ t ^ (d - 1) := pow_nonneg ht0.le _
  have hr : 0 ≤ 1 - t ^ (d - 1) := sub_nonneg.mpr (pow_le_one₀ ht0.le ht1.le)
  have hs : (∑ i : TruncationFacetIndex d,
      |inner ℝ (truncationFacetNormal d i) u| *
        finiteHalfspaceFacetArea (truncationFacetNormal d) (truncationFacetHeight d t) i) =
      ∑ i : TruncationFacetIndex d, |inner ℝ (truncationRawHorizontal d t i) u| := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← truncation_actual_facet_vector hd t ht0 ht1 i, real_inner_smul_left,
      abs_mul, abs_of_nonneg (finite_halfspace_facet_area_nonneg _ _ i)]
    ring
  have hcoords : (∑ i : Fin d, |inner ℝ (truncationRawHorizontal d t (Sum.inl i)) u|) =
      truncationFacetScale d * (1 - t ^ (d - 1)) * ∑ i, |u i| := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [truncationRawHorizontal, real_inner_smul_left, truncationVertex,
      EuclideanSpace.inner_single_left, abs_mul, abs_neg, abs_of_nonneg hscale,
      abs_of_nonneg hr]
  have htop : |inner ℝ (truncationRawHorizontal d t (Sum.inr false)) u| =
      truncationFacetScale d * |∑ i, u i| := by
    rw [truncationRawHorizontal, real_inner_smul_left, truncation_diagonal_inner,
      abs_mul, abs_of_nonneg hscale]
  have hbottom : |inner ℝ (truncationRawHorizontal d t (Sum.inr true)) u| =
      truncationFacetScale d * t ^ (d - 1) * |∑ i, u i| := by
    rw [truncationRawHorizontal, real_inner_smul_left, truncation_diagonal_inner,
      abs_mul, abs_mul, abs_neg, abs_of_nonneg hscale, abs_of_nonneg hq]
  rw [he, hs, Fintype.sum_sum_type, Fintype.sum_bool, hcoords, htop, hbottom]
  ring

end Entry005
