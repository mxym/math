import Entry005.ProjectionVolumeSqueeze
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open Metric MeasureTheory Module Function Filter
open scoped BigOperators RealInnerProductSpace Pointwise Topology

namespace Entry005

def halfspaceApproximationTolerance (m : ℕ) : ℝ := 1 / ((m : ℝ) + 1)

theorem halfspace_approximation_tolerance_pos (m : ℕ) :
    0 < halfspaceApproximationTolerance m := by
  unfold halfspaceApproximationTolerance
  positivity

theorem halfspace_approximation_tolerance_tendsto :
    Tendsto halfspaceApproximationTolerance atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

section ChosenBodies

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A chosen actual finite sphere net, with actual supporting heights. -/
def halfspaceApproximationNormals (K : Set E) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : E) 1 ⊆ K) (m : ℕ) : Finset E :=
  Classical.choose (exists_finite_support_halfspace_approximation K hc hconv hb
    (halfspaceApproximationTolerance m) (halfspace_approximation_tolerance_pos m))

def halfspaceApproximationBody (K : Set E) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : E) 1 ⊆ K) (m : ℕ) : Set E :=
  finiteHalfspaceSet (fun u : halfspaceApproximationNormals K hc hconv hb m => (u : E))
    (fun u : halfspaceApproximationNormals K hc hconv hb m => compactSupportHeight K (u : E))

theorem halfspace_approximation_spec (K : Set E) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : E) 1 ⊆ K) (m : ℕ) :
    (∀ u : halfspaceApproximationNormals K hc hconv hb m,
      ‖(u : E)‖ = 1 ∧ 0 < compactSupportHeight K (u : E)) ∧
    Function.Injective (fun u : halfspaceApproximationNormals K hc hconv hb m => (u : E)) ∧
    IsCompact (halfspaceApproximationBody K hc hconv hb m) ∧
    K ⊆ halfspaceApproximationBody K hc hconv hb m ∧
    halfspaceApproximationBody K hc hconv hb m ⊆ (1 + halfspaceApproximationTolerance m) • K :=
  Classical.choose_spec (exists_finite_support_halfspace_approximation K hc hconv hb
    (halfspaceApproximationTolerance m) (halfspace_approximation_tolerance_pos m))

theorem halfspace_approximation_normals_unit (K : Set E) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : E) 1 ⊆ K) (m : ℕ) :
    ∀ u : halfspaceApproximationNormals K hc hconv hb m, ‖(u : E)‖ = 1 :=
  fun u => (halfspace_approximation_spec K hc hconv hb m).1 u |>.1

theorem halfspace_approximation_heights_pos (K : Set E) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : E) 1 ⊆ K) (m : ℕ) :
    ∀ u : halfspaceApproximationNormals K hc hconv hb m, 0 < compactSupportHeight K (u : E) :=
  fun u => (halfspace_approximation_spec K hc hconv hb m).1 u |>.2

theorem halfspace_approximation_normals_injective (K : Set E) (hc : IsCompact K)
    (hconv : Convex ℝ K) (hb : closedBall (0 : E) 1 ⊆ K) (m : ℕ) :
    Function.Injective (fun u : halfspaceApproximationNormals K hc hconv hb m => (u : E)) :=
  (halfspace_approximation_spec K hc hconv hb m).2.1

theorem halfspace_approximation_body_compact (K : Set E) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : E) 1 ⊆ K) (m : ℕ) :
    IsCompact (halfspaceApproximationBody K hc hconv hb m) :=
  (halfspace_approximation_spec K hc hconv hb m).2.2.1

theorem subset_halfspace_approximation_body (K : Set E) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : E) 1 ⊆ K) (m : ℕ) :
    K ⊆ halfspaceApproximationBody K hc hconv hb m :=
  (halfspace_approximation_spec K hc hconv hb m).2.2.2.1

theorem halfspace_approximation_body_subset_dilation (K : Set E) (hc : IsCompact K)
    (hconv : Convex ℝ K) (hb : closedBall (0 : E) 1 ⊆ K) (m : ℕ) :
    halfspaceApproximationBody K hc hconv hb m ⊆ (1 + halfspaceApproximationTolerance m) • K :=
  (halfspace_approximation_spec K hc hconv hb m).2.2.2.2

theorem halfspace_approximation_body_contains_unit_ball (K : Set E) (hc : IsCompact K)
    (hconv : Convex ℝ K) (hb : closedBall (0 : E) 1 ⊆ K) (m : ℕ) :
    closedBall (0 : E) 1 ⊆ halfspaceApproximationBody K hc hconv hb m :=
  hb.trans (subset_halfspace_approximation_body K hc hconv hb m)

variable [MeasurableSpace E] [BorelSpace E]

theorem halfspace_approximation_volume_tendsto (K : Set E) (hc : IsCompact K)
    (hconv : Convex ℝ K) (hb : closedBall (0 : E) 1 ⊆ K) :
    Tendsto (fun m => (volume (halfspaceApproximationBody K hc hconv hb m)).toReal)
      atTop (𝓝 (volume K).toReal) :=
  tendsto_real_volume_of_dilation_sandwich K _ hc
    (halfspace_approximation_body_compact K hc hconv hb) halfspaceApproximationTolerance
    (fun m => (halfspace_approximation_tolerance_pos m).le) halfspace_approximation_tolerance_tendsto
    (subset_halfspace_approximation_body K hc hconv hb)
    (halfspace_approximation_body_subset_dilation K hc hconv hb)

theorem halfspace_approximation_projection_volume_tendsto (K : Set E) (hc : IsCompact K)
    (hconv : Convex ℝ K) (hb : closedBall (0 : E) 1 ⊆ K) (u : E) (hu : ‖u‖ = 1) :
    Tendsto (fun m => projectionVolumeSet (halfspaceApproximationBody K hc hconv hb m) u)
      atTop (𝓝 (projectionVolumeSet K u)) :=
  tendsto_projection_volume_of_dilation_sandwich K _ hc
    (halfspace_approximation_body_compact K hc hconv hb) halfspaceApproximationTolerance
    (fun m => (halfspace_approximation_tolerance_pos m).le) halfspace_approximation_tolerance_tendsto
    (subset_halfspace_approximation_body K hc hconv hb)
    (halfspace_approximation_body_subset_dilation K hc hconv hb) u hu

end ChosenBodies

section ChosenEuclideanBodies

variable {d : ℕ} [Nontrivial (Space d)]

theorem compact_projection_body_of_compact_body (K : Set (Space d)) (hc : IsCompact K) :
    IsCompact (projectionBodySet K) := by
  obtain ⟨R, hR, hbound⟩ := hc.isBounded.subset_closedBall_lt 0 (0 : Space d)
  exact bounded_projection_body_compact K R hR.le hbound

theorem halfspace_approximation_projection_body_volume_tendsto (K : Set (Space d))
    (hc : IsCompact K) (hconv : Convex ℝ K) (hb : closedBall (0 : Space d) 1 ⊆ K) :
    Tendsto (fun m => (volume (projectionBodySet (halfspaceApproximationBody K hc hconv hb m))).toReal)
      atTop (𝓝 (volume (projectionBodySet K)).toReal) :=
  tendsto_projection_body_volume_of_dilation_sandwich K _ hc
    (halfspace_approximation_body_compact K hc hconv hb) (compact_projection_body_of_compact_body K hc)
    halfspaceApproximationTolerance (fun m => (halfspace_approximation_tolerance_pos m).le)
    halfspace_approximation_tolerance_tendsto (subset_halfspace_approximation_body K hc hconv hb)
    (halfspace_approximation_body_subset_dilation K hc hconv hb)

theorem halfspace_approximation_projection_ratio_tendsto (K : Set (Space d))
    (hc : IsCompact K) (hconv : Convex ℝ K) (hb : closedBall (0 : Space d) 1 ⊆ K) :
    Tendsto (fun m => projectionRatio (halfspaceApproximationBody K hc hconv hb m))
      atTop (𝓝 (projectionRatio K)) :=
  tendsto_projection_ratio_of_dilation_sandwich K _ hc
    (halfspace_approximation_body_compact K hc hconv hb) (compact_projection_body_of_compact_body K hc)
    (compact_body_volume_pos_of_unit_ball K hc hb).ne' halfspaceApproximationTolerance
    (fun m => (halfspace_approximation_tolerance_pos m).le) halfspace_approximation_tolerance_tendsto
    (subset_halfspace_approximation_body K hc hconv hb)
    (halfspace_approximation_body_subset_dilation K hc hconv hb)

/-- The raw laws all have the same ambient type, although their finite
normal index sets vary with the approximation stage. -/
def halfspaceApproximationLaw (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K) (m : ℕ) : Measure (Fin d → ℝ) :=
  finiteHalfspaceConeLaw (fun u : halfspaceApproximationNormals K hc hconv hb m => (u : Space d))
    (fun u : halfspaceApproximationNormals K hc hconv hb m => compactSupportHeight K (u : Space d))

theorem halfspace_approximation_law_probability (K : Set (Space d)) (hc : IsCompact K)
    (hconv : Convex ℝ K) (hb : closedBall (0 : Space d) 1 ⊆ K) (m : ℕ) :
    IsProbabilityMeasure (halfspaceApproximationLaw K hc hconv hb m) :=
  finite_halfspace_cone_probability _ _ (halfspace_approximation_normals_unit K hc hconv hb m)
    (halfspace_approximation_heights_pos K hc hconv hb m)
    (halfspace_approximation_normals_injective K hc hconv hb m)
    (halfspace_approximation_body_compact K hc hconv hb m)

theorem halfspace_approximation_law_centered (K : Set (Space d)) (hc : IsCompact K)
    (hconv : Convex ℝ K) (hb : closedBall (0 : Space d) 1 ⊆ K) (m : ℕ) :
    ∀ j, (∫ x, x j ∂halfspaceApproximationLaw K hc hconv hb m) = 0 :=
  finite_halfspace_cone_centered _ _ (halfspace_approximation_normals_unit K hc hconv hb m)
    (halfspace_approximation_heights_pos K hc hconv hb m)
    (halfspace_approximation_normals_injective K hc hconv hb m)
    (halfspace_approximation_body_compact K hc hconv hb m)

omit [Nontrivial (Space d)] in
theorem halfspace_approximation_law_ae_unit_ball (K : Set (Space d)) (hc : IsCompact K)
    (hconv : Convex ℝ K) (hb : closedBall (0 : Space d) 1 ⊆ K) (m : ℕ) :
    ∀ᵐ x ∂halfspaceApproximationLaw K hc hconv hb m, ‖WithLp.toLp 2 x‖ ≤ 1 :=
  finite_halfspace_cone_ae_unit_ball _ _ (halfspace_approximation_normals_unit K hc hconv hb m)
    (halfspace_approximation_body_contains_unit_ball K hc hconv hb m)

omit [Nontrivial (Space d)] in
theorem halfspace_approximation_law_support_unit_ball (K : Set (Space d)) (hc : IsCompact K)
    (hconv : Convex ℝ K) (hb : closedBall (0 : Space d) 1 ⊆ K) (m : ℕ) :
    ∀ x ∈ (halfspaceApproximationLaw K hc hconv hb m).support, ‖WithLp.toLp 2 x‖ ≤ 1 :=
  unit_ball_support_bound _ (halfspace_approximation_law_ae_unit_ball K hc hconv hb m)

theorem halfspace_approximation_law_negative_brightness (K : Set (Space d)) (hc : IsCompact K)
    (hconv : Convex ℝ K) (hb : closedBall (0 : Space d) 1 ⊆ K) (m : ℕ)
    (u : Space d) (hu : ‖u‖ = 1) :
    negativeIntegral (halfspaceApproximationLaw K hc hconv hb m) (fun x => dotProduct (fun j => u j) x) =
      projectionVolumeSet (halfspaceApproximationBody K hc hconv hb m) u /
        ((finrank ℝ (Space d) : ℝ) * (volume (halfspaceApproximationBody K hc hconv hb m)).toReal) :=
  finite_halfspace_cone_negative_brightness _ _ (halfspace_approximation_normals_unit K hc hconv hb m)
    (halfspace_approximation_heights_pos K hc hconv hb m)
    (halfspace_approximation_normals_injective K hc hconv hb m)
    (halfspace_approximation_body_compact K hc hconv hb m) u hu

theorem halfspace_approximation_law_negative_tendsto (K : Set (Space d)) (hc : IsCompact K)
    (hconv : Convex ℝ K) (hb : closedBall (0 : Space d) 1 ⊆ K) (u : Space d) (hu : ‖u‖ = 1) :
    Tendsto (fun m => negativeIntegral (halfspaceApproximationLaw K hc hconv hb m)
      (fun x => dotProduct (fun j => u j) x)) atTop
      (𝓝 (projectionVolumeSet K u / ((finrank ℝ (Space d) : ℝ) * (volume K).toReal))) := by
  simp_rw [halfspace_approximation_law_negative_brightness K hc hconv hb _ u hu]
  exact tendsto_brightness_normalization_of_dilation_sandwich K _ hc
    (halfspace_approximation_body_compact K hc hconv hb)
    (compact_body_normalization_pos_of_unit_ball K hc hb).ne' halfspaceApproximationTolerance
    (fun m => (halfspace_approximation_tolerance_pos m).le) halfspace_approximation_tolerance_tendsto
    (subset_halfspace_approximation_body K hc hconv hb)
    (halfspace_approximation_body_subset_dilation K hc hconv hb) u hu

end ChosenEuclideanBodies
end Entry005
