import Entry005.ActualBodyConeLaw
import Entry005.CompactIidMomentContinuity
import Entry005.FiniteHalfspaceHorizontalMoment
import Entry005.OfficialProjectionDefinitions

noncomputable section
open Metric MeasureTheory Module Filter
open scoped BigOperators Topology

namespace Entry005

variable {d : ℕ} [Nontrivial (Space d)]

/-- The exact first horizontal determinant moment of every actual finite
supporting-halfspace approximation. -/
theorem halfspace_approximation_horizontal_first_moment
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K) (m : ℕ) :
    (∫ base, |horizontalDeterminant base| ∂iidLaw (halfspaceApproximationLaw K hc hconv hb m) d) =
      (d.factorial : ℝ) /
        ((d : ℝ) * (volume (halfspaceApproximationBody K hc hconv hb m)).toReal) ^ d *
          (volume (projectionBodySet (halfspaceApproximationBody K hc hconv hb m))).toReal := by
  exact finite_halfspace_horizontal_first_moment _ _
    (halfspace_approximation_normals_unit K hc hconv hb m)
    (halfspace_approximation_heights_pos K hc hconv hb m)
    (halfspace_approximation_normals_injective K hc hconv hb m)
    (halfspace_approximation_body_compact K hc hconv hb m)

/-- The actual cone law's first horizontal moment equals actual projection-body
volume. The only limiting-law premise is the displayed actual finite-law weak
subsequence; such a subsequence is constructed by actual_body_compact_cone_law_exists.
Official projection-body compactness is consumed through a proved definition bridge. -/
theorem actual_body_horizontal_first_moment_of_compact_limit
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K)
    (μ : ProbabilityMeasure (CompactConeBall d)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (fun k => compactBallLaw (halfspaceApproximationProbability K hc hconv hb (φ k)))
      atTop (𝓝 μ)) :
    (∫ base, |horizontalDeterminant base|
      ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) d) =
        (d.factorial : ℝ) / ((d : ℝ) * (volume K).toReal) ^ d *
          (volume (projectionBodySet K)).toReal := by
  let ν := halfspaceApproximationProbability K hc hconv hb
  let x : C(CompactConeBall d, Fin d → ℝ) := ⟨compactBallRaw, continuous_compactBallRaw⟩
  have hball : ∀ m, ∀ᵐ z ∂(ν m : Measure (Fin d → ℝ)), ‖WithLp.toLp 2 z‖ ≤ 1 :=
    halfspace_approximation_law_ae_unit_ball K hc hconv hb
  have hmap (k : ℕ) : (compactBallLaw (ν (φ k))).map x = ν (φ k) :=
    compactBallLaw_raw_probability_pushforward _ (hball (φ k))
  have ht := tendsto_horizontal_mapped_iid_first_moment hlim x
  have htest : Tendsto (fun k => ∫ base, |horizontalDeterminant base|
      ∂iidLaw (halfspaceApproximationLaw K hc hconv hb (φ k)) d) atTop
      (𝓝 (∫ base, |horizontalDeterminant base|
        ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) d)) := by
    change Tendsto (fun k => ∫ base, |horizontalDeterminant base|
      ∂iidLaw ((compactBallLaw (ν (φ k))).map x : Measure (Fin d → ℝ)) d) atTop
      (𝓝 (∫ base, |horizontalDeterminant base|
        ∂iidLaw (μ.map x : Measure (Fin d → ℝ)) d)) at ht
    simp_rw [hmap] at ht
    exact ht
  have hvol := halfspace_approximation_volume_tendsto K hc hconv hb
  have hpivol := tendsto_projection_body_volume_of_dilation_sandwich K
    (halfspaceApproximationBody K hc hconv hb) hc
    (halfspace_approximation_body_compact K hc hconv hb)
    (actual_projection_body_compact_via_official K) halfspaceApproximationTolerance
    (fun m => (halfspace_approximation_tolerance_pos m).le)
    halfspace_approximation_tolerance_tendsto
    (subset_halfspace_approximation_body K hc hconv hb)
    (halfspace_approximation_body_subset_dilation K hc hconv hb)
  have hM : (d : ℝ) * (volume K).toReal ≠ 0 := by
    simpa only [finrank_euclideanSpace_fin] using
      (compact_body_normalization_pos_of_unit_ball K hc hb).ne'
  have hgeo0 : Tendsto (fun m => (d.factorial : ℝ) /
      ((d : ℝ) * (volume (halfspaceApproximationBody K hc hconv hb m)).toReal) ^ d *
        (volume (projectionBodySet (halfspaceApproximationBody K hc hconv hb m))).toReal)
      atTop (𝓝 ((d.factorial : ℝ) / ((d : ℝ) * (volume K).toReal) ^ d *
        (volume (projectionBodySet K)).toReal)) :=
    (tendsto_const_nhds.div ((hvol.const_mul (d : ℝ)).pow d)
      (pow_ne_zero d hM)).mul hpivol
  have hgeo := hgeo0.comp hφ.tendsto_atTop
  have hid (k : ℕ) := halfspace_approximation_horizontal_first_moment K hc hconv hb (φ k)
  simp_rw [Function.comp_def, ← hid] at hgeo
  exact tendsto_nhds_unique htest hgeo

/-- Every normalized actual compact convex body has a centered unit-ball cone
law with actual brightness and the exact first horizontal determinant moment.
No limiting law, moment identity or probabilistic hypothesis is supplied. -/
theorem actual_body_cone_law_with_horizontal_first_moment
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K) :
    ∃ ν : ProbabilityMeasure (Fin d → ℝ),
      (∀ᵐ x ∂(ν : Measure (Fin d → ℝ)), ‖WithLp.toLp 2 x‖ ≤ 1) ∧
      (∀ i, (∫ x, x i ∂(ν : Measure (Fin d → ℝ))) = 0) ∧
      (∀ u : Space d, ‖u‖ = 1 → negativeIntegral (ν : Measure (Fin d → ℝ))
        (fun x => dotProduct (fun j => u j) x) =
        projectionVolumeSet K u / ((finrank ℝ (Space d) : ℝ) * (volume K).toReal)) ∧
      (∫ base, |horizontalDeterminant base| ∂iidLaw (ν : Measure (Fin d → ℝ)) d) =
        (d.factorial : ℝ) / ((d : ℝ) * (volume K).toReal) ^ d *
          (volume (projectionBodySet K)).toReal := by
  obtain ⟨μ, φ, hφ, hlim, _, hball, hcenter, hbrightness⟩ :=
    actual_body_compact_cone_law_exists K hc hconv hb
  exact ⟨compactBallRawLaw μ, hball, hcenter, hbrightness,
    actual_body_horizontal_first_moment_of_compact_limit K hc hconv hb μ φ hφ hlim⟩

end Entry005
