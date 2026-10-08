import Entry005.HalfspaceApproximationSequence
import Entry005.CompactBallConeLaw
import Entry005.FiniteBodyWeightedAssignment

noncomputable section
open Metric MeasureTheory Module Filter
open scoped BigOperators Topology

namespace Entry005

variable {d : ℕ} [Nontrivial (Space d)]

/-- The actual supporting-halfspace law at every approximation stage, bundled
as a probability measure using the proved radial facet mass identity. -/
def halfspaceApproximationProbability (K : Set (Space d)) (hc : IsCompact K)
    (hconv : Convex ℝ K) (hb : closedBall (0 : Space d) 1 ⊆ K) (m : ℕ) :
    ProbabilityMeasure (Fin d → ℝ) :=
  rawProbabilityLaw (halfspaceApproximationLaw K hc hconv hb m)
    (halfspace_approximation_law_probability K hc hconv hb m)

/-- An actual normalized compact convex body has an actual weak limit of its
supporting-halfspace cone laws. Centering and all directional brightness
identities are derived by compact test-integral passage. -/
theorem actual_body_compact_cone_law_exists (K : Set (Space d)) (hc : IsCompact K)
    (hconv : Convex ℝ K) (hb : closedBall (0 : Space d) 1 ⊆ K) :
    ∃ μ : ProbabilityMeasure (CompactConeBall d), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      Tendsto (fun k => compactBallLaw (halfspaceApproximationProbability K hc hconv hb (φ k)))
        atTop (𝓝 μ) ∧
      Tendsto (fun k => halfspaceApproximationProbability K hc hconv hb (φ k))
        atTop (𝓝 (compactBallRawLaw μ)) ∧
      (∀ᵐ x ∂(compactBallRawLaw μ : Measure (Fin d → ℝ)), ‖WithLp.toLp 2 x‖ ≤ 1) ∧
      (∀ i, (∫ x, x i ∂(compactBallRawLaw μ : Measure (Fin d → ℝ))) = 0) ∧
      (∀ u : Space d, ‖u‖ = 1 →
        negativeIntegral (compactBallRawLaw μ : Measure (Fin d → ℝ))
          (fun x => dotProduct (fun j => u j) x) =
          projectionVolumeSet K u / ((finrank ℝ (Space d) : ℝ) * (volume K).toReal)) := by
  let ν := halfspaceApproximationProbability K hc hconv hb
  have hball : ∀ m, ∀ᵐ x ∂(ν m : Measure (Fin d → ℝ)), ‖WithLp.toLp 2 x‖ ≤ 1 :=
    halfspace_approximation_law_ae_unit_ball K hc hconv hb
  obtain ⟨μ, φ, hφ, hlim, hraw, _⟩ := compactBallLaw_exists_subsequence ν hball
  refine ⟨μ, φ, hφ, hlim, hraw, compactBallRawLaw_ae_unit_ball μ, ?_, ?_⟩
  · intro i
    have ht := compactBallLaw_coordinate_integral_tendsto ν hball μ φ hlim i
    have hz : Tendsto (fun k => ∫ x, x i ∂(ν (φ k) : Measure (Fin d → ℝ)))
        atTop (𝓝 0) := by
      have heq : (fun k => ∫ x, x i ∂(ν (φ k) : Measure (Fin d → ℝ))) = fun _ => 0 :=
        funext (fun k => halfspace_approximation_law_centered K hc hconv hb (φ k) i)
      rw [heq]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique ht hz
  · intro u hu
    have ht := compactBallLaw_negative_direction_integral_tendsto ν hball μ φ hlim
      (fun j => u j)
    have hbri := (halfspace_approximation_law_negative_tendsto K hc hconv hb u hu).comp
      hφ.tendsto_atTop
    exact tendsto_nhds_unique ht hbri

/-- The actual body's brightness and its unit ball give a positive affine
first determinant moment for its cone law. -/
theorem actual_body_brightness_law_affine_first_moment_pos
    (K : Set (Space d)) (hc : IsCompact K) (hb : closedBall (0 : Space d) 1 ⊆ K)
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hball : ∀ᵐ x ∂ν, ‖WithLp.toLp 2 x‖ ≤ 1)
    (hcenter : ∀ i, (∫ x, x i ∂ν) = 0)
    (hbrightness : ∀ u : Space d, ‖u‖ = 1 →
      negativeIntegral ν (fun x => dotProduct (fun j => u j) x) =
        projectionVolumeSet K u / ((finrank ℝ (Space d) : ℝ) * (volume K).toReal)) :
    0 < ∫ w : Fin (d + 1) → Fin d → ℝ, |(anchorMatrix w).det| ∂iidLaw ν (d + 1) := by
  have hd : 1 ≤ d := by
    have hp : 0 < d := by simpa [Space] using (finrank_pos : 0 < finrank ℝ (Space d))
    omega
  let γ := unitProjectionBallVolume d /
    ((finrank ℝ (Space d) : ℝ) * (volume K).toReal)
  have hM := compact_body_normalization_pos_of_unit_ball K hc hb
  have hγ : 0 < γ := div_pos unit_projection_ball_volume_pos hM
  apply unit_ball_round_affine_first_moment_pos hd ν hball hcenter
    (show 0 < γ / 2 by positivity)
  intro u hu
  rw [hbrightness u hu]
  have hl := div_le_div_of_nonneg_right (normalized_body_brightness_lower K hc hb u hu) hM.le
  change γ ≤ _ at hl
  linarith

/-- Strong actual assignment for every normalized compact convex body. The
law is constructed from its finite support-halfspace approximations; no
probability, balance, roundness, moment or weak-limit premise is supplied. -/
theorem actual_body_cone_first_moment_assignment
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K) :
    ∃ ν : ProbabilityMeasure (Fin d → ℝ),
      (∀ᵐ x ∂(ν : Measure (Fin d → ℝ)), ‖WithLp.toLp 2 x‖ ≤ 1) ∧
      (∀ i, (∫ x, x i ∂(ν : Measure (Fin d → ℝ))) = 0) ∧
      (∀ u : Space d, ‖u‖ = 1 → negativeIntegral (ν : Measure (Fin d → ℝ))
        (fun x => dotProduct (fun j => u j) x) =
        projectionVolumeSet K u / ((finrank ℝ (Space d) : ℝ) * (volume K).toReal)) ∧
      ∃ w : Fin (d + 1) → Fin d → ℝ, ∃ _hdet : (anchorMatrix w).det ≠ 0,
        (∀ i, w i ∈ (ν : Measure (Fin d → ℝ)).support ∧ ‖WithLp.toLp 2 (w i)‖ ≤ 1) ∧
        AffineIndependent ℝ (fun i => WithLp.toLp 2 (w i)) ∧
        Measurable (fun x => largestCoordinate (anchorCoordinates w x)) ∧
        Integrable (fun x => ‖WithLp.toLp 2 x -
          WithLp.toLp 2 (w (largestCoordinate (anchorCoordinates w x)))‖) (ν : Measure (Fin d → ℝ)) ∧
        (∫ x, ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (largestCoordinate (anchorCoordinates w x)))‖
          ∂(ν : Measure (Fin d → ℝ))) ≤
          ((((d : ℝ) + 1) * ((d : ℝ) + 2)) *
            determinantLawDefect (iidLaw (ν : Measure (Fin d → ℝ)) d)
              (ν : Measure (Fin d → ℝ)) id id) /
            (∫ v : Fin (d + 1) → Fin d → ℝ,
              |(anchorMatrix v).det| ∂iidLaw (ν : Measure (Fin d → ℝ)) (d + 1)) := by
  obtain ⟨μ, _, _, _, _, hball, hcenter, hbrightness⟩ :=
    actual_body_compact_cone_law_exists K hc hconv hb
  refine ⟨compactBallRawLaw μ, hball, hcenter, hbrightness, ?_⟩
  exact unit_ball_first_moment_assignment (compactBallRawLaw μ : Measure (Fin d → ℝ))
    hball hcenter (actual_body_brightness_law_affine_first_moment_pos K hc hb _
      hball hcenter hbrightness)

end Entry005
