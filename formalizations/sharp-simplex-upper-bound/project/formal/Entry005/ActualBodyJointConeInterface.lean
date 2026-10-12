import Entry005.ActualBodyPolarBoundary
import Entry005.FirstMomentAssignment

noncomputable section
open Metric MeasureTheory Module Filter
open scoped BigOperators Topology

namespace Entry005
variable {d : ℕ} [Nontrivial (Space d)]

/-- One constructed actual law simultaneously has exact horizontal A,
fixed-body polar-boundary support and strong first-moment assignment. All facts
use the same μ and φ. No law, support, moment, positivity or assignment premise
is supplied; the actual pyramid B/entryDefect identity remains a separate task. -/
theorem actual_body_joint_polar_horizontal_assignment
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K) :
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
          projectionVolumeSet K u / ((finrank ℝ (Space d) : ℝ) * (volume K).toReal)) ∧
      (∀ᵐ x ∂(compactBallRawLaw μ : Measure (Fin d → ℝ)), x ∈ actualPolarBoundaryRaw K) ∧
      (compactBallRawLaw μ : Measure (Fin d → ℝ)).support ⊆ actualPolarBoundaryRaw K ∧
      (∫ base, |horizontalDeterminant base|
        ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) d) =
        (d.factorial : ℝ) / ((d : ℝ) * (volume K).toReal) ^ d *
          (volume (projectionBodySet K)).toReal ∧
      (0 < ∫ v : Fin (d + 1) → Fin d → ℝ, |(anchorMatrix v).det|
        ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) (d + 1)) ∧
      ∃ w : Fin (d + 1) → Fin d → ℝ, ∃ _hdet : (anchorMatrix w).det ≠ 0,
        (∀ i, w i ∈ (compactBallRawLaw μ : Measure (Fin d → ℝ)).support ∧ ‖WithLp.toLp 2 (w i)‖ ≤ 1) ∧
        AffineIndependent ℝ (fun i => WithLp.toLp 2 (w i)) ∧
        Measurable (fun x => largestCoordinate (anchorCoordinates w x)) ∧
        Integrable (fun x => ‖WithLp.toLp 2 x -
          WithLp.toLp 2 (w (largestCoordinate (anchorCoordinates w x)))‖) (compactBallRawLaw μ : Measure (Fin d → ℝ)) ∧
        (∫ x, ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (largestCoordinate (anchorCoordinates w x)))‖
          ∂(compactBallRawLaw μ : Measure (Fin d → ℝ))) ≤
          ((((d : ℝ) + 1) * ((d : ℝ) + 2)) *
            determinantLawDefect (iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) d)
              (compactBallRawLaw μ : Measure (Fin d → ℝ)) id id) /
            (∫ v : Fin (d + 1) → Fin d → ℝ,
              |(anchorMatrix v).det| ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) (d + 1)) := by
  obtain ⟨μ, φ, hφ, hlim, hraw, hball, hcenter, hbrightness,
      hboundary, hsupport, hA⟩ :=
    actual_body_compact_cone_law_exists_with_polar_boundary K hc hconv hb
  have hB := actual_body_brightness_law_affine_first_moment_pos K hc hb
    (compactBallRawLaw μ : Measure (Fin d → ℝ)) hball hcenter hbrightness
  refine ⟨μ, φ, hφ, hlim, hraw, hball, hcenter, hbrightness,
    hboundary, hsupport, hA, hB, ?_⟩
  exact unit_ball_first_moment_assignment (compactBallRawLaw μ : Measure (Fin d → ℝ))
    hball hcenter hB

end Entry005
