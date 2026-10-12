import Entry005.ActualPyramidAssignment
import Entry005.ActualBodyJointConeInterface

noncomputable section
open Metric MeasureTheory Module Filter
open scoped BigOperators Topology
namespace Entry005
variable {d : ℕ} [Nontrivial (Space d)]

/-- Joint final interface: one compact-limit witness and its one raw law supply
polar boundary, brightness, A, B, D and the same assignment points. -/
theorem actual_body_joint_polar_pyramid_assignment
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
      (∫ w, |horizontalDeterminant w| ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) d) =
        (d.factorial : ℝ) / ((d : ℝ) * (volume K).toReal) ^ d *
          (volume (projectionBodySet K)).toReal ∧
      0 < (∫ w, |horizontalDeterminant w| ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) d) ∧
      entryA K =
        (∫ w : Fin (d + 1) → Fin d → ℝ,
          |liftedDeterminant (fun j => w j.succ) (w 0)|
          ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) (d + 1)) /
        ((d + 1 : ℝ) *
          (∫ w, |horizontalDeterminant w| ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) d)) ∧
      determinantLawDefect (iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) d)
        (compactBallRawLaw μ : Measure (Fin d → ℝ)) id id =
        (d + 1 : ℝ) *
          (∫ w, |horizontalDeterminant w| ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) d) *
            entryDefect K ∧
      0 < (∫ v : Fin (d + 1) → Fin d → ℝ,
        |liftedDeterminant (fun j => v j.succ) (v 0)|
        ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) (d + 1)) ∧
      ∃ w : Fin (d + 1) → Fin d → ℝ, ∃ _hdet : (anchorMatrix w).det ≠ 0,
        (∀ i, w i ∈ (compactBallRawLaw μ : Measure (Fin d → ℝ)).support ∧ ‖WithLp.toLp 2 (w i)‖ ≤ 1) ∧
        AffineIndependent ℝ (fun i => WithLp.toLp 2 (w i)) ∧
        Measurable (fun x => largestCoordinate (anchorCoordinates w x)) ∧
        Integrable (fun x => ‖WithLp.toLp 2 x -
          WithLp.toLp 2 (w (largestCoordinate (anchorCoordinates w x)))‖)
          (compactBallRawLaw μ : Measure (Fin d → ℝ)) ∧
        (∫ x, ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (largestCoordinate (anchorCoordinates w x)))‖
          ∂(compactBallRawLaw μ : Measure (Fin d → ℝ))) ≤
          ((d + 1 : ℝ) * (d + 2 : ℝ)) *
            ((d + 1 : ℝ) * entryDefect K / (1 + (d + 1 : ℝ) * entryDefect K)) := by
  obtain ⟨μ, φ, hφ, hlim, hraw, hball, hcenter, hbright,
      hboundary, hsupport, hhorizontal, hB, w, hdet, hw, ha, hm, hi, he⟩ :=
    actual_body_joint_polar_horizontal_assignment K hc hconv hb
  have hA := actual_body_horizontal_moment_pos_of_compact_limit K hc hconv hb μ φ hφ hlim
  have hentry := actual_body_entryA_of_compact_limit K hc hconv hb μ φ hφ hlim
  have hX := unit_ball_coordinate_integrable (compactBallRawLaw μ : Measure (Fin d → ℝ)) hball
  refine ⟨μ, φ, hφ, hlim, hraw, hball, hcenter, hbright, hboundary, hsupport, hhorizontal,
    hA, hentry, entryDefect_iid_moment_identity K _ hA hentry,
    hB, w, hdet, hw, ha, hm, hi, ?_⟩
  change (∫ x, ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (largestCoordinate (anchorCoordinates w x)))‖
    ∂(compactBallRawLaw μ : Measure (Fin d → ℝ))) ≤ ((d + 1 : ℝ) * (d + 2 : ℝ)) *
      determinantLawDefect (iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) d)
        (compactBallRawLaw μ : Measure (Fin d → ℝ)) id id /
        (∫ v : Fin (d + 1) → Fin d → ℝ,
          |liftedDeterminant (fun j => v j.succ) (v 0)|
          ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) (d + 1)) at he
  rw [mul_div_assoc, entryDefect_iid_defect_ratio K _ hX hcenter hA hentry] at he
  exact he

end Entry005
