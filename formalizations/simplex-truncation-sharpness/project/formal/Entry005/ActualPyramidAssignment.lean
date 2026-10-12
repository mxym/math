import Entry005.ActualPyramidDefect

noncomputable section
open Metric MeasureTheory Module
open scoped BigOperators
namespace Entry005
variable {d : ℕ} [Nontrivial (Space d)]

/-- One actual compact-limit cone law supplies A, B, D, brightness and the
quantitative assignment. The assignment is applied to that same law directly;
no independently chosen existential probability measures are identified. -/
theorem actual_body_geometric_first_moment_assignment
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K) :
    ∃ ν : ProbabilityMeasure (Fin d → ℝ),
      (∀ᵐ x ∂(ν : Measure (Fin d → ℝ)), ‖WithLp.toLp 2 x‖ ≤ 1) ∧
      (∀ i, (∫ x, x i ∂(ν : Measure (Fin d → ℝ))) = 0) ∧
      (∀ u : Space d, ‖u‖ = 1 → negativeIntegral (ν : Measure (Fin d → ℝ))
        (fun x => dotProduct (fun j => u j) x) =
        projectionVolumeSet K u / ((finrank ℝ (Space d) : ℝ) * (volume K).toReal)) ∧
      (∫ w, |horizontalDeterminant w| ∂iidLaw (ν : Measure (Fin d → ℝ)) d) =
        (d.factorial : ℝ) / ((d : ℝ) * (volume K).toReal) ^ d *
          (volume (projectionBodySet K)).toReal ∧
      0 < (∫ w, |horizontalDeterminant w| ∂iidLaw (ν : Measure (Fin d → ℝ)) d) ∧
      entryA K =
        (∫ w : Fin (d + 1) → Fin d → ℝ,
          |liftedDeterminant (fun j => w j.succ) (w 0)| ∂iidLaw (ν : Measure (Fin d → ℝ)) (d + 1)) /
        ((d + 1 : ℝ) * (∫ w, |horizontalDeterminant w| ∂iidLaw (ν : Measure (Fin d → ℝ)) d)) ∧
      determinantLawDefect (iidLaw (ν : Measure (Fin d → ℝ)) d) (ν : Measure (Fin d → ℝ)) id id =
        (d + 1 : ℝ) * (∫ w, |horizontalDeterminant w| ∂iidLaw (ν : Measure (Fin d → ℝ)) d) * entryDefect K ∧
      ∃ w : Fin (d + 1) → Fin d → ℝ, ∃ _hdet : (anchorMatrix w).det ≠ 0,
        (∀ i, w i ∈ (ν : Measure (Fin d → ℝ)).support ∧ ‖WithLp.toLp 2 (w i)‖ ≤ 1) ∧
        AffineIndependent ℝ (fun i => WithLp.toLp 2 (w i)) ∧
        Measurable (fun x => largestCoordinate (anchorCoordinates w x)) ∧
        Integrable (fun x => ‖WithLp.toLp 2 x -
          WithLp.toLp 2 (w (largestCoordinate (anchorCoordinates w x)))‖) (ν : Measure (Fin d → ℝ)) ∧
        (∫ x, ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (largestCoordinate (anchorCoordinates w x)))‖
          ∂(ν : Measure (Fin d → ℝ))) ≤
          ((d + 1 : ℝ) * (d + 2 : ℝ)) *
            ((d + 1 : ℝ) * entryDefect K / (1 + (d + 1 : ℝ) * entryDefect K)) := by
  obtain ⟨ν, hball, hcenter, hbright, hhorizontal, hA, hentry⟩ :=
    actual_body_cone_law_with_pyramid_first_moment K hc hconv hb
  have hX := unit_ball_coordinate_integrable (ν : Measure (Fin d → ℝ)) hball
  have hB := hA.trans_le (centered_iid_lifted_moment_ge_horizontal _ hX hcenter)
  have hBanchor : 0 < (∫ w : Fin (d + 1) → Fin d → ℝ,
      |(anchorMatrix w).det| ∂iidLaw (ν : Measure (Fin d → ℝ)) (d + 1)) := hB
  obtain ⟨w, hdet, hw, ha, hm, hi, he⟩ :=
    unit_ball_first_moment_assignment (ν : Measure (Fin d → ℝ)) hball hcenter hBanchor
  refine ⟨ν, hball, hcenter, hbright, hhorizontal, hA, hentry,
    entryDefect_iid_moment_identity K _ hA hentry, w, hdet, hw, ha, hm, hi, ?_⟩
  change (∫ x, ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (largestCoordinate (anchorCoordinates w x)))‖
    ∂(ν : Measure (Fin d → ℝ))) ≤ ((d + 1 : ℝ) * (d + 2 : ℝ)) *
      determinantLawDefect (iidLaw (ν : Measure (Fin d → ℝ)) d) (ν : Measure (Fin d → ℝ)) id id /
        (∫ v : Fin (d + 1) → Fin d → ℝ,
          |liftedDeterminant (fun j => v j.succ) (v 0)| ∂iidLaw (ν : Measure (Fin d → ℝ)) (d + 1)) at he
  rw [mul_div_assoc, entryDefect_iid_defect_ratio K _ hX hcenter hA hentry] at he
  exact he

end Entry005
