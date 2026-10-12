import Entry005.ClippedAssignmentKernel
import Entry005.UnitBallAnchorChain
import Entry005.IidWeightedAnchorSelection
import Entry005.SelectedAnchorSimplex
import Entry005.IidAnchorSpanningSupport
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Entry005

/-- The actual determinant witness controls Euclidean assignment with factor 2,
without an inverse-determinant coefficient bound or any roundness assumption. -/
theorem unit_ball_clipped_actual_witness_assignment {d : ℕ}
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hball : ∀ᵐ x ∂ν, ‖WithLp.toLp 2 x‖ ≤ 1)
    (w : Fin (d + 1) → Fin d → ℝ)
    (hw : ∀ i, ‖WithLp.toLp 2 (w i)‖ ≤ 1)
    (hdet : (anchorMatrix w).det ≠ 0) :
    Measurable (fun x => largestCoordinate (anchorCoordinates w x)) ∧
      Integrable (fun x => ‖WithLp.toLp 2 x -
        WithLp.toLp 2 (w (largestCoordinate (anchorCoordinates w x)))‖) ν ∧
      (∫ x, ‖WithLp.toLp 2 x -
        WithLp.toLp 2 (w (largestCoordinate (anchorCoordinates w x)))‖ ∂ν) ≤
        2 * ((∫ x, determinantAssignmentWitness w x ∂ν) / |(anchorMatrix w).det|) := by
  have hrec (x : Fin d → ℝ) :
      ∑ i, anchorCoordinates w x i • WithLp.toLp 2 (w i) = WithLp.toLp 2 x := by
    simpa only [WithLp.toLp_sum, WithLp.toLp_smul] using
      congrArg (WithLp.toLp 2) (anchor_coordinates_reconstruct w hdet x)
  apply integrated_clipped_largest_assignment_error (by norm_num) _ _
    (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable
    (measurable_anchor_coordinates w)
    (Filter.Eventually.of_forall (anchor_coordinates_sum w hdet))
    (Filter.Eventually.of_forall hrec)
    (assignment_cost_integrable ν (anchorCoordinates w)
      (integrable_anchor_coordinates ν (unit_ball_coordinate_integrable ν hball) w))
    (integrated_actual_determinant_assignment_cost ν
      (unit_ball_coordinate_integrable ν hball) w hdet)
  · intro i j
    exact (norm_sub_le _ _).trans (by linarith [hw i, hw j])
  · filter_upwards [hball] with x hx
    intro i
    exact (norm_sub_le _ _).trans (by linarith [hw i])

/-- The stronger first absolute-moment assignment. There is no directional
dispersion, covariance, second determinant moment or coefficient bound premise. -/
theorem unit_ball_first_moment_assignment {d : ℕ}
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hball : ∀ᵐ x ∂ν, ‖WithLp.toLp 2 x‖ ≤ 1)
    (hcenter : ∀ i, (∫ x : Fin d → ℝ, x i ∂ν) = 0)
    (hB : 0 < ∫ w : Fin (d + 1) → Fin d → ℝ,
      |(anchorMatrix w).det| ∂iidLaw ν (d + 1)) :
    ∃ w : Fin (d + 1) → Fin d → ℝ, ∃ _hdet : (anchorMatrix w).det ≠ 0,
      (∀ i, w i ∈ ν.support ∧ ‖WithLp.toLp 2 (w i)‖ ≤ 1) ∧
      AffineIndependent ℝ (fun i => WithLp.toLp 2 (w i)) ∧
      Measurable (fun x => largestCoordinate (anchorCoordinates w x)) ∧
      Integrable (fun x => ‖WithLp.toLp 2 x -
        WithLp.toLp 2 (w (largestCoordinate (anchorCoordinates w x)))‖) ν ∧
      (∫ x, ‖WithLp.toLp 2 x -
        WithLp.toLp 2 (w (largestCoordinate (anchorCoordinates w x)))‖ ∂ν) ≤
        ((((d : ℝ) + 1) * ((d : ℝ) + 2)) * determinantLawDefect (iidLaw ν d) ν id id) /
          (∫ v : Fin (d + 1) → Fin d → ℝ,
            |(anchorMatrix v).det| ∂iidLaw ν (d + 1)) := by
  obtain ⟨w, hw, hV, hratio⟩ := unit_ball_volume_weighted_paper_witness_anchor ν hball hcenter hB
  have hdet : (anchorMatrix w).det ≠ 0 := abs_pos.mp hV
  obtain ⟨hr, hi, he⟩ := unit_ball_clipped_actual_witness_assignment ν hball w
    (fun i => (hw i).2) hdet
  refine ⟨w, hdet, hw, selected_anchor_affineIndependent w hdet, hr, hi, he.trans ?_⟩
  calc
    2 * ((∫ x, determinantAssignmentWitness w x ∂ν) / |(anchorMatrix w).det|) ≤
        2 * (((((d : ℝ) + 1) * ((d : ℝ) + 2) / 2) *
          determinantLawDefect (iidLaw ν d) ν id id) /
            (∫ v : Fin (d + 1) → Fin d → ℝ,
              |(anchorMatrix v).det| ∂iidLaw ν (d + 1))) :=
      mul_le_mul_of_nonneg_left hratio (by norm_num)
    _ = _ := by ring

/-- Full-dimensional support supplies first-moment positivity. The stronger
assignment therefore needs no assumed determinant moment lower bound. -/
theorem unit_ball_spanning_first_moment_assignment {d : ℕ}
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hball : ∀ᵐ x ∂ν, ‖WithLp.toLp 2 x‖ ≤ 1)
    (hcenter : ∀ i, (∫ x : Fin d → ℝ, x i ∂ν) = 0)
    (hspan : affineSpan ℝ ((WithLp.toLp 2) '' ν.support) = ⊤) :
    ∃ w : Fin (d + 1) → Fin d → ℝ,
      (∀ i, w i ∈ ν.support ∧ ‖WithLp.toLp 2 (w i)‖ ≤ 1) ∧
      AffineIndependent ℝ (fun i => WithLp.toLp 2 (w i)) ∧
      Measurable (fun x => largestCoordinate (anchorCoordinates w x)) ∧
      Integrable (fun x => ‖WithLp.toLp 2 x -
        WithLp.toLp 2 (w (largestCoordinate (anchorCoordinates w x)))‖) ν ∧
      (∫ x, ‖WithLp.toLp 2 x -
        WithLp.toLp 2 (w (largestCoordinate (anchorCoordinates w x)))‖ ∂ν) ≤
        ((((d : ℝ) + 1) * ((d : ℝ) + 2)) * determinantLawDefect (iidLaw ν d) ν id id) /
          (∫ v : Fin (d + 1) → Fin d → ℝ,
            |(anchorMatrix v).det| ∂iidLaw ν (d + 1)) := by
  have hB := iid_anchor_volume_integral_pos_of_euclidean_support_affineSpan_top ν
    (unit_ball_coordinate_integrable ν hball) hspan
  obtain ⟨w, _, hw, ha, hr, hi, he⟩ := unit_ball_first_moment_assignment ν hball hcenter hB
  exact ⟨w, hw, ha, hr, hi, he⟩

end Entry005
