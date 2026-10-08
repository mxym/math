import Entry005.UnitBallAnchorChain
import Entry005.PaperWitnessTransport
import Entry005.Constants
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Actual Euclidean assignment from actual determinant witnesses. No final
assignment budget is assumed: it follows from the Cramer-coordinate and
integrated witness estimates already proved in this project. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Entry005

theorem unit_ball_actual_witness_assignment {d : ℕ} (hd : 1 ≤ d)
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
        2 * ((2 : ℝ) ^ d / |(anchorMatrix w).det|) *
          ((∫ x, determinantAssignmentWitness w x ∂ν) / |(anchorMatrix w).det|) := by
  let : MeasurableSpace (EuclideanSpace ℝ (Fin d)) := borel _
  let : BorelSpace (EuclideanSpace ℝ (Fin d)) := ⟨rfl⟩
  have hV : 0 < |(anchorMatrix w).det| := abs_pos.mpr hdet
  have hL : 1 ≤ (2 : ℝ) ^ d / |(anchorMatrix w).det| := by
    apply (le_div_iff₀ hV).2
    simpa only [one_mul, anchorMatrix] using unit_ball_anchor_determinant hd w hw
  have hrec (x : Fin d → ℝ) :
      ∑ i, anchorCoordinates w x i • WithLp.toLp 2 (w i) = WithLp.toLp 2 x := by
    simpa only [WithLp.toLp_sum, WithLp.toLp_smul] using
      congrArg (WithLp.toLp 2) (anchor_coordinates_reconstruct w hdet x)
  apply integrated_largest_assignment_error hw
    (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable
    (measurable_anchor_coordinates w) hL
    (Filter.Eventually.of_forall (anchor_coordinates_sum w hdet))
    (Filter.Eventually.of_forall hrec) _
    (assignment_cost_integrable ν (anchorCoordinates w)
      (integrable_anchor_coordinates ν (unit_ball_coordinate_integrable ν hball) w))
    (integrated_actual_determinant_assignment_cost ν
      (unit_ball_coordinate_integrable ν hball) w hdet)
  filter_upwards [hball] with x hx
  exact unit_ball_anchor_coordinate_bound hd w hw hdet x hx

theorem unit_ball_determinant_law_defect_nonneg {d : ℕ}
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hball : ∀ᵐ x ∂ν, ‖WithLp.toLp 2 x‖ ≤ 1)
    (hcenter : ∀ i, (∫ x : Fin d → ℝ, x i ∂ν) = 0) :
    0 ≤ determinantLawDefect (iidLaw ν d) ν id id := by
  exact (centered_determinant_family_budget
    (unit_ball_coordinate_integrable ν hball) hcenter
    (measurable_lifted_determinant
      (fun i j => (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_fst))
      (fun i => (measurable_pi_apply i).comp measurable_snd))
    (iid_lifted_determinant_integrable id (unit_ball_coordinate_integrable ν hball))).1

/-- Actual support anchors and their measurable largest-coordinate assignment,
with the original explicit coefficient and no assumed assignment estimate. -/
theorem unit_ball_round_actual_assignment {d : ℕ} (hd : 1 ≤ d)
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hball : ∀ᵐ x ∂ν, ‖WithLp.toLp 2 x‖ ≤ 1)
    (hcenter : ∀ i, (∫ x : Fin d → ℝ, x i ∂ν) = 0)
    {β : ℝ} (hβ : 0 < β)
    (hround : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 →
      2 * β ≤ negativeIntegral ν (fun x => dotProduct u x)) :
    ∃ w : Fin (d + 1) → Fin d → ℝ,
      (∀ i, w i ∈ ν.support ∧ ‖WithLp.toLp 2 (w i)‖ ≤ 1) ∧
      β ^ d ≤ |(anchorMatrix w).det| ∧
      Measurable (fun x => largestCoordinate (anchorCoordinates w x)) ∧
      Integrable (fun x => ‖WithLp.toLp 2 x -
        WithLp.toLp 2 (w (largestCoordinate (anchorCoordinates w x)))‖) ν ∧
      (∫ x, ‖WithLp.toLp 2 x -
        WithLp.toLp 2 (w (largestCoordinate (anchorCoordinates w x)))‖ ∂ν) ≤
        (((d : ℝ) + 1) * ((d : ℝ) + 2) * (8 : ℝ) ^ d / β ^ (4 * d)) *
          determinantLawDefect (iidLaw ν d) ν id id := by
  let D := determinantLawDefect (iidLaw ν d) ν id id
  let N := (((d : ℝ) + 1) * ((d : ℝ) + 2) / 2)
  obtain ⟨w, hw, hV, hH⟩ := unit_ball_round_witness_anchor hd ν hball hcenter hβ
    hround (paperWitnessPermutation d)
  change β ^ d ≤ |(anchorMatrix w).det| at hV
  have hβd : 0 < β ^ d := pow_pos hβ d
  have hVpos : 0 < |(anchorMatrix w).det| := hβd.trans_le hV
  have hdet : (anchorMatrix w).det ≠ 0 := abs_pos.mp hVpos
  have hD : 0 ≤ D := unit_ball_determinant_law_defect_nonneg ν hball hcenter
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hW : (∫ x, determinantAssignmentWitness w x ∂ν) ≤
      (N * D) * (4 : ℝ) ^ d / (β ^ d) ^ 2 := by
    rw [integral_determinant_assignment_witness_eq_transportedWitnessSum]
    simpa only [paper_witness_index_card_real, N, D] using hH
  have hbudget : 0 ≤ (N * D) * (4 : ℝ) ^ d / (β ^ d) ^ 2 := by
    exact div_nonneg (mul_nonneg (mul_nonneg hN hD) (by positivity)) (by positivity)
  have hL : (2 : ℝ) ^ d / |(anchorMatrix w).det| ≤ (2 : ℝ) ^ d / β ^ d :=
    div_le_div_of_nonneg_left (by positivity) hβd hV
  have hWdiv : (∫ x, determinantAssignmentWitness w x ∂ν) / |(anchorMatrix w).det| ≤
      ((N * D) * (4 : ℝ) ^ d / (β ^ d) ^ 2) / β ^ d := by
    exact (div_le_div_of_nonneg_right hW hVpos.le).trans
      (div_le_div_of_nonneg_left hbudget hβd hV)
  obtain ⟨hr, hi, he⟩ := unit_ball_actual_witness_assignment hd ν hball w
    (fun i => (hw i).2) hdet
  refine ⟨w, hw, hV, hr, hi, he.trans ?_⟩
  calc
    2 * ((2 : ℝ) ^ d / |(anchorMatrix w).det|) *
        ((∫ x, determinantAssignmentWitness w x ∂ν) / |(anchorMatrix w).det|) ≤
      2 * ((2 : ℝ) ^ d / |(anchorMatrix w).det|) *
        (((N * D) * (4 : ℝ) ^ d / (β ^ d) ^ 2) / β ^ d) :=
      mul_le_mul_of_nonneg_left hWdiv (by positivity)
    _ ≤ 2 * ((2 : ℝ) ^ d / β ^ d) *
        (((N * D) * (4 : ℝ) ^ d / (β ^ d) ^ 2) / β ^ d) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hL (by norm_num)) (div_nonneg hbudget hβd.le)
    _ = (((d : ℝ) + 1) * ((d : ℝ) + 2) * (8 : ℝ) ^ d / β ^ (4 * d)) * D := by
      have hpow : (2 : ℝ) ^ d * (4 : ℝ) ^ d = (8 : ℝ) ^ d := by
        rw [← mul_pow]; norm_num
      have hβpow : β ^ (4 * d) = (β ^ d) ^ 4 := by rw [← pow_mul]; congr 1; omega
      rw [hβpow]
      dsimp [N]
      field_simp
      nlinarith [hpow]

theorem original_Q_assignment {d : ℕ} (hd : 1 ≤ d)
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hball : ∀ᵐ x ∂ν, ‖WithLp.toLp 2 x‖ ≤ 1)
    (hcenter : ∀ i, (∫ x : Fin d → ℝ, x i ∂ν) = 0)
    (hround : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 →
      2 * b d ≤ negativeIntegral ν (fun x => dotProduct u x)) :
    ∃ w : Fin (d + 1) → Fin d → ℝ,
      (∀ i, w i ∈ ν.support ∧ ‖WithLp.toLp 2 (w i)‖ ≤ 1) ∧
      b d ^ d ≤ |(anchorMatrix w).det| ∧
      Measurable (fun x => largestCoordinate (anchorCoordinates w x)) ∧
      Integrable (fun x => ‖WithLp.toLp 2 x -
        WithLp.toLp 2 (w (largestCoordinate (anchorCoordinates w x)))‖) ν ∧
      (∫ x, ‖WithLp.toLp 2 x -
        WithLp.toLp 2 (w (largestCoordinate (anchorCoordinates w x)))‖ ∂ν) ≤
        Q d * determinantLawDefect (iidLaw ν d) ν id id := by
  have hQ : (((d : ℝ) + 1) * ((d : ℝ) + 2) * (8 : ℝ) ^ d / b d ^ (4 * d)) = Q d := by
    unfold Q M
    rw [div_pow, one_pow, div_eq_mul_inv, one_div]
  simpa only [hQ] using unit_ball_round_actual_assignment hd ν hball hcenter (b_pos hd) hround

end Entry005
