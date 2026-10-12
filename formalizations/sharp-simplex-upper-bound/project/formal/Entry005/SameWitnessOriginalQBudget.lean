import Entry005.SharpConstantGates
import Entry005.SelectedAnchorHullRoundness

/-! Scalar transfer and hull roundness for the SAME supplied assignment.
This file never selects a new law or a new point tuple and does not assume
the determinant-selected Q witness is the pyramid-selected witness. -/

noncomputable section
open MeasureTheory Metric
namespace Entry005

theorem original_one_le_M {d : ℕ} (hd : 1 ≤ d) : 1 ≤ M d := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hR : 1 ≤ R0 d := by unfold R0; nlinarith
  have hx : 1 ≤ (d : ℝ) * R0 d := by nlinarith
  have hp : (1 : ℝ) ≤ ((d : ℝ) * R0 d) ^ d := one_le_pow₀ hx
  simpa only [M, b, one_div_one_div] using
    (show (1 : ℝ) ≤ 4 * ((d : ℝ) * R0 d) ^ d by nlinarith)

theorem original_Q_dominates_strong_assignment_coefficient {d : ℕ} (hd : 1 ≤ d) :
    (d + 1 : ℝ) * (d + 2 : ℝ) ≤ Q d := by
  have h8 : (1 : ℝ) ≤ (8 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have hM : (1 : ℝ) ≤ M d ^ (4 * d) := one_le_pow₀ (original_one_le_M hd)
  have hp : (1 : ℝ) ≤ (8 : ℝ) ^ d * M d ^ (4 * d) := by nlinarith
  have hc : 0 ≤ (d + 1 : ℝ) * (d + 2 : ℝ) := by positivity
  have h := mul_le_mul_of_nonneg_left hp hc
  simpa only [Q, mul_one, mul_assoc] using h

theorem strong_ratio_assignment_le_original_Q_budget {d : ℕ} (hd : 1 ≤ d)
    (e : ℝ) (he : 0 ≤ e) :
    ((d + 1 : ℝ) * (d + 2 : ℝ)) *
      ((d + 1 : ℝ) * e / (1 + (d + 1 : ℝ) * e)) ≤ Q d * (d + 1) * e := by
  have hx : 0 ≤ (d + 1 : ℝ) * e := by positivity
  have hden : 0 < 1 + (d + 1 : ℝ) * e := by positivity
  have hratio : (d + 1 : ℝ) * e / (1 + (d + 1 : ℝ) * e) ≤
      (d + 1 : ℝ) * e := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  calc
    _ ≤ ((d + 1 : ℝ) * (d + 2 : ℝ)) * ((d + 1 : ℝ) * e) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ ≤ Q d * ((d + 1 : ℝ) * e) :=
      mul_le_mul_of_nonneg_right
        (original_Q_dominates_strong_assignment_coefficient hd) hx
    _ = Q d * (d + 1) * e := by ring

/-- The strong assignment and original small-error threshold give Q control
and b-ball hull roundness for the same supplied law, tuple and assignment. -/
theorem same_witness_original_Q_and_round_hull {d : ℕ} (hd : 1 ≤ d)
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hball : ∀ᵐ x ∂ν, ‖WithLp.toLp 2 x‖ ≤ 1)
    (w : Fin (d + 1) → Fin d → ℝ)
    (hw : ∀ i, ‖WithLp.toLp 2 (w i)‖ ≤ 1)
    (r : (Fin d → ℝ) → Fin (d + 1)) (hr : Measurable r)
    (hround : ∀ u : Space d, ‖u‖ = 1 →
      2 * b d ≤ negativeIntegral ν (fun x => dotProduct u x))
    (e : ℝ) (he : 0 ≤ e) (hsmall : e ≤ eSharp d)
    (hcost : (∫ x, ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (r x))‖ ∂ν) ≤
      ((d + 1 : ℝ) * (d + 2 : ℝ)) *
        ((d + 1 : ℝ) * e / (1 + (d + 1 : ℝ) * e))) :
    (∫ x, ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (r x))‖ ∂ν) ≤
      Q d * (d + 1) * e ∧
    closedBall (0 : Space d) (b d) ⊆
      convexHull ℝ (Set.range (fun i => WithLp.toLp 2 (w i))) := by
  have hQ := hcost.trans (strong_ratio_assignment_le_original_Q_budget hd e he)
  have hb : Q d * (d + 1) * e ≤ b d :=
    (original_small_error_budget hd e hsmall).trans (min_le_left _ _)
  exact ⟨hQ, unit_ball_selected_anchor_ball_subset_convexHull ν hball w hw r hr
    (b_pos hd) hround (hQ.trans hb)⟩

end Entry005

