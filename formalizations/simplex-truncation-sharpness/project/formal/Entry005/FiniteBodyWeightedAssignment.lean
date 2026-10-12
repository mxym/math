import Entry005.FiniteHalfspaceConeLaw
import Entry005.FirstMomentAssignment
import Entry005.ActualAssignmentAssembly

noncomputable section
open Metric MeasureTheory Module
open scoped BigOperators

namespace Entry005

/-- A genuine round unit-ball law has positive first affine determinant
moment. Its lower moment is derived from an actual nonsingular support tuple,
not asserted as a hypothesis. -/
theorem unit_ball_round_affine_first_moment_pos {d : ℕ} (hd : 1 ≤ d)
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hball : ∀ᵐ x ∂ν, ‖WithLp.toLp 2 x‖ ≤ 1)
    (hcenter : ∀ i, (∫ x : Fin d → ℝ, x i ∂ν) = 0)
    {β : ℝ} (hβ : 0 < β)
    (hround : ∀ u : Space d, ‖u‖ = 1 →
      2 * β ≤ negativeIntegral ν (fun x => dotProduct u x)) :
    0 < ∫ w : Fin (d + 1) → Fin d → ℝ,
      |(anchorMatrix w).det| ∂iidLaw ν (d + 1) := by
  obtain ⟨w, hw, hV, _, _, _⟩ :=
    unit_ball_round_actual_assignment hd ν hball hcenter hβ hround
  have hdet : (anchorMatrix w).det ≠ 0 :=
    abs_pos.mp ((pow_pos hβ d).trans_le hV)
  exact iid_anchor_volume_integral_pos_of_support_det_ne_zero ν
    (unit_ball_coordinate_integrable ν hball) w (fun i => (hw i).1) hdet

section ActualFiniteBody

variable {ι : Type*} [Fintype ι] {d : ℕ} [Nontrivial (Space d)]

/-- The actual finite body's normalized cone law has positive first affine
determinant moment, using proved facet mass, balance, brightness and ball
containment. No moment or directional-roundness premise is supplied. -/
theorem finite_body_cone_affine_first_moment_pos
    (n : ι → Space d) (h : ι → ℝ) (hn : ∀ i, ‖n i‖ = 1)
    (hinj : Function.Injective n) (hc : IsCompact (finiteHalfspaceSet n h))
    (hb : closedBall (0 : Space d) 1 ⊆ finiteHalfspaceSet n h) :
    0 < ∫ w : Fin (d + 1) → Fin d → ℝ,
      |(anchorMatrix w).det| ∂iidLaw (finiteHalfspaceConeLaw n h) (d + 1) := by
  have hh : ∀ i, 0 < h i := fun i =>
    zero_lt_one.trans_le (finite_halfspace_unit_ball_heights n h hn hb i)
  let _ : IsProbabilityMeasure (finiteHalfspaceConeLaw n h) :=
    finite_halfspace_cone_probability n h hn hh hinj hc
  have hd : 1 ≤ d := by
    have hp : 0 < d := by simpa [Space] using (finrank_pos : 0 < finrank ℝ (Space d))
    omega
  let γ : ℝ := (volume (closedBall (0 : Space (d - 1)) 1)).toReal /
    ((finrank ℝ (Space d) : ℝ) * (volume (finiteHalfspaceSet n h)).toReal)
  have hγ : 0 < γ := finite_halfspace_cone_round_coefficient_pos n h hn hh hc
  apply unit_ball_round_affine_first_moment_pos hd (finiteHalfspaceConeLaw n h)
    (finite_halfspace_cone_ae_unit_ball n h hn hb)
    (finite_halfspace_cone_centered n h hn hh hinj hc)
    (show 0 < γ / 2 by positivity)
  intro u hu
  have hl := finite_halfspace_cone_round_lower n h hn hh hinj hc hb u hu
  change γ ≤ _ at hl
  calc
    2 * (γ / 2) = γ := by ring
    _ ≤ _ := hl

/-- Strong weighted assignment for the actual cone law of a compact finite
halfspace body containing its unit ball. Every probabilistic input, including
the first-moment denominator's positivity, follows from actual geometry. -/
theorem finite_body_cone_first_moment_assignment
    (n : ι → Space d) (h : ι → ℝ) (hn : ∀ i, ‖n i‖ = 1)
    (hinj : Function.Injective n) (hc : IsCompact (finiteHalfspaceSet n h))
    (hb : closedBall (0 : Space d) 1 ⊆ finiteHalfspaceSet n h) :
    ∃ w : Fin (d + 1) → Fin d → ℝ, ∃ _hdet : (anchorMatrix w).det ≠ 0,
      (∀ i, w i ∈ (finiteHalfspaceConeLaw n h).support ∧
        ‖WithLp.toLp 2 (w i)‖ ≤ 1) ∧
      AffineIndependent ℝ (fun i => WithLp.toLp 2 (w i)) ∧
      Measurable (fun x => largestCoordinate (anchorCoordinates w x)) ∧
      Integrable (fun x => ‖WithLp.toLp 2 x -
        WithLp.toLp 2 (w (largestCoordinate (anchorCoordinates w x)))‖)
          (finiteHalfspaceConeLaw n h) ∧
      (∫ x, ‖WithLp.toLp 2 x -
        WithLp.toLp 2 (w (largestCoordinate (anchorCoordinates w x)))‖
          ∂finiteHalfspaceConeLaw n h) ≤
        ((((d : ℝ) + 1) * ((d : ℝ) + 2)) *
          determinantLawDefect (iidLaw (finiteHalfspaceConeLaw n h) d)
            (finiteHalfspaceConeLaw n h) id id) /
          (∫ v : Fin (d + 1) → Fin d → ℝ,
            |(anchorMatrix v).det| ∂iidLaw (finiteHalfspaceConeLaw n h) (d + 1)) := by
  have hh : ∀ i, 0 < h i := fun i =>
    zero_lt_one.trans_le (finite_halfspace_unit_ball_heights n h hn hb i)
  let _ : IsProbabilityMeasure (finiteHalfspaceConeLaw n h) :=
    finite_halfspace_cone_probability n h hn hh hinj hc
  exact unit_ball_first_moment_assignment (finiteHalfspaceConeLaw n h)
    (finite_halfspace_cone_ae_unit_ball n h hn hb)
    (finite_halfspace_cone_centered n h hn hh hinj hc)
    (finite_body_cone_affine_first_moment_pos n h hn hinj hc hb)

end ActualFiniteBody
end Entry005
