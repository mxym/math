import SemanticControls

open Set MeasureTheory ContinuumGeometric ContinuumRemainder
set_option autoImplicit false
namespace IndependentRemainderControls

-- Each weakening is impossible for every E, not merely one inconvenient E.
theorem nonzero_coefficient_is_essential (E : Set ℝ) :
    ¬ (∀ (s α y c M : ℝ) (f : ℝ → ℝ),
      0 < s → 0 < α → 0 ≤ M →
      PowerRemainderOn dyadicInputs f y c s α M →
      ∀ ρ : ℝ, 0 < ρ → (TailValuesOutside dyadicInputs f E ρ).Infinite) := by
  intro h
  exact (constant_tail_values_finite dyadicInputs E 1 0).not_infinite
    (h 1 1 0 0 0 (fun _ => 0) (by norm_num) (by norm_num) (by norm_num)
      zero_coefficient_constant_remainder 1 (by norm_num))

theorem positive_remainder_rate_is_essential (E : Set ℝ) :
    ¬ (∀ (s α y c M : ℝ) (f : ℝ → ℝ),
      0 < s → 0 ≤ α → c ≠ 0 → 0 ≤ M →
      PowerRemainderOn dyadicInputs f y c s α M →
      ∀ ρ : ℝ, 0 < ρ → (TailValuesOutside dyadicInputs f E ρ).Infinite) := by
  intro h
  exact (constant_tail_values_finite dyadicInputs E 1 0).not_infinite
    (h 1 0 0 1 1 (fun _ => 0) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) zero_rate_constant_remainder 1 (by norm_num))

theorem positive_leading_power_is_essential (E : Set ℝ) :
    ¬ (∀ (s α y c M : ℝ) (f : ℝ → ℝ),
      0 ≤ s → 0 < α → c ≠ 0 → 0 ≤ M →
      PowerRemainderOn dyadicInputs f y c s α M →
      ∀ ρ : ℝ, 0 < ρ → (TailValuesOutside dyadicInputs f E ρ).Infinite) := by
  intro h
  exact (constant_tail_values_finite dyadicInputs E 1 1).not_infinite
    (h 0 1 0 1 0 (fun _ => 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) zero_power_constant_remainder 1 (by norm_num))

-- Closing the inner buffer would lose the strict slack at the outer boundary.
theorem closed_inner_buffer_breaks_outer :
    (1:ℝ) ∈ Metric.closedBall 0 1 ∧ |(1:ℝ)| ≤ 1 ∧
      (1:ℝ)+1 ∉ Metric.thickening 2 ({0}:Set ℝ) := by
  refine ⟨by norm_num [Metric.mem_closedBall, Real.dist_eq], by norm_num, ?_⟩
  intro h
  obtain ⟨z, hz, hd⟩ := Metric.mem_thickening_iff.1 h
  have hz0 : z = 0 := by simpa using hz
  subst z
  norm_num [Real.dist_eq] at hd

#print axioms nonzero_coefficient_is_essential
#print axioms positive_remainder_rate_is_essential
#print axioms positive_leading_power_is_essential
#print axioms closed_inner_buffer_breaks_outer
end IndependentRemainderControls
