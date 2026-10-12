import ContinuumRemainder.FinalProof
import SemanticControls

open Set MeasureTheory ContinuumGeometric ContinuumRemainder
set_option autoImplicit false
namespace IndependentRemainderControls

-- A kernel-checked application to an explicit nonempty family and nonzero error.
-- The output is one actual E with the full topology and shifted density package.
theorem explicit_nonvacuous_final_target :
    ∃ E : Set ℝ, IsClosed E ∧ interior E = ∅ ∧ OnePeriodic E ∧
      (∀ x : ℝ, ENNReal.ofReal (1 / 2) < volume (E ∩ Icc x (x+1))) ∧
      ∀ ρ : ℝ, 0 < ρ →
        (TailValuesOutside dyadicInputs nonlinearExample E ρ).Infinite := by
  obtain ⟨E, hc, hi, hp, hm, ha⟩ := continuum_power_target Unit
    (fun _ => dyadicInputs) (fun _ => ⟨dyadicInputs_positive, dyadicInputs_syndetic⟩)
    (1/2) (by norm_num) (by norm_num)
  refine ⟨E, hc, hi, hp, ?_, ?_⟩
  · convert hm using 1 <;> norm_num
  · intro ρ hρ
    exact ha () (1/2) (1/3) 7 (-2) 1 nonlinearExample
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      nonlinearExample_remainder ρ hρ

-- Nonempty index and finite budget conditions are discharged, not presumed.
theorem explicit_compact_corollary :
    ∃ K : Set ℝ, IsCompact K ∧ K ⊆ Icc (0:ℝ) 1 ∧ interior K=∅ ∧
      ENNReal.ofReal (1/2) < volume K ∧
      AvoidsPowerRemainderTails (fun _ : Unit => dyadicInputs) K := by
  convert compact_power_avoidance (fun _ : Unit => dyadicInputs)
    (fun _ => ⟨dyadicInputs_positive, dyadicInputs_syndetic⟩)
    (1/2) (by norm_num) (by norm_num) using 1 <;> norm_num

#print axioms explicit_nonvacuous_final_target
#print axioms explicit_compact_corollary
end IndependentRemainderControls
