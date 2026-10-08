import SemanticControls
open Set ContinuumRemainder IndependentRemainderControls
example : (TailValuesOutside dyadicInputs (fun _ => (0:ℝ)) ∅ 1).Infinite := by
  have h := (constant_tail_values_finite dyadicInputs ∅ 1 0).not_infinite
  simp_all
