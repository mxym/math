import SemanticControls
open Set ContinuumRemainder IndependentRemainderControls
example : LogSyndetic (∅ : Set ℝ) := by
  have h := empty_not_syndetic
  simp_all
