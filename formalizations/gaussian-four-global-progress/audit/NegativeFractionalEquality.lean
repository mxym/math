import GaussianEqualityGuard
open MeasureTheory ProbabilityTheory Set GaussianMeasureBridge GaussianFourGlobal
-- Deliberately false: uniform one-quarter labels are not hard labels.
example : ∀ᵐ x ∂gaussian 3,
    (uniformPartition 3).labels 0 x = (univ : Set (Space 3)).indicator (fun _ => (1 : ℝ)) x := by
  simp [uniformPartition]
