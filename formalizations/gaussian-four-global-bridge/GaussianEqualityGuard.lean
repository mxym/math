import GaussianBalancedValue

/-! A checked guard against dropping the equality hypothesis in fractional
purification: the uniform fractional partition is never an indicator label. -/
open MeasureTheory ProbabilityTheory Set
namespace GaussianFourGlobal
open GaussianMeasureBridge

theorem uniform_not_ae_indicator {d : ℕ} (A : Set (Space d)) (i : Fin 4) :
    ¬ (∀ᵐ x ∂gaussian d, (uniformPartition d).labels i x = A.indicator (fun _ => (1 : ℝ)) x) := by
  intro h
  obtain ⟨x, hx⟩ := h.exists
  by_cases ha : x ∈ A <;> norm_num [uniformPartition, ha] at hx

end GaussianFourGlobal