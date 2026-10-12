import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.Sequences

noncomputable section
open Filter MeasureTheory TopologicalSpace
open scoped Topology BoundedContinuousFunction

namespace Entry005

/-- Every sequence of actual probability measures on a compact metrizable
second-countable Borel space has a strictly increasing weakly convergent
subsequence. Compactness is supplied by Prokhorov, not assumed for the laws. -/
theorem compact_probability_tendsto_subseq {X : Type*}
    [TopologicalSpace X] [MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    (μ : ℕ → ProbabilityMeasure X) :
    ∃ ν : ProbabilityMeasure X, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 ν) := by
  obtain ⟨ν, _, φ, hφ, hν⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (ProbabilityMeasure X))).tendsto_subseq
      (fun n => Set.mem_univ (μ n))
  exact ⟨ν, φ, hφ, hν⟩

/-- The same actual subsequence, with weak convergence displayed as convergence
of every bounded continuous real integral. -/
theorem compact_probability_subsequence_integrals {X : Type*}
    [TopologicalSpace X] [MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    (μ : ℕ → ProbabilityMeasure X) :
    ∃ ν : ProbabilityMeasure X, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 ν) ∧
      ∀ f : X →ᵇ ℝ,
        Tendsto (fun n => ∫ x, f x ∂(μ (φ n) : Measure X)) atTop
          (𝓝 (∫ x, f x ∂(ν : Measure X))) := by
  obtain ⟨ν, φ, hφ, hν⟩ := compact_probability_tendsto_subseq μ
  exact ⟨ν, φ, hφ, hν, ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν⟩

end Entry005
