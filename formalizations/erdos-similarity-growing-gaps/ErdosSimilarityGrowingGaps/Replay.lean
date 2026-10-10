import ErdosSimilarityGrowingGaps.Basic
import ErdosSimilarityGrowingGaps.First
import ErdosSimilarityGrowingGaps.Corollary
import ErdosSimilarityGrowingGaps.Input
import ErdosSimilarityGrowingGaps.AnnulusSequence
import ErdosSimilarityGrowingGaps.VariableTree
import ErdosSimilarityGrowingGaps.FiniteRouting
import ErdosSimilarityGrowingGaps.Avoidance
import ErdosSimilarityGrowingGaps.TailAnalysis

namespace ErdosSimilarityGrowingGaps
open GrowingGap
open Set MeasureTheory

/-- Public replay roots for the formally closed sampling layer. -/
theorem replay_first_sample :
    ∀ (Z : LogScale) (v : ℝ),
      ∃ n : ℕ, v ≤ Z.z n ∧ ∀ m : ℕ, m < n → Z.z m < v := by
  intro Z v
  exact exists_first_ge Z v

theorem replay_annular_sampling :
    ∀ (Z : LogScale), ConsecutiveLogGapLittleO Z → AnnularFilling Z := by
  intro Z h
  exact consecutiveGap_implies_annularFilling h

theorem replay_late_window {Z : LogScale} (hW : WindowFilling Z)
    (R : ℕ) (hR : 2 ≤ R) (U₀ η : ℝ) (hU₀ : 0 < U₀) (hη : 0 < η) :
    ∃ U : ℕ, ∃ D : ℝ, U₀ ≤ (U : ℝ) ∧ 1 < Real.log (U : ℝ) ∧
      FillsAnnulus Z (U : ℝ) R D ∧
      D / Real.log (Real.log (U : ℝ)) < η :=
  hW.exists_late_annulus R hR U₀ η hU₀ hη

theorem replay_variable_tree_span (b g L : ℝ) (hb : 2 ≤ b) (hg : 0 ≤ g)
    (n : ℕ) : span b g L (n + 1) + 2 * g ≤ b * (2 * b) ^ n * (L + 2 * g) :=
  uniform_span b g L hb hg n

theorem replay_distinct_terminal_all_miss
    {I T : Type*} [Fintype I] [Fintype T] [DecidableEq T]
    (p : ℝ) (address : I → T) (hinj : Function.Injective address) :
    (∑ τ : T → Bool, bitTableWeight p τ *
      ∏ i, if τ (address i) = true then 0 else 1) =
      (1 - p) ^ Fintype.card I :=
  distinct_terminal_all_miss p address hinj

theorem replay_blocker_assembly
    {ι : Type*} [Countable ι] [Nonempty ι]
    {F : ι → LogScale} (B : BlockerFamily F)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hsum : ∑' i, B.budget i < ENNReal.ofReal ε) :
    ∃ E : Set ℝ, IsClosed E ∧ OnePeriodic E ∧ interior E = ∅ := by
  obtain ⟨E, hEc, hEp, hEi, _, _⟩ :=
    closed_periodic_avoidance_of_blockers B ε hε hε1 hsum
  exact ⟨E, hEc, hEp, hEi⟩

theorem replay_compact_blocker_assembly
    {ι : Type*} [Countable ι] [Nonempty ι]
    {F : ι → LogScale} (B : BlockerFamily F)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hsum : ∑' i, B.budget i < ENNReal.ofReal ε) :
    ∃ K : Set ℝ, IsCompact K ∧ K ⊆ Set.Icc (0 : ℝ) 1 ∧ interior K = ∅ := by
  obtain ⟨K, hKc, hKsub, hKi, _, _⟩ :=
    compact_restriction_of_blockers B ε hε hε1 hsum
  exact ⟨K, hKc, hKsub, hKi⟩

theorem replay_theorem2_assembly
    {ι : Type*} [Countable ι] [Nonempty ι]
    {F : ι → LogScale} (hB : WindowBlockerSpec F)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ E : Set ℝ, IsClosed E ∧ OnePeriodic E ∧ interior E = ∅ := by
  obtain ⟨E, hEc, hEp, hEi, _⟩ := theorem2_of_windowBlockerSpec hB ε hε hε1
  exact ⟨E, hEc, hEp, hEi⟩

theorem replay_tail_grid_reduction {Z : LogScale} {H : Set ℝ}
    (hH : GridWeakRobustBlocker Z H) : RobustBlocker Z H :=
  weakRobustBlocker_implies_robust (gridWeakRobustBlocker_implies_weak hH)

theorem replay_window_filling (Z : LogScale) (h : ConsecutiveLogGapLittleO Z) :
    WindowFilling Z := consecutiveGap_implies_windowFilling h

theorem replay_input_sequence (Z : LogScale) :
    (∀ n, 0 < input Z n) ∧ StrictAnti (input Z) ∧
      Filter.Tendsto (input Z) Filter.atTop (nhds 0) ∧
      ∀ n, -Real.logb 2 (input Z n) = Z.z n := by
  exact ⟨input_pos Z, input_strictAnti Z, input_tendsto_zero Z, input_logb Z⟩

#print axioms replay_window_filling
#print axioms replay_input_sequence
#print axioms replay_first_sample
#print axioms replay_annular_sampling
#print axioms replay_late_window
#print axioms replay_variable_tree_span
#print axioms replay_distinct_terminal_all_miss
#print axioms replay_blocker_assembly
#print axioms replay_compact_blocker_assembly
#print axioms replay_theorem2_assembly
#print axioms replay_tail_grid_reduction

end ErdosSimilarityGrowingGaps
