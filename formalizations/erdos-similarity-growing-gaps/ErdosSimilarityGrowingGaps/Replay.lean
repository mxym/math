import ErdosSimilarityGrowingGaps.Basic
import ErdosSimilarityGrowingGaps.First
import ErdosSimilarityGrowingGaps.Corollary
import ErdosSimilarityGrowingGaps.Input
import ErdosSimilarityGrowingGaps.AnnulusSequence
import ErdosSimilarityGrowingGaps.WindowBridge
import ErdosSimilarityGrowingGaps.VariableTree
import ErdosSimilarityGrowingGaps.FiniteRouting
import ErdosSimilarityGrowingGaps.Avoidance
import ErdosSimilarityGrowingGaps.TailAnalysis
import ErdosSimilarityGrowingGaps.ParameterStrata
import ErdosSimilarityGrowingGaps.SignFiberQuadratic
import ErdosSimilarityGrowingGaps.LineSignQuadratic
import ErdosSimilarityGrowingGaps.ParameterStrataQuadratic

namespace ErdosSimilarityGrowingGaps
open GrowingGap
open Set MeasureTheory
open scoped BigOperators
open scoped ENNReal

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

theorem replay_sampled_output_buffer
    {Z : LogScale} {f : ℝ → ℝ} {B : Set ℝ} {n : ℕ}
    {s α y c M v D r : ℝ} (hs : 0 < s) (hα : 0 < α) (hM : 0 ≤ M)
    (happrox : |f (input Z n) - y - c * (input Z n) ^ s| ≤
      M * (input Z n) ^ (s + α))
    (hideal : y + c * (2 : ℝ) ^ (-v * s) ∈ B)
    (hpower : |c * (input Z n) ^ s - c * (2 : ℝ) ^ (-v * s)| ≤
      |c| * ((2 : ℝ) ^ (-v * s) - (2 : ℝ) ^ (-(v + D) * s)))
    (hwidth : |c| * ((2 : ℝ) ^ (-v * s) - (2 : ℝ) ^ (-(v + D) * s)) +
        M * (input Z n) ^ (s + α) < r) :
    f (input Z n) ∈ Metric.thickening r B :=
  sampled_output_mem_thickening hs hα hM happrox hideal hpower hwidth

theorem replay_window_power_error
    {Z : LogScale} {U R D v s c : ℝ}
    (h : FillsAnnulus Z U R D)
    (hv : U / R ≤ v) (hvD : v + D ≤ R * U) (hs : 0 < s) :
    ∃ n : ℕ,
      |c * (input Z n) ^ s - c * (2 : ℝ) ^ (-v * s)| ≤
        |c| * ((2 : ℝ) ^ (-v * s) - (2 : ℝ) ^ (-(v + D) * s)) :=
  h.sample_power_error hv hvD hs

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

theorem replay_parameter_representatives (m : ℕ)
    (cuts : Fin m → AffineCut) (lo hi : ℝ × ℝ) :
    ∃ reps : Finset (ℝ × ℝ),
      (∀ r ∈ reps, inRectangle lo hi r) ∧ reps.card ≤ 3 ^ m := by
  obtain ⟨reps, hrep, hcard, _⟩ :=
    finite_parameter_representatives m cuts lo hi
  exact ⟨reps, hrep, hcard⟩

theorem replay_quadratic_parameter_representatives (m : ℕ)
    (cuts : Fin m → AffineCut) (lo hi : ℝ × ℝ)
    (hlo : lo.1 ≤ hi.1) (hhi : lo.2 ≤ hi.2) :
    ∃ reps : Finset (ℝ × ℝ),
      (∀ r ∈ reps, inRectangle lo hi r) ∧ reps.card ≤ 20 * (m + 5) ^ 2 := by
  obtain ⟨reps, hrep, hcard, _⟩ :=
    quadratic_arrangement_representative_bound m cuts lo hi hlo hhi
  exact ⟨reps, hrep, hcard⟩

theorem replay_budget_allocation {ι : Type*} [Countable ι] [Nonempty ι]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ b : ι → ℝ≥0∞, (∀ i, 0 < b i) ∧ ∑' i, b i < ENNReal.ofReal ε :=
  exists_budget_allocation hε

theorem replay_grid_blocker_assembly
    {ι : Type*} [Countable ι] [Nonempty ι]
    {F : ι → LogScale} {ε : ℝ}
    (w : ι × (ℕ × ℕ) → ℝ≥0∞)
    (hw : ∑' p, w p < ENNReal.ofReal ε)
    (hgrid : ∀ (i : ι) (j q : ℕ), ∃ H : Set ℝ,
      IsOpen H ∧ OnePeriodic H ∧ unitDensity H ≤ w (i, (j, q)) ∧
      ∀ s y c : ℝ, 0 < s → c ≠ 0 →
        ∀ f : ℝ → ℝ,
          TailApproximation (F i) f s (1 / (j + 1 : ℝ)) y c q →
          ∀ ρ : ℝ, 0 < ρ →
            ∃ n : ℕ, input (F i) n < ρ ∧ f (input (F i) n) ∈ H) :
    ∃ B : BlockerFamily F, ∑' i, B.budget i < ENNReal.ofReal ε :=
  blockerFamily_of_grid_blockers w hw hgrid

theorem replay_window_filling (Z : LogScale) (h : ConsecutiveLogGapLittleO Z) :
    WindowFilling Z := consecutiveGap_implies_windowFilling h

theorem replay_input_sequence (Z : LogScale) :
    (∀ n, 0 < input Z n) ∧ StrictAnti (input Z) ∧
      Filter.Tendsto (input Z) Filter.atTop (nhds 0) ∧
      ∀ n, -Real.logb 2 (input Z n) = Z.z n := by
  exact ⟨input_pos Z, input_strictAnti Z, input_tendsto_zero Z, input_logb Z⟩

theorem replay_input_ratio_zero {Z : LogScale}
    (hgap : Filter.Tendsto (fun n : ℕ => Z.z (n + 1) - Z.z n)
      Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n => input Z (n + 1) / input Z n)
      Filter.atTop (nhds 0) :=
  input_ratio_tendsto_zero hgap

#print axioms replay_window_filling
#print axioms replay_input_sequence
#print axioms replay_input_ratio_zero
#print axioms replay_first_sample
#print axioms replay_annular_sampling
#print axioms replay_late_window
#print axioms replay_window_power_error
#print axioms replay_sampled_output_buffer
#print axioms replay_variable_tree_span
#print axioms replay_distinct_terminal_all_miss
#print axioms replay_blocker_assembly
#print axioms replay_compact_blocker_assembly
#print axioms replay_theorem2_assembly
#print axioms replay_tail_grid_reduction
#print axioms replay_parameter_representatives
#print axioms replay_quadratic_parameter_representatives
#print axioms replay_budget_allocation
#print axioms replay_grid_blocker_assembly

end ErdosSimilarityGrowingGaps
