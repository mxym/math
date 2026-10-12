import ErdosSimilarityGrowingGaps.RoutingLaw
import ErdosSimilarityGrowingGaps.GridGeometry
import ErdosSimilarityGrowingGaps.PowerCore
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Tactic


/-!
Finite weighted Fubini and outcome selection for the actual missed-center set.
No probability bound or routing construction is assumed globally: the final
theorems expose the pointwise estimates that the finite routing proof must supply.
Real weights match the finite selector/terminal table model, including zero weights.
-/
namespace ErdosSimilarityGrowingGaps

open Set MeasureTheory
open scoped ENNReal

attribute [local instance] Classical.propDecidable

section FiniteOutcomes
variable {Ω : Type*} [Fintype Ω]

/-- Probability of an event under explicit finite real weights. -/
noncomputable def finiteOutcomeProbability (w : Ω → ℝ) (E : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if E ω then w ω else 0

/-- Nonnegative expectation, retaining the original density in `ℝ≥0∞`. -/
noncomputable def finiteOutcomeExpectation (w : Ω → ℝ) (f : Ω → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ ω, ENNReal.ofReal (w ω) * f ω

noncomputable def expectedUnitDensity (w : Ω → ℝ) (S : Ω → Set ℝ) : ℝ≥0∞ :=
  finiteOutcomeExpectation w (fun ω => unitDensity (S ω))

theorem finiteOutcomeProbability_nonneg (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (E : Ω → Prop) : 0 ≤ finiteOutcomeProbability w E := by
  classical
  exact Finset.sum_nonneg fun ω _ => by split_ifs <;> simp_all

theorem ofReal_finiteOutcomeProbability (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (E : Ω → Prop) :
    ENNReal.ofReal (finiteOutcomeProbability w E) =
      ∑ ω, ENNReal.ofReal (w ω) * (if E ω then 1 else 0) := by
  classical
  rw [finiteOutcomeProbability, ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> simp
  · intro ω _
    split_ifs <;> simp_all

/-- The density definition is exactly integration over the whole real unit interval. -/
theorem unitDensity_eq_lintegral_indicator (S : Set ℝ) (hS : MeasurableSet S) :
    unitDensity S = ∫⁻ x in Ico (0 : ℝ) 1, S.indicator (fun _ => 1) x := by
  rw [lintegral_indicator hS, setLIntegral_const]
  simp [unitDensity, Measure.restrict_apply hS]

/-- Finite Fubini with actual continuum event probabilities; no center discretization. -/
theorem expectedUnitDensity_eq_lintegral_probability
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (S : Ω → Set ℝ)
    (hS : ∀ ω, MeasurableSet (S ω)) :
    expectedUnitDensity w S =
      ∫⁻ x in Ico (0 : ℝ) 1,
        ENNReal.ofReal (finiteOutcomeProbability w (fun ω => x ∈ S ω)) := by
  classical
  have hmeas : ∀ ω : Ω, Measurable (fun x : ℝ =>
      ENNReal.ofReal (w ω) * (S ω).indicator (fun _ => 1) x) :=
    fun ω => measurable_const.mul (measurable_const.indicator (hS ω))
  calc
    expectedUnitDensity w S = ∑ ω,
        ∫⁻ x in Ico (0 : ℝ) 1,
          ENNReal.ofReal (w ω) * (S ω).indicator (fun _ => 1) x := by
      unfold expectedUnitDensity finiteOutcomeExpectation
      apply Finset.sum_congr rfl
      intro ω _
      rw [lintegral_const_mul _ (measurable_const.indicator (hS ω)),
        ← unitDensity_eq_lintegral_indicator (S ω) (hS ω)]
    _ = ∫⁻ x in Ico (0 : ℝ) 1,
        ∑ ω, ENNReal.ofReal (w ω) * (S ω).indicator (fun _ => 1) x :=
      (lintegral_finsetSum Finset.univ (fun ω _ => hmeas ω)).symm
    _ = _ := by
      apply lintegral_congr
      intro x
      rw [ofReal_finiteOutcomeProbability w hw]
      simp only [Set.indicator_apply]

/-- Pointwise control on all centers of one period integrates to the density bound. -/
theorem expectedUnitDensity_le_of_probability_le
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (S : Ω → Set ℝ)
    (hS : ∀ ω, MeasurableSet (S ω)) (c : ℝ)
    (hprob : ∀ x ∈ Ico (0 : ℝ) 1,
      finiteOutcomeProbability w (fun ω => x ∈ S ω) ≤ c) :
    expectedUnitDensity w S ≤ ENNReal.ofReal c := by
  rw [expectedUnitDensity_eq_lintegral_probability w hw S hS]
  calc
    _ ≤ ∫⁻ _x in Ico (0 : ℝ) 1, ENNReal.ofReal c := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
      exact ENNReal.ofReal_le_ofReal (hprob x hx)
    _ = _ := by simp [Real.volume_Ico]

/-- Constant pointwise occupancy gives the exact expected density `p`. -/
theorem expectedUnitDensity_eq_of_probability_eq
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (S : Ω → Set ℝ)
    (hS : ∀ ω, MeasurableSet (S ω)) (p : ℝ)
    (hprob : ∀ x ∈ Ico (0 : ℝ) 1,
      finiteOutcomeProbability w (fun ω => x ∈ S ω) = p) :
    expectedUnitDensity w S = ENNReal.ofReal p := by
  rw [expectedUnitDensity_eq_lintegral_probability w hw S hS]
  calc
    _ = ∫⁻ _x in Ico (0 : ℝ) 1, ENNReal.ofReal p := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
      rw [hprob x hx]
    _ = _ := by simp [Real.volume_Ico]

theorem finiteOutcomeExpectation_add (w : Ω → ℝ) (f g : Ω → ℝ≥0∞) :
    finiteOutcomeExpectation w (fun ω => f ω + g ω) =
      finiteOutcomeExpectation w f + finiteOutcomeExpectation w g := by
  simp [finiteOutcomeExpectation, mul_add, Finset.sum_add_distrib]

theorem finiteOutcomeProbability_le_one (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hnorm : ∑ ω, w ω = 1) (E : Ω → Prop) :
    finiteOutcomeProbability w E ≤ 1 := by
  unfold finiteOutcomeProbability
  rw [← hnorm]
  apply Finset.sum_le_sum
  intro ω _
  split_ifs <;> simp [hw ω]

/-- A small exceptional-center set can be charged its density, while the
pointwise stable-center miss bound is integrated over EVERY real center.
No measurable choice of parameter representatives occurs. -/
theorem expectedUnitDensity_le_stable_probability
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hnorm : ∑ ω, w ω = 1)
    (S : Ω → Set ℝ) (hS : ∀ ω, MeasurableSet (S ω))
    (bad : Set ℝ) (hbad : MeasurableSet bad) (c : ℝ) (hc : 0 ≤ c)
    (hstable : ∀ x ∈ Ico (0 : ℝ) 1, x ∉ bad →
      finiteOutcomeProbability w (fun ω => x ∈ S ω) ≤ c) :
    expectedUnitDensity w S ≤ ENNReal.ofReal c + unitDensity bad := by
  rw [expectedUnitDensity_eq_lintegral_probability w hw S hS]
  calc
    _ ≤ ∫⁻ x in Ico (0 : ℝ) 1,
        ENNReal.ofReal c + bad.indicator (fun _ => 1) x := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
      by_cases hb : x ∈ bad
      · have hprob := finiteOutcomeProbability_le_one w hw hnorm (fun ω => x ∈ S ω)
        simp only [Set.indicator_of_mem hb, Pi.one_apply]
        exact (ENNReal.ofReal_le_ofReal hprob).trans (by simp)
      · simp only [Set.indicator_of_notMem hb, add_zero]
        exact ENNReal.ofReal_le_ofReal (hstable x hx hb)
    _ = ENNReal.ofReal c + unitDensity bad := by
      rw [lintegral_add_left measurable_const]
      simp only [setLIntegral_const, Real.volume_Ico, sub_zero,
        ENNReal.ofReal_one, mul_one]
      rw [← unitDensity_eq_lintegral_indicator bad hbad]

theorem finiteOutcomeExpectation_mono (w : Ω → ℝ) (f g : Ω → ℝ≥0∞)
    (hfg : ∀ ω, f ω ≤ g ω) :
    finiteOutcomeExpectation w f ≤ finiteOutcomeExpectation w g := by
  apply Finset.sum_le_sum
  intro ω _
  gcongr
  exact hfg ω

theorem finiteOutcomeExpectation_const (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hnorm : ∑ ω, w ω = 1) (c : ℝ≥0∞) :
    finiteOutcomeExpectation w (fun _ => c) = c := by
  unfold finiteOutcomeExpectation
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun ω _ => hw ω), hnorm]
  simp

/-- A deterministic enlargement cost can be averaged under the same finite law. -/
theorem expectedUnitDensity_enlargement_le
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hnorm : ∑ ω, w ω = 1)
    (B B₂ : Ω → Set ℝ) (c : ℝ≥0∞)
    (hbuffer : ∀ ω, unitDensity (B₂ ω) ≤ unitDensity (B ω) + c) :
    expectedUnitDensity w B₂ ≤ expectedUnitDensity w B + c := by
  calc
    _ ≤ finiteOutcomeExpectation w (fun ω => unitDensity (B ω) + c) :=
      finiteOutcomeExpectation_mono w _ _ hbuffer
    _ = _ := by
      rw [finiteOutcomeExpectation_add, finiteOutcomeExpectation_const w hw hnorm]
      rfl

/-- Normalization prevents the finite outcome space from being empty. -/
theorem finiteOutcome_nonempty (w : Ω → ℝ) (hnorm : ∑ ω, w ω = 1) :
    Nonempty Ω := by
  classical
  by_contra hempty
  have : IsEmpty Ω := not_nonempty_iff.mp hempty
  have hzero : ∑ ω, w ω = 0 := by simp
  linarith

/-- A minimum outcome costs at most its normalized weighted expectation.
This includes zero weights and does not require a strictly positive law.
-/
theorem exists_outcome_le_expectation (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hnorm : ∑ ω, w ω = 1) (f : Ω → ℝ≥0∞) :
    ∃ ω, f ω ≤ finiteOutcomeExpectation w f := by
  classical
  have : Nonempty Ω := finiteOutcome_nonempty w hnorm
  obtain ⟨ω, _, hmin⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  have hsum : ∑ ω, ENNReal.ofReal (w ω) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ => hw ω), hnorm]
    simp
  refine ⟨ω, ?_⟩
  calc
    f ω = (∑ a, ENNReal.ofReal (w a)) * f ω := by rw [hsum, one_mul]
    _ = ∑ a, ENNReal.ofReal (w a) * f ω := Finset.sum_mul _ _ _
    _ ≤ finiteOutcomeExpectation w f := by
      apply Finset.sum_le_sum
      intro a _
      gcongr
      exact hmin a (Finset.mem_univ a)

/-- The two expected costs select one outcome with the combined budget. -/
theorem exists_outcome_density_add_le (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hnorm : ∑ ω, w ω = 1) (B R : Ω → Set ℝ) (p : ℝ) (hp : 0 ≤ p)
    (hB : expectedUnitDensity w B ≤ ENNReal.ofReal (2 * p))
    (hR : expectedUnitDensity w R ≤ ENNReal.ofReal (3 * p)) :
    ∃ ω, unitDensity (B ω) + unitDensity (R ω) ≤ ENNReal.ofReal (5 * p) := by
  obtain ⟨ω, hω⟩ := exists_outcome_le_expectation w hw hnorm
    (fun ω => unitDensity (B ω) + unitDensity (R ω))
  refine ⟨ω, hω.trans ?_⟩
  rw [finiteOutcomeExpectation_add]
  calc
    _ ≤ ENNReal.ofReal (2 * p) + ENNReal.ofReal (3 * p) := add_le_add hB hR
    _ = ENNReal.ofReal (5 * p) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

end FiniteOutcomes

section PeriodicReadouts

theorem periodicGridKey_add_one_for_density (N : ℕ) (x : ℝ) :
    periodicGridKey N (x + 1) = periodicGridKey N x := by
  simp [periodicGridKey, mul_add, Int.floor_add_natCast]

theorem onePeriodic_periodicGridSet_for_density (N : ℕ) (cells : Finset ℤ) :
    OnePeriodic (periodicGridSet N cells) := by
  intro x
  simp only [periodicGridSet, Set.mem_ofPred_eq, periodicGridKey_add_one_for_density]

theorem measurable_periodicGridKey_for_density (N : ℕ) :
    Measurable (periodicGridKey N) := by
  exact (measurable_of_countable (fun b : ℤ => b % (N : ℤ))).comp
    ((measurable_const.mul measurable_id).floor)

theorem measurableSet_periodicGridSet_for_density (N : ℕ) (cells : Finset ℤ) :
    MeasurableSet (periodicGridSet N cells) := by
  exact cells.finite_toSet.measurableSet.preimage (measurable_periodicGridKey_for_density N)

/-- Cell-marginal occupancy gives the exact expected density of the actual
periodic grid set. Only the genuine grid keys `0 ≤ b < N` need a marginal bound.
-/
theorem expected_periodicGridSet_density_eq {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (N : ℕ) (hN : 0 < N)
    (cells : Ω → Finset ℤ) (p : ℝ)
    (hcell : ∀ b : ℤ, 0 ≤ b → b < (N : ℤ) →
      finiteOutcomeProbability w (fun ω => b ∈ cells ω) = p) :
    expectedUnitDensity w (fun ω => periodicGridSet N (cells ω)) = ENNReal.ofReal p := by
  apply expectedUnitDensity_eq_of_probability_eq w hw _
    (fun ω => measurableSet_periodicGridSet_for_density N (cells ω)) p
  intro x _
  exact hcell (periodicGridKey N x)
    (Int.emod_nonneg _ (by exact_mod_cast (Nat.ne_of_gt hN)))
    (Int.emod_lt_of_pos _ (by exact_mod_cast hN))

/-- A table readout may route using every selector; terminal addresses remain finite. -/
noncomputable def periodicTerminalReadoutSet {S T : Type*}
    (N : ℕ) (address : (S → Bool) → ℤ → T) (ω : FiniteRoutingTables S T) : Set ℝ :=
  {x | ω.terminals (address ω.selectors (periodicGridKey N x)) = true}

theorem onePeriodic_periodicTerminalReadoutSet {S T : Type*}
    (N : ℕ) (address : (S → Bool) → ℤ → T) (ω : FiniteRoutingTables S T) :
    OnePeriodic (periodicTerminalReadoutSet N address ω) := by
  intro x
  simp only [periodicTerminalReadoutSet, Set.mem_ofPred_eq, periodicGridKey_add_one_for_density]

theorem measurableSet_periodicTerminalReadoutSet {S T : Type*}
    (N : ℕ) (address : (S → Bool) → ℤ → T) (ω : FiniteRoutingTables S T) :
    MeasurableSet (periodicTerminalReadoutSet N address ω) := by
  exact ((measurableSet_singleton true).preimage (measurable_of_countable
    (fun b : ℤ => ω.terminals (address ω.selectors b)))).preimage
      (measurable_periodicGridKey_for_density N)

/-- Exact expected density for a finite terminal-table readout, allowing
selector-dependent routing. The finite probability model supplies its marginals.
-/
theorem expected_periodicTerminalReadout_density_eq {S T : Type*}
    [Fintype (FiniteRoutingTables S T)]
    (w : FiniteRoutingTables S T → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (N : ℕ) (hN : 0 < N) (address : (S → Bool) → ℤ → T) (p : ℝ)
    (hterminal : ∀ b : ℤ, 0 ≤ b → b < (N : ℤ) →
      finiteOutcomeProbability w
        (fun ω => ω.terminals (address ω.selectors b) = true) = p) :
    expectedUnitDensity w (periodicTerminalReadoutSet N address) = ENNReal.ofReal p := by
  apply expectedUnitDensity_eq_of_probability_eq w hw _
    (measurableSet_periodicTerminalReadoutSet N address) p
  intro x _
  exact hterminal (periodicGridKey N x)
    (Int.emod_nonneg _ (by exact_mod_cast (Nat.ne_of_gt hN)))
    (Int.emod_lt_of_pos _ (by exact_mod_cast hN))

end PeriodicReadouts

section ActualMissedCenters
variable {Ω : Type*} [Fintype Ω]

/-- Fubini specialized to the actual finite dyadic tests and strict windows.
The only measurability input is openness of each selected inner buffer.
-/
theorem expected_powerMissedCenters_eq_lintegral_probability
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (s₀ s₁ : ℝ)
    (tests : Finset ℕ) (k : ℤ) {W : ℕ} (windows : Fin W → ℝ × ℝ)
    (B₁ : Ω → Set ℝ) (hB₁ : ∀ ω, IsOpen (B₁ ω)) :
    expectedUnitDensity w (fun ω => powerMissedCenters
      (s₀ := s₀) (s₁ := s₁) tests k windows (B₁ ω)) =
    ∫⁻ x in Ico (0 : ℝ) 1, ENNReal.ofReal (finiteOutcomeProbability w
      (fun ω => x ∈ powerMissedCenters
        (s₀ := s₀) (s₁ := s₁) tests k windows (B₁ ω))) := by
  exact expectedUnitDensity_eq_lintegral_probability w hw _
    (fun ω => measurableSet_powerMissedCenters s₀ s₁ tests k windows (B₁ ω) (hB₁ ω))

theorem expected_powerMissedCenters_le_of_probability_le
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (s₀ s₁ : ℝ)
    (tests : Finset ℕ) (k : ℤ) {W : ℕ} (windows : Fin W → ℝ × ℝ)
    (B₁ : Ω → Set ℝ) (hB₁ : ∀ ω, IsOpen (B₁ ω)) (c : ℝ)
    (hprob : ∀ x ∈ Ico (0 : ℝ) 1, finiteOutcomeProbability w
      (fun ω => x ∈ powerMissedCenters
        (s₀ := s₀) (s₁ := s₁) tests k windows (B₁ ω)) ≤ c) :
    expectedUnitDensity w (fun ω => powerMissedCenters
      (s₀ := s₀) (s₁ := s₁) tests k windows (B₁ ω)) ≤ ENNReal.ofReal c := by
  exact expectedUnitDensity_le_of_probability_le w hw _
    (fun ω => measurableSet_powerMissedCenters s₀ s₁ tests k windows (B₁ ω) (hB₁ ω))
    c hprob

/-- A genuine outcome of the finite table law, selected for the actual real failure set. -/
theorem exists_powerRouting_outcome_density_add_le
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hnorm : ∑ ω, w ω = 1)
    (s₀ s₁ : ℝ) (tests : Finset ℕ) (k : ℤ) {W : ℕ}
    (windows : Fin W → ℝ × ℝ) (B₁ B₂ : Ω → Set ℝ)
    (hB₁ : ∀ ω, IsOpen (B₁ ω)) (p : ℝ) (hp : 0 ≤ p)
    (hB₂ : expectedUnitDensity w B₂ ≤ ENNReal.ofReal (2 * p))
    (hmiss : ∀ x ∈ Ico (0 : ℝ) 1, finiteOutcomeProbability w
      (fun ω => x ∈ powerMissedCenters
        (s₀ := s₀) (s₁ := s₁) tests k windows (B₁ ω)) ≤ 3 * p) :
    ∃ ω, unitDensity (B₂ ω) + unitDensity (powerMissedCenters
      (s₀ := s₀) (s₁ := s₁) tests k windows (B₁ ω)) ≤ ENNReal.ofReal (5 * p) := by
  apply exists_outcome_density_add_le w hw hnorm B₂ _ p hp hB₂
  exact expected_powerMissedCenters_le_of_probability_le w hw s₀ s₁ tests k windows
    B₁ hB₁ (3 * p) hmiss

/-- The actual stable-center estimate and the measured unstable-center budget
select one outcome for the closed real failure set. -/
theorem exists_powerRouting_outcome_density_add_le_of_stable
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hnorm : ∑ ω, w ω = 1)
    (s₀ s₁ : ℝ) (tests : Finset ℕ) (k : ℤ) {W : ℕ}
    (windows : Fin W → ℝ × ℝ) (B₁ B₂ : Ω → Set ℝ)
    (hB₁ : ∀ ω, IsOpen (B₁ ω)) (p : ℝ) (hp : 0 ≤ p)
    (hB₂ : expectedUnitDensity w B₂ ≤ ENNReal.ofReal (2 * p))
    (bad : Set ℝ) (hbad : MeasurableSet bad) (hbad_density : unitDensity bad ≤ ENNReal.ofReal p)
    (hstable : ∀ x ∈ Ico (0 : ℝ) 1, x ∉ bad → finiteOutcomeProbability w
      (fun ω => x ∈ powerMissedCenters
        (s₀ := s₀) (s₁ := s₁) tests k windows (B₁ ω)) ≤ 2 * p) :
    ∃ ω, unitDensity (B₂ ω) + unitDensity (powerMissedCenters
      (s₀ := s₀) (s₁ := s₁) tests k windows (B₁ ω)) ≤ ENNReal.ofReal (5 * p) := by
  apply exists_outcome_density_add_le w hw hnorm B₂ _ p hp hB₂
  have hR := expectedUnitDensity_le_stable_probability w hw hnorm _
    (fun ω => measurableSet_powerMissedCenters s₀ s₁ tests k windows (B₁ ω) (hB₁ ω))
    bad hbad (2 * p) (by positivity) hstable
  apply hR.trans
  calc
    _ ≤ ENNReal.ofReal (2 * p) + ENNReal.ofReal p := add_le_add le_rfl hbad_density
    _ = ENNReal.ofReal (3 * p) := by
      rw [← ENNReal.ofReal_add (by positivity) hp]
      congr 1
      ring

end ActualMissedCenters

end ErdosSimilarityGrowingGaps
