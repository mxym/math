import ContinuumGeometric.CountableExhaustion

open Set MeasureTheory ContinuumGeometric
open scoped ENNReal

/-- Negative lifts and right endpoints use the canonical modulo-floor cell. -/
example : periodicGridKey 4 (-1 / 4) = 3 := by
  norm_num [periodicGridKey]

example : periodicGridKey 4 (1 / 4) = 1 := by
  norm_num [periodicGridKey]

example : (1 / 4 : ℝ) ∉ periodicGridSet 4 {0} := by
  norm_num [periodicGridSet, periodicGridKey]

example : (-1 / 4 : ℝ) ∈ periodicGridSet 4 {3} := by
  norm_num [periodicGridSet, periodicGridKey]

/-- A buffer around the last cell wraps across zero, and is covered by 4Nr. -/
example : unitDensity (Metric.thickening (2 * (1 / 100 : ℝ)) (periodicGridSet 4 {3})) ≤
    unitDensity (periodicGridSet 4 {3}) + ENNReal.ofReal (16 / 100) := by
  convert unitDensity_periodicGridSet_double_buffer_le 4 (by norm_num) {3}
    (by intro j hj; simp only [Finset.mem_singleton] at hj; subst j; norm_num)
    (1 / 100) (by norm_num) using 1 <;> norm_num

/-- Empty selection is included in the exact width formula. -/
example : unitDensity (periodicGridSet 4 ∅) = 0 := by
  simpa using unitDensity_periodicGridSet 4 (by norm_num) ∅ (by simp)

#print axioms closed_onePeriodic_open_cover
#print axioms periodicGridSet_eq_integerPeriodization
#print axioms unitDensity_periodicGridSet_double_buffer_le
#print axioms periodic_grid_outcome_repair
#print axioms unitDensity_reflectedSet
#print axioms smallCompactBlockerSpec_open_exhaustion
#print axioms mainTarget_of_smallCompactBlockerSpec
