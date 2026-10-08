import ContinuumGeometric.RoutingStableMeasure

open Set MeasureTheory ContinuumGeometric
open scoped ENNReal

/-- Starting exactly on a boundary is allowed when the right endpoint stays
strictly before the next boundary. -/
example : NoGridBoundary 4 0 (1 / 8) := by
  intro b hb
  have hb₀ : (0 : ℝ) < b := by linarith [hb.1]
  have hb₁ : (b : ℝ) < 1 := by linarith [hb.2]
  have hi₀ : (0 : ℤ) < b := by exact_mod_cast hb₀
  have hi₁ : b < (1 : ℤ) := by exact_mod_cast hb₁
  omega

/-- Equality at the right endpoint is bad. -/
example : (0 : ℝ) ∈ gridBoundaryBad 4 (1 / 4) := by
  apply (mem_gridBoundaryBad_iff 4 (1 / 4) 0).2
  exact ⟨1, by norm_num⟩

/-- The left strip endpoint is included, and a negative lift wraps to zero. -/
example : (-1 / 8 : ℝ) ∈ gridBoundaryBad 4 (1 / 8) := by
  apply (mem_gridBoundaryBad_iff 4 (1 / 8) (-1 / 8)).2
  exact ⟨0, by norm_num⟩

example : NoGridBoundary 4 0 0 := by
  intro b hb
  linarith [hb.1, hb.2]

example : (((2 : ℕ) ^ (17 + 3) : ℕ) : ℝ) * stableDyadicRadius 17 10 =
    (2 : ℝ) ^ (-7 : ℤ) := by
  simpa using dyadic_gridBoundary_cost 17 10

example (b₀ : Fin 5 → ℕ) : unitDensity (routingStableCenters b₀ 10)ᶜ ≤
    ENNReal.ofReal (5 * (2 : ℝ) ^ (-7 : ℤ)) := by
  simpa using unitDensity_routingStable_compl_le b₀ 10

#print axioms gridBoundaryBad_eq_integerPeriodization
#print axioms unitDensity_gridBoundaryBad_le
#print axioms dyadic_gridBoundary_cost
#print axioms unitDensity_routingStable_compl_le
#print axioms measurableSet_routingStableCenters
#print axioms onePeriodic_routingStableCenters
