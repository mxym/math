import ChromaticCyclesAllN.CyclePolynomialAll
import ChromaticCyclesAllN.CycleInfinitePositive

namespace ChromaticCycleAll

/-- Complete classification of the explicit cycle-chromatic polynomial family.

This theorem concerns the genuine coefficient sequence of
`(X-1)^n + (-1)^n (X-1)` as a polynomial in `ℤ[X]`.
To use it as a theorem about actual graph coloring one must separately prove
the coloring-count identity for `SimpleGraph.cycleGraph n` at each n.
-/
theorem cycle_polynomial_infinite_logconcavity_iff (n : ℕ) (hn : 3 ≤ n) :
    InfinitelyLogConcave (cycleAbsCoeff n) ↔ n ≤ 11 := by
  rw [cycleAbsCoeff_eq_binomialBase n (by omega)]
  exact cycle_binomial_infinite_classification n hn

/-- Negative infinite family, no enumeration of lengths. -/
theorem every_cycle_formula_n_ge_17_is_counterexample (n : ℕ) (hn : 17 ≤ n) :
    ¬ InfinitelyLogConcave (cycleAbsCoeff n) := by
  rw [cycleAbsCoeff_eq_binomialBase n (by omega)]
  exact all_other_cycle_binomial_sequences_fail n (by omega)

/-- Positive direction includes infinitely many LC iterates for each of 3,...,11. -/
theorem every_cycle_formula_n_le_11_is_infinitely_logconcave (n : ℕ)
    (h₃ : 3 ≤ n) (h₁₁ : n ≤ 11) :
    InfinitelyLogConcave (cycleAbsCoeff n) :=
  (cycle_polynomial_infinite_logconcavity_iff n h₃).2 h₁₁

end ChromaticCycleAll
