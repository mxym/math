import Alpha

#print axioms EntropyCounterexample.alpha_exists
#print axioms EntropyCounterexample.alpha_equation
#print axioms EntropyCounterexample.alpha_lower
#print axioms EntropyCounterexample.alpha_upper
#print axioms EntropyCounterexample.alpha_unique
#print axioms EntropyCounterexample.alpha_existsUnique

example : (117 / 125 : ℝ) < EntropyCounterexample.alpha ∧
    EntropyCounterexample.alpha < (937 / 1000 : ℝ) :=
  ⟨EntropyCounterexample.alpha_lower, EntropyCounterexample.alpha_upper⟩

example : ∃! x : ℝ, 0 < x ∧ x < 1 ∧ x ^ 10 * (1 + x) = 1 := by
  refine ⟨EntropyCounterexample.alpha,
    ⟨EntropyCounterexample.alpha_pos, EntropyCounterexample.alpha_lt_one,
      EntropyCounterexample.alpha_equation⟩, ?_⟩
  intro x hx
  exact EntropyCounterexample.alpha_unique hx.1 hx.2.2
