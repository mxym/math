import ContinuumGeometric.RoutingAssembly

open Set MeasureTheory ContinuumGeometric
open scoped ENNReal

/-- A fixed affine tree span and arbitrarily late absolute origin can satisfy
the strict scalar entropy budget together. -/
example : ∃ U L : ℕ, 10000 ≤ U ∧ 4 ≤ L ∧ 7 * L + 11 ≤ U ∧
    ((U : ℝ) + 1) ^ 2 * Real.exp (-(L : ℝ)) < 1 / 100 := by
  simpa using exists_late_entropy_schedule 1 (1 / 100) 1
    (by norm_num) (by norm_num) (by norm_num) 7 11 4 10000

/-- The actual schedule handles a negative coefficient scale and a late
ORIGINAL tail without choosing any center or table outcome. -/
example : Nonempty (RoutingSchedule 2 (-17) 100 (1 / 100)) :=
  exists_routing_schedule 2 (by norm_num) (-17) 100 (1 / 100) (by norm_num)

/-- P=0 retains the constant entropy cost; an empty candidate family does
not make the numerical arrangement bound zero. -/
example : 20 * ((0 : ℝ) * (3 + (2 : ℝ) ^ 3) + 5) ^ 2 = 500 := by norm_num

example (ell : ℕ) : 500 ≤ 5120 * Real.exp (4 * Real.log 2 * (ell : ℝ)) := by
  have h := signature_entropy_exp_bound 0 ell
  norm_num at h
  exact h

/-- Both absolute output position and the absolute coefficient scale remain
in the actual finite candidate budget. -/
example : candidateLabelBudget 3000 0 0 = 1001 := by
  norm_num [candidateLabelBudget]

example : candidateLabelBudget 0 0 (-300) = 101 := by
  norm_num [candidateLabelBudget]

example : ¬ candidateLabelBudget 3000 0 0 ≤ candidateLabelBudget 0 0 0 := by
  norm_num [candidateLabelBudget]

example : ¬ candidateLabelBudget 0 0 (-300) ≤ candidateLabelBudget 0 0 0 := by
  norm_num [candidateLabelBudget]

example : (2 : ℝ) ^ ((3 : ℤ) - (10 : ℤ)) = (2 : ℝ) ^ (-7 : ℤ) := by norm_num

example : (2 : ℝ) ^ (3 - (10 : ℝ)) = (2 : ℝ) ^ (-7 : ℤ) := by
  simpa using (dyadic_integer_gap_rpow 10).symm

/-- The entropy coefficient cannot be treated as independent of the
absolute-position candidate count. -/
example : ¬ 20 * ((100 : ℝ) * (3 + (2 : ℝ) ^ 3) + 5) ^ 2 ≤ 5120 := by norm_num

def auditTemplate : RoutingTemplate 2 1 := ⟨1, 1, 0⟩

/-- The ACTUAL terminal readout matches across a negative lift and its
wrapped canonical cell, uniformly for every selector and terminal table. -/
example (ω : FiniteRoutingTables (SelectorAddress auditTemplate)
    (TerminalAddress auditTemplate (by norm_num))) :
    (-1 / 32 : ℝ) ∈ routedSet auditTemplate (by norm_num) (by norm_num) ω ↔
      (31 / 32 : ℝ) ∈ routedSet auditTemplate (by norm_num) (by norm_num) ω := by
  rw [actual_routedSet_finite_grid auditTemplate (by norm_num) (by norm_num)
    (by norm_num [auditTemplate]) ω]
  change periodicGridKey 32 (-1 / 32) ∈
    routedCanonicalCells auditTemplate (by norm_num) (by norm_num) 2 ω ↔
      periodicGridKey 32 (31 / 32) ∈
        routedCanonicalCells auditTemplate (by norm_num) (by norm_num) 2 ω
  have heq : periodicGridKey 32 (-1 / 32) = periodicGridKey 32 (31 / 32) := by
    norm_num [periodicGridKey]
  rw [heq]

/-- The upper endpoint zero is the NEXT cell, not the preceding wrapped cell. -/
example : periodicGridKey 32 (-1 / 32) ≠ periodicGridKey 32 0 := by
  norm_num [periodicGridKey]

example {M d : ℕ} (c : RoutingTemplate M d) (K N : ℕ) (k : ℤ)
    (n : ℕ) (hn : n ∈ globalRoutingTests c K N k) : N ≤ n :=
  globalRoutingTests_tail c K N k n hn

/-- A zero scalar terminal configuration has EMPTY actual routed output,
so outcome repair cannot obtain hits from its finite buffer alone. -/
example (σ : SelectorAddress auditTemplate → Bool) :
    routedSet auditTemplate (by norm_num) (by norm_num) ⟨σ, fun _ => false⟩ = ∅ := by
  ext z
  simp [routedSet]

example : ¬ unitDensity (univ : Set ℝ) ≤ ENNReal.ofReal (1 / 100) := by
  norm_num [unitDensity, Real.volume_Ico]

-- This type check retains the actual stable miss premise explicitly.
#check actual_routing_blocker_of_stable_estimate
#check actual_routing_blocker_of_actual_stable_miss

#print axioms exists_late_entropy_schedule
#print axioms exists_routing_schedule
#print axioms signature_entropy_position_bound
#print axioms routingSchedule_node_entropy_lt
#print axioms actual_routedSet_finite_grid
#print axioms routingOuterBuffer_density_le
#print axioms actual_routing_blocker_of_stable_estimate
#print axioms actual_routing_blocker_of_actual_stable_miss
