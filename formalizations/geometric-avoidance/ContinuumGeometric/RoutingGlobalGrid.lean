import ContinuumGeometric.RoutingModel
import ContinuumGeometric.RoutingTreeBounds
import ContinuumGeometric.PeriodicRepair

/-!
Actual finite-grid representation of the global first-true/default readout.
The explicit endpoint bound is a deterministic tree premise and carries no
probabilistic assertion. All representatives are canonical half-open cells.
-/
namespace ContinuumGeometric

theorem periodicGridKey_canonical_left (G : ℕ) (hG : 0 < G) (j : ℤ)
    (hj : j ∈ Finset.Ico 0 (G : ℤ)) :
    periodicGridKey G ((j : ℝ) / G) = j := by
  have hGr : (G : ℝ) ≠ 0 := by exact_mod_cast hG.ne'
  rw [periodicGridKey, mul_div_cancel₀ _ hGr, Int.floor_intCast]
  exact Int.emod_eq_of_lt (Finset.mem_Ico.1 hj).1 (Finset.mem_Ico.1 hj).2

theorem actual_routing_readout_eq_of_finest_key {M d : ℕ}
    (c : RoutingTemplate M d) (hM : 0 < M) (hd : 0 < d)
    (B : ℕ) (hselectors : ∀ e : SelectorEdge M d, c.selectorEnd e ≤ B)
    (hterminals : ∀ l : RoutingLeaf M d, c.leafEnd hd l ≤ B)
    (ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd))
    (z z' : ℝ) (hkey : periodicGridKey (2 ^ (B + 3)) z =
      periodicGridKey (2 ^ (B + 3)) z') :
    ω.terminals (terminalAddress c hd (routeLeaf c hM ω.selectors z) z) =
      ω.terminals (terminalAddress c hd (routeLeaf c hM ω.selectors z') z') := by
  have hfine := (gridAddress_eq_iff B z z').2 hkey
  have hroute : routeLeaf c hM ω.selectors z = routeLeaf c hM ω.selectors z' := by
    apply routeLeaf_eq_of_selector_reads
    intro e
    have he := dyadic_grid_eq_of_finer_eq _ _ (hselectors e) z z' hfine
    simp only [selectorAddress, he]
  have ht := dyadic_grid_eq_of_finer_eq _ _
    (hterminals (routeLeaf c hM ω.selectors z')) z z' hfine
  apply congrArg ω.terminals
  unfold terminalAddress
  rw [hroute, ht]

noncomputable def routedCanonicalCells {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (B : ℕ)
    (ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd)) : Finset ℤ := by
  classical
  exact (Finset.Ico 0 ((2 ^ (B + 3) : ℕ) : ℤ)).filter
    (fun j => ((j : ℝ) / (2 ^ (B + 3) : ℕ)) ∈ routedSet c hM hd ω)

theorem routedCanonicalCells_subset {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (B : ℕ)
    (ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd)) :
    routedCanonicalCells c hM hd B ω ⊆ Finset.Ico 0 ((2 ^ (B + 3) : ℕ) : ℤ) := by
  classical
  exact Finset.filter_subset _ _

/-- The concrete routed set is an actual finite canonical periodic grid set. -/
theorem routedSet_eq_periodicGridSet {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (B : ℕ)
    (hselectors : ∀ e : SelectorEdge M d, c.selectorEnd e ≤ B)
    (hterminals : ∀ l : RoutingLeaf M d, c.leafEnd hd l ≤ B)
    (ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd)) :
    routedSet c hM hd ω =
      periodicGridSet (2 ^ (B + 3)) (routedCanonicalCells c hM hd B ω) := by
  classical
  ext z
  let j := periodicGridKey (2 ^ (B + 3)) z
  have hj : j ∈ Finset.Ico 0 ((2 ^ (B + 3) : ℕ) : ℤ) :=
    Finset.mem_Ico.2 ⟨periodicGridKey_nonneg _ (by positivity) z,
      periodicGridKey_lt _ (by positivity) z⟩
  have hk := periodicGridKey_canonical_left (2 ^ (B + 3)) (by positivity) j hj
  have hr := actual_routing_readout_eq_of_finest_key c hM hd B hselectors hterminals ω
    z ((j : ℝ) / (2 ^ (B + 3) : ℕ)) (by exact hk.symm)
  change (_ = true) ↔ _
  simp only [periodicGridSet, Set.mem_setOf_eq, routedCanonicalCells, Finset.mem_filter]
  change (_ = true) ↔ j ∈ Finset.Ico 0 ((2 ^ (B + 3) : ℕ) : ℤ) ∧ _ = true
  rw [hr]
  exact (and_iff_right hj).symm

theorem measurableSet_actual_routedSet {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (B : ℕ)
    (hselectors : ∀ e : SelectorEdge M d, c.selectorEnd e ≤ B)
    (hterminals : ∀ l : RoutingLeaf M d, c.leafEnd hd l ≤ B)
    (ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd)) :
    MeasurableSet (routedSet c hM hd ω) := by
  rw [routedSet_eq_periodicGridSet c hM hd B hselectors hterminals ω]
  exact measurableSet_periodicGridSet _ (by positivity) _
    (routedCanonicalCells_subset c hM hd B ω)

theorem onePeriodic_actual_routedSet {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (B : ℕ)
    (hselectors : ∀ e : SelectorEdge M d, c.selectorEnd e ≤ B)
    (hterminals : ∀ l : RoutingLeaf M d, c.leafEnd hd l ≤ B)
    (ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd)) :
    OnePeriodic (routedSet c hM hd ω) := by
  rw [routedSet_eq_periodicGridSet c hM hd B hselectors hterminals ω]
  exact onePeriodic_periodicGridSet _ (by positivity) _
    (routedCanonicalCells_subset c hM hd B ω)

/-- The canonical tree supplies the global endpoint bound without a hypothesis. -/
theorem actual_routedSet_finite_grid {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (hL : 0 < c.baseLength)
    (ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd)) :
    let B := c.origin + RoutingTemplate.span M c.gap c.baseLength d - 1
    routedSet c hM hd ω =
      periodicGridSet (2 ^ (B + 3)) (routedCanonicalCells c hM hd B ω) := by
  dsimp only
  apply routedSet_eq_periodicGridSet
  · intro e
    have h := selectorEnd_global_bound c hM hL e
    omega
  · intro l
    have h := leafEnd_global_bound c hM hd hL l
    omega

theorem measurableSet_actual_routedSet_of_template {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (hL : 0 < c.baseLength)
    (ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd)) :
    MeasurableSet (routedSet c hM hd ω) := by
  rw [actual_routedSet_finite_grid c hM hd hL ω]
  exact measurableSet_periodicGridSet _ (by positivity) _
    (routedCanonicalCells_subset c hM hd _ ω)

theorem onePeriodic_actual_routedSet_of_template {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (hL : 0 < c.baseLength)
    (ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd)) :
    OnePeriodic (routedSet c hM hd ω) := by
  rw [actual_routedSet_finite_grid c hM hd hL ω]
  exact onePeriodic_periodicGridSet _ (by positivity) _
    (routedCanonicalCells_subset c hM hd _ ω)

end ContinuumGeometric
