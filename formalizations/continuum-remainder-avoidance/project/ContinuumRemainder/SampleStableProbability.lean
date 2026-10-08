import ContinuumRemainder.SampleLocalProbability
import ContinuumRemainder.SampleSchedule
import ContinuumRemainder.RobustAssembly
import ContinuumGeometric.RoutingStableProbability

/-!
The actual sampled missed-center event is bounded on every stable center by
partitioning the genuine finite-table law into center-exposure atoms.  The
candidate family comes from the fixed prescribed configuration, and every
own/terminal separation and continuum representative bound is proved upstream.
-/
namespace ContinuumRemainder

open scoped BigOperators
open Set ContinuumGeometric
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency false

/-- Every potentially active sample index is included, at all real parameters. -/
noncomputable def sampledGlobalRoutingTests {M d : ℕ} (c : RoutingTemplate M d)
    (k : ℤ) : Finset ℕ :=
  Finset.range (candidateLabelBudget c.origin
    (RoutingTemplate.span M c.gap c.baseLength d) k)

/-- A global miss at an actual stable center forces the genuine vertex event
at any default vertex fixed by the center atom. -/
theorem sampled_missed_center_forces_vertex_miss
    {A : Set ℝ} {s₀ s₁ α₀ : ℝ} {k : ℤ} {q h : ℕ} {p : ℝ}
    (S : SampleRoutingSchedule A s₀ s₁ α₀ k q h p)
    (x : ℝ) (hx : x ∈ actualStableCenters S.template)
    (bits : SelectorEdge S.branching S.depth → Bool)
    (ω : FiniteRoutingTables (SelectorAddress S.template)
      (TerminalAddress S.template S.depth_pos))
    (hσ : centerExposureAtom (actualCenterExposure S.template x bits) ω.selectors)
    (v : InternalNode S.branching S.depth)
    (hprefix : (List.ofFn v.2).IsPrefix (List.ofFn
      (routeLeaf S.template (by have := S.branching_ge_two; omega) ω.selectors x)))
    (hdefault : ∀ i : Fin (S.branching - 1), bits ⟨v, i⟩ = false)
    (hmiss : x ∈ sampledMissedCenters (s₀ := s₀) (s₁ := s₁)
      (sampledGlobalRoutingTests S.template k) S.sample.a S.sample.z k
      (globalRoutingWindows S.template)
      (sampledRoutingInnerBuffer S.template (by have := S.branching_ge_two; omega)
        S.depth_pos q k α₀ s₁ ω)) :
    let pairs := sampleVertexPairs S.sample S.template v s₁ k
    ∃ r : PowerParams s₀ s₁,
      logLocalAllMiss S.template (by have := S.branching_ge_two; omega) S.depth_pos
        s₀ s₁ x k (fun i => ⟨v, candidatePairEdge pairs i⟩)
        (fun i => S.sample.z (candidatePairIndex pairs i)) r ω := by
  dsimp only
  let pairs := sampleVertexPairs S.sample S.template v s₁ k
  obtain ⟨r, hr⟩ := (mem_missedCenters_iff _ _ _ x).1 hmiss
  refine ⟨r, ?_⟩
  intro i hi hsuccess
  have hpair := (candidatePairEnumeration pairs i).property
  obtain ⟨hind, _⟩ := (S.sample.mem_potentialPairs_iff s₁ S.template.origin
    (RoutingTemplate.span S.branching S.template.gap S.template.baseLength S.depth)
    k _ _).1 hpair
  have hindex : candidatePairIndex pairs i ∈ sampledGlobalRoutingTests S.template k :=
    Finset.mem_range.2 hind
  let e : RoutingEdge S.branching S.depth :=
    RoutingTemplate.selectorRoutingEdge ⟨v, candidatePairEdge pairs i⟩
  have hactive : r ∈ sampledWindowActivations (S.sample.z (candidatePairIndex pairs i))
      k (globalRoutingWindows S.template) := by
    apply mem_iUnion.2
    refine ⟨(globalRoutingEdgeEnumeration S.branching S.depth).symm e, ?_⟩
    simpa only [globalRoutingWindows, Equiv.apply_symm_apply, e, sampledActivation, logActivation] using hi
  apply hr ⟨candidatePairIndex pairs i, hindex⟩ hactive
  apply Metric.self_subset_thickening (errorRadius_pos q k α₀ s₁ S.template.origin)
  rw [S.sample.a_eq_logInput]
  exact log_stable_local_success_mem_routedSet S.template
    (by have := S.branching_ge_two; omega) S.depth_pos S.length_pos S.gap_guard
    s₀ s₁ x (S.sample.z (candidatePairIndex pairs i)) k r ω bits hσ v
    (candidatePairEdge pairs i) hprefix hdefault hx hi hsuccess

/-- The scheduled strict entropy budget applies to each actual vertex. -/
theorem sampled_scheduled_vertex_continuum_joint_miss_bound
    {A : Set ℝ} {s₀ s₁ α₀ : ℝ} {k : ℤ} {q h : ℕ} {p : ℝ}
    (S : SampleRoutingSchedule A s₀ s₁ α₀ k q h p)
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s₁) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (x : ℝ) (bits : SelectorEdge S.branching S.depth → Bool)
    (v : InternalNode S.branching S.depth) :
    let pairs := sampleVertexPairs S.sample S.template v s₁ k
    tableProbability p (fun ω =>
      centerExposureAtom (actualCenterExposure S.template x bits) ω.selectors ∧
      ∃ r : PowerParams s₀ s₁,
        logLocalAllMiss S.template (by have := S.branching_ge_two; omega) S.depth_pos
          s₀ s₁ x k (fun i => ⟨v, candidatePairEdge pairs i⟩)
          (fun i => S.sample.z (candidatePairIndex pairs i)) r ω) ≤
      tableProbability (T := TerminalAddress S.template S.depth_pos) p
        (fun ω => centerExposureAtom (actualCenterExposure S.template x bits) ω.selectors) * p := by
  dsimp only
  let pairs := sampleVertexPairs S.sample S.template v s₁ k
  have hM : 0 < S.branching := by have := S.branching_ge_two; omega
  have hbase : S.template.baseLength ≤ vertexWindowLength S.template v :=
    RoutingTemplate.base_le_length _ _ _ _ (by omega)
  have hbasereal : (S.template.baseLength : ℝ) ≤ vertexWindowLength S.template v := by
    exact_mod_cast hbase
  have hell : 2 * (s₁ * S.sample.B) ≤ vertexWindowLength S.template v :=
    S.active_count_guard.trans hbasereal
  have hbudget := (sampleSchedule_node_entropy_lt S pairs.card
    (vertexWindowLength S.template v)
    (sampleVertexPairs_card_le S.sample S.template v s₁ k) hbase).le
  apply sample_vertex_continuum_joint_miss_bound S.sample hs₀ S.template hM S.depth_pos
    S.length_pos S.origin_ge_four p s₁ x hp₀ hp₁ hs k bits v hell S.start_guard
  simpa only [sampleActivationRate] using hbudget

/-- The actual predecessor-grid stability constraints meet the selected budget. -/
theorem sampled_stable_bad_density_le
    {A : Set ℝ} {s₀ s₁ α₀ : ℝ} {k : ℤ} {q h : ℕ} {p : ℝ}
    (S : SampleRoutingSchedule A s₀ s₁ α₀ k q h p) :
    unitDensity (actualStableCenters S.template)ᶜ ≤ ENNReal.ofReal p := by
  apply (unitDensity_actualStable_compl_le S.template).trans
  apply ENNReal.ofReal_le_ofReal
  rw [dyadic_integer_gap_rpow]
  exact S.stable_boundary_small.le

/-- The ACTUAL global sampled missed-center event has probability at most 2p
at EVERY stable real center.  No independent-path or abstract blocker premise
is used: the finite center atoms and the fixed vertex joint laws are summed. -/
theorem sampled_stable_missed_center_probability_le
    {A : Set ℝ} {s₀ s₁ α₀ : ℝ} {k : ℤ} {q h : ℕ} {p : ℝ}
    (S : SampleRoutingSchedule A s₀ s₁ α₀ k q h p)
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s₁) (hp : 0 < p) (hp₁ : p ≤ 1)
    (x : ℝ) (hx : x ∈ actualStableCenters S.template) :
    tableProbability p (fun ω => x ∈ sampledMissedCenters (s₀ := s₀) (s₁ := s₁)
      (sampledGlobalRoutingTests S.template k) S.sample.a S.sample.z k
      (globalRoutingWindows S.template)
      (sampledRoutingInnerBuffer S.template (by have := S.branching_ge_two; omega)
        S.depth_pos q k α₀ s₁ ω)) ≤ 2 * p := by
  let hM : 0 < S.branching := by have := S.branching_ge_two; omega
  let E := fun ω : FiniteRoutingTables (SelectorAddress S.template)
      (TerminalAddress S.template S.depth_pos) =>
    x ∈ sampledMissedCenters (s₀ := s₀) (s₁ := s₁)
      (sampledGlobalRoutingTests S.template k) S.sample.a S.sample.z k
      (globalRoutingWindows S.template)
      (sampledRoutingInnerBuffer S.template hM S.depth_pos q k α₀ s₁ ω)
  let D := fun ω : FiniteRoutingTables (SelectorAddress S.template)
      (TerminalAddress S.template S.depth_pos) => routeHasNoDefault S.template hM ω.selectors x
  have hD : tableProbability p D ≤ p := by
    rw [actual_routeHasNoDefault_probability_rpow S.template hM S.depth_pos p x]
    exact S.no_default_small.le
  have hdefault : tableProbability p (fun ω => E ω ∧ ¬ D ω) ≤ p := by
    rw [actual_center_atom_partition S.template S.depth_pos p x]
    have hbits (bits : SelectorEdge S.branching S.depth → Bool) :
        tableProbability p (fun ω =>
          centerExposureAtom (actualCenterExposure S.template x bits) ω.selectors ∧
          (E ω ∧ ¬ D ω)) ≤
        tableProbability (T := TerminalAddress S.template S.depth_pos) p
          (fun ω => centerExposureAtom (actualCenterExposure S.template x bits) ω.selectors) * p := by
      by_cases hd : routeHasNoDefault S.template hM (centerTableAssignment S.template bits) x
      · have heq : tableProbability p (fun ω =>
            centerExposureAtom (actualCenterExposure S.template x bits) ω.selectors ∧
            (E ω ∧ ¬ D ω)) = 0 := by
          apply (tableProbability_congr p _ (fun _ => False) ?_).trans (tableProbability_false p)
          intro ω
          constructor
          · rintro ⟨ha, _, hn⟩
            apply hn
            exact (center_atom_noDefault_iff S.template hM x bits ω.selectors
              (centerTableAssignment S.template bits) ha
              (centerTableAssignment_satisfies_atom S.template x bits)).2 hd
          · exact False.elim
        rw [heq]
        exact mul_nonneg (tableProbability_nonneg p hp.le hp₁ _) hp.le
      · obtain ⟨v, hv, hprefix⟩ := center_atom_default_vertex_exists S.template hM x bits hd
        let pairs := sampleVertexPairs S.sample S.template v s₁ k
        have hmono := tableProbability_mono p hp.le hp₁
          (fun ω => centerExposureAtom (actualCenterExposure S.template x bits) ω.selectors ∧
            (E ω ∧ ¬ D ω))
          (fun ω => centerExposureAtom (actualCenterExposure S.template x bits) ω.selectors ∧
            ∃ r : PowerParams s₀ s₁,
              logLocalAllMiss S.template hM S.depth_pos s₀ s₁ x k
                (fun i => ⟨v, candidatePairEdge pairs i⟩)
                (fun i => S.sample.z (candidatePairIndex pairs i)) r ω) (by
              intro ω hω
              exact ⟨hω.1, sampled_missed_center_forces_vertex_miss S x hx bits ω
                hω.1 v (hprefix ω.selectors hω.1) hv hω.2.1⟩)
        exact hmono.trans (sampled_scheduled_vertex_continuum_joint_miss_bound S
          hs₀ hs hp.le hp₁ x bits v)
    calc
      _ ≤ ∑ bits : SelectorEdge S.branching S.depth → Bool,
          tableProbability (T := TerminalAddress S.template S.depth_pos) p
            (fun ω => centerExposureAtom (actualCenterExposure S.template x bits) ω.selectors) * p :=
        Finset.sum_le_sum fun bits _ => hbits bits
      _ = p := by
        rw [← Finset.sum_mul, actual_center_atoms_sum_one S.template S.depth_pos p x, one_mul]
  have hcover := tableProbability_two_event_cover p hp.le hp₁ E D (fun ω => E ω ∧ ¬ D ω) (by
    intro ω hω
    by_cases hd : D ω
    · exact Or.inl hd
    · exact Or.inr ⟨hω, hd⟩)
  exact hcover.trans (by linarith)

end ContinuumRemainder
