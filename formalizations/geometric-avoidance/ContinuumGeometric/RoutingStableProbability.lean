import ContinuumGeometric.RoutingLocalProbability
import ContinuumGeometric.RoutingStableGeometry
import ContinuumGeometric.RoutingAssembly
import ContinuumGeometric.NoDefaultProbability
import ContinuumGeometric.RoutingCenterAtoms

/-! Actual fixed-center failure inclusion and the atom-weighted continuum law. -/
namespace ContinuumGeometric

open scoped BigOperators
open Set
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency false

theorem actual_missed_center_forces_vertex_miss {K : ℕ} {k : ℤ} {N : ℕ} {p : ℝ}
    (s : RoutingSchedule K k N p) (hK : 2 ≤ K) (hp : 0 < p)
    (x : ℝ) (hx : x ∈ actualStableCenters s.template)
    (bits : SelectorEdge s.branching s.depth → Bool)
    (ω : FiniteRoutingTables (SelectorAddress s.template)
      (TerminalAddress s.template s.depth_pos))
    (hσ : centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors)
    (v : InternalNode s.branching s.depth)
    (hprefix : (List.ofFn v.2).IsPrefix (List.ofFn
      (routeLeaf s.template (by have := s.branching_ge_two; omega) ω.selectors x)))
    (hdefault : ∀ i : Fin (s.branching - 1), bits ⟨v, i⟩ = false)
    (hmiss : x ∈ powerMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
      (globalRoutingTests s.template K N k) k (globalRoutingWindows s.template)
      (routingInnerBuffer s.template (by have := s.branching_ge_two; omega)
        s.depth_pos p ω)) :
    let pairs := vertexPotentialPairs s.template v (1 / (K : ℝ)) K
      (candidateStride (1 / (K : ℝ))) N k
    ∃ r : PowerParams (1 / (K : ℝ)) K,
      actualLocalAllMiss s.template (by have := s.branching_ge_two; omega) s.depth_pos
        (1 / (K : ℝ)) K x k (fun i => ⟨v, candidatePairEdge pairs i⟩)
        (candidatePairIndex pairs) r ω := by
  dsimp only
  let pairs := vertexPotentialPairs s.template v (1 / (K : ℝ)) K
    (candidateStride (1 / (K : ℝ))) N k
  obtain ⟨r, hr⟩ := (mem_missedCenters_iff _ _ _ x).1 hmiss
  refine ⟨r, ?_⟩
  intro i hi hsuccess
  have hpair := (candidatePairEnumeration pairs i).property
  obtain ⟨hind, _⟩ := (mem_potentialOriginalPairs_iff _ _ _ _ _ _ _ _ _).1 hpair
  have hindex : candidatePairIndex pairs i ∈ globalRoutingTests s.template K N k := hind
  let e : RoutingEdge s.branching s.depth :=
    RoutingTemplate.selectorRoutingEdge ⟨v, candidatePairEdge pairs i⟩
  have hactive : r ∈ windowActivations (candidatePairIndex pairs i) k
      (globalRoutingWindows s.template) := by
    apply Set.mem_iUnion.2
    refine ⟨(globalRoutingEdgeEnumeration s.branching s.depth).symm e, ?_⟩
    simpa only [globalRoutingWindows, Equiv.apply_symm_apply, e] using hi
  apply hr ⟨candidatePairIndex pairs i, hindex⟩ hactive
  apply Metric.self_subset_thickening (routingBufferRadius_pos s.template p hp)
  exact actual_stable_local_success_mem_routedSet s.template
    (by have := s.branching_ge_two; omega) s.depth_pos s.length_pos s.gap_guard
    (1 / (K : ℝ)) K x (candidatePairIndex pairs i) k r ω bits hσ v
    (candidatePairEdge pairs i) hprefix hdefault hx hi hsuccess

theorem actual_stable_bad_density_le {K : ℕ} {k : ℤ} {N : ℕ} {p : ℝ}
    (s : RoutingSchedule K k N p) :
    unitDensity (actualStableCenters s.template)ᶜ ≤ ENNReal.ofReal p := by
  apply (unitDensity_actualStable_compl_le s.template).trans
  apply ENNReal.ofReal_le_ofReal
  rw [dyadic_integer_gap_rpow]
  exact s.stable_boundary_small.le

theorem tableProbability_two_event_cover {S T : Type*} [Fintype S] [Fintype T]
    (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (E F G : FiniteRoutingTables S T → Prop) (hcover : ∀ ω, E ω → F ω ∨ G ω) :
    tableProbability p E ≤ tableProbability p F + tableProbability p G := by
  have h := tableProbability_union_bound p hp₀ hp₁ (Finset.univ : Finset Bool)
    E (fun b => if b then F else G) (by
      intro ω hω
      rcases hcover ω hω with hF | hG
      · exact ⟨true, Finset.mem_univ _, hF⟩
      · exact ⟨false, Finset.mem_univ _, hG⟩)
  simpa only [Fintype.sum_bool, Bool.false_eq_true, Bool.true_eq, ite_false, ite_true,
    add_comm] using h

theorem tableProbability_false {S T : Type*} [Fintype S] [Fintype T] (p : ℝ) :
    tableProbability (S := S) (T := T) p (fun _ => False) = 0 := by
  rw [tableProbability_eq_weight_sum]
  simp

/-- The actual global missed-center event has probability at most 2p at EVERY
stable real center.  The finite template is selected before the center, the
outcome, and all real parameter choices. -/
theorem actual_stable_missed_center_probability_le {K : ℕ} {k : ℤ} {N : ℕ} {p : ℝ}
    (s : RoutingSchedule K k N p) (hK : 2 ≤ K) (hp : 0 < p) (hp₁ : p ≤ 1)
    (x : ℝ) (hx : x ∈ actualStableCenters s.template) :
    tableProbability p (fun ω => x ∈ powerMissedCenters
      (s₀ := 1 / (K : ℝ)) (s₁ := K) (globalRoutingTests s.template K N k) k
      (globalRoutingWindows s.template)
      (routingInnerBuffer s.template (by have := s.branching_ge_two; omega)
        s.depth_pos p ω)) ≤ 2 * p := by
  let hM : 0 < s.branching := by have := s.branching_ge_two; omega
  let E := fun ω : FiniteRoutingTables (SelectorAddress s.template)
      (TerminalAddress s.template s.depth_pos) =>
    x ∈ powerMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
      (globalRoutingTests s.template K N k) k (globalRoutingWindows s.template)
      (routingInnerBuffer s.template hM s.depth_pos p ω)
  let D := fun ω : FiniteRoutingTables (SelectorAddress s.template)
      (TerminalAddress s.template s.depth_pos) => routeHasNoDefault s.template hM ω.selectors x
  have hD : tableProbability p D ≤ p := by
    rw [actual_routeHasNoDefault_probability_rpow s.template hM s.depth_pos p x]
    exact s.no_default_small.le
  have hdefault : tableProbability p (fun ω => E ω ∧ ¬ D ω) ≤ p := by
    rw [actual_center_atom_partition s.template s.depth_pos p x]
    have hbits (bits : SelectorEdge s.branching s.depth → Bool) :
        tableProbability p (fun ω =>
          centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors ∧
          (E ω ∧ ¬D ω)) ≤
        tableProbability (T := TerminalAddress s.template s.depth_pos) p
          (fun ω => centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors) * p := by
      by_cases hd : routeHasNoDefault s.template hM (centerTableAssignment s.template bits) x
      · have heq : tableProbability p (fun ω =>
            centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors ∧
            (E ω ∧ ¬D ω)) = 0 := by
          apply (tableProbability_congr p _ (fun _ => False) ?_).trans (tableProbability_false p)
          intro ω
          constructor
          · rintro ⟨ha, _, hn⟩
            apply hn
            exact (center_atom_noDefault_iff s.template hM x bits ω.selectors
              (centerTableAssignment s.template bits) ha
              (centerTableAssignment_satisfies_atom s.template x bits)).2 hd
          · exact False.elim
        rw [heq]
        exact mul_nonneg (tableProbability_nonneg p hp.le hp₁ _) hp.le
      · obtain ⟨v, hv, hprefix⟩ := center_atom_default_vertex_exists s.template hM x bits hd
        let pairs := vertexPotentialPairs s.template v (1 / (K : ℝ)) K
          (candidateStride (1 / (K : ℝ))) N k
        have hmono := tableProbability_mono p hp.le hp₁
          (fun ω => centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors ∧
            (E ω ∧ ¬D ω))
          (fun ω => centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors ∧
            ∃ r : PowerParams (1 / (K : ℝ)) K,
              actualLocalAllMiss s.template hM s.depth_pos (1 / (K : ℝ)) K x k
                (fun i => ⟨v, candidatePairEdge pairs i⟩) (candidatePairIndex pairs) r ω) (by
              intro ω hω
              exact ⟨hω.1, actual_missed_center_forces_vertex_miss s hK hp x hx bits ω
                hω.1 v (hprefix ω.selectors hω.1) hv hω.2.1⟩)
        exact hmono.trans (scheduled_vertex_continuum_joint_miss_bound s hK hp.le hp₁ x bits v)
    calc
      _ ≤ ∑ bits : SelectorEdge s.branching s.depth → Bool,
          tableProbability (T := TerminalAddress s.template s.depth_pos) p
            (fun ω => centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors) * p :=
        Finset.sum_le_sum fun bits _ => hbits bits
      _ = p := by
        rw [← Finset.sum_mul, actual_center_atoms_sum_one s.template s.depth_pos p x, one_mul]
  have hcover := tableProbability_two_event_cover p hp.le hp₁ E D (fun ω => E ω ∧ ¬D ω) (by
    intro ω hω
    by_cases hd : D ω
    · exact Or.inl hd
    · exact Or.inr ⟨hω, hd⟩)
  exact hcover.trans (by linarith)

end ContinuumGeometric
