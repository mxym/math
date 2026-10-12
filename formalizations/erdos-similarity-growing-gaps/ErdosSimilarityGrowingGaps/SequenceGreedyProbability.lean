import ErdosSimilarityGrowingGaps.SequenceGreedyFamily
import ErdosSimilarityGrowingGaps.SequenceStableProbability

namespace ErdosSimilarityGrowingGaps

open Set MeasureTheory
attribute [local instance] Classical.propDecidable Classical.decEq

/-- A missed-center witness over an arbitrary finite test family forces the
local all-miss event for any finite candidate list whose indices lie in that
family.  The proof keeps the actual sequence index and the routing slot
separate, so no arithmetic reindexing assumption is hidden. -/
theorem sequence_missed_center_forces_vertex_miss_of_list
    {K : ℕ} {k : ℤ} {N : ℕ} {p : ℝ}
    {P : ℕ} (Z : LogScale) (s : RoutingSchedule K k N p)
    (hK : 2 ≤ K) (tests : Finset ℕ)
    (children : Fin P → Fin (s.branching - 1)) (indices : Fin P → ℕ)
    (hmem : ∀ i, indices i ∈ tests)
    (x : ℝ) (hx : x ∈ actualStableCenters s.template)
    (bits : SelectorEdge s.branching s.depth → Bool)
    (ω : FiniteRoutingTables (SelectorAddress s.template)
      (TerminalAddress s.template s.depth_pos))
    (hσ : centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors)
    (v : InternalNode s.branching s.depth)
    (hprefix : (List.ofFn v.2).IsPrefix (List.ofFn
      (routeLeaf s.template (by have := s.branching_ge_two; omega) ω.selectors x)))
    (hdefault : ∀ i : Fin (s.branching - 1), bits ⟨v, i⟩ = false)
    (hmiss : x ∈ sequenceMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
      Z tests k (globalRoutingWindows s.template)
      (routingInnerBuffer s.template (by have := s.branching_ge_two; omega)
        s.depth_pos p ω)) :
    ∃ r : PowerParams (1 / (K : ℝ)) K,
      sequenceLocalAllMiss Z s.template
        (by have := s.branching_ge_two; omega) s.depth_pos
        (1 / (K : ℝ)) K x k (fun i => ⟨v, children i⟩) indices r ω := by
  obtain ⟨r, hr⟩ := (mem_missedCenters_iff _ _ _ x).1 hmiss
  refine ⟨r, ?_⟩
  intro i hi hsuccess
  let e : RoutingEdge s.branching s.depth :=
    RoutingTemplate.selectorRoutingEdge ⟨v, children i⟩
  have hactive : r ∈ sequenceWindowActivations Z (indices i) k
      (globalRoutingWindows s.template) := by
    apply Set.mem_iUnion.2
    refine ⟨(globalRoutingEdgeEnumeration s.branching s.depth).symm e, ?_⟩
    dsimp [e]
    simp only [globalRoutingWindows, Equiv.apply_symm_apply]
    exact hi
  let j : {m // m ∈ tests} := ⟨indices i, hmem i⟩
  apply hr j hactive
  apply Metric.self_subset_thickening (routingBufferRadius_pos s.template p (by
    have hrate := routingActivationRate_pos K hK
    have hb : 0 < (s.branching : ℝ) - 1 := by
      have hbg : 2 ≤ s.branching := s.branching_ge_two
      have hbr : (2 : ℝ) ≤ (s.branching : ℝ) := by exact_mod_cast hbg
      linarith
    have hprod : 0 < routingActivationRate K * ((s.branching : ℝ) - 1) / 2 := by
      positivity
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith [s.decay_pos]))
  exact sequence_stable_local_success_mem_routedSet Z s.template
    (by have := s.branching_ge_two; omega) s.depth_pos s.length_pos s.gap_guard
    (1 / (K : ℝ)) K x (indices i) k r ω bits hσ v (children i)
    hprefix hdefault hx hi hsuccess

/-- The fixed-center probability reduction for an arbitrary finite actual
candidate list.  It is the center-atom partition plus the no-default budget;
the only analytic input is the supplied local vertex estimate. -/
theorem sequence_stable_missed_center_probability_le_of_vertex_bound_of_list
    {K : ℕ} {k : ℤ} {N : ℕ} {p : ℝ}
    {P : ℕ} (Z : LogScale) (s : RoutingSchedule K k N p)
    (hK : 2 ≤ K) (hp : 0 < p) (hp₁ : p ≤ 1)
    (tests : Finset ℕ)
    (children : Fin P → Fin (s.branching - 1)) (indices : Fin P → ℕ)
    (hmem : ∀ i, indices i ∈ tests)
    (x : ℝ) (hx : x ∈ actualStableCenters s.template)
    (hvertex : ∀ (bits : SelectorEdge s.branching s.depth → Bool)
      (v : InternalNode s.branching s.depth),
      tableProbability p (fun ω =>
        centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors ∧
        ∃ r : PowerParams (1 / (K : ℝ)) K,
          sequenceLocalAllMiss Z s.template
            (by have := s.branching_ge_two; omega) s.depth_pos
            (1 / (K : ℝ)) K x k (fun i => ⟨v, children i⟩) indices r ω) ≤
        tableProbability (T := TerminalAddress s.template s.depth_pos) p
          (fun ω => centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors) * p) :
    tableProbability p (fun ω => x ∈ sequenceMissedCenters
      (s₀ := 1 / (K : ℝ)) (s₁ := K) Z tests k
      (globalRoutingWindows s.template)
      (routingInnerBuffer s.template (by have := s.branching_ge_two; omega)
        s.depth_pos p ω)) ≤ 2 * p := by
  let hM : 0 < s.branching := by have := s.branching_ge_two; omega
  let E := fun ω : FiniteRoutingTables (SelectorAddress s.template)
      (TerminalAddress s.template s.depth_pos) =>
    x ∈ sequenceMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
      Z tests k (globalRoutingWindows s.template)
      (routingInnerBuffer s.template hM s.depth_pos p ω)
  let D := fun ω : FiniteRoutingTables (SelectorAddress s.template)
      (TerminalAddress s.template s.depth_pos) =>
    routeHasNoDefault s.template hM ω.selectors x
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
      by_cases hd : routeHasNoDefault s.template hM
          (centerTableAssignment s.template bits) x
      · have heq : tableProbability p (fun ω =>
            centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors ∧
            (E ω ∧ ¬D ω)) = 0 := by
          apply (tableProbability_congr p _ (fun _ => False) ?_).trans
            (tableProbability_false p)
          intro ω
          constructor
          · rintro ⟨ha, _, hn⟩
            apply hn
            exact (center_atom_noDefault_iff s.template hM x bits ω.selectors
              (centerTableAssignment s.template bits)
              ha (centerTableAssignment_satisfies_atom s.template x bits)).2 hd
          · exact False.elim
        rw [heq]
        exact mul_nonneg
          (tableProbability_nonneg p hp.le hp₁ _) hp.le
      · obtain ⟨v, hv, hprefix⟩ := center_atom_default_vertex_exists
          s.template hM x bits hd
        have hmono := tableProbability_mono p hp.le hp₁
          (fun ω => centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors ∧
            (E ω ∧ ¬D ω)) (fun ω =>
            centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors ∧
            ∃ r : PowerParams (1 / (K : ℝ)) K,
              sequenceLocalAllMiss Z s.template hM s.depth_pos
                (1 / (K : ℝ)) K x k (fun i => ⟨v, children i⟩) indices r ω) (by
              intro ω hω
              exact ⟨hω.1, sequence_missed_center_forces_vertex_miss_of_list
                Z s hK tests children indices hmem x hx bits ω hω.1 v
                (hprefix ω.selectors hω.1) hv hω.2.1⟩)
        exact hmono.trans (hvertex bits v)
    calc
      _ ≤ ∑ bits : SelectorEdge s.branching s.depth → Bool,
          tableProbability (T := TerminalAddress s.template s.depth_pos) p
            (fun ω => centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors) * p :=
        Finset.sum_le_sum fun bits _ => hbits bits
      _ = p := by
        rw [← Finset.sum_mul, actual_center_atoms_sum_one s.template s.depth_pos p x,
          one_mul]
  have hcover := tableProbability_two_event_cover p hp.le hp₁ E D
    (fun ω => E ω ∧ ¬ D ω) (by
      intro ω hω
      by_cases hd : D ω
      · exact Or.inl hd
      · exact Or.inr ⟨hω, hd⟩)
  exact hcover.trans (by linarith)

/-- The continuum estimate for an arbitrary actual finite candidate list, with
its logarithmic gap and cardinality hypotheses exposed explicitly. -/
theorem scheduled_vertex_sequence_continuum_joint_miss_bound_of_list
    {K : ℕ} {k : ℤ} {N : ℕ} {p : ℝ}
    {M d P : ℕ} (Z : LogScale) (s : RoutingSchedule K k N p)
    (hK : 2 ≤ K) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hU : 4 ≤ s.template.origin)
    (x : ℝ) (bits : SelectorEdge s.branching s.depth → Bool)
    (v : InternalNode s.branching s.depth) (children : Fin P → Fin (s.branching - 1))
    (indices : Fin P → ℕ) (η : ℝ) (ell : ℕ)
    (hell : ∀ i, s.template.edgeLength
      (RoutingTemplate.selectorRoutingEdge ⟨v, children i⟩) = ell)
    (hindex : Function.Injective (fun i => (children i, indices i)))
    (hgap : ∀ i j, i ≠ j → children i = children j →
      3 ≤ (1 / (K : ℝ)) * |Z.z (indices j) - Z.z (indices i)|)
    (hmany : ∀ r : PowerParams (1 / (K : ℝ)) K,
      η * ((s.branching : ℝ) - 1) * (ell : ℝ) ≤
        (sequenceActiveLocalCandidates Z s.template v children indices k r).card) :
    tableProbability p (fun ω =>
      centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors ∧
      ∃ r : PowerParams (1 / (K : ℝ)) K,
        sequenceLocalAllMiss Z s.template
          (by have := s.branching_ge_two; omega) s.depth_pos
          (1 / (K : ℝ)) K x k (fun i => ⟨v, children i⟩) indices r ω) ≤
      tableProbability (T := TerminalAddress s.template s.depth_pos) p
        (fun ω => centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors) *
      (20 * (P * (3 + 2 ^ (2 * ell + 3)) + 5) ^ 2 : ℕ) *
      Real.exp (-(p * η * ((s.branching : ℝ) - 1) / 2) * ell) := by
  apply sequence_continuum_joint_miss_bound_of_lower_gap Z s.template
    (by have := s.branching_ge_two; omega) s.depth_pos s.length_pos hU p
    (1 / (K : ℝ)) K x η hp₀ hp₁
    (by have hK' : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
        have h₁ : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (show 1 ≤ K by omega)
        apply (div_le_iff₀ hK').2
        nlinarith)
    k bits v children indices ell hell hindex
  · exact hgap
  · exact hmany

end ErdosSimilarityGrowingGaps
