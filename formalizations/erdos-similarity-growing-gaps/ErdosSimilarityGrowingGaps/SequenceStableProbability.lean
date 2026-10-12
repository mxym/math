import ErdosSimilarityGrowingGaps.RoutingStableProbability
import ErdosSimilarityGrowingGaps.SequenceStableGeometry
import ErdosSimilarityGrowingGaps.SequenceSignatures
import ErdosSimilarityGrowingGaps.SequenceRoutingProbability
import ErdosSimilarityGrowingGaps.WindowRepair
import ErdosSimilarityGrowingGaps.RoutingAssembly
import ErdosSimilarityGrowingGaps.RoutingCenterAtoms

namespace ErdosSimilarityGrowingGaps

open scoped BigOperators
open Set
attribute [local instance] Classical.propDecidable Classical.decEq

/-- At a stable center, missing every actual sampled active point forces a
vertex-level actual-log miss.  This is the exact sequence analogue of the
finite dyadic default-node reduction. -/
theorem sequence_missed_center_forces_vertex_miss
    {K : ℕ} {k : ℤ} {N : ℕ} {p : ℝ}
    (Z : LogScale) (s : RoutingSchedule K k N p) (hK : 2 ≤ K)
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
      Z (globalRoutingTests s.template K N k) k (globalRoutingWindows s.template)
      (routingInnerBuffer s.template (by have := s.branching_ge_two; omega)
        s.depth_pos p ω)) :
    let pairs := vertexPotentialPairs s.template v (1 / (K : ℝ)) K
      (candidateStride (1 / (K : ℝ))) N k
    ∃ r : PowerParams (1 / (K : ℝ)) K,
      sequenceLocalAllMiss Z s.template (by have := s.branching_ge_two; omega)
        s.depth_pos (1 / (K : ℝ)) K x k
        (fun i => ⟨v, candidatePairEdge pairs i⟩)
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
  have hactive : r ∈ sequenceWindowActivations Z (candidatePairIndex pairs i) k
      (globalRoutingWindows s.template) := by
    apply Set.mem_iUnion.2
    refine ⟨(globalRoutingEdgeEnumeration s.branching s.depth).symm e, ?_⟩
    dsimp [pairs, e]
    simp only [globalRoutingWindows, Equiv.apply_symm_apply]
    change sequencePowerActivation Z (candidatePairIndex
      (vertexPotentialPairs s.template v (1 / (K : ℝ)) K
        (candidateStride (1 / (K : ℝ))) N k) i) k
      (s.template.edgeStart (RoutingTemplate.selectorRoutingEdge
        ⟨v, candidatePairEdge (vertexPotentialPairs s.template v (1 / (K : ℝ)) K
          (candidateStride (1 / (K : ℝ))) N k) i⟩) : ℝ)
      ((s.template.edgeStart (RoutingTemplate.selectorRoutingEdge
        ⟨v, candidatePairEdge (vertexPotentialPairs s.template v (1 / (K : ℝ)) K
          (candidateStride (1 / (K : ℝ))) N k) i⟩) : ℝ) +
        s.template.edgeLength (RoutingTemplate.selectorRoutingEdge
          ⟨v, candidatePairEdge (vertexPotentialPairs s.template v (1 / (K : ℝ)) K
            (candidateStride (1 / (K : ℝ))) N k) i⟩)) r
    exact hi
  apply hr ⟨candidatePairIndex pairs i, hindex⟩ hactive
  have hp : 0 < p := by
    have hrate := routingActivationRate_pos K hK
    have hb : 0 < (s.branching : ℝ) - 1 := by
      have hbg : 2 ≤ s.branching := s.branching_ge_two
      have hbr : (2 : ℝ) ≤ (s.branching : ℝ) := by exact_mod_cast hbg
      linarith
    have hprod : 0 < routingActivationRate K * ((s.branching : ℝ) - 1) / 2 := by
      positivity
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith [s.decay_pos]
  apply Metric.self_subset_thickening (routingBufferRadius_pos s.template p hp)
  exact sequence_stable_local_success_mem_routedSet Z s.template
    (by have := s.branching_ge_two; omega) s.depth_pos s.length_pos s.gap_guard
    (1 / (K : ℝ)) K x (candidatePairIndex pairs i) k r ω bits hσ v
    (candidatePairEdge pairs i) hprefix hdefault hx hi hsuccess

/-! The same reduction with an explicit sample map.  This is the form used by
the annular transfer: the finite dyadic candidate index and the actual
logarithmic sample index are deliberately kept distinct. -/

theorem sequence_missed_center_forces_vertex_miss_sampled
    {K : ℕ} {k : ℤ} {N : ℕ} {p : ℝ}
    (Z : LogScale) (s : RoutingSchedule K k N p) (hK : 2 ≤ K)
    (sample : ℕ → ℕ)
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
      Z ((globalRoutingTests s.template K N k).image sample) k (globalRoutingWindows s.template)
      (routingInnerBuffer s.template (by have := s.branching_ge_two; omega)
        s.depth_pos p ω)) :
    let pairs := vertexPotentialPairs s.template v (1 / (K : ℝ)) K
      (candidateStride (1 / (K : ℝ))) N k
    ∃ r : PowerParams (1 / (K : ℝ)) K,
      sequenceLocalAllMiss Z s.template (by have := s.branching_ge_two; omega)
        s.depth_pos (1 / (K : ℝ)) K x k
        (fun i => ⟨v, candidatePairEdge pairs i⟩)
        (fun i => sample (candidatePairIndex pairs i)) r ω := by
  dsimp only
  let pairs := vertexPotentialPairs s.template v (1 / (K : ℝ)) K
    (candidateStride (1 / (K : ℝ))) N k
  obtain ⟨r, hr⟩ := (mem_missedCenters_iff _ _ _ x).1 hmiss
  refine ⟨r, ?_⟩
  intro i hi hsuccess
  have hpair := (candidatePairEnumeration pairs i).property
  obtain ⟨hind, _⟩ := (mem_potentialOriginalPairs_iff _ _ _ _ _ _ _ _ _).1 hpair
  let e : RoutingEdge s.branching s.depth :=
    RoutingTemplate.selectorRoutingEdge ⟨v, candidatePairEdge pairs i⟩
  have hactive : r ∈ sequenceWindowActivations Z
      (sample (candidatePairIndex pairs i)) k
      (globalRoutingWindows s.template) := by
    apply Set.mem_iUnion.2
    refine ⟨(globalRoutingEdgeEnumeration s.branching s.depth).symm e, ?_⟩
    dsimp [e]
    simp only [globalRoutingWindows, Equiv.apply_symm_apply]
    change sequencePowerActivation Z (sample (candidatePairIndex pairs i)) k
      (s.template.edgeStart (RoutingTemplate.selectorRoutingEdge
        ⟨v, candidatePairEdge pairs i⟩) : ℝ)
      ((s.template.edgeStart (RoutingTemplate.selectorRoutingEdge
        ⟨v, candidatePairEdge pairs i⟩) : ℝ) +
        s.template.edgeLength (RoutingTemplate.selectorRoutingEdge
          ⟨v, candidatePairEdge pairs i⟩)) r
    exact hi
  let j : {m // m ∈ (globalRoutingTests s.template K N k).image sample} :=
    ⟨sample (candidatePairIndex pairs i),
      Finset.mem_image.2 ⟨candidatePairIndex pairs i, hind, rfl⟩⟩
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
    (1 / (K : ℝ)) K x (sample (candidatePairIndex pairs i)) k r ω bits hσ v
    (candidatePairEdge pairs i) hprefix hdefault hx hi hsuccess

/-! Once the local sequence continuum estimate is supplied, the center-atom
partition and the no-default exceptional event assemble it into the global
missed-center bound.  This separates the probabilistic finite routing from
the annular sample-map analysis. -/

theorem sequence_stable_missed_center_probability_le_of_vertex_bound
    {K : ℕ} {k : ℤ} {N : ℕ} {p : ℝ}
    (Z : LogScale) (s : RoutingSchedule K k N p) (hK : 2 ≤ K)
    (hp : 0 < p) (hp₁ : p ≤ 1) (sample : ℕ → ℕ)
    (x : ℝ) (hx : x ∈ actualStableCenters s.template)
    (hvertex : ∀ (bits : SelectorEdge s.branching s.depth → Bool)
      (v : InternalNode s.branching s.depth),
      tableProbability p (fun ω =>
        centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors ∧
        ∃ r : PowerParams (1 / (K : ℝ)) K,
          sequenceLocalAllMiss Z s.template
            (by have := s.branching_ge_two; omega) s.depth_pos
            (1 / (K : ℝ)) K x k
            (fun i => ⟨v, candidatePairEdge (vertexPotentialPairs s.template v
              (1 / (K : ℝ)) K (candidateStride (1 / (K : ℝ))) N k) i⟩)
            (fun i => sample (candidatePairIndex (vertexPotentialPairs s.template v
              (1 / (K : ℝ)) K (candidateStride (1 / (K : ℝ))) N k) i)) r ω) ≤
        tableProbability (T := TerminalAddress s.template s.depth_pos) p
          (fun ω => centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors) * p) :
    tableProbability p (fun ω => x ∈ sequenceMissedCenters
      (s₀ := 1 / (K : ℝ)) (s₁ := K)
      Z ((globalRoutingTests s.template K N k).image sample) k
      (globalRoutingWindows s.template)
      (routingInnerBuffer s.template (by have := s.branching_ge_two; omega)
        s.depth_pos p ω)) ≤ 2 * p := by
  let hM : 0 < s.branching := by have := s.branching_ge_two; omega
  let E := fun ω : FiniteRoutingTables (SelectorAddress s.template)
      (TerminalAddress s.template s.depth_pos) =>
    x ∈ sequenceMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
      Z ((globalRoutingTests s.template K N k).image sample) k
      (globalRoutingWindows s.template)
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
            (E ω ∧ ¬D ω))
          (fun ω => centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors ∧
            ∃ r : PowerParams (1 / (K : ℝ)) K,
              sequenceLocalAllMiss Z s.template hM s.depth_pos
                (1 / (K : ℝ)) K x k
                (fun i => ⟨v, candidatePairEdge (vertexPotentialPairs s.template v
                  (1 / (K : ℝ)) K (candidateStride (1 / (K : ℝ))) N k) i⟩)
                (fun i => sample (candidatePairIndex (vertexPotentialPairs s.template v
                  (1 / (K : ℝ)) K (candidateStride (1 / (K : ℝ))) N k) i)) r ω) (by
              intro ω hω
              exact ⟨hω.1, sequence_missed_center_forces_vertex_miss_sampled
                Z s hK (sample := sample) x hx bits ω hω.1 v
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

/-! The sequence analogue of the scheduled vertex continuum law.  The only
additional inputs are the genuine logarithmic gap and active-count bounds;
both are supplied by the annular counting layer when a concrete schedule is
chosen. -/

theorem scheduled_vertex_sequence_continuum_joint_miss_bound
    {K : ℕ} {k : ℤ} {N : ℕ} {p : ℝ}
    (Z : LogScale) (s : RoutingSchedule K k N p) (hK : 2 ≤ K)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hU : 4 ≤ s.template.origin)
    (x : ℝ) (bits : SelectorEdge s.branching s.depth → Bool)
    (v : InternalNode s.branching s.depth) (η : ℝ)
    (hgap : ∀ i j : Fin (vertexPotentialPairs s.template v
        (1 / (K : ℝ)) K (candidateStride (1 / (K : ℝ))) N k).card,
      i ≠ j →
      candidatePairEdge (vertexPotentialPairs s.template v
        (1 / (K : ℝ)) K (candidateStride (1 / (K : ℝ))) N k) i =
        candidatePairEdge (vertexPotentialPairs s.template v
          (1 / (K : ℝ)) K (candidateStride (1 / (K : ℝ))) N k) j →
      3 ≤ (1 / (K : ℝ)) *
        |Z.z (candidatePairIndex (vertexPotentialPairs s.template v
            (1 / (K : ℝ)) K (candidateStride (1 / (K : ℝ))) N k) j) -
          Z.z (candidatePairIndex (vertexPotentialPairs s.template v
            (1 / (K : ℝ)) K (candidateStride (1 / (K : ℝ))) N k) i)|)
    (hmany : ∀ r : PowerParams (1 / (K : ℝ)) K,
      η * ((s.branching : ℝ) - 1) *
          (vertexWindowLength s.template v : ℝ) ≤
        (sequenceActiveLocalCandidates Z s.template v
          (fun i => candidatePairEdge (vertexPotentialPairs s.template v
            (1 / (K : ℝ)) K (candidateStride (1 / (K : ℝ))) N k) i)
          (fun i => candidatePairIndex (vertexPotentialPairs s.template v
            (1 / (K : ℝ)) K (candidateStride (1 / (K : ℝ))) N k) i)
          k r).card) :
    tableProbability p (fun ω =>
      centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors ∧
      ∃ r : PowerParams (1 / (K : ℝ)) K,
        sequenceLocalAllMiss Z s.template
          (by have := s.branching_ge_two; omega) s.depth_pos
          (1 / (K : ℝ)) K x k
          (fun i => ⟨v, candidatePairEdge (vertexPotentialPairs s.template v
            (1 / (K : ℝ)) K (candidateStride (1 / (K : ℝ))) N k) i⟩)
          (fun i => candidatePairIndex (vertexPotentialPairs s.template v
            (1 / (K : ℝ)) K (candidateStride (1 / (K : ℝ))) N k) i) r ω) ≤
      tableProbability (T := TerminalAddress s.template s.depth_pos) p
        (fun ω => centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors) *
      (20 * ((vertexPotentialPairs s.template v (1 / (K : ℝ)) K
        (candidateStride (1 / (K : ℝ))) N k).card *
        (3 + 2 ^ (2 * vertexWindowLength s.template v + 3)) + 5) ^ 2 : ℕ) *
      Real.exp (-(p * η * ((s.branching : ℝ) - 1) / 2) *
        (vertexWindowLength s.template v : ℝ)) := by
  let pairs := vertexPotentialPairs s.template v (1 / (K : ℝ)) K
    (candidateStride (1 / (K : ℝ))) N k
  let children : Fin pairs.card → Fin (s.branching - 1) :=
    fun i => candidatePairEdge pairs i
  let indices : Fin pairs.card → ℕ := fun i => candidatePairIndex pairs i
  have hM : 0 < s.branching := by have := s.branching_ge_two; omega
  have hindex : Function.Injective (fun i => (children i, indices i)) := by
    simpa [children, indices] using candidatePairEnumeration_injective pairs
  have hell : ∀ i : Fin pairs.card,
      s.template.edgeLength (RoutingTemplate.selectorRoutingEdge
        ⟨v, children i⟩) = vertexWindowLength s.template v := by
    intro i
    rfl
  have hmany' : ∀ r : PowerParams (1 / (K : ℝ)) K,
      η * ((s.branching : ℝ) - 1) *
          (vertexWindowLength s.template v : ℝ) ≤
        (sequenceActiveLocalCandidates Z s.template v children indices k r).card := by
    intro r
    simpa [children, indices, pairs] using hmany r
  simpa [pairs, children, indices] using
    (sequence_continuum_joint_miss_bound_of_lower_gap Z s.template hM s.depth_pos
      s.length_pos hU p (1 / (K : ℝ)) K x η hp₀ hp₁
      (by have hK' : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
          have h₁ : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (show 1 ≤ K by omega)
          apply (div_le_iff₀ hK').2
          nlinarith)
      k bits v children indices (vertexWindowLength s.template v) hell hindex
      (by simpa [children, indices, pairs] using hgap) hmany')

end ErdosSimilarityGrowingGaps
