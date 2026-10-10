import ErdosSimilarityGrowingGaps.RoutingProbabilityFinite
import ErdosSimilarityGrowingGaps.RoutingSeparation
import ErdosSimilarityGrowingGaps.RoutingFactorization
import ErdosSimilarityGrowingGaps.RoutingEntropy
import ErdosSimilarityGrowingGaps.CandidateBounds
import ErdosSimilarityGrowingGaps.RoutingSchedule

/-!
The finite probability law on ACTUAL active original indices, and its
boundary-complete union bound over the whole real parameter rectangle.
-/
namespace ErdosSimilarityGrowingGaps

open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency false

noncomputable def activeLocalCandidates {M d P : ℕ} (c : RoutingTemplate M d)
    (v : InternalNode M d) (children : Fin P → Fin (M - 1)) (indices : Fin P → ℕ)
    {s₀ s₁ : ℝ} (k : ℤ) (r : PowerParams s₀ s₁) : Finset (Fin P) :=
  Finset.univ.filter fun i => r ∈ powerActivation (indices i) k
    (c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, children i⟩))
    ((c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, children i⟩) : ℝ) +
      c.edgeLength (RoutingTemplate.selectorRoutingEdge ⟨v, children i⟩))

noncomputable def activeLocalIndex {M d P : ℕ} (c : RoutingTemplate M d)
    (v : InternalNode M d) (children : Fin P → Fin (M - 1)) (indices : Fin P → ℕ)
    {s₀ s₁ : ℝ} (k : ℤ) (r : PowerParams s₀ s₁) :
    Fin (activeLocalCandidates c v children indices k r).card → Fin P :=
  fun j => ((activeLocalCandidates c v children indices k r).equivFin.symm j).val

theorem activeLocalIndex_injective {M d P : ℕ} (c : RoutingTemplate M d)
    (v : InternalNode M d) (children : Fin P → Fin (M - 1)) (indices : Fin P → ℕ)
    {s₀ s₁ : ℝ} (k : ℤ) (r : PowerParams s₀ s₁) :
    Function.Injective (activeLocalIndex c v children indices k r) := by
  intro i j hij
  exact ((activeLocalCandidates c v children indices k r).equivFin.symm).injective
    (Subtype.ext hij)

theorem activeLocalIndex_active {M d P : ℕ} (c : RoutingTemplate M d)
    (v : InternalNode M d) (children : Fin P → Fin (M - 1)) (indices : Fin P → ℕ)
    {s₀ s₁ : ℝ} (k : ℤ) (r : PowerParams s₀ s₁)
    (j : Fin (activeLocalCandidates c v children indices k r).card) :
    r ∈ powerActivation (indices (activeLocalIndex c v children indices k r j)) k
      (c.edgeStart (RoutingTemplate.selectorRoutingEdge
        ⟨v, children (activeLocalIndex c v children indices k r j)⟩))
      ((c.edgeStart (RoutingTemplate.selectorRoutingEdge
        ⟨v, children (activeLocalIndex c v children indices k r j)⟩) : ℝ) +
        c.edgeLength (RoutingTemplate.selectorRoutingEdge
          ⟨v, children (activeLocalIndex c v children indices k r j)⟩)) := by
  exact (Finset.mem_filter.1
    (((activeLocalCandidates c v children indices k r).equivFin.symm j).property)).2

theorem actualLocalAllMiss_iff_active_tests {M d P : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (s₀ s₁ x : ℝ) (k : ℤ)
    (v : InternalNode M d) (children : Fin P → Fin (M - 1)) (indices : Fin P → ℕ)
    (r : PowerParams s₀ s₁)
    (ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd)) :
    actualLocalAllMiss c hM hd s₀ s₁ x k (fun i => ⟨v, children i⟩) indices r ω ↔
      localRoutingAllMiss
        (localOwnAddresses c v (fun j => children (activeLocalIndex c v children indices k r j))
          (fun j => powerPoint (dyadic (indices (activeLocalIndex c v children indices k r j)))
            ((2 : ℝ) ^ k) (x, r)))
        (localTerminalAddresses c hM hd v
          (fun j => children (activeLocalIndex c v children indices k r j))
          (fun j => powerPoint (dyadic (indices (activeLocalIndex c v children indices k r j)))
            ((2 : ℝ) ^ k) (x, r))) ω := by
  constructor
  · intro h j
    exact h _ (activeLocalIndex_active c v children indices k r j)
  · intro h i hi
    have himem : i ∈ activeLocalCandidates c v children indices k r :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩
    obtain ⟨j, hj⟩ := ((activeLocalCandidates c v children indices k r).equivFin.symm).surjective
      ⟨i, himem⟩
    have heq : activeLocalIndex c v children indices k r j = i := congrArg Subtype.val hj
    simpa only [localRoutingSuccess, localOwnAddresses, localTerminalAddresses, heq] using h j

/-- Exact joint failure on the genuine center atom for EVERY fixed real
parameter. Both own and terminal separation come from actual dyadic geometry. -/
theorem actual_fixed_parameter_joint_miss {M d P : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (hL : 0 < c.baseLength) (hU : 4 ≤ c.origin)
    (p s₀ s₁ x : ℝ) (m : ℕ) (k : ℤ) (hgap : 3 ≤ (m : ℝ) * s₀)
    (bits : SelectorEdge M d → Bool) (v : InternalNode M d)
    (children : Fin P → Fin (M - 1)) (indices : Fin P → ℕ)
    (hinj : Function.Injective (fun i => (children i, indices i)))
    (hmul : ∀ i, ∃ n, m * n = indices i) (r : PowerParams s₀ s₁) :
    tableProbability p (fun ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors ∧
      actualLocalAllMiss c hM hd s₀ s₁ x k (fun i => ⟨v, children i⟩) indices r ω) =
    tableProbability (T := TerminalAddress c hd) p
      (fun ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors) *
        (1 - p / 2) ^ (activeLocalCandidates c v children indices k r).card := by
  let ix := activeLocalIndex c v children indices k r
  have hsep := active_original_local_address_separation c hM hd hL hU s₀ s₁ x m k hgap
    bits v (fun j => children (ix j)) (fun j => indices (ix j))
    (fun i j hij => activeLocalIndex_injective c v children indices k r (hinj hij))
    (fun j => hmul (ix j)) r (fun j => activeLocalIndex_active c v children indices k r j)
  have hevent : (fun ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors ∧
      actualLocalAllMiss c hM hd s₀ s₁ x k (fun i => ⟨v, children i⟩) indices r ω) =
    (fun ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors ∧
      localRoutingAllMiss
        (localOwnAddresses c v (fun j => children (ix j))
          (fun j => powerPoint (dyadic (indices (ix j))) ((2 : ℝ) ^ k) (x, r)))
        (localTerminalAddresses c hM hd v (fun j => children (ix j))
          (fun j => powerPoint (dyadic (indices (ix j))) ((2 : ℝ) ^ k) (x, r))) ω) := by
    funext ω
    exact propext (and_congr_right fun _ => actualLocalAllMiss_iff_active_tests
      c hM hd s₀ s₁ x k v children indices r ω)
  rw [hevent]
  exact joint_center_atom_all_miss p (actualCenterExposure c x bits) _ _ hsep

/-- The representative union bound now concerns ACTUAL routing successes, with
the actual real parameter rectangle and the exact active-index joint law. -/
theorem actual_continuum_joint_miss_bound {M d P : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (hL : 0 < c.baseLength) (hU : 4 ≤ c.origin)
    (p s₀ s₁ x η : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hs : s₀ ≤ s₁)
    (m : ℕ) (k : ℤ) (hgap : 3 ≤ (m : ℝ) * s₀)
    (bits : SelectorEdge M d → Bool) (v : InternalNode M d)
    (children : Fin P → Fin (M - 1)) (indices : Fin P → ℕ)
    (hinj : Function.Injective (fun i => (children i, indices i)))
    (hmul : ∀ i, ∃ n, m * n = indices i) (ell : ℕ)
    (hell : ∀ i, c.edgeLength (RoutingTemplate.selectorRoutingEdge ⟨v, children i⟩) = ell)
    (hmany : ∀ r : PowerParams s₀ s₁, η * ((M : ℝ) - 1) * ell ≤
      (activeLocalCandidates c v children indices k r).card) :
    tableProbability p (fun ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors ∧
      ∃ r : PowerParams s₀ s₁,
        actualLocalAllMiss c hM hd s₀ s₁ x k (fun i => ⟨v, children i⟩) indices r ω) ≤
    tableProbability (T := TerminalAddress c hd) p
      (fun ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors) *
      (20 * (P * (3 + 2 ^ (2 * ell + 3)) + 5) ^ 2 : ℕ) *
      Real.exp (-(p * η * ((M : ℝ) - 1) / 2) * ell) := by
  classical
  obtain ⟨reps, hcard, hrep⟩ := actual_routing_local_representatives c hM hd hL s₀ s₁ x hs k
    (fun i => ⟨v, children i⟩) indices ell hell
  have hub := tableProbability_union_bound p hp₀ hp₁ reps
    (fun ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors ∧
      ∃ r : PowerParams s₀ s₁,
        actualLocalAllMiss c hM hd s₀ s₁ x k (fun i => ⟨v, children i⟩) indices r ω)
    (fun r ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors ∧
      actualLocalAllMiss c hM hd s₀ s₁ x k (fun i => ⟨v, children i⟩) indices r ω) (by
        intro ω hω
        obtain ⟨ha, r, hr⟩ := hω
        obtain ⟨r', hr', heq⟩ := hrep r
        exact ⟨r', hr', ha, (heq ω).2 hr⟩)
  apply hub.trans
  have ha := tableProbability_nonneg (T := TerminalAddress c hd) p hp₀ hp₁
    (fun ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors)
  calc
    _ ≤ ∑ _r ∈ reps,
        tableProbability (T := TerminalAddress c hd) p
          (fun ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors) *
        Real.exp (-(p * η * ((M : ℝ) - 1) / 2) * ell) := by
      apply Finset.sum_le_sum
      intro r _
      rw [actual_fixed_parameter_joint_miss c hM hd hL hU p s₀ s₁ x m k hgap bits v
        children indices hinj hmul r]
      exact mul_le_mul_of_nonneg_left (fair_selector_terminal_miss_window_bound p η hp₀ hp₁
        M _ ell (hmany r)) ha
    _ = tableProbability (T := TerminalAddress c hd) p
        (fun ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors) *
      (reps.card : ℝ) * Real.exp (-(p * η * ((M : ℝ) - 1) / 2) * ell) := by
      simp [mul_comm, mul_left_comm, mul_assoc]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      apply mul_le_mul_of_nonneg_left _ ha
      exact_mod_cast hcard

noncomputable def vertexWindowLength {M d : ℕ} (c : RoutingTemplate M d)
    (v : InternalNode M d) : ℕ :=
  RoutingTemplate.lengthAt M c.gap c.baseLength (d - v.1.val)

noncomputable def vertexWindowStart {M d : ℕ} (c : RoutingTemplate M d)
    (v : InternalNode M d) (i : Fin (M - 1)) : ℕ :=
  c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, i⟩)

noncomputable def vertexPotentialPairs {M d : ℕ} (c : RoutingTemplate M d)
    (v : InternalNode M d) (s₀ s₁ : ℝ) (m N : ℕ) (k : ℤ) :
    Finset (Fin (M - 1) × ℕ) :=
  potentialOriginalPairs s₀ s₁ m N c.origin
    (RoutingTemplate.span M c.gap c.baseLength d) k
    (fun i => ((vertexWindowStart c v i : ℝ),
      (vertexWindowStart c v i : ℝ) + vertexWindowLength c v))

theorem candidatePair_active_card {W : ℕ} (pairs : Finset (Fin W × ℕ))
    (C : Fin W × ℕ → Prop) :
    (Finset.univ.filter fun i : Fin pairs.card =>
      C (candidatePairEdge pairs i, candidatePairIndex pairs i)).card =
      (pairs.filter C).card := by
  let f := fun i : Fin pairs.card => (candidatePairEdge pairs i, candidatePairIndex pairs i)
  have heq : (Finset.univ.filter fun i => C (f i)).image f = pairs.filter C := by
    ext q
    constructor
    · intro h
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 h
      exact Finset.mem_filter.2 ⟨(candidatePairEnumeration pairs i).property,
        (Finset.mem_filter.1 hi).2⟩
    · intro h
      obtain ⟨i, hi₁, hi₂⟩ := candidatePairEnumeration_complete pairs q (Finset.mem_filter.1 h).1
      have hi : f i = q := Prod.ext hi₁ hi₂
      exact Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _,
        by rw [hi]; exact (Finset.mem_filter.1 h).2⟩, hi⟩
  rw [← heq]
  exact (Finset.card_image_of_injective _ (candidatePairEnumeration_injective pairs)).symm

theorem vertex_candidate_multiples {M d : ℕ} (c : RoutingTemplate M d)
    (v : InternalNode M d) (s₀ s₁ : ℝ) (m N : ℕ) (k : ℤ)
    (i : Fin (vertexPotentialPairs c v s₀ s₁ m N k).card) :
    ∃ n, m * n = candidatePairIndex (vertexPotentialPairs c v s₀ s₁ m N k) i := by
  have h := (candidatePairEnumeration (vertexPotentialPairs c v s₀ s₁ m N k) i).property
  obtain ⟨hc, _⟩ := (mem_potentialOriginalPairs_iff _ _ _ _ _ _ _ _ _).1 h
  obtain ⟨n, _, _, hn⟩ := (mem_candidateOriginalIndices_iff _ _ _ _ _ _).1 hc
  exact ⟨n, hn⟩

theorem vertex_active_card {M d : ℕ} (c : RoutingTemplate M d)
    (v : InternalNode M d) (s₀ s₁ : ℝ) (m N : ℕ) (k : ℤ)
    (r : PowerParams s₀ s₁) :
    (activeLocalCandidates c v
      (candidatePairEdge (vertexPotentialPairs c v s₀ s₁ m N k))
      (candidatePairIndex (vertexPotentialPairs c v s₀ s₁ m N k)) k r).card =
      ((vertexPotentialPairs c v s₀ s₁ m N k).filter fun q =>
        r ∈ powerActivation q.2 k (vertexWindowStart c v q.1)
          ((vertexWindowStart c v q.1 : ℝ) + vertexWindowLength c v)).card := by
  simpa only [activeLocalCandidates, vertexWindowStart, vertexWindowLength,
    RoutingTemplate.edgeLength, RoutingTemplate.selectorRoutingEdge] using
      candidatePair_active_card (vertexPotentialPairs c v s₀ s₁ m N k)
        (fun q => r ∈ powerActivation q.2 k (vertexWindowStart c v q.1)
          ((vertexWindowStart c v q.1 : ℝ) + vertexWindowLength c v))

theorem scheduled_vertex_active_count {K : ℕ} {k : ℤ} {N : ℕ} {p : ℝ}
    (s : RoutingSchedule K k N p) (hK : 2 ≤ K) (v : InternalNode s.branching s.depth)
    (r : PowerParams (1 / (K : ℝ)) K) :
    routingActivationRate K * ((s.branching : ℝ) - 1) * vertexWindowLength s.template v ≤
      (activeLocalCandidates s.template v
        (candidatePairEdge (vertexPotentialPairs s.template v (1 / (K : ℝ)) K
          (candidateStride (1 / (K : ℝ))) N k))
        (candidatePairIndex (vertexPotentialPairs s.template v (1 / (K : ℝ)) K
          (candidateStride (1 / (K : ℝ))) N k)) k r).card := by
  have hK₀ : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hM₁ : 1 ≤ s.branching := by have := s.branching_ge_two; omega
  have hstride := candidateStride_gap (1 / (K : ℝ)) (by positivity)
  have hbase : s.template.baseLength ≤ vertexWindowLength s.template v :=
    RoutingTemplate.base_le_length _ _ _ _ hM₁
  have hlen : 2 * ((candidateStride (1 / (K : ℝ)) : ℝ) * (K : ℝ)) ≤
      vertexWindowLength s.template v := by
    have hb : (s.template.baseLength : ℝ) ≤ vertexWindowLength s.template v := by
      exact_mod_cast hbase
    calc
      _ = 2 * (candidateStride (1 / (K : ℝ)) : ℝ) * (K : ℝ) := by ring
      _ ≤ _ := s.active_count_guard.trans hb
  have htail := (candidateTailStart_guards K N s.template.origin k s.tail_guard).2
  have hends : ∀ i : Fin (s.branching - 1),
      (vertexWindowStart s.template v i : ℝ) + vertexWindowLength s.template v ≤
        (s.template.origin : ℝ) +
          RoutingTemplate.span s.branching s.template.gap s.template.baseLength s.depth := by
    intro i
    have h := (s.template.edgeEnd_within_total hM₁ s.length_pos
      (RoutingTemplate.selectorRoutingEdge ⟨v, i⟩)).2
    have hl := RoutingTemplate.length_positive s.branching s.template.gap
      s.template.baseLength (s.depth - v.1.val) hM₁ s.length_pos
    change vertexWindowStart s.template v i + vertexWindowLength s.template v - 1 + 1 ≤
      s.template.origin +
        RoutingTemplate.span s.branching s.template.gap s.template.baseLength s.depth at h
    change 0 < vertexWindowLength s.template v at hl
    have hh : vertexWindowStart s.template v i + vertexWindowLength s.template v ≤
        s.template.origin +
          RoutingTemplate.span s.branching s.template.gap s.template.baseLength s.depth := by
      omega
    exact_mod_cast hh
  have htails : ∀ i : Fin (s.branching - 1), (K : ℝ) * N ≤
      (vertexWindowStart s.template v i : ℝ) + (k : ℝ) := by
    intro i
    have hstart : (s.template.origin : ℝ) ≤ vertexWindowStart s.template v i := by
      exact_mod_cast s.template.edgeStart_ge_origin (RoutingTemplate.selectorRoutingEdge ⟨v, i⟩)
    linarith
  have hc := (potentialOriginalPairs_active_count (1 / (K : ℝ)) K s.template.origin
    (RoutingTemplate.span s.branching s.template.gap s.template.baseLength s.depth)
    (candidateStride (1 / (K : ℝ))) N (fun i => (vertexWindowStart s.template v i : ℝ))
    (vertexWindowLength s.template v) k (by positivity) hstride.1 hstride.2.le
    hlen hends htails r).1
  rw [vertex_active_card]
  convert hc using 1
  · rw [Nat.cast_sub hM₁]
    unfold routingActivationRate
    ring
  · rfl

/-- Every actual scheduled vertex, with its canonical original-tail candidate
list, has atom-weighted continuum miss probability at most p. -/
theorem scheduled_vertex_continuum_joint_miss_bound {K : ℕ} {k : ℤ} {N : ℕ} {p : ℝ}
    (s : RoutingSchedule K k N p) (hK : 2 ≤ K) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (x : ℝ) (bits : SelectorEdge s.branching s.depth → Bool)
    (v : InternalNode s.branching s.depth) :
    let pairs := vertexPotentialPairs s.template v (1 / (K : ℝ)) K
      (candidateStride (1 / (K : ℝ))) N k
    tableProbability p (fun ω =>
      centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors ∧
      ∃ r : PowerParams (1 / (K : ℝ)) K,
        actualLocalAllMiss s.template (by have := s.branching_ge_two; omega) s.depth_pos
          (1 / (K : ℝ)) K x k (fun i => ⟨v, candidatePairEdge pairs i⟩)
          (candidatePairIndex pairs) r ω) ≤
      tableProbability (T := TerminalAddress s.template s.depth_pos) p
        (fun ω => centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors) * p := by
  dsimp only
  let pairs := vertexPotentialPairs s.template v (1 / (K : ℝ)) K
    (candidateStride (1 / (K : ℝ))) N k
  have hM₀ : 0 < s.branching := by have := s.branching_ge_two; omega
  have hK₀ : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hstride := candidateStride_gap (1 / (K : ℝ)) (by positivity)
  have hs : 1 / (K : ℝ) ≤ (K : ℝ) := by
    have hK₁ : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
    apply (div_le_iff₀ hK₀).2
    nlinarith
  have hU := (candidateTailStart_guards K N s.template.origin k s.tail_guard).1
  have hb := actual_continuum_joint_miss_bound s.template hM₀ s.depth_pos s.length_pos hU
    p (1 / (K : ℝ)) K x (routingActivationRate K) hp₀ hp₁ hs
    (candidateStride (1 / (K : ℝ))) k hstride.2.le bits v
    (candidatePairEdge pairs) (candidatePairIndex pairs)
    (candidatePairEnumeration_injective pairs)
    (vertex_candidate_multiples s.template v (1 / (K : ℝ)) K _ N k)
    (vertexWindowLength s.template v) (fun _ => rfl)
    (scheduled_vertex_active_count s hK v)
  have hP : pairs.card ≤ (s.branching - 1) * candidateLabelBudget s.template.origin
      (RoutingTemplate.span s.branching s.template.gap s.template.baseLength s.depth) k :=
    potentialOriginalPairs_card_le _ _ _ _ _ _ _ _
  have hbase : s.template.baseLength ≤ vertexWindowLength s.template v :=
    RoutingTemplate.base_le_length _ _ _ _ (by have := s.branching_ge_two; omega)
  have he := (routingSchedule_node_entropy_lt s pairs.card (vertexWindowLength s.template v)
    hP hbase).le
  have ha := tableProbability_nonneg (T := TerminalAddress s.template s.depth_pos) p hp₀ hp₁
    (fun ω => centerExposureAtom (actualCenterExposure s.template x bits) ω.selectors)
  apply hb.trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he ha

end ErdosSimilarityGrowingGaps
