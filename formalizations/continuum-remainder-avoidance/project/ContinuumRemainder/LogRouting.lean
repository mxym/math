import ContinuumRemainder.LogSignatures
import ContinuumGeometric.RoutingFactorization
import ContinuumGeometric.FiniteRoutingProbability
import ContinuumGeometric.RoutingSeparation

namespace ContinuumRemainder
open ContinuumGeometric Set
attribute [local instance] Classical.propDecidable Classical.decEq

def logLocalAllMiss {M d P : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (s₀ s₁ x : ℝ) (k : ℤ)
    (edges : Fin P → SelectorEdge M d) (logs : Fin P → ℝ)
    (p : PowerParams s₀ s₁)
    (ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd)) : Prop :=
  ∀ i, p ∈ logActivation (logs i) k
      (c.edgeStart (RoutingTemplate.selectorRoutingEdge (edges i)))
      ((c.edgeStart (RoutingTemplate.selectorRoutingEdge (edges i)) : ℝ) +
        c.edgeLength (RoutingTemplate.selectorRoutingEdge (edges i))) →
    ¬(ω.selectors (selectorAddress c (edges i)
          (powerPoint (logInput (logs i)) ((2 : ℝ) ^ k) (x, p))) = true ∧
      ω.terminals (localTerminalAddress c hM hd ω.selectors (edges i)
          (powerPoint (logInput (logs i)) ((2 : ℝ) ^ k) (x, p))) = true)

theorem logLocalAllMiss_iff_of_logGridVector_eq {M d P : ℕ}
    (c : RoutingTemplate M d) (hM : 0 < M) (hd : 0 < d) (hL : 0 < c.baseLength)
    (s₀ s₁ x : ℝ) (k : ℤ) (edges : Fin P → SelectorEdge M d) (logs : Fin P → ℝ)
    (p p' : PowerParams s₀ s₁)
    (hvec : logGridVector x logs
        (fun i => 2 ^ (c.edgeStar (RoutingTemplate.selectorRoutingEdge (edges i)) + 3)) k
        (fun i => ((c.edgeStart (RoutingTemplate.selectorRoutingEdge (edges i)) : ℝ),
          (c.edgeStart (RoutingTemplate.selectorRoutingEdge (edges i)) : ℝ) +
            c.edgeLength (RoutingTemplate.selectorRoutingEdge (edges i)))) p =
      logGridVector x logs
        (fun i => 2 ^ (c.edgeStar (RoutingTemplate.selectorRoutingEdge (edges i)) + 3)) k
        (fun i => ((c.edgeStart (RoutingTemplate.selectorRoutingEdge (edges i)) : ℝ),
          (c.edgeStart (RoutingTemplate.selectorRoutingEdge (edges i)) : ℝ) +
            c.edgeLength (RoutingTemplate.selectorRoutingEdge (edges i)))) p')
    (ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd)) :
    logLocalAllMiss c hM hd s₀ s₁ x k edges logs p ω ↔
      logLocalAllMiss c hM hd s₀ s₁ x k edges logs p' ω := by
  have hentry := congrFun hvec
  have hactive : ∀ i, p ∈ logActivation (logs i) k
        (c.edgeStart (RoutingTemplate.selectorRoutingEdge (edges i)))
        ((c.edgeStart (RoutingTemplate.selectorRoutingEdge (edges i)) : ℝ) +
          c.edgeLength (RoutingTemplate.selectorRoutingEdge (edges i))) ↔
      p' ∈ logActivation (logs i) k
        (c.edgeStart (RoutingTemplate.selectorRoutingEdge (edges i)))
        ((c.edgeStart (RoutingTemplate.selectorRoutingEdge (edges i)) : ℝ) +
          c.edgeLength (RoutingTemplate.selectorRoutingEdge (edges i))) := by
    intro i
    have hh := hentry i
    simp only [logGridVector] at hh
    split_ifs at hh <;> simp_all
  have hsuccess : ∀ i, p ∈ logActivation (logs i) k
      (c.edgeStart (RoutingTemplate.selectorRoutingEdge (edges i)))
      ((c.edgeStart (RoutingTemplate.selectorRoutingEdge (edges i)) : ℝ) +
        c.edgeLength (RoutingTemplate.selectorRoutingEdge (edges i))) →
      ((ω.selectors (selectorAddress c (edges i)
          (powerPoint (logInput (logs i)) ((2 : ℝ) ^ k) (x, p))) = true ∧
        ω.terminals (localTerminalAddress c hM hd ω.selectors (edges i)
          (powerPoint (logInput (logs i)) ((2 : ℝ) ^ k) (x, p))) = true) ↔
      (ω.selectors (selectorAddress c (edges i)
          (powerPoint (logInput (logs i)) ((2 : ℝ) ^ k) (x, p'))) = true ∧
        ω.terminals (localTerminalAddress c hM hd ω.selectors (edges i)
          (powerPoint (logInput (logs i)) ((2 : ℝ) ^ k) (x, p'))) = true)) := by
    intro i hi
    apply actual_local_success_finest_key_iff c hM hd hL ω (edges i)
    apply (gridAddress_eq_iff _ _ _).2
    have hh := hentry i
    simpa only [logGridVector, ite_eq_left hi, ite_eq_left ((hactive i).1 hi),
      Option.some.injEq] using hh
  constructor
  · intro hm i hi hs
    exact hm i ((hactive i).2 hi) ((hsuccess i ((hactive i).2 hi)).2 hs)
  · intro hm i hi hs
    exact hm i ((hactive i).1 hi) ((hsuccess i hi).1 hs)

/-- Boundary-complete finite representatives for ACTUAL all-parameter local misses.
The representative choice precedes ALL unexposed random table sampling. -/
theorem log_routing_local_representatives {M d P : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (hL : 0 < c.baseLength)
    (s₀ s₁ x : ℝ) (hs : s₀ ≤ s₁) (k : ℤ)
    (edges : Fin P → SelectorEdge M d) (logs : Fin P → ℝ) (ell : ℕ)
    (hell : ∀ i, c.edgeLength (RoutingTemplate.selectorRoutingEdge (edges i)) = ell) :
    ∃ reps : Finset (PowerParams s₀ s₁),
      reps.card ≤ 20 * (P * (3 + 2 ^ (2 * ell + 3)) + 5) ^ 2 ∧
      ∀ p : PowerParams s₀ s₁, ∃ r ∈ reps,
        ∀ ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd),
          logLocalAllMiss c hM hd s₀ s₁ x k edges logs r ω ↔
            logLocalAllMiss c hM hd s₀ s₁ x k edges logs p ω := by
  obtain ⟨reps, hc, hr⟩ := log_representatives_entropy_bound s₀ s₁ x hs logs
    (fun i => c.edgeStart (RoutingTemplate.selectorRoutingEdge (edges i)))
    (fun i => c.edgeStart (RoutingTemplate.selectorRoutingEdge (edges i)) + ell)
    (fun i => c.edgeStar (RoutingTemplate.selectorRoutingEdge (edges i))) k ell (by
      intro i
      simpa only [hell i] using c.edge_span_bound hM hL (RoutingTemplate.selectorRoutingEdge (edges i)))
  refine ⟨reps, hc, ?_⟩
  intro p
  obtain ⟨r, hmem, hvec⟩ := hr p
  refine ⟨r, hmem, ?_⟩
  intro ω
  apply logLocalAllMiss_iff_of_logGridVector_eq c hM hd hL s₀ s₁ x k edges logs r p ?_ ω
  simpa only [hell, Nat.cast_add] using hvec


/-- All-assignment terminal separation is inherited from the verified actual
routing tree after the new real-log geometry proves own-address separation. -/
theorem log_local_address_separation {M d P : ℕ} (c : RoutingTemplate M d)
    (hM : 0<M) (hd : 0<d) (hL : 0<c.baseLength) (hU : 4≤c.origin)
    (s₀ s₁ x : ℝ) (k : ℤ) (bits : SelectorEdge M d → Bool)
    (v : InternalNode M d) (children : Fin P → Fin (M-1)) (logs : Fin P → ℝ)
    (p : PowerParams s₀ s₁)
    (hgap : ∀ i j, i≠j → children i=children j → 3≤|p.1.1*logs j-p.1.1*logs i|)
    (ha : ∀ i,p∈logActivation (logs i) k
      (c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v,children i⟩))
      ((c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v,children i⟩):ℝ)+
        c.edgeLength (RoutingTemplate.selectorRoutingEdge ⟨v,children i⟩))) :
    LocalAddressSeparation (actualCenterExposure c x bits)
      (localOwnAddresses c v children (fun i=>logPoint (logs i) k (x,p)))
      (localTerminalAddresses c hM hd v children (fun i=>logPoint (logs i) k (x,p))) := by
  apply actual_local_address_separation c hM hd hL x bits v children
  · intro i
    exact log_gridAddress_ne_center s₀ s₁ x (logs i) _ _ k
      (hU.trans (c.edgeStart_ge_origin _))
      (RoutingTemplate.length_positive _ _ _ _ hM hL) p (ha i)
  · intro i j hij hc
    have hg:=hgap i j hij hc
    have haj : p∈logActivation (logs j) k
      (c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v,children i⟩))
      ((c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v,children i⟩):ℝ)+
        c.edgeLength (RoutingTemplate.selectorRoutingEdge ⟨v,children i⟩)) := by
      simpa only [hc] using ha j
    rcases le_total (p.1.1*logs i) (p.1.1*logs j) with hh|hh
    · rw [abs_of_nonneg (by linarith)] at hg
      exact log_gridAddress_ne_of_output_gap s₀ s₁ x (logs i) (logs j) _ _ k
        (hU.trans (c.edgeStart_ge_origin _))
        (RoutingTemplate.length_positive _ _ _ _ hM hL) p hg (ha i) haj
    · rw [abs_of_nonpos (by linarith)] at hg
      exact (log_gridAddress_ne_of_output_gap s₀ s₁ x (logs j) (logs i) _ _ k
        (hU.trans (c.edgeStart_ge_origin _))
        (RoutingTemplate.length_positive _ _ _ _ hM hL) p (by linarith) haj (ha i)).symm

end ContinuumRemainder
