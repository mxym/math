import ErdosSimilarityGrowingGaps.RoutingTreeBounds
import ErdosSimilarityGrowingGaps.LocalSignatures

/-! Adapted in this repository from the finite geometric routing construction.
The real-logarithm sampler and variable schedule are supplied separately. -/

namespace ErdosSimilarityGrowingGaps

/-- A local finest key controls every actual selector read in its child subtree. -/
theorem localRouteLeaf_eq_of_finest_key {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hL : 0 < c.baseLength) (σ : SelectorAddress c → Bool)
    (e : SelectorEdge M d) (z z' : ℝ)
    (hkey : gridAddress (c.edgeStar (RoutingTemplate.selectorRoutingEdge e)) z =
      gridAddress (c.edgeStar (RoutingTemplate.selectorRoutingEdge e)) z') :
    localRouteLeaf c hM σ e z = localRouteLeaf c hM σ e z' := by
  unfold localRouteLeaf routeLeafFrom
  apply congrArg leafOfList
  apply routeFromList_eq_on_prefix c hM σ σ z z' (childPrefix e)
  · intro f hp
    apply congrArg σ
    unfold selectorAddress
    congr 1
    exact dyadic_grid_eq_of_finer_eq _ _
      (descendant_selectorEnd_le_star c hM hL e f hp) z z' hkey
  · exact List.prefix_refl _

theorem localTerminalAddress_eq_of_finest_key {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (hL : 0 < c.baseLength)
    (σ : SelectorAddress c → Bool) (e : SelectorEdge M d) (z z' : ℝ)
    (hkey : gridAddress (c.edgeStar (RoutingTemplate.selectorRoutingEdge e)) z =
      gridAddress (c.edgeStar (RoutingTemplate.selectorRoutingEdge e)) z') :
    localTerminalAddress c hM hd σ e z = localTerminalAddress c hM hd σ e z' := by
  have hleaf := localRouteLeaf_eq_of_finest_key c hM hL σ e z z' hkey
  unfold localTerminalAddress terminalAddress
  rw [← hleaf]
  congr 1
  exact dyadic_grid_eq_of_finer_eq _ _
    (localRouteLeaf_grid_bounds c hM hd hL σ e z).2 z z' hkey

theorem localOwnAddress_eq_of_finest_key {M d : ℕ} (c : RoutingTemplate M d)
    (e : SelectorEdge M d) (z z' : ℝ)
    (hkey : gridAddress (c.edgeStar (RoutingTemplate.selectorRoutingEdge e)) z =
      gridAddress (c.edgeStar (RoutingTemplate.selectorRoutingEdge e)) z') :
    selectorAddress c e z = selectorAddress c e z' := by
  unfold selectorAddress
  congr 1
  apply dyadic_grid_eq_of_finer_eq _ _ ?_ z z' hkey
  unfold RoutingTemplate.selectorEnd RoutingTemplate.edgeEnd RoutingTemplate.edgeStar
    RoutingTemplate.edgeLength
  have hh := RoutingTemplate.length_le_blockSpan M c.gap c.baseLength
    (d - (RoutingTemplate.selectorRoutingEdge e).1.1.val)
  omega

/-- The actual local success readout factors through its actual local finest key,
uniformly for ALL still-unexposed selector and terminal assignments. -/
theorem actual_local_success_finest_key_iff {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (hL : 0 < c.baseLength)
    (ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd))
    (e : SelectorEdge M d) (z z' : ℝ)
    (hkey : gridAddress (c.edgeStar (RoutingTemplate.selectorRoutingEdge e)) z =
      gridAddress (c.edgeStar (RoutingTemplate.selectorRoutingEdge e)) z') :
    (ω.selectors (selectorAddress c e z) = true ∧
      ω.terminals (localTerminalAddress c hM hd ω.selectors e z) = true) ↔
    (ω.selectors (selectorAddress c e z') = true ∧
      ω.terminals (localTerminalAddress c hM hd ω.selectors e z') = true) := by
  rw [localOwnAddress_eq_of_finest_key c e z z' hkey,
    localTerminalAddress_eq_of_finest_key c hM hd hL ω.selectors e z z' hkey]

noncomputable def actualLocalAllMiss {M d P : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (s₀ s₁ x : ℝ) (k : ℤ)
    (edges : Fin P → SelectorEdge M d) (indices : Fin P → ℕ)
    (p : PowerParams s₀ s₁)
    (ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd)) : Prop :=
  ∀ i, p ∈ powerActivation (indices i) k
      (c.edgeStart (RoutingTemplate.selectorRoutingEdge (edges i)))
      ((c.edgeStart (RoutingTemplate.selectorRoutingEdge (edges i)) : ℝ) +
        c.edgeLength (RoutingTemplate.selectorRoutingEdge (edges i))) →
    ¬(ω.selectors (selectorAddress c (edges i)
          (powerPoint (dyadic (indices i)) ((2 : ℝ) ^ k) (x, p))) = true ∧
      ω.terminals (localTerminalAddress c hM hd ω.selectors (edges i)
          (powerPoint (dyadic (indices i)) ((2 : ℝ) ^ k) (x, p))) = true)

theorem actualLocalAllMiss_iff_of_localGridVector_eq {M d P : ℕ}
    (c : RoutingTemplate M d) (hM : 0 < M) (hd : 0 < d) (hL : 0 < c.baseLength)
    (s₀ s₁ x : ℝ) (k : ℤ) (edges : Fin P → SelectorEdge M d) (indices : Fin P → ℕ)
    (p p' : PowerParams s₀ s₁)
    (hvec : localGridVector x indices
        (fun i => 2 ^ (c.edgeStar (RoutingTemplate.selectorRoutingEdge (edges i)) + 3)) k
        (fun i => ((c.edgeStart (RoutingTemplate.selectorRoutingEdge (edges i)) : ℝ),
          (c.edgeStart (RoutingTemplate.selectorRoutingEdge (edges i)) : ℝ) +
            c.edgeLength (RoutingTemplate.selectorRoutingEdge (edges i)))) p =
      localGridVector x indices
        (fun i => 2 ^ (c.edgeStar (RoutingTemplate.selectorRoutingEdge (edges i)) + 3)) k
        (fun i => ((c.edgeStart (RoutingTemplate.selectorRoutingEdge (edges i)) : ℝ),
          (c.edgeStart (RoutingTemplate.selectorRoutingEdge (edges i)) : ℝ) +
            c.edgeLength (RoutingTemplate.selectorRoutingEdge (edges i)))) p')
    (ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd)) :
    actualLocalAllMiss c hM hd s₀ s₁ x k edges indices p ω ↔
      actualLocalAllMiss c hM hd s₀ s₁ x k edges indices p' ω := by
  have hentry := congrFun hvec
  have hactive : ∀ i, p ∈ powerActivation (indices i) k
        (c.edgeStart (RoutingTemplate.selectorRoutingEdge (edges i)))
        ((c.edgeStart (RoutingTemplate.selectorRoutingEdge (edges i)) : ℝ) +
          c.edgeLength (RoutingTemplate.selectorRoutingEdge (edges i))) ↔
      p' ∈ powerActivation (indices i) k
        (c.edgeStart (RoutingTemplate.selectorRoutingEdge (edges i)))
        ((c.edgeStart (RoutingTemplate.selectorRoutingEdge (edges i)) : ℝ) +
          c.edgeLength (RoutingTemplate.selectorRoutingEdge (edges i))) := by
    intro i
    have hh := hentry i
    simp only [localGridVector] at hh
    split_ifs at hh <;> simp_all
  have hsuccess : ∀ i, p ∈ powerActivation (indices i) k
      (c.edgeStart (RoutingTemplate.selectorRoutingEdge (edges i)))
      ((c.edgeStart (RoutingTemplate.selectorRoutingEdge (edges i)) : ℝ) +
        c.edgeLength (RoutingTemplate.selectorRoutingEdge (edges i))) →
      ((ω.selectors (selectorAddress c (edges i)
          (powerPoint (dyadic (indices i)) ((2 : ℝ) ^ k) (x, p))) = true ∧
        ω.terminals (localTerminalAddress c hM hd ω.selectors (edges i)
          (powerPoint (dyadic (indices i)) ((2 : ℝ) ^ k) (x, p))) = true) ↔
      (ω.selectors (selectorAddress c (edges i)
          (powerPoint (dyadic (indices i)) ((2 : ℝ) ^ k) (x, p'))) = true ∧
        ω.terminals (localTerminalAddress c hM hd ω.selectors (edges i)
          (powerPoint (dyadic (indices i)) ((2 : ℝ) ^ k) (x, p'))) = true)) := by
    intro i hi
    apply actual_local_success_finest_key_iff c hM hd hL ω (edges i)
    apply (gridAddress_eq_iff _ _ _).2
    have hh := hentry i
    simpa only [localGridVector, ite_eq_left hi, ite_eq_left ((hactive i).1 hi),
      Option.some.injEq] using hh
  constructor
  · intro hm i hi hs
    exact hm i ((hactive i).2 hi) ((hsuccess i ((hactive i).2 hi)).2 hs)
  · intro hm i hi hs
    exact hm i ((hactive i).1 hi) ((hsuccess i hi).1 hs)

/-- Boundary-complete finite representatives for ACTUAL all-parameter local misses.
The representative choice precedes ALL unexposed random table sampling. -/
theorem actual_routing_local_representatives {M d P : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (hL : 0 < c.baseLength)
    (s₀ s₁ x : ℝ) (hs : s₀ ≤ s₁) (k : ℤ)
    (edges : Fin P → SelectorEdge M d) (indices : Fin P → ℕ) (ell : ℕ)
    (hell : ∀ i, c.edgeLength (RoutingTemplate.selectorRoutingEdge (edges i)) = ell) :
    ∃ reps : Finset (PowerParams s₀ s₁),
      reps.card ≤ 20 * (P * (3 + 2 ^ (2 * ell + 3)) + 5) ^ 2 ∧
      ∀ p : PowerParams s₀ s₁, ∃ r ∈ reps,
        ∀ ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd),
          actualLocalAllMiss c hM hd s₀ s₁ x k edges indices r ω ↔
            actualLocalAllMiss c hM hd s₀ s₁ x k edges indices p ω := by
  obtain ⟨reps, hc, hr⟩ := actual_local_representatives_entropy_bound s₀ s₁ x hs indices
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
  apply actualLocalAllMiss_iff_of_localGridVector_eq c hM hd hL s₀ s₁ x k edges indices r p ?_ ω
  simpa only [hell, Nat.cast_add] using hvec

end ErdosSimilarityGrowingGaps
