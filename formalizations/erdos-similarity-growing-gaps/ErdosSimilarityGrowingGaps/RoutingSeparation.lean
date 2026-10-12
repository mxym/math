import ErdosSimilarityGrowingGaps.RoutingTreeBounds
import ErdosSimilarityGrowingGaps.RoutingActiveGeometry
import ErdosSimilarityGrowingGaps.LocalSignatures
import Mathlib.Tactic


namespace ErdosSimilarityGrowingGaps

theorem localRouteLeaf_child {M d : ℕ} (c : RoutingTemplate M d) (hM : 0 < M)
    (σ : SelectorAddress c → Bool) (v : InternalNode M d) (i : Fin (M - 1)) (z : ℝ) :
    localRouteLeaf c hM σ ⟨v, i⟩ z v.1 = nondefaultChild i := by
  have hp := localRouteLeaf_prefix c hM σ ⟨v, i⟩ z
  have hh := hp.getElem (i := v.1.val) (by simp [childPrefix_length])
  simpa [childPrefix, List.getElem_append_right] using hh.symm

noncomputable def localOwnAddresses {M d t : ℕ} (c : RoutingTemplate M d)
    (v : InternalNode M d) (child : Fin t → Fin (M - 1)) (point : Fin t → ℝ) :
    Fin t → SelectorAddress c :=
  fun i => selectorAddress c ⟨v, child i⟩ (point i)

noncomputable def localTerminalAddresses {M d t : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (v : InternalNode M d)
    (child : Fin t → Fin (M - 1)) (point : Fin t → ℝ) :
    (SelectorAddress c → Bool) → Fin t → TerminalAddress c hd :=
  fun σ i => localTerminalAddress c hM hd σ ⟨v, child i⟩ (point i)

/-- The actual finite routing satisfies the probability contract once geometric
own-key separation is proved. Terminal separation is proved for EVERY selector
assignment, even when an own selector is zero and routes share auxiliary reads. -/
theorem actual_local_address_separation {M d t : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (hL : 0 < c.baseLength)
    (x : ℝ) (bits : SelectorEdge M d → Bool) (v : InternalNode M d)
    (child : Fin t → Fin (M - 1)) (point : Fin t → ℝ)
    (hcenter : ∀ i, gridAddress (c.selectorEnd ⟨v, child i⟩) (point i) ≠
      gridAddress (c.selectorEnd ⟨v, child i⟩) x)
    (hpair : ∀ i j, i ≠ j → child i = child j →
      gridAddress (c.selectorEnd ⟨v, child i⟩) (point i) ≠
        gridAddress (c.selectorEnd ⟨v, child i⟩) (point j)) :
    LocalAddressSeparation (actualCenterExposure c x bits)
      (localOwnAddresses c v child point)
      (localTerminalAddresses c hM hd v child point) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j heq
    have he : (⟨v, child i⟩ : SelectorEdge M d) = ⟨v, child j⟩ := congrArg Sigma.fst heq
    have hchild : child i = child j := eq_of_heq (Sigma.mk.inj_iff.1 he).2
    by_contra hne
    apply hpair i j hne hchild
    unfold localOwnAddresses selectorAddress at heq
    rw [← hchild] at heq
    exact eq_of_heq (Sigma.mk.inj_iff.1 heq).2
  · intro i
    apply own_selector_unexposed c x (point i) bits ⟨v, child i⟩ (hcenter i)
  · intro σ _ i j heq
    have hleaf : localRouteLeaf c hM σ ⟨v, child i⟩ (point i) =
        localRouteLeaf c hM σ ⟨v, child j⟩ (point j) := congrArg Sigma.fst heq
    have hchild : child i = child j := by
      have hh := congrArg (fun p : RoutingLeaf M d => p v.1) hleaf
      rw [localRouteLeaf_child, localRouteLeaf_child] at hh
      exact Fin.ext (congrArg (fun q : Fin M => q.val) hh)
    by_contra hne
    have hb := (localRouteLeaf_grid_bounds c hM hd hL σ ⟨v, child i⟩ (point i)).1
    have hk : gridAddress (c.leafEnd hd (localRouteLeaf c hM σ ⟨v, child i⟩ (point i)))
        (point i) =
      gridAddress (c.leafEnd hd (localRouteLeaf c hM σ ⟨v, child i⟩ (point i))) (point j) := by
      unfold localTerminalAddresses localTerminalAddress terminalAddress at heq
      rw [← hleaf] at heq
      exact eq_of_heq (Sigma.mk.inj_iff.1 heq).2
    exact hpair i j hne hchild
      (dyadic_grid_eq_of_finer_eq _ _ hb (point i) (point j) hk)

/-- Instantiation for actual strict-active original dyadic subsequence points.
No address-separation law is assumed: own and terminal injection are conclusions. -/
theorem active_subsequence_local_address_separation {M d t : ℕ}
    (c : RoutingTemplate M d) (hM : 0 < M) (hd : 0 < d)
    (hL : 0 < c.baseLength) (hU : 4 ≤ c.origin)
    (s₀ s₁ x : ℝ) (m : ℕ) (k : ℤ) (hgap : 3 ≤ (m : ℝ) * s₀)
    (bits : SelectorEdge M d → Bool) (v : InternalNode M d)
    (child : Fin t → Fin (M - 1)) (label : Fin t → ℕ)
    (hlabels : Function.Injective (fun i => (child i, label i)))
    (p : PowerParams s₀ s₁)
    (hactive : ∀ i, p ∈ powerActivation (m * label i) k
      (c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩))
      ((c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩) : ℝ) +
        c.edgeLength (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩))) :
    LocalAddressSeparation (actualCenterExposure c x bits)
      (localOwnAddresses c v child
        (fun i => powerPoint (dyadic (m * label i)) ((2 : ℝ) ^ k) (x, p)))
      (localTerminalAddresses c hM hd v child
        (fun i => powerPoint (dyadic (m * label i)) ((2 : ℝ) ^ k) (x, p))) := by
  apply actual_local_address_separation c hM hd hL x bits v child
  · intro i
    exact active_power_gridAddress_ne_center s₀ s₁ x _ _ (m * label i) k
      (hU.trans (c.edgeStart_ge_origin _))
      (RoutingTemplate.length_positive _ _ _ _ hM hL) p (hactive i)
  · intro i j hij hchild
    have hn : label i ≠ label j := by
      intro hh
      exact hij (hlabels (Prod.ext hchild hh))
    have ha : p ∈ powerActivation (m * label j) k
        (c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩))
        ((c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩) : ℝ) +
          c.edgeLength (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩)) := by
      simpa only [hchild] using hactive j
    exact active_subsequence_gridAddress_ne s₀ s₁ x _ _ m (label i) (label j) k
      (hU.trans (c.edgeStart_ge_origin _))
      (RoutingTemplate.length_positive _ _ _ _ hM hL) hgap hn p (hactive i) ha

/-- Original-index version used by the concrete finite candidate-pair enumeration. -/
theorem active_original_local_address_separation {M d t : ℕ}
    (c : RoutingTemplate M d) (hM : 0 < M) (hd : 0 < d)
    (hL : 0 < c.baseLength) (hU : 4 ≤ c.origin)
    (s₀ s₁ x : ℝ) (m : ℕ) (k : ℤ) (hgap : 3 ≤ (m : ℝ) * s₀)
    (bits : SelectorEdge M d → Bool) (v : InternalNode M d)
    (child : Fin t → Fin (M - 1)) (indices : Fin t → ℕ)
    (hinj : Function.Injective (fun i => (child i, indices i)))
    (hmul : ∀ i, ∃ n, m * n = indices i) (p : PowerParams s₀ s₁)
    (hactive : ∀ i, p ∈ powerActivation (indices i) k
      (c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩))
      ((c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩) : ℝ) +
        c.edgeLength (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩))) :
    LocalAddressSeparation (actualCenterExposure c x bits)
      (localOwnAddresses c v child
        (fun i => powerPoint (dyadic (indices i)) ((2 : ℝ) ^ k) (x, p)))
      (localTerminalAddresses c hM hd v child
        (fun i => powerPoint (dyadic (indices i)) ((2 : ℝ) ^ k) (x, p))) := by
  apply actual_local_address_separation c hM hd hL x bits v child
  · intro i
    exact active_power_gridAddress_ne_center s₀ s₁ x _ _ (indices i) k
      (hU.trans (c.edgeStart_ge_origin _))
      (RoutingTemplate.length_positive _ _ _ _ hM hL) p (hactive i)
  · intro i j hij hchild
    have hn : indices i ≠ indices j := fun hh => hij (hinj (Prod.ext hchild hh))
    have ha : p ∈ powerActivation (indices j) k
        (c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩))
        ((c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩) : ℝ) +
          c.edgeLength (RoutingTemplate.selectorRoutingEdge ⟨v, child i⟩)) := by
      simpa only [hchild] using hactive j
    exact active_original_finer_gridAddress_ne s₀ s₁ x _ _ m (indices i) (indices j) _ k
      (hU.trans (c.edgeStart_ge_origin _))
      (RoutingTemplate.length_positive _ _ _ _ hM hL) hgap hn le_rfl
      (hmul i) (hmul j) p (hactive i) ha

end ErdosSimilarityGrowingGaps
