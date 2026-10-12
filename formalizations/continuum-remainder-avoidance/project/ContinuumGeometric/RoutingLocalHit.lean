import ContinuumGeometric.RoutingProbability
import ContinuumGeometric.RoutingTreeBounds

namespace ContinuumGeometric

def nodePrefixAt {M d : ℕ} (v : InternalNode M d) (j : Fin v.1.val) : InternalNode M d :=
  nodeOfPrefix ((List.ofFn v.2).take j.val) (by simp only [List.length_take]; omega)

def followsNodePrefix {M d : ℕ} (c : RoutingTemplate M d) (hM : 0 < M)
    (σ : SelectorAddress c → Bool) (z : ℝ) (v : InternalNode M d) : Prop :=
  ∀ j : Fin v.1.val,
    chooseRoutingChild M hM (nodeSelectorBits c σ z (nodePrefixAt v j)) = v.2 j

theorem center_followsNodePrefix {M d : ℕ} (c : RoutingTemplate M d) (hM : 0 < M)
    (σ : SelectorAddress c → Bool) (x : ℝ) (v : InternalNode M d)
    (hp : (List.ofFn v.2).IsPrefix (List.ofFn (routeLeaf c hM σ x))) :
    followsNodePrefix c hM σ x v := by
  obtain ⟨q, hq⟩ := hp
  have hc := (routeLeaf_eq_iff_prefix_choices c hM σ x (routeLeaf c hM σ x)).1 rfl
  intro j
  have hh := hc ⟨j.val, j.isLt.trans v.1.isLt⟩
  have ht : (List.ofFn (routeLeaf c hM σ x)).take j.val = (List.ofFn v.2).take j.val := by
    rw [← hq, List.take_append_of_le_length (by simp only [List.length_ofFn]; exact j.isLt.le)]
  have hg : (routeLeaf c hM σ x) ⟨j.val, j.isLt.trans v.1.isLt⟩ = v.2 j := by
    have hgp := (show (List.ofFn v.2).IsPrefix (List.ofFn (routeLeaf c hM σ x)) from ⟨q, hq⟩).getElem
      (i := j.val) (by simp only [List.length_ofFn]; exact j.isLt)
    simpa using hgp.symm
  simpa only [ht, hg, nodePrefixAt] using hh

theorem ancestor_selector_precedes {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hL : 0 < c.baseLength) (v : InternalNode M d)
    (j : Fin v.1.val) (i : Fin (M - 1)) (hi : i.val ≤ (v.2 j).val)
    (child : Fin (M - 1)) :
    c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨nodePrefixAt v j, i⟩) <
      c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩) := by
  let p := List.ofFn v.2
  have hpLen : p.length = v.1.val := List.length_ofFn
  have hj : j.val < p.length := by rw [hpLen]; exact j.isLt
  have hpSplit : p = p.take j.val ++ v.2 j :: p.drop (j.val + 1) := by
    have hh := (List.take_append_drop j.val p).symm
    rw [List.drop_eq_getElem_cons hj] at hh
    simpa only [p, List.getElem_ofFn] using hh
  have htakeLen : (p.take j.val).length = j.val := by simp [hpLen, j.isLt.le]
  have hnPath : List.ofFn (nodePrefixAt v j).2 = p.take j.val := nodeOfPrefix_path _ _
  have hnLevel : (nodePrefixAt v j).1.val = j.val := by
    simp only [nodePrefixAt, nodeOfPrefix]
    exact htakeLen
  have hstart : c.nodeStart v =
      RoutingTemplate.subtreeStart M c.gap c.baseLength (d - j.val - 1)
        (c.nodeStart (nodePrefixAt v j) + (v.2 j).val *
          (RoutingTemplate.blockSpan M c.gap c.baseLength (d - j.val) + c.gap) +
          RoutingTemplate.lengthAt M c.gap c.baseLength (d - j.val) + c.gap)
        (p.drop (j.val + 1)) := by
    unfold RoutingTemplate.nodeStart
    rw [hnPath]
    change RoutingTemplate.subtreeStart M c.gap c.baseLength d c.origin p = _
    calc
      _ = RoutingTemplate.subtreeStart M c.gap c.baseLength d c.origin
          (p.take j.val ++ v.2 j :: p.drop (j.val + 1)) :=
        congrArg (RoutingTemplate.subtreeStart M c.gap c.baseLength d c.origin) hpSplit
      _ = _ := by
        rw [RoutingTemplate.subtreeStart_append, htakeLen, RoutingTemplate.subtreeStart]
  have hs := RoutingTemplate.subtreeStart_ge M c.gap c.baseLength (d - j.val - 1)
    (c.nodeStart (nodePrefixAt v j) + (v.2 j).val *
      (RoutingTemplate.blockSpan M c.gap c.baseLength (d - j.val) + c.gap) +
      RoutingTemplate.lengthAt M c.gap c.baseLength (d - j.val) + c.gap)
    (p.drop (j.val + 1))
  rw [← hstart] at hs
  have hl := RoutingTemplate.length_positive M c.gap c.baseLength (d - j.val) hM hL
  have hm := Nat.mul_le_mul_right
    (RoutingTemplate.blockSpan M c.gap c.baseLength (d - j.val) + c.gap) hi
  unfold RoutingTemplate.edgeStart RoutingTemplate.selectorRoutingEdge
  simp only [Fin.val_castLE, hnLevel]
  omega

def EarlierAddressAgreement {M d : ℕ} (c : RoutingTemplate M d)
    (x z : ℝ) (e : SelectorEdge M d) : Prop :=
  ∀ f : SelectorEdge M d,
    c.edgeStart (RoutingTemplate.selectorRoutingEdge f) <
      c.edgeStart (RoutingTemplate.selectorRoutingEdge e) →
    gridAddress (c.selectorEnd f) z = gridAddress (c.selectorEnd f) x

/-- Actual earlier-key stability preserves every routing decision through the
center's prescribed prefix, without reading later sibling tables. -/
theorem point_followsNodePrefix_of_earlier_keys {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hL : 0 < c.baseLength) (σ : SelectorAddress c → Bool)
    (x z : ℝ) (v : InternalNode M d) (child : Fin (M - 1))
    (hp : (List.ofFn v.2).IsPrefix (List.ofFn (routeLeaf c hM σ x)))
    (hkeys : EarlierAddressAgreement c x z ⟨v, child⟩) :
    followsNodePrefix c hM σ z v := by
  have hc := center_followsNodePrefix c hM σ x v hp
  intro j
  rw [← hc j]
  apply chooseRoutingChild_eq_of_reads_before_choice
  intro i hi
  rw [hc j] at hi
  apply congrArg σ
  unfold selectorAddress
  congr 1
  exact hkeys ⟨nodePrefixAt v j, i⟩ (ancestor_selector_precedes c hM hL v j i hi child)

/-- Once earlier decisions reach v and earlier siblings are zero, the own
selector success makes the global route follow the actual local child route. -/
theorem routeLeaf_eq_localRouteLeaf_of_prefix_and_success {M d : ℕ}
    (c : RoutingTemplate M d) (hM : 0 < M) (σ : SelectorAddress c → Bool)
    (v : InternalNode M d) (child : Fin (M - 1)) (z : ℝ)
    (hp : followsNodePrefix c hM σ z v)
    (hprev : ∀ i : Fin (M - 1), i.val < child.val →
      σ (selectorAddress c ⟨v, i⟩ z) = false)
    (hown : σ (selectorAddress c ⟨v, child⟩ z) = true) :
    routeLeaf c hM σ z = localRouteLeaf c hM σ ⟨v, child⟩ z := by
  unfold localRouteLeaf
  apply routeLeaf_eq_routeLeafFrom_of_prefix_choices
  intro j
  by_cases hj : j.val < v.1.val
  · have ht : (childPrefix (⟨v, child⟩ : SelectorEdge M d)).take j.val =
        (List.ofFn v.2).take j.val := by
      exact List.take_append_of_le_length (by simp; omega)
    have hg : (childPrefix (⟨v, child⟩ : SelectorEdge M d))[j.val] = v.2 ⟨j.val, hj⟩ := by
      change (List.ofFn v.2 ++ [nondefaultChild child])[j.val] = _
      rw [List.getElem_append_left (by simpa only [List.length_ofFn] using hj), List.getElem_ofFn]
    simpa only [ht, hg, nodePrefixAt] using hp ⟨j.val, hj⟩
  · have hj' : j.val = v.1.val := by
      have hh : j.val < v.1.val + 1 := by simpa only [childPrefix_length] using j.isLt
      omega
    have ht : (childPrefix (⟨v, child⟩ : SelectorEdge M d)).take j.val = List.ofFn v.2 := by
      rw [hj']
      simpa only [childPrefix, List.length_ofFn] using
        (List.take_append_length (l₁ := List.ofFn v.2) (l₂ := [nondefaultChild child]))
    have hg : (childPrefix (⟨v, child⟩ : SelectorEdge M d))[j.val] = nondefaultChild child := by
      change (List.ofFn v.2 ++ [nondefaultChild child])[j.val] = _
      calc
        _ = [nondefaultChild child][j.val - (List.ofFn v.2).length]'(by
            simp only [List.length_ofFn, List.length_singleton]; omega) :=
          List.getElem_append_right (by simp only [List.length_ofFn]; omega)
        _ = _ := by simp [hj']
    simp only [ht, hg, nodeOfPrefix_ofFn]
    exact chooseRoutingChild_of_first_true M hM _ child hown hprev

/-- At a default center vertex, an actual successful local test is membership
in the actual globally routed set, on EVERY center-exposure selector assignment. -/
theorem actual_local_success_mem_routedSet {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (hL : 0 < c.baseLength)
    (ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd))
    (x z : ℝ) (bits : SelectorEdge M d → Bool)
    (hσ : centerExposureAtom (actualCenterExposure c x bits) ω.selectors)
    (v : InternalNode M d) (child : Fin (M - 1))
    (hp : (List.ofFn v.2).IsPrefix (List.ofFn (routeLeaf c hM ω.selectors x)))
    (hdefault : ∀ i : Fin (M - 1), bits ⟨v, i⟩ = false)
    (hkeys : EarlierAddressAgreement c x z ⟨v, child⟩)
    (hsuccess : ω.selectors (selectorAddress c ⟨v, child⟩ z) = true ∧
      ω.terminals (localTerminalAddress c hM hd ω.selectors ⟨v, child⟩ z) = true) :
    z ∈ routedSet c hM hd ω := by
  have hfollow := point_followsNodePrefix_of_earlier_keys c hM hL ω.selectors x z v child hp hkeys
  have hprev : ∀ i : Fin (M - 1), i.val < child.val →
      ω.selectors (selectorAddress c ⟨v, i⟩ z) = false := by
    intro i hi
    have hstart : c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, i⟩) <
        c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩) := by
      have hs := c.sibling_starts v (nondefaultChild i) (nondefaultChild child) hi.le
      have hb := RoutingTemplate.blockSpan_positive M c.gap c.baseLength (d - v.1.val) hM hL
      simp only [nondefaultChild, Fin.val_castLE] at hs
      have hprod : 0 < (child.val - i.val) *
          (RoutingTemplate.blockSpan M c.gap c.baseLength (d - v.1.val) + c.gap) :=
        Nat.mul_pos (by omega) (by omega)
      change c.edgeStart ⟨v, nondefaultChild i⟩ < c.edgeStart ⟨v, nondefaultChild child⟩
      simp only [nondefaultChild]
      omega
    have hk := hkeys ⟨v, i⟩ hstart
    have ha : selectorAddress c ⟨v, i⟩ z = selectorAddress c ⟨v, i⟩ x := by
      unfold selectorAddress; congr 1
    rw [ha, centerExposure_reads c x bits ω.selectors hσ, hdefault i]
  have hroute := routeLeaf_eq_localRouteLeaf_of_prefix_and_success c hM ω.selectors v child z
    hfollow hprev hsuccess.1
  change ω.terminals (terminalAddress c hd (routeLeaf c hM ω.selectors z) z) = true
  rw [hroute]
  exact hsuccess.2

end ContinuumGeometric
