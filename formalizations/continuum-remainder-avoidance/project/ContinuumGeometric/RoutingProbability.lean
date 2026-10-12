import ContinuumGeometric.FiniteRoutingProbability

namespace ContinuumGeometric

attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency false

theorem prefix_take_eq {A : Type*} {a b : List A} (h : a.IsPrefix b) :
    b.take a.length = a := by
  obtain ⟨t, rfl⟩ := h
  exact List.take_append_length

theorem prefix_append_get {A : Type*} {a b : List A} {i : A}
    (h : (a ++ [i]).IsPrefix b) :
    b[a.length]'(by have := h.length_le; simp only [List.length_append,
      List.length_singleton] at this; omega) = i := by
  have hg := h.getElem (i := a.length) (by simp)
  simpa using hg.symm

/-- The actual route obeys the first-true selector decision at every prefix of
its returned full leaf. -/
theorem routeFromList_prefix_choices {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (σ : SelectorAddress c → Bool) (z : ℝ) (h : ℕ)
    (a : List (Fin M)) (ha : a.length + h = d) (j : Fin d)
    (hj : a.length ≤ j.val) :
    let l := (routeFromList c hM σ z h a ha).val
    chooseRoutingChild M hM (nodeSelectorBits c σ z
      (nodeOfPrefix (l.take j.val) (by
        simp only [List.length_take]
        exact (Nat.min_le_left _ _).trans_lt j.isLt))) =
      l[j.val]'(by rw [(routeFromList c hM σ z h a ha).property]; exact j.isLt) := by
  induction h generalizing a with
  | zero =>
    have : d = a.length := by omega
    omega
  | succ h ih =>
    let node := nodeOfPrefix a (show a.length < d from by omega)
    let child := chooseRoutingChild M hM (nodeSelectorBits c σ z node)
    have happ : (a ++ [child]).length + h = d := by simp; omega
    change chooseRoutingChild M hM (nodeSelectorBits c σ z
      (nodeOfPrefix ((routeFromList c hM σ z h (a ++ [child]) happ).val.take j.val) _)) =
        (routeFromList c hM σ z h (a ++ [child]) happ).val[j.val]'(by
          rw [(routeFromList c hM σ z h (a ++ [child]) happ).property]; exact j.isLt)
    by_cases heq : j.val = a.length
    · have hpre := routeFromList_prefix c hM σ z h (a ++ [child]) happ
      have hpreA : a.IsPrefix (routeFromList c hM σ z h (a ++ [child]) happ).val :=
        (List.prefix_append a _).trans hpre
      have htake : (routeFromList c hM σ z h (a ++ [child]) happ).val.take j.val = a := by
        rw [heq]; exact prefix_take_eq hpreA
      have hget := prefix_append_get hpre
      have htakeA := prefix_take_eq hpreA
      simpa only [heq, htakeA, child, node] using hget.symm
    · exact ih (a ++ [child]) happ (by simp; omega)

/-- Conversely, prescribed first-true decisions along a leaf force the actual
route to be exactly that leaf. -/
theorem routeFromList_eq_of_prefix_choices {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (σ : SelectorAddress c → Bool) (z : ℝ) (h : ℕ)
    (a : List (Fin M)) (ha : a.length + h = d)
    (l : List (Fin M)) (hl : l.length = d) (hpre : a.IsPrefix l)
    (hchoice : ∀ j : Fin d, a.length ≤ j.val →
      chooseRoutingChild M hM (nodeSelectorBits c σ z
        (nodeOfPrefix (l.take j.val) (by
          simp only [List.length_take]
          exact (Nat.min_le_left _ _).trans_lt j.isLt))) =
        l[j.val]'(by rw [hl]; exact j.isLt)) :
    (routeFromList c hM σ z h a ha).val = l := by
  induction h generalizing a with
  | zero =>
    simp only [routeFromList]
    have hlen : a.length = l.length := by omega
    exact List.IsPrefix.eq_of_length hpre hlen
  | succ h ih =>
    have hlt : a.length < d := by omega
    let node := nodeOfPrefix a hlt
    let child := chooseRoutingChild M hM (nodeSelectorBits c σ z node)
    have htake := prefix_take_eq hpre
    have hchild : child = l[a.length]'(by omega) := by
      have hc := hchoice ⟨a.length, hlt⟩ le_rfl
      simpa [htake, node, child] using hc
    have hpre' : (a ++ [child]).IsPrefix l := by
      have he : a ++ [child] = l.take (a.length + 1) := by
        calc
          a ++ [child] = l.take a.length ++ [l[a.length]'(by omega)] := by
            rw [hchild]
            exact congrArg (fun q => q ++ [l[a.length]'(by omega)]) htake.symm
          _ = l.take (a.length + 1) := List.take_append_getElem (by omega)
      rw [he]
      exact List.take_prefix _ _
    unfold routeFromList
    apply ih (a ++ [child]) _ hpre'
    intro j hj
    exact hchoice j (by simp only [List.length_append, List.length_singleton] at hj; omega)

/-- Exact actual leaf-route characterization used by the finite no-default law. -/
theorem routeLeaf_eq_iff_prefix_choices {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (σ : SelectorAddress c → Bool) (z : ℝ) (leaf : RoutingLeaf M d) :
    routeLeaf c hM σ z = leaf ↔
      ∀ j : Fin d, chooseRoutingChild M hM (nodeSelectorBits c σ z
        (nodeOfPrefix ((List.ofFn leaf).take j.val) (by simpa [Nat.min_eq_left j.isLt.le]
          using j.isLt))) = leaf j := by
  constructor
  · intro hleaf j
    have hc := routeFromList_prefix_choices c hM σ z d [] (by simp) j (by simp)
    have hl : (routeFromList c hM σ z d [] (by simp)).val = List.ofFn leaf := by
      rw [← ofFn_leafOfList]; exact congrArg List.ofFn hleaf
    simpa only [hl, List.getElem_ofFn] using hc
  · intro hchoice
    have hl := routeFromList_eq_of_prefix_choices c hM σ z d [] (by simp)
      (List.ofFn leaf) (by simp) (by simp) (by simpa using hchoice)
    apply funext
    intro j
    have he := congrArg (fun l : List (Fin M) => l[j.val]?) hl
    simpa [routeLeaf, leafOfList, List.getElem?_eq_getElem] using he

/-- Starting again at a prefix of the ACTUAL route returns the same actual leaf. -/
theorem routeLeafFrom_eq_of_actual_prefix {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (σ : SelectorAddress c → Bool) (z : ℝ)
    (a : List (Fin M)) (ha : a.length ≤ d)
    (hpre : a.IsPrefix (List.ofFn (routeLeaf c hM σ z))) :
    routeLeafFrom c hM σ z a ha = routeLeaf c hM σ z := by
  have hchoice := (routeLeaf_eq_iff_prefix_choices c hM σ z
    (routeLeaf c hM σ z)).1 rfl
  have hl := routeFromList_eq_of_prefix_choices c hM σ z (d - a.length) a (by omega)
    (List.ofFn (routeLeaf c hM σ z)) (by simp) hpre (fun j _ => by simpa using hchoice j)
  apply funext
  intro j
  have he := congrArg (fun l : List (Fin M) => l[j.val]?) hl
  simpa [routeLeafFrom, leafOfList, List.getElem?_eq_getElem] using he

/-- Matching the actual ordered decisions through a prescribed prefix makes
that prefix part of the full actual route. -/
theorem routeLeaf_prefix_of_prefix_choices {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (σ : SelectorAddress c → Bool) (z : ℝ)
    (a : List (Fin M)) (ha : a.length ≤ d)
    (hchoice : ∀ j : Fin a.length,
      chooseRoutingChild M hM (nodeSelectorBits c σ z
        (nodeOfPrefix (a.take j.val) (by simp only [List.length_take]; omega))) = a[j.val]) :
    a.IsPrefix (List.ofFn (routeLeaf c hM σ z)) := by
  let l := List.ofFn (routeLeaf c hM σ z)
  have hl : l.length = d := by simp [l]
  have actual := routeFromList_prefix_choices c hM σ z d [] (by simp)
  have hleaf : (routeFromList c hM σ z d [] (by simp)).val = l := by
    exact (ofFn_leafOfList _).symm
  have htake : ∀ n : ℕ, n ≤ a.length → l.take n = a.take n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hn
      have hnA : n < a.length := by omega
      have hnD : n < d := hnA.trans_le ha
      have heq := ih (by omega)
      have hc := actual ⟨n, hnD⟩ (by simp)
      have hg : l[n]'(by omega) = a[n] := by
        have hcl : chooseRoutingChild M hM (nodeSelectorBits c σ z
            (nodeOfPrefix (l.take n) (by rw [List.length_take, hl]; omega))) = l[n] := by
          simpa only [hleaf] using hc
        have hca := hchoice ⟨n, hnA⟩
        have hnodes : nodeOfPrefix (d := d) (l.take n) (by rw [List.length_take, hl]; omega) =
            nodeOfPrefix (d := d) (a.take n) (by simp only [List.length_take]; omega) := by
          simp only [heq]
        rw [hnodes] at hcl
        exact hcl.symm.trans hca
      rw [List.take_succ_eq_append_getElem (show n < l.length from by omega),
        List.take_succ_eq_append_getElem hnA, heq, hg]
  have ht := htake a.length le_rfl
  rw [List.take_length] at ht
  rw [← ht]
  exact List.take_prefix _ _

/-- Exact jump interface used for local-success ⇒ global routed-set membership. -/
theorem routeLeaf_eq_routeLeafFrom_of_prefix_choices {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (σ : SelectorAddress c → Bool) (z : ℝ)
    (a : List (Fin M)) (ha : a.length ≤ d)
    (hchoice : ∀ j : Fin a.length,
      chooseRoutingChild M hM (nodeSelectorBits c σ z
        (nodeOfPrefix (a.take j.val) (by simp only [List.length_take]; omega))) = a[j.val]) :
    routeLeaf c hM σ z = routeLeafFrom c hM σ z a ha := by
  exact (routeLeafFrom_eq_of_actual_prefix c hM σ z a ha
    (routeLeaf_prefix_of_prefix_choices c hM σ z a ha hchoice)).symm

end ContinuumGeometric
