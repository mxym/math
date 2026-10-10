import ErdosSimilarityGrowingGaps.RoutingGeometry

/-! Adapted in this repository from the finite geometric routing construction.
The real-logarithm sampler and variable schedule are supplied separately. -/

namespace ErdosSimilarityGrowingGaps

def defaultChild (M : ℕ) (hM : 0 < M) : Fin M := ⟨M - 1, by omega⟩

def nondefaultChild {M : ℕ} (i : Fin (M - 1)) : Fin M :=
  Fin.castLE (Nat.sub_le M 1) i

/-- First true nondefault child in the actual ordered tree. -/
def chooseRoutingChild (M : ℕ) (hM : 0 < M) (bits : Fin (M - 1) → Bool) : Fin M :=
  ((List.ofFn (fun i : Fin (M - 1) => i)).find? bits).map nondefaultChild
    |>.getD (defaultChild M hM)

theorem chooseRoutingChild_of_all_false (M : ℕ) (hM : 0 < M)
    (bits : Fin (M - 1) → Bool) (hf : ∀ i, bits i = false) :
    chooseRoutingChild M hM bits = defaultChild M hM := by
  have hfind : (List.ofFn (fun i : Fin (M - 1) => i)).find? bits = none := by
    apply List.find?_eq_none.2
    intro i _
    simp [hf i]
  simp [chooseRoutingChild, hfind]

theorem chooseRoutingChild_of_first_true (M : ℕ) (hM : 0 < M)
    (bits : Fin (M - 1) → Bool) (i : Fin (M - 1))
    (hi : bits i = true) (hprev : ∀ j : Fin (M - 1), j.val < i.val → bits j = false) :
    chooseRoutingChild M hM bits = nondefaultChild i := by
  have hfind : (List.ofFn (fun j : Fin (M - 1) => j)).find? bits = some i := by
    apply (List.find?_ofFn_eq_some_of_injective (fun _ _ h => h)).2
    exact ⟨hi, fun j hj => by simp [hprev j hj]⟩
  simp [chooseRoutingChild, hfind]

/-- A routing decision reads only through its selected child, including every
nondefault selector when it takes the default. -/
theorem chooseRoutingChild_eq_of_reads_before_choice (M : ℕ) (hM : 0 < M)
    (bits bits' : Fin (M - 1) → Bool)
    (hread : ∀ i, i.val ≤ (chooseRoutingChild M hM bits).val → bits' i = bits i) :
    chooseRoutingChild M hM bits' = chooseRoutingChild M hM bits := by
  cases hf : (List.ofFn (fun i : Fin (M - 1) => i)).find? bits with
  | none =>
    have hc : chooseRoutingChild M hM bits = defaultChild M hM := by
      simp [chooseRoutingChild, hf]
    have hfalse : ∀ i, bits i = false := by
      intro i
      have hh := (List.find?_eq_none.1 hf) i (by simp)
      simpa only [Bool.not_eq_true] using hh
    rw [hc]
    apply chooseRoutingChild_of_all_false
    intro i
    rw [hread i (by rw [hc]; exact i.isLt.le), hfalse i]
  | some i =>
    have hc : chooseRoutingChild M hM bits = nondefaultChild i := by
      simp [chooseRoutingChild, hf]
    have hb := (List.find?_ofFn_eq_some_of_injective (fun _ _ h => h)).1 hf
    rw [hc]
    apply chooseRoutingChild_of_first_true
    · rw [hread i (by rw [hc]; rfl)]
      exact hb.1
    · intro j hj
      rw [hread j (by rw [hc]; exact hj.le)]
      simpa only [Bool.not_eq_true] using hb.2 j hj

def nodeOfPrefix {M d : ℕ} (p : List (Fin M)) (hp : p.length < d) : InternalNode M d :=
  ⟨⟨p.length, hp⟩, fun i => p.get i⟩

@[simp] theorem nodeOfPrefix_path {M d : ℕ} (p : List (Fin M)) (hp : p.length < d) :
    List.ofFn (nodeOfPrefix p hp).2 = p := List.ofFn_get p

theorem nodeOfPrefix_ofFn {M d : ℕ} (v : InternalNode M d) :
    nodeOfPrefix (List.ofFn v.2) (by simp only [List.length_ofFn]; exact v.1.isLt) = v := by
  rcases v with ⟨⟨l, hl⟩, p⟩
  apply Sigma.ext (Fin.ext (List.length_ofFn (f := p)))
  have hh : HEq (fun i : Fin (List.ofFn p).length => (List.ofFn p).get i) p := by
    have hh' : (⟨(List.ofFn p).length, (List.ofFn p).get⟩ : Σ n : ℕ, Fin n → Fin M) =
        ⟨l, p⟩ := List.equivSigmaTuple.right_inv ⟨l, p⟩
    exact (Sigma.mk.inj_iff.1 hh').2
  exact hh

noncomputable def nodeSelectorBits {M d : ℕ} (c : RoutingTemplate M d)
    (σ : SelectorAddress c → Bool) (z : ℝ) (v : InternalNode M d) : Fin (M - 1) → Bool :=
  fun i => σ (selectorAddress c ⟨v, i⟩ z)

/-- Routing returns a full actual leaf path and retains its prescribed prefix.
The recursion is structural in the remaining tree height. -/
noncomputable def routeFromList {M d : ℕ} (c : RoutingTemplate M d) (hM : 0 < M)
    (σ : SelectorAddress c → Bool) (z : ℝ) :
    (h : ℕ) → (p : List (Fin M)) → p.length + h = d → {l : List (Fin M) // l.length = d}
  | 0, p, hp => ⟨p, by simpa using hp⟩
  | h + 1, p, hp =>
      let v := nodeOfPrefix p (by omega)
      let i := chooseRoutingChild M hM (nodeSelectorBits c σ z v)
      routeFromList c hM σ z h (p ++ [i]) (by simp only [List.length_append, List.length_singleton]; omega)

theorem routeFromList_prefix {M d : ℕ} (c : RoutingTemplate M d) (hM : 0 < M)
    (σ : SelectorAddress c → Bool) (z : ℝ) (h : ℕ)
    (p : List (Fin M)) (hp : p.length + h = d) :
    p.IsPrefix (routeFromList c hM σ z h p hp).val := by
  induction h generalizing p with
  | zero => simp [routeFromList]
  | succ h ih =>
    unfold routeFromList
    exact (List.prefix_append p _).trans (ih _ _)

def leafOfList {M d : ℕ} (l : {p : List (Fin M) // p.length = d}) : RoutingLeaf M d :=
  fun i => l.val.get ⟨i.val, by rw [l.property]; exact i.isLt⟩

@[simp] theorem ofFn_leafOfList {M d : ℕ} (l : {p : List (Fin M) // p.length = d}) :
    List.ofFn (leafOfList l) = l.val := by
  apply List.ext_get
  · simp [l.property]
  · intro n hn hn'
    simp [leafOfList]

noncomputable def routeLeaf {M d : ℕ} (c : RoutingTemplate M d) (hM : 0 < M)
    (σ : SelectorAddress c → Bool) (z : ℝ) : RoutingLeaf M d :=
  leafOfList (routeFromList c hM σ z d [] (by simp))

noncomputable def routeLeafFrom {M d : ℕ} (c : RoutingTemplate M d) (hM : 0 < M)
    (σ : SelectorAddress c → Bool) (z : ℝ) (p : List (Fin M)) (hp : p.length ≤ d) :
    RoutingLeaf M d :=
  leafOfList (routeFromList c hM σ z (d - p.length) p (by omega))

noncomputable def childPrefix {M d : ℕ} (e : SelectorEdge M d) : List (Fin M) :=
  List.ofFn e.1.2 ++ [nondefaultChild e.2]

theorem childPrefix_length {M d : ℕ} (e : SelectorEdge M d) :
    (childPrefix e).length = e.1.1.val + 1 := by
  simp [childPrefix]

noncomputable def localRouteLeaf {M d : ℕ} (c : RoutingTemplate M d) (hM : 0 < M)
    (σ : SelectorAddress c → Bool) (e : SelectorEdge M d) (z : ℝ) : RoutingLeaf M d :=
  routeLeafFrom c hM σ z (childPrefix e) (by rw [childPrefix_length]; exact e.1.1.isLt)

noncomputable def localTerminalAddress {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (σ : SelectorAddress c → Bool)
    (e : SelectorEdge M d) (z : ℝ) : TerminalAddress c hd :=
  terminalAddress c hd (localRouteLeaf c hM σ e z) z

noncomputable def routedSet {M d : ℕ} (c : RoutingTemplate M d) (hM : 0 < M)
    (hd : 0 < d) (ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd)) : Set ℝ :=
  {z | ω.terminals (terminalAddress c hd (routeLeaf c hM ω.selectors z) z) = true}

def routeHasNoDefault {M d : ℕ} (c : RoutingTemplate M d) (hM : 0 < M)
    (σ : SelectorAddress c → Bool) (z : ℝ) : Prop :=
  ∀ j : Fin d, routeLeaf c hM σ z j ≠ defaultChild M hM

theorem localRouteLeaf_prefix {M d : ℕ} (c : RoutingTemplate M d) (hM : 0 < M)
    (σ : SelectorAddress c → Bool) (e : SelectorEdge M d) (z : ℝ) :
    (childPrefix e).IsPrefix (List.ofFn (localRouteLeaf c hM σ e z)) := by
  simp only [localRouteLeaf, routeLeafFrom, ofFn_leafOfList]
  apply routeFromList_prefix

theorem routeFromList_eq_of_selector_reads {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (σ τ : SelectorAddress c → Bool) (z z' : ℝ)
    (hread : ∀ e : SelectorEdge M d,
      σ (selectorAddress c e z) = τ (selectorAddress c e z'))
    (h : ℕ) (p : List (Fin M)) (hp : p.length + h = d) :
    routeFromList c hM σ z h p hp = routeFromList c hM τ z' h p hp := by
  induction h generalizing p with
  | zero => rfl
  | succ h ih =>
    have hb : nodeSelectorBits c σ z (nodeOfPrefix p (by omega)) =
        nodeSelectorBits c τ z' (nodeOfPrefix p (by omega)) := by
      funext i
      exact hread _
    simp only [routeFromList, hb]
    exact ih _ _

theorem routeLeaf_eq_of_selector_reads {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (σ τ : SelectorAddress c → Bool) (z z' : ℝ)
    (hread : ∀ e : SelectorEdge M d,
      σ (selectorAddress c e z) = τ (selectorAddress c e z')) :
    routeLeaf c hM σ z = routeLeaf c hM τ z' := by
  exact congrArg leafOfList (routeFromList_eq_of_selector_reads c hM σ τ z z' hread d [] (by simp))

/-- Center exposure actually fixes its route; this is not an independence premise. -/
theorem center_atom_routeLeaf_eq {M d : ℕ} (c : RoutingTemplate M d) (hM : 0 < M)
    (x : ℝ) (bits : SelectorEdge M d → Bool) (σ τ : SelectorAddress c → Bool)
    (hσ : centerExposureAtom (actualCenterExposure c x bits) σ)
    (hτ : centerExposureAtom (actualCenterExposure c x bits) τ) :
    routeLeaf c hM σ x = routeLeaf c hM τ x := by
  apply routeLeaf_eq_of_selector_reads c hM σ τ x x
  intro e
  rw [centerExposure_reads c x bits σ hσ e, centerExposure_reads c x bits τ hτ e]

theorem center_atom_noDefault_iff {M d : ℕ} (c : RoutingTemplate M d) (hM : 0 < M)
    (x : ℝ) (bits : SelectorEdge M d → Bool) (σ τ : SelectorAddress c → Bool)
    (hσ : centerExposureAtom (actualCenterExposure c x bits) σ)
    (hτ : centerExposureAtom (actualCenterExposure c x bits) τ) :
    routeHasNoDefault c hM σ x ↔ routeHasNoDefault c hM τ x := by
  unfold routeHasNoDefault
  rw [center_atom_routeLeaf_eq c hM x bits σ τ hσ hτ]

/-- Routes below a fixed subtree only consult that subtree's selector tables. -/
theorem routeFromList_eq_on_prefix {M d : ℕ} (c : RoutingTemplate M d) (hM : 0 < M)
    (σ τ : SelectorAddress c → Bool) (z z' : ℝ) (p₀ : List (Fin M))
    (hread : ∀ e : SelectorEdge M d, p₀.IsPrefix (List.ofFn e.1.2) →
      σ (selectorAddress c e z) = τ (selectorAddress c e z'))
    (h : ℕ) (p : List (Fin M)) (hp : p.length + h = d) (hpp : p₀.IsPrefix p) :
    routeFromList c hM σ z h p hp = routeFromList c hM τ z' h p hp := by
  induction h generalizing p with
  | zero => rfl
  | succ h ih =>
    have hb : nodeSelectorBits c σ z (nodeOfPrefix p (by omega)) =
        nodeSelectorBits c τ z' (nodeOfPrefix p (by omega)) := by
      funext i
      apply hread
      simpa only [nodeOfPrefix_path] using hpp
    simp only [routeFromList, hb]
    exact ih _ _ (hpp.trans (List.prefix_append _ _))

end ErdosSimilarityGrowingGaps
