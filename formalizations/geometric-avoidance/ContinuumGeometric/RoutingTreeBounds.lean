import ContinuumGeometric.RoutingModel

namespace ContinuumGeometric
namespace RoutingTemplate

theorem subtreeStart_ge (M g L h U : ℕ) (p : List (Fin M)) :
    U ≤ subtreeStart M g L h U p := by
  induction p generalizing h U with
  | nil => rfl
  | cons i p ih =>
    exact (Nat.le_add_right U _).trans
      ((Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans (ih _ _)))

theorem subtreeStart_append (M g L h U : ℕ) (p q : List (Fin M)) :
    subtreeStart M g L h U (p ++ q) =
      subtreeStart M g L (h - p.length) (subtreeStart M g L h U p) q := by
  induction p generalizing h U with
  | nil => simp [subtreeStart]
  | cons i p ih =>
    simp only [List.cons_append, subtreeStart, List.length_cons]
    rw [ih]
    congr 1
    omega

theorem incomingEnd_append (M g L h U : ℕ) (p q : List (Fin M)) (hq : q ≠ []) :
    incomingEnd M g L h U (p ++ q) =
      incomingEnd M g L (h - p.length) (subtreeStart M g L h U p) q := by
  induction p generalizing h U with
  | nil => simp [subtreeStart]
  | cons i p ih =>
    have hpq : p ++ q ≠ [] := fun h => hq (List.append_eq_nil_iff.1 h).2
    simp only [List.cons_append, incomingEnd, hpq, ↓reduceIte, subtreeStart,
      List.length_cons]
    rw [ih]
    congr 1
    omega

theorem blockSpan_positive (M g L h : ℕ) (hM : 1 ≤ M) (hL : 0 < L) :
    0 < blockSpan M g L h := by
  unfold blockSpan
  split_ifs with hh
  · exact hL
  · have hl := base_le_length M g L h hM
    simp only [lengthAt, hh, ↓reduceIte] at hl
    omega

theorem length_le_blockSpan (M g L h : ℕ) :
    lengthAt M g L h ≤ blockSpan M g L h := by
  unfold lengthAt blockSpan
  split_ifs <;> omega

theorem child_block_within_span (M g L h U : ℕ) (i : Fin M) :
    U + i.val * (blockSpan M g L (h + 1) + g) + blockSpan M g L (h + 1) ≤
      U + span M g L (h + 1) := by
  rw [span_succ]
  have hi : i.val ≤ M - 1 := by omega
  have hm : 1 ≤ M := by omega
  have hi' := Nat.mul_le_mul_right (blockSpan M g L (h + 1) + g) hi
  have heq : M = (M - 1) + 1 := by omega
  nlinarith

/-- EVERY window along EVERY nonempty path is inside the canonical full span. -/
theorem incomingEnd_bounds (M g L h U : ℕ) (hM : 1 ≤ M) (hL : 0 < L)
    (p : List (Fin M)) (hp : p ≠ []) (hlen : p.length ≤ h) :
    U ≤ incomingEnd M g L h U p ∧ incomingEnd M g L h U p + 1 ≤ U + span M g L h := by
  induction h generalizing U p with
  | zero => cases p <;> simp_all
  | succ h ih =>
    cases p with
    | nil => contradiction
    | cons i p =>
      have hlen' : p.length ≤ h := by simp only [List.length_cons] at hlen; omega
      have hl := length_positive M g L (h + 1) hM hL
      have hb := length_le_blockSpan M g L (h + 1)
      have hblock := child_block_within_span M g L h U i
      by_cases hp' : p = []
      · subst p
        simp only [incomingEnd, ↓reduceIte]
        constructor <;> omega
      · have hh : 0 < h := by
          have hpLen : 0 < p.length := List.length_pos_iff.2 hp'
          omega
        have hrec := ih
          (U + i.val * (blockSpan M g L (h + 1) + g) + lengthAt M g L (h + 1) + g)
          p hp' hlen'
        have hsplit : blockSpan M g L (h + 1) =
            lengthAt M g L (h + 1) + g + span M g L h := by
          obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hh.ne'
          subst h
          exact blockSpan_succ_succ M g L r
        simp only [incomingEnd, hp', ↓reduceIte, Nat.add_sub_cancel]
        constructor <;> omega

/-- The grid attached to a prescribed path's final edge. -/
theorem incomingEnd_of_edge {M d : ℕ} (c : RoutingTemplate M d) (e : RoutingEdge M d) :
    incomingEnd M c.gap c.baseLength d c.origin (List.ofFn e.1.2 ++ [e.2]) =
      c.edgeEnd e := by
  rw [incomingEnd_append M c.gap c.baseLength d c.origin _ _ (by simp)]
  simp only [List.length_ofFn, incomingEnd, ↓reduceIte]
  rfl

theorem edgeEnd_within_total {M d : ℕ} (c : RoutingTemplate M d) (hM : 1 ≤ M)
    (hL : 0 < c.baseLength) (e : RoutingEdge M d) :
    c.origin ≤ c.edgeEnd e ∧ c.edgeEnd e + 1 ≤ c.origin + span M c.gap c.baseLength d := by
  rw [← incomingEnd_of_edge c e]
  apply incomingEnd_bounds M c.gap c.baseLength d c.origin hM hL
  · simp
  · simp only [List.length_append, List.length_ofFn, List.length_singleton]
    exact e.1.1.isLt

theorem nodeStart_ge_origin {M d : ℕ} (c : RoutingTemplate M d) (v : InternalNode M d) :
    c.origin ≤ c.nodeStart v := subtreeStart_ge _ _ _ _ _ _

theorem edgeStart_ge_origin {M d : ℕ} (c : RoutingTemplate M d) (e : RoutingEdge M d) :
    c.origin ≤ c.edgeStart e := (nodeStart_ge_origin c e.1).trans (Nat.le_add_right _ _)

/-- All descendants of a given child lie in its consecutive preorder block. -/
theorem descendant_incomingEnd_bounds {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 1 ≤ M) (hL : 0 < c.baseLength) (e : RoutingEdge M d)
    (q : List (Fin M)) (hlen : e.1.1.val + 1 + q.length ≤ d) :
    c.edgeEnd e ≤ incomingEnd M c.gap c.baseLength d c.origin
        (List.ofFn e.1.2 ++ e.2 :: q) ∧
      incomingEnd M c.gap c.baseLength d c.origin
        (List.ofFn e.1.2 ++ e.2 :: q) ≤ c.edgeStar e := by
  rw [incomingEnd_append M c.gap c.baseLength d c.origin _ _ (by simp)]
  simp only [List.length_ofFn]
  have hr : 0 < d - e.1.1.val := by have := e.1.1.isLt; omega
  have hl := length_positive M c.gap c.baseLength (d - e.1.1.val) hM hL
  have hb := length_le_blockSpan M c.gap c.baseLength (d - e.1.1.val)
  by_cases hq : q = []
  · subst q
    simp only [incomingEnd, ↓reduceIte]
    change c.edgeEnd e ≤ c.edgeEnd e ∧ c.edgeEnd e ≤ c.edgeStar e
    constructor
    · rfl
    · unfold edgeEnd edgeLength edgeStar; omega
  · have hr' : 0 < d - e.1.1.val - 1 := by cases q <;> simp_all; omega
    have hrec := incomingEnd_bounds M c.gap c.baseLength (d - e.1.1.val - 1)
      (c.edgeStart e + c.edgeLength e + c.gap) hM hL q hq (by
        omega)
    have hsplit : blockSpan M c.gap c.baseLength (d - e.1.1.val) =
        lengthAt M c.gap c.baseLength (d - e.1.1.val) + c.gap +
          span M c.gap c.baseLength (d - e.1.1.val - 1) := by
      obtain ⟨r, hr''⟩ : ∃ r, d - e.1.1.val = r + 2 := ⟨d - e.1.1.val - 2, by omega⟩
      rw [hr'']
      exact blockSpan_succ_succ _ _ _ _
    simp only [incomingEnd, hq, ↓reduceIte]
    change c.edgeEnd e ≤ incomingEnd _ _ _ _ (c.edgeStart e + c.edgeLength e + c.gap) q ∧
      incomingEnd _ _ _ _ (c.edgeStart e + c.edgeLength e + c.gap) q ≤ c.edgeStar e
    unfold edgeEnd edgeStar edgeLength at *
    constructor <;> omega

end RoutingTemplate

theorem localRouteLeaf_grid_bounds {M d : ℕ} (c : RoutingTemplate M d) (hM : 0 < M)
    (hd : 0 < d) (hL : 0 < c.baseLength) (σ : SelectorAddress c → Bool)
    (e : SelectorEdge M d) (z : ℝ) :
    c.selectorEnd e ≤ c.leafEnd hd (localRouteLeaf c hM σ e z) ∧
      c.leafEnd hd (localRouteLeaf c hM σ e z) ≤
        c.edgeStar (RoutingTemplate.selectorRoutingEdge e) := by
  obtain ⟨q, hq⟩ := localRouteLeaf_prefix c hM σ e z
  have hlen : e.1.1.val + 1 + q.length ≤ d := by
    have hh := congrArg List.length hq
    simp only [List.length_append, List.length_ofFn, childPrefix_length] at hh
    omega
  have hh := c.descendant_incomingEnd_bounds hM hL (RoutingTemplate.selectorRoutingEdge e) q hlen
  simpa only [RoutingTemplate.leafEnd, childPrefix, List.append_assoc, List.singleton_append,
    ← hq, RoutingTemplate.selectorEnd, RoutingTemplate.selectorRoutingEdge,
    nondefaultChild] using hh

theorem descendant_selectorEnd_le_star {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hL : 0 < c.baseLength) (e f : SelectorEdge M d)
    (hprefix : (childPrefix e).IsPrefix (List.ofFn f.1.2)) :
    c.selectorEnd f ≤ c.edgeStar (RoutingTemplate.selectorRoutingEdge e) := by
  obtain ⟨q, hq⟩ := hprefix
  have hlen : e.1.1.val + 1 + (q ++ [nondefaultChild f.2]).length ≤ d := by
    have hh := congrArg List.length hq
    simp only [List.length_append, List.length_ofFn, childPrefix_length] at hh
    simp only [List.length_append, List.length_singleton]
    have := f.1.1.isLt
    omega
  have hb := (c.descendant_incomingEnd_bounds hM hL
    (RoutingTemplate.selectorRoutingEdge e) (q ++ [nondefaultChild f.2]) hlen).2
  have heq : List.ofFn f.1.2 ++ [nondefaultChild f.2] =
      List.ofFn e.1.2 ++ nondefaultChild e.2 :: (q ++ [nondefaultChild f.2]) := by
    rw [← hq]
    simp only [childPrefix, List.append_assoc, List.cons_append, List.nil_append]
  change RoutingTemplate.incomingEnd M c.gap c.baseLength d c.origin
    (List.ofFn e.1.2 ++ nondefaultChild e.2 :: (q ++ [nondefaultChild f.2])) ≤ _ at hb
  rw [← heq] at hb
  change RoutingTemplate.incomingEnd M c.gap c.baseLength d c.origin
    (List.ofFn (RoutingTemplate.selectorRoutingEdge f).1.2 ++
      [(RoutingTemplate.selectorRoutingEdge f).2]) ≤ _ at hb
  rw [RoutingTemplate.incomingEnd_of_edge] at hb
  exact hb

theorem selectorEnd_global_bound {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hL : 0 < c.baseLength) (e : SelectorEdge M d) :
    c.selectorEnd e + 1 ≤ c.origin + RoutingTemplate.span M c.gap c.baseLength d :=
  (c.edgeEnd_within_total hM hL (RoutingTemplate.selectorRoutingEdge e)).2

theorem leafEnd_global_bound {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (hL : 0 < c.baseLength) (p : RoutingLeaf M d) :
    c.leafEnd hd p + 1 ≤ c.origin + RoutingTemplate.span M c.gap c.baseLength d := by
  exact (RoutingTemplate.incomingEnd_bounds M c.gap c.baseLength d c.origin hM hL
    (List.ofFn p) (by simp only [ne_eq, List.ofFn_eq_nil_iff]; omega) (by simp)).2

/-- The terminal grid is exactly the window grid of the leaf's incoming edge. -/
theorem leafEnd_eq_incoming_edge {M d : ℕ} (c : RoutingTemplate M d)
    (hd : 0 < d) (p : RoutingLeaf M d) :
    c.leafEnd hd p = c.edgeEnd (RoutingTemplate.leafIncomingEdge hd p) := by
  cases d with
  | zero => omega
  | succ r =>
    unfold RoutingTemplate.leafEnd
    rw [List.ofFn_succ_last]
    let e : RoutingEdge M (r + 1) :=
      ⟨⟨⟨r, by omega⟩, fun i => p i.castSucc⟩, p (Fin.last r)⟩
    change RoutingTemplate.incomingEnd M c.gap c.baseLength (r + 1) c.origin
      (List.ofFn e.1.2 ++ [e.2]) = c.edgeEnd e
    exact RoutingTemplate.incomingEnd_of_edge c e

end ContinuumGeometric
