import ContinuumGeometric.RoutingTemplate
import Mathlib.Data.List.Chain

namespace ContinuumGeometric

/-- Canonical complete ordered-tree preorder; ALL children have windows. -/
def preorderPaths (M : ℕ) : ℕ → List (List (Fin M))
  | 0 => []
  | h + 1 => (List.ofFn (fun i : Fin M => i)).flatMap
      (fun i => [i] :: (preorderPaths M h).map (fun p => i :: p))

theorem mem_preorderPaths_iff (M h : ℕ) (p : List (Fin M)) :
    p ∈ preorderPaths M h ↔ p ≠ [] ∧ p.length ≤ h := by
  induction h generalizing p with
  | zero => simp [preorderPaths]
  | succ h ih =>
    cases p with
    | nil => simp [preorderPaths]
    | cons i p =>
      simp only [preorderPaths, List.mem_flatMap, List.mem_ofFn, List.mem_cons,
        List.mem_map]
      constructor
      · rintro ⟨j, _, h | ⟨q, hq, heq⟩⟩
        · cases h
          simp
        · cases heq
          have hh := (ih p).1 hq
          simp only [ne_eq, List.cons_ne_nil, not_false_eq_true, List.length_cons,
            true_and]
          omega
      · intro hp
        by_cases hnil : p = []
        · subst p
          exact ⟨i, ⟨i, rfl⟩, Or.inl rfl⟩
        · refine ⟨i, ⟨i, rfl⟩, Or.inr ⟨p, (ih p).2 ⟨hnil, ?_⟩, rfl⟩⟩
          simp only [List.length_cons] at hp
          omega

def preorderEdgeCount (M : ℕ) : ℕ → ℕ
  | 0 => 0
  | h + 1 => M * (1 + preorderEdgeCount M h)

theorem preorderPaths_length (M h : ℕ) :
    (preorderPaths M h).length = preorderEdgeCount M h := by
  induction h with
  | zero => rfl
  | succ h ih =>
    simp [preorderPaths, preorderEdgeCount, List.length_flatMap, ih, Function.comp_def,
      Nat.add_comm]

namespace RoutingTemplate

/-- Start of the actual incoming window, using the canonical subtree positions. -/
def incomingStart (M g L : ℕ) : ℕ → ℕ → List (Fin M) → ℕ
  | _, U, [] => U
  | h, U, i :: p =>
      let a := U + i.val * (blockSpan M g L h + g)
      if p = [] then a
      else incomingStart M g L (h - 1) (a + lengthAt M g L h + g) p

theorem incomingStart_append (M g L h U : ℕ) (p q : List (Fin M)) (hq : q ≠ []) :
    incomingStart M g L h U (p ++ q) =
      incomingStart M g L (h - p.length) (subtreeStart M g L h U p) q := by
  induction p generalizing h U with
  | nil => simp [subtreeStart]
  | cons i p ih =>
    have hpq : p ++ q ≠ [] := fun h => hq (List.append_eq_nil_iff.1 h).2
    simp only [List.cons_append, incomingStart, hpq, ↓reduceIte, subtreeStart,
      List.length_cons]
    rw [ih]
    congr 1
    omega

theorem incomingStart_of_edge {M d : ℕ} (c : RoutingTemplate M d) (e : RoutingEdge M d) :
    incomingStart M c.gap c.baseLength d c.origin (List.ofFn e.1.2 ++ [e.2]) =
      c.edgeStart e := by
  rw [incomingStart_append M c.gap c.baseLength d c.origin _ _ (by simp)]
  simp only [List.length_ofFn, incomingStart, ↓reduceIte]
  rfl

theorem incomingEnd_eq_start_add_length (M g L h U : ℕ)
    (p : List (Fin M)) (hp : p ≠ []) (hlen : p.length ≤ h) :
    incomingEnd M g L h U p =
      incomingStart M g L h U p + lengthAt M g L (h + 1 - p.length) - 1 := by
  induction p generalizing h U with
  | nil => contradiction
  | cons i p ih =>
    by_cases hnil : p = []
    · subst p
      simp [incomingEnd, incomingStart]
    · simp only [incomingEnd, incomingStart, hnil, ↓reduceIte]
      rw [ih _ _ hnil (by simp only [List.length_cons] at hlen; omega)]
      have hheight : h - 1 + 1 - p.length = h + 1 - (i :: p).length := by
        simp only [List.length_cons] at hlen ⊢
        omega
      rw [hheight]

end RoutingTemplate

/-- Positive actual window lengths in canonical path order. -/
def preorderLengths (M g L h : ℕ) : List ℕ :=
  (preorderPaths M h).map (fun p => RoutingTemplate.lengthAt M g L (h + 1 - p.length))

def preorderWeight (g : ℕ) (lengths : List ℕ) : ℕ :=
  (lengths.map (fun ell => ell + g)).sum

/-- Elementary finite schedule, including its real intervening gaps. -/
def preorderSchedule (g : ℕ) : ℕ → List ℕ → List (ℕ × ℕ)
  | _, [] => []
  | U, ell :: lengths =>
      (U, U + ell - 1) :: preorderSchedule g (U + ell + g) lengths

theorem preorderWeight_append (g : ℕ) (a b : List ℕ) :
    preorderWeight g (a ++ b) = preorderWeight g a + preorderWeight g b := by
  simp [preorderWeight]

theorem preorderSchedule_append (g U : ℕ) (a b : List ℕ) :
    preorderSchedule g U (a ++ b) =
      preorderSchedule g U a ++ preorderSchedule g (U + preorderWeight g a) b := by
  induction a generalizing U with
  | nil => simp [preorderSchedule, preorderWeight]
  | cons ell a ih =>
    simp only [List.cons_append, preorderSchedule, ih, preorderWeight, List.map_cons,
      List.sum_cons]
    congr 2
    simp only [Nat.add_assoc]

theorem preorderSchedule_replicate (g U n : ℕ) (block : List ℕ) :
    preorderSchedule g U (List.replicate n block).flatten =
      (List.ofFn (fun i : Fin n =>
        preorderSchedule g (U + i.val * preorderWeight g block) block)).flatten := by
  induction n generalizing U with
  | zero => simp [preorderSchedule]
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, preorderSchedule_append, ih,
      List.ofFn_succ, List.flatten_cons]
    simp only [Fin.val_zero, zero_mul, Nat.add_zero, Fin.val_succ]
    congr 1
    congr 1
    apply congrArg List.ofFn
    funext i
    congr 1
    ring

theorem preorderSchedule_mem_start_ge (g U : ℕ) (lengths : List ℕ)
    (q : ℕ × ℕ) (hq : q ∈ preorderSchedule g U lengths) : U ≤ q.1 := by
  induction lengths generalizing U with
  | nil => simp [preorderSchedule] at hq
  | cons ell lengths ih =>
    simp only [preorderSchedule, List.mem_cons] at hq
    rcases hq with rfl | hq
    · rfl
    · exact (by omega : U ≤ U + ell + g).trans (ih _ hq)

theorem preorderSchedule_mem_end_ge_start (g U : ℕ) (lengths : List ℕ)
    (hpos : ∀ ell ∈ lengths, 0 < ell) (q : ℕ × ℕ)
    (hq : q ∈ preorderSchedule g U lengths) : q.1 ≤ q.2 := by
  induction lengths generalizing U with
  | nil => simp [preorderSchedule] at hq
  | cons ell lengths ih =>
    simp only [preorderSchedule, List.mem_cons] at hq
    rcases hq with rfl | hq
    · have := hpos ell (by simp); dsimp; omega
    · exact ih _ (fun l hl => hpos l (by simp [hl])) hq

theorem preorderSchedule_chain (g U : ℕ) (lengths : List ℕ)
    (hpos : ∀ ell ∈ lengths, 0 < ell) :
    (preorderSchedule g U lengths).IsChain (fun e f => f.1 = e.2 + g + 1) := by
  induction lengths generalizing U with
  | nil => simp [preorderSchedule]
  | cons ell lengths ih =>
    cases lengths with
    | nil => simp [preorderSchedule]
    | cons ell' lengths =>
      rw [preorderSchedule, preorderSchedule, List.isChain_cons_cons]
      refine ⟨?_, ih _ (fun l hl => hpos l (by simp [hl]))⟩
      have := hpos ell (by simp)
      dsimp
      omega

theorem preorderSchedule_pairwise_ends (g U : ℕ) (lengths : List ℕ)
    (hpos : ∀ ell ∈ lengths, 0 < ell) :
    (preorderSchedule g U lengths).Pairwise (fun e f => e.2 < f.2) := by
  induction lengths generalizing U with
  | nil => simp [preorderSchedule]
  | cons ell lengths ih =>
    rw [preorderSchedule, List.pairwise_cons]
    refine ⟨?_, ih _ (fun l hl => hpos l (by simp [hl]))⟩
    intro q hq
    have hs := preorderSchedule_mem_start_ge g (U + ell + g) lengths q hq
    have he := preorderSchedule_mem_end_ge_start g (U + ell + g) lengths
      (fun l hl => hpos l (by simp [hl])) q hq
    have := hpos ell (by simp)
    dsimp
    omega

theorem preorderPaths_succ_flatten (M h : ℕ) :
    preorderPaths M (h + 1) =
      (List.ofFn (fun i : Fin M =>
        [i] :: (preorderPaths M h).map (fun p => i :: p))).flatten := by
  simp [preorderPaths, List.flatMap_def, List.map_ofFn, Function.comp_def]

theorem preorderLengths_succ (M g L h : ℕ) :
    preorderLengths M g L (h + 1) =
      (List.replicate M
        (RoutingTemplate.lengthAt M g L (h + 1) :: preorderLengths M g L h)).flatten := by
  rw [preorderLengths, preorderPaths_succ_flatten, List.map_flatten, List.map_ofFn]
  simp only [Function.comp_def]
  have hb : ∀ i : Fin M,
      ([i] :: (preorderPaths M h).map (fun p => i :: p)).map
          (fun p => RoutingTemplate.lengthAt M g L (h + 1 + 1 - p.length)) =
        RoutingTemplate.lengthAt M g L (h + 1) :: preorderLengths M g L h := by
    intro i
    simp only [List.map_cons, List.map_map, Function.comp_def, preorderLengths,
      List.length_cons, List.length_nil, Nat.sub_zero, Nat.add_sub_add_right]
  simp_rw [hb]
  simp

theorem preorderLengths_positive (M g L h : ℕ) (hM : 1 ≤ M) (hL : 0 < L) :
    ∀ ell ∈ preorderLengths M g L h, 0 < ell := by
  intro ell hell
  obtain ⟨p, _, rfl⟩ := List.mem_map.1 hell
  exact RoutingTemplate.length_positive M g L _ hM hL

theorem preorderWeight_replicate (g n : ℕ) (block : List ℕ) :
    preorderWeight g (List.replicate n block).flatten = n * preorderWeight g block := by
  induction n with
  | zero => simp [preorderWeight]
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, preorderWeight_append, ih]
    ring

/-- Exact total duration, with ONE trailing gap included for concatenation. -/
theorem preorderLengths_weight (M g L h : ℕ) (hM : 1 ≤ M) (hh : 0 < h) :
    preorderWeight g (preorderLengths M g L h) = RoutingTemplate.span M g L h + g := by
  induction h with
  | zero => omega
  | succ h ih =>
    rw [preorderLengths_succ, preorderWeight_replicate]
    have hb : preorderWeight g
        (RoutingTemplate.lengthAt M g L (h + 1) :: preorderLengths M g L h) =
        RoutingTemplate.blockSpan M g L (h + 1) + g := by
      cases h with
      | zero => simp [preorderWeight, preorderLengths, preorderPaths]
      | succ h =>
        have hw := ih (by omega)
        change RoutingTemplate.lengthAt M g L (h + 2) + g +
          preorderWeight g (preorderLengths M g L (h + 1)) = _
        rw [hw, RoutingTemplate.blockSpan_succ_succ]
        omega
    rw [hb, RoutingTemplate.span_succ]
    have hMeq : M = (M - 1) + 1 := by omega
    nlinarith

/-- ACTUAL window positions in the canonical complete tree. -/
def preorderActualWindows (M g L h U : ℕ) : List (ℕ × ℕ) :=
  (preorderPaths M h).map (fun p =>
    (RoutingTemplate.incomingStart M g L h U p, RoutingTemplate.incomingEnd M g L h U p))

/-- The concrete recursively placed tree is EXACTLY the finite gap schedule. -/
theorem preorderActualWindows_eq_schedule (M g L h U : ℕ) (hM : 1 ≤ M) :
    preorderActualWindows M g L h U = preorderSchedule g U (preorderLengths M g L h) := by
  induction h generalizing U with
  | zero => simp [preorderActualWindows, preorderPaths, preorderLengths, preorderSchedule]
  | succ h ih =>
    have hb : preorderWeight g
        (RoutingTemplate.lengthAt M g L (h + 1) :: preorderLengths M g L h) =
        RoutingTemplate.blockSpan M g L (h + 1) + g := by
      cases h with
      | zero => simp [preorderWeight, preorderLengths, preorderPaths]
      | succ h =>
        change RoutingTemplate.lengthAt M g L (h + 2) + g +
          preorderWeight g (preorderLengths M g L (h + 1)) = _
        rw [preorderLengths_weight _ _ _ _ hM (by omega), RoutingTemplate.blockSpan_succ_succ]
        omega
    rw [preorderActualWindows, preorderPaths_succ_flatten, List.map_flatten, List.map_ofFn,
      preorderLengths_succ, preorderSchedule_replicate, hb]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    simp only [Function.comp_def]
    simp only [List.map_cons, RoutingTemplate.incomingStart, RoutingTemplate.incomingEnd,
      ↓reduceIte, preorderSchedule]
    congr 1
    rw [List.map_map]
    simp only [Function.comp_def]
    have heq : ∀ p ∈ preorderPaths M h,
        (RoutingTemplate.incomingStart M g L (h + 1) U (i :: p),
          RoutingTemplate.incomingEnd M g L (h + 1) U (i :: p)) =
        (RoutingTemplate.incomingStart M g L h
            (U + i.val * (RoutingTemplate.blockSpan M g L (h + 1) + g) +
              RoutingTemplate.lengthAt M g L (h + 1) + g) p,
          RoutingTemplate.incomingEnd M g L h
            (U + i.val * (RoutingTemplate.blockSpan M g L (h + 1) + g) +
              RoutingTemplate.lengthAt M g L (h + 1) + g) p) := by
      intro p hp
      have hp' := (mem_preorderPaths_iff M h p).1 hp |>.1
      simp only [RoutingTemplate.incomingStart, RoutingTemplate.incomingEnd, hp', ↓reduceIte,
        Nat.add_sub_cancel]
    rw [List.map_congr_left heq]
    exact ih _

theorem preorderSchedule_last_endpoint (g U : ℕ) (lengths : List ℕ)
    (hpos : ∀ ell ∈ lengths, 0 < ell) (q : ℕ × ℕ)
    (hlast : (preorderSchedule g U lengths).getLast? = some q) :
    q.2 + g + 1 = U + preorderWeight g lengths := by
  induction lengths generalizing U with
  | nil => simp [preorderSchedule] at hlast
  | cons ell lengths ih =>
    cases lengths with
    | nil =>
      have hq : (U, U + ell - 1) = q := by simpa [preorderSchedule] using hlast
      subst q
      have := hpos ell (by simp)
      simp only [preorderWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      dsimp
      omega
    | cons ell' lengths =>
      have hl : (preorderSchedule g (U + ell + g) (ell' :: lengths)).getLast? = some q := by
        simpa only [preorderSchedule, List.getLast?_cons_cons] using hlast
      have hrec := ih (U + ell + g) (fun l hl => hpos l (by simp [hl])) hl
      change q.2 + g + 1 = U + (ell + g + preorderWeight g (ell' :: lengths))
      omega

theorem preorderPaths_chain (M g L h U : ℕ) (hM : 1 ≤ M) (hL : 0 < L) :
    (preorderPaths M h).IsChain (fun e f =>
      RoutingTemplate.incomingStart M g L h U f =
        RoutingTemplate.incomingEnd M g L h U e + g + 1) := by
  have hs := preorderSchedule_chain g U (preorderLengths M g L h)
    (preorderLengths_positive M g L h hM hL)
  rw [← preorderActualWindows_eq_schedule M g L h U hM] at hs
  exact (List.isChain_map _).1 hs

theorem preorderPaths_pairwise_ends (M g L h U : ℕ) (hM : 1 ≤ M) (hL : 0 < L) :
    (preorderPaths M h).Pairwise (fun e f =>
      RoutingTemplate.incomingEnd M g L h U e < RoutingTemplate.incomingEnd M g L h U f) := by
  have hs := preorderSchedule_pairwise_ends g U (preorderLengths M g L h)
    (preorderLengths_positive M g L h hM hL)
  rw [← preorderActualWindows_eq_schedule M g L h U hM] at hs
  exact (List.pairwise_map
    (f := fun p : List (Fin M) => (RoutingTemplate.incomingStart M g L h U p,
      RoutingTemplate.incomingEnd M g L h U p))
    (R := fun e f : ℕ × ℕ => e.2 < f.2)).1 hs

theorem preorderPaths_nodup (M h : ℕ) (hM : 1 ≤ M) : (preorderPaths M h).Nodup := by
  have hs := preorderPaths_pairwise_ends M 0 1 h 0 hM (by decide)
  change (preorderPaths M h).Pairwise (fun e f => e ≠ f)
  exact hs.imp (fun {e f} hef heq => by subst f; exact Nat.lt_irrefl _ hef)

/-- Exact consecutive-window gap derived from the canonical preorder itself. -/
theorem preorder_adjacent_gap (M g L h U : ℕ) (hM : 1 ≤ M) (hL : 0 < L)
    (before after : List (List (Fin M))) (e f : List (Fin M))
    (horder : preorderPaths M h = before ++ e :: f :: after) :
    RoutingTemplate.incomingStart M g L h U f =
      RoutingTemplate.incomingEnd M g L h U e + g + 1 :=
  (List.isChain_iff_forall_rel_of_append_cons_cons.1
    (preorderPaths_chain M g L h U hM hL)) horder

/-- All earlier window endpoints are bounded by the ACTUAL predecessor endpoint.
One predecessor interval therefore controls every earlier nested-grid address.
-/
theorem preorder_adjacent_earlier_end_le (M g L h U : ℕ) (hM : 1 ≤ M) (hL : 0 < L)
    (before after : List (List (Fin M))) (e f q : List (Fin M))
    (horder : preorderPaths M h = before ++ e :: f :: after)
    (hq : q ∈ before ++ [e]) :
    RoutingTemplate.incomingEnd M g L h U q ≤ RoutingTemplate.incomingEnd M g L h U e := by
  have hs := preorderPaths_pairwise_ends M g L h U hM hL
  rw [horder, List.pairwise_append] at hs
  rcases List.mem_append.1 hq with hq | hq
  · exact (hs.2.2 q hq e (by simp)).le
  · have hqe : q = e := by simpa using hq
    subst q
    rfl

/-- The last ACTUAL window finishes at `U+span(h)-1`, including all subtrees. -/
theorem preorder_last_endpoint (M g L h U : ℕ) (hM : 1 ≤ M) (hL : 0 < L)
    (hh : 0 < h) (p : List (Fin M)) (hlast : (preorderPaths M h).getLast? = some p) :
    RoutingTemplate.incomingEnd M g L h U p = U + RoutingTemplate.span M g L h - 1 := by
  have hlast' : (preorderActualWindows M g L h U).getLast? =
      some (RoutingTemplate.incomingStart M g L h U p,
        RoutingTemplate.incomingEnd M g L h U p) := by
    simp [preorderActualWindows, hlast]
  rw [preorderActualWindows_eq_schedule M g L h U hM] at hlast'
  have hs := preorderSchedule_last_endpoint g U (preorderLengths M g L h)
    (preorderLengths_positive M g L h hM hL) _ hlast'
  rw [preorderLengths_weight M g L h hM hh] at hs
  dsimp at hs
  omega

theorem routingEdge_mem_preorderPaths {M d : ℕ} (e : RoutingEdge M d) :
    List.ofFn e.1.2 ++ [e.2] ∈ preorderPaths M d := by
  apply (mem_preorderPaths_iff _ _ _).2
  constructor
  · simp
  · simp only [List.length_append, List.length_ofFn, List.length_singleton]
    exact e.1.1.isLt

theorem preorderSchedule_head_start (g U : ℕ) (lengths : List ℕ) (q : ℕ × ℕ)
    (hhead : (preorderSchedule g U lengths).head? = some q) : q.1 = U := by
  cases lengths with
  | nil => simp [preorderSchedule] at hhead
  | cons ell lengths =>
    have hq : (U, U + ell - 1) = q := by simpa [preorderSchedule] using hhead
    subst q
    rfl

theorem preorder_first_start (M g L h U : ℕ) (hM : 1 ≤ M)
    (p : List (Fin M)) (hfirst : (preorderPaths M h).head? = some p) :
    RoutingTemplate.incomingStart M g L h U p = U := by
  have hfirst' : (preorderActualWindows M g L h U).head? =
      some (RoutingTemplate.incomingStart M g L h U p,
        RoutingTemplate.incomingEnd M g L h U p) := by
    simp [preorderActualWindows, hfirst]
  rw [preorderActualWindows_eq_schedule M g L h U hM] at hfirst'
  exact preorderSchedule_head_start _ _ _ _ hfirst'

abbrev PreorderWindowIndex (M h : ℕ) := Fin (preorderPaths M h).length

def preorderWindowPath {M h : ℕ} (i : PreorderWindowIndex M h) : List (Fin M) :=
  (preorderPaths M h).get i

def preorderPredecessorPath {M h : ℕ} (i : PreorderWindowIndex M h) (hi : 0 < i.val) :
    List (Fin M) := (preorderPaths M h).get ⟨i.val - 1, by have := i.isLt; omega⟩

def preorderPredecessorEnd {M h : ℕ} (g L U : ℕ)
    (i : PreorderWindowIndex M h) (hi : 0 < i.val) : ℕ :=
  RoutingTemplate.incomingEnd M g L h U (preorderPredecessorPath i hi)

theorem preorderWindowPath_complete (M h : ℕ) (p : List (Fin M)) :
    p ∈ preorderPaths M h ↔ ∃ i : PreorderWindowIndex M h, preorderWindowPath i = p := by
  exact List.mem_iff_get

/-- Each noninitial actual window has ONE concrete preceding-window endpoint. -/
theorem preorder_index_predecessor_gap (M g L h U : ℕ) (hM : 1 ≤ M) (hL : 0 < L)
    (i : PreorderWindowIndex M h) (hi : 0 < i.val) :
    RoutingTemplate.incomingStart M g L h U (preorderWindowPath i) =
      preorderPredecessorEnd g L U i hi + g + 1 := by
  have hs := (List.isChain_iff_getElem.1 (preorderPaths_chain M g L h U hM hL))
    (i.val - 1) (by have := i.isLt; omega)
  have hid : i.val - 1 + 1 = i.val := by omega
  simpa only [hid, preorderWindowPath, preorderPredecessorEnd, preorderPredecessorPath,
    List.get_eq_getElem] using hs

theorem preorder_index_earlier_end_le (M g L h U : ℕ) (hM : 1 ≤ M) (hL : 0 < L)
    (i j : PreorderWindowIndex M h) (hi : 0 < i.val) (hji : j.val < i.val) :
    RoutingTemplate.incomingEnd M g L h U (preorderWindowPath j) ≤
      preorderPredecessorEnd g L U i hi := by
  let prev : PreorderWindowIndex M h := ⟨i.val - 1, by have := i.isLt; omega⟩
  have hjp : j.val ≤ prev.val := by dsimp [prev]; omega
  by_cases heq : j.val = prev.val
  · have hjeq : j = prev := Fin.ext heq
    change RoutingTemplate.incomingEnd M g L h U ((preorderPaths M h).get j) ≤
      RoutingTemplate.incomingEnd M g L h U ((preorderPaths M h).get prev)
    rw [hjeq]
  · have hjp' : j < prev := by change j.val < prev.val; omega
    exact ((preorderPaths_pairwise_ends M g L h U hM hL).rel_get_of_lt hjp').le

theorem preorderWindowIndex_card (M h : ℕ) :
    Fintype.card (PreorderWindowIndex M h) = preorderEdgeCount M h := by
  simp [PreorderWindowIndex, preorderPaths_length]

abbrev PreorderNoninitialIndex (M h : ℕ) := {i : PreorderWindowIndex M h // 0 < i.val}

theorem preorderNoninitialIndex_card_le (M h : ℕ) :
    Fintype.card (PreorderNoninitialIndex M h) ≤ preorderEdgeCount M h := by
  exact (Fintype.card_subtype_le _).trans (preorderWindowIndex_card M h).le

theorem preorderSchedule_pairwise_gaps (g U : ℕ) (lengths : List ℕ)
    (hpos : ∀ ell ∈ lengths, 0 < ell) :
    (preorderSchedule g U lengths).Pairwise (fun e f => e.2 + g + 1 ≤ f.1) := by
  induction lengths generalizing U with
  | nil => simp [preorderSchedule]
  | cons ell lengths ih =>
    rw [preorderSchedule, List.pairwise_cons]
    refine ⟨?_, ih _ (fun l hl => hpos l (by simp [hl]))⟩
    intro q hq
    have hs := preorderSchedule_mem_start_ge g (U + ell + g) lengths q hq
    have := hpos ell (by simp)
    dsimp
    omega

theorem preorderSchedule_pairwise_starts (g U : ℕ) (lengths : List ℕ)
    (hpos : ∀ ell ∈ lengths, 0 < ell) :
    (preorderSchedule g U lengths).Pairwise (fun e f => e.1 < f.1) := by
  induction lengths generalizing U with
  | nil => simp [preorderSchedule]
  | cons ell lengths ih =>
    rw [preorderSchedule, List.pairwise_cons]
    refine ⟨?_, ih _ (fun l hl => hpos l (by simp [hl]))⟩
    intro q hq
    have hs := preorderSchedule_mem_start_ge g (U + ell + g) lengths q hq
    have := hpos ell (by simp)
    dsimp
    omega

theorem preorderPaths_pairwise_gaps (M g L h U : ℕ) (hM : 1 ≤ M) (hL : 0 < L) :
    (preorderPaths M h).Pairwise (fun e f =>
      RoutingTemplate.incomingEnd M g L h U e + g + 1 ≤
        RoutingTemplate.incomingStart M g L h U f) := by
  have hs := preorderSchedule_pairwise_gaps g U (preorderLengths M g L h)
    (preorderLengths_positive M g L h hM hL)
  rw [← preorderActualWindows_eq_schedule M g L h U hM] at hs
  exact (List.pairwise_map
    (f := fun p : List (Fin M) => (RoutingTemplate.incomingStart M g L h U p,
      RoutingTemplate.incomingEnd M g L h U p))
    (R := fun e f : ℕ × ℕ => e.2 + g + 1 ≤ f.1)).1 hs

theorem preorderPaths_pairwise_starts (M g L h U : ℕ) (hM : 1 ≤ M) (hL : 0 < L) :
    (preorderPaths M h).Pairwise (fun e f =>
      RoutingTemplate.incomingStart M g L h U e <
        RoutingTemplate.incomingStart M g L h U f) := by
  have hs := preorderSchedule_pairwise_starts g U (preorderLengths M g L h)
    (preorderLengths_positive M g L h hM hL)
  rw [← preorderActualWindows_eq_schedule M g L h U hM] at hs
  exact (List.pairwise_map
    (f := fun p : List (Fin M) => (RoutingTemplate.incomingStart M g L h U p,
      RoutingTemplate.incomingEnd M g L h U p))
    (R := fun e f : ℕ × ℕ => e.1 < f.1)).1 hs

theorem preorder_positions_lt_of_start_lt (M g L h U : ℕ) (hM : 1 ≤ M) (hL : 0 < L)
    (i j : PreorderWindowIndex M h)
    (hstart : RoutingTemplate.incomingStart M g L h U (preorderWindowPath i) <
      RoutingTemplate.incomingStart M g L h U (preorderWindowPath j)) : i < j := by
  by_contra hn
  have hji : j.val ≤ i.val := by change ¬ i.val < j.val at hn; omega
  by_cases heq : i.val = j.val
  · have hij : i = j := Fin.ext heq
    subst j
    exact Nat.lt_irrefl _ hstart
  · have hji' : j < i := by change j.val < i.val; omega
    have hs := (preorderPaths_pairwise_starts M g L h U hM hL).rel_get_of_lt hji'
    exact Nat.lt_asymm hstart hs

namespace RoutingTemplate

theorem preorderIncomingEnd_of_edge {M d : ℕ} (c : RoutingTemplate M d)
    (e : RoutingEdge M d) :
    incomingEnd M c.gap c.baseLength d c.origin (List.ofFn e.1.2 ++ [e.2]) = c.edgeEnd e := by
  rw [incomingEnd_eq_start_add_length _ _ _ _ _ _ (by simp) (by
    simp only [List.length_append, List.length_ofFn, List.length_singleton]
    exact e.1.1.isLt), incomingStart_of_edge]
  simp only [List.length_append, List.length_ofFn, List.length_singleton,
    Nat.add_sub_add_right]
  rfl

theorem incomingStart_ge (M g L h U : ℕ) (p : List (Fin M)) :
    U ≤ incomingStart M g L h U p := by
  induction p generalizing h U with
  | nil => rfl
  | cons i p ih =>
    by_cases hp : p = []
    · subst p
      simp only [incomingStart, ↓reduceIte]
      omega
    · simp only [incomingStart, hp, ↓reduceIte]
      exact (by omega : U ≤ U + i.val * (blockSpan M g L h + g) + lengthAt M g L h + g).trans
        (ih _ _)

/-- ACTUAL edge-start order implies full endpoint separation, because the
canonical complete preorder was proved to equal the finite gap schedule.
-/
theorem earlier_edgeEnd_add_gap_le {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 1 ≤ M) (hL : 0 < c.baseLength) (f e : RoutingEdge M d)
    (hbefore : c.edgeStart f < c.edgeStart e) :
    c.edgeEnd f + c.gap + 1 ≤ c.edgeStart e := by
  obtain ⟨i, hi⟩ := (preorderWindowPath_complete M d _).1 (routingEdge_mem_preorderPaths f)
  obtain ⟨j, hj⟩ := (preorderWindowPath_complete M d _).1 (routingEdge_mem_preorderPaths e)
  have hstart : incomingStart M c.gap c.baseLength d c.origin (preorderWindowPath i) <
      incomingStart M c.gap c.baseLength d c.origin (preorderWindowPath j) := by
    simpa only [hi, hj, incomingStart_of_edge] using hbefore
  have hij := preorder_positions_lt_of_start_lt M c.gap c.baseLength d c.origin hM hL i j hstart
  have hg := (preorderPaths_pairwise_gaps M c.gap c.baseLength d c.origin hM hL).rel_get_of_lt hij
  change incomingEnd M c.gap c.baseLength d c.origin (preorderWindowPath i) + c.gap + 1 ≤
    incomingStart M c.gap c.baseLength d c.origin (preorderWindowPath j) at hg
  simpa only [hi, hj, incomingStart_of_edge, preorderIncomingEnd_of_edge] using hg

/-- Boundary used for each actual edge by the stable-center union bound. The
first edge's extra constraint is harmless; the number of constraints is K.
-/
def predecessorBoundary {M d : ℕ} (c : RoutingTemplate M d) (e : RoutingEdge M d) : ℕ :=
  c.edgeStart e - c.gap - 1

theorem predecessorBoundary_start {M d : ℕ} (c : RoutingTemplate M d)
    (hU : c.gap + 1 ≤ c.origin) (e : RoutingEdge M d) :
    c.edgeStart e = c.predecessorBoundary e + c.gap + 1 := by
  have hg := incomingStart_ge M c.gap c.baseLength d c.origin (List.ofFn e.1.2 ++ [e.2])
  rw [incomingStart_of_edge] at hg
  unfold predecessorBoundary
  omega

theorem earlier_edgeEnd_le_predecessorBoundary {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 1 ≤ M) (hL : 0 < c.baseLength) (f e : RoutingEdge M d)
    (hbefore : c.edgeStart f < c.edgeStart e) : c.edgeEnd f ≤ c.predecessorBoundary e := by
  have hg := c.earlier_edgeEnd_add_gap_le hM hL f e hbefore
  unfold predecessorBoundary
  omega

end RoutingTemplate

end ContinuumGeometric
