import ErdosSimilarityGrowingGaps.RoutingLaw
import Mathlib.Data.List.OfFn

/-! Adapted in this repository from the finite geometric routing construction.
The real-logarithm sampler and variable schedule are supplied separately. -/

/-!
The canonical complete ordered tree. All M children carry windows; only the
first M-1 have selectors. Paths, not an abstract independence hypothesis,
identify the finite tables.
-/
namespace ErdosSimilarityGrowingGaps

abbrev InternalNode (M d : ℕ) := Σ l : Fin d, (Fin l.val → Fin M)
abbrev RoutingEdge (M d : ℕ) := Σ v : InternalNode M d, Fin M
abbrev SelectorEdge (M d : ℕ) := Σ v : InternalNode M d, Fin (M - 1)
abbrev RoutingLeaf (M d : ℕ) := Fin d → Fin M

structure RoutingTemplate (M d : ℕ) where
  gap : ℕ
  baseLength : ℕ
  origin : ℕ

namespace RoutingTemplate

/-- Span of the entire complete tree, including the intervening gaps. -/
def span (M g L : ℕ) : ℕ → ℕ
  | 0 => 0
  | h + 1 => M * (if h = 0 then L else 2 * (g + span M g L h)) + (M - 1) * g

def lengthAt (M g L h : ℕ) : ℕ :=
  if h ≤ 1 then L else g + span M g L (h - 1)

/-- The consecutive preorder block consisting of an edge and its child tree. -/
def blockSpan (M g L h : ℕ) : ℕ :=
  if h ≤ 1 then L else 2 * (g + span M g L (h - 1))

@[simp] theorem span_zero (M g L : ℕ) : span M g L 0 = 0 := rfl
@[simp] theorem span_one (M g L : ℕ) :
    span M g L 1 = M * L + (M - 1) * g := by simp [span]
@[simp] theorem lengthAt_one (M g L : ℕ) : lengthAt M g L 1 = L := by
  simp [lengthAt]
@[simp] theorem blockSpan_one (M g L : ℕ) : blockSpan M g L 1 = L := by
  simp [blockSpan]

theorem span_succ (M g L h : ℕ) :
    span M g L (h + 1) = M * blockSpan M g L (h + 1) + (M - 1) * g := by
  by_cases hh : h = 0
  · subst h; simp
  · have hh' : ¬ h + 1 ≤ 1 := by omega
    simp [span, blockSpan, hh, hh']

theorem blockSpan_succ_succ (M g L h : ℕ) :
    blockSpan M g L (h + 2) =
      lengthAt M g L (h + 2) + g + span M g L (h + 1) := by
  simp [blockSpan, lengthAt]
  omega

theorem blockSpan_le_twice_length (M g L h : ℕ) :
    blockSpan M g L h ≤ 2 * lengthAt M g L h := by
  unfold blockSpan lengthAt
  split_ifs <;> omega

theorem span_base_le (M g L h : ℕ) (hM : 1 ≤ M) :
    L ≤ span M g L (h + 1) := by
  induction h with
  | zero => change L ≤ M * L + (M - 1) * g; nlinarith
  | succ h ih =>
    change L ≤ M * (2 * (g + span M g L (h + 1))) + (M - 1) * g
    nlinarith

theorem base_le_length (M g L h : ℕ) (hM : 1 ≤ M) :
    L ≤ lengthAt M g L h := by
  unfold lengthAt
  split_ifs with hh
  · exact le_rfl
  · have : ∃ r, h - 1 = r + 1 := by exact ⟨h - 2, by omega⟩
    obtain ⟨r, hr⟩ := this
    rw [hr]
    exact (span_base_le M g L r hM).trans (Nat.le_add_left _ _)

theorem length_positive (M g L h : ℕ) (hM : 1 ≤ M) (hL : 0 < L) :
    0 < lengthAt M g L h := lt_of_lt_of_le hL (base_le_length M g L h hM)

/-- Start of a subtree after following the prescribed prefix from the root. -/
def subtreeStart (M g L : ℕ) : ℕ → ℕ → List (Fin M) → ℕ
  | _, U, [] => U
  | h, U, i :: p =>
      subtreeStart M g L (h - 1)
        (U + i.val * (blockSpan M g L h + g) + lengthAt M g L h + g) p

def nodeStart {M d : ℕ} (c : RoutingTemplate M d) (v : InternalNode M d) : ℕ :=
  subtreeStart M c.gap c.baseLength d c.origin (List.ofFn v.2)

def edgeStart {M d : ℕ} (c : RoutingTemplate M d) (e : RoutingEdge M d) : ℕ :=
  nodeStart c e.1 + e.2.val * (blockSpan M c.gap c.baseLength (d - e.1.1.val) + c.gap)

def edgeLength {M d : ℕ} (c : RoutingTemplate M d) (e : RoutingEdge M d) : ℕ :=
  lengthAt M c.gap c.baseLength (d - e.1.1.val)

def edgeEnd {M d : ℕ} (c : RoutingTemplate M d) (e : RoutingEdge M d) : ℕ :=
  edgeStart c e + edgeLength c e - 1

def edgeStar {M d : ℕ} (c : RoutingTemplate M d) (e : RoutingEdge M d) : ℕ :=
  edgeStart c e + blockSpan M c.gap c.baseLength (d - e.1.1.val) - 1

def selectorRoutingEdge {M d : ℕ} (e : SelectorEdge M d) : RoutingEdge M d :=
  ⟨e.1, Fin.castLE (Nat.sub_le M 1) e.2⟩

def selectorEnd {M d : ℕ} (c : RoutingTemplate M d) (e : SelectorEdge M d) : ℕ :=
  edgeEnd c (selectorRoutingEdge e)

def leafIncomingEdge {M d : ℕ} (hd : 0 < d) (p : RoutingLeaf M d) : RoutingEdge M d :=
  ⟨⟨⟨d - 1, by omega⟩, fun i => p ⟨i.val, by omega⟩⟩,
    p ⟨d - 1, by omega⟩⟩

/-- Endpoint of the last incoming edge in a prescribed path. -/
def incomingEnd (M g L : ℕ) : ℕ → ℕ → List (Fin M) → ℕ
  | _, U, [] => U
  | h, U, i :: p =>
      let a := U + i.val * (blockSpan M g L h + g)
      if p = [] then a + lengthAt M g L h - 1
      else incomingEnd M g L (h - 1) (a + lengthAt M g L h + g) p

def leafEnd {M d : ℕ} (c : RoutingTemplate M d) (_hd : 0 < d)
    (p : RoutingLeaf M d) : ℕ :=
  incomingEnd M c.gap c.baseLength d c.origin (List.ofFn p)

theorem edge_span_bound {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 1 ≤ M) (hL : 0 < c.baseLength) (e : RoutingEdge M d) :
    edgeStar c e + 1 ≤ edgeStart c e + 2 * edgeLength c e := by
  have hb := blockSpan_le_twice_length M c.gap c.baseLength (d - e.1.1.val)
  have hp : 0 < blockSpan M c.gap c.baseLength (d - e.1.1.val) := by
    unfold blockSpan
    split_ifs with hh
    · exact hL
    · have : c.baseLength ≤ c.gap + span M c.gap c.baseLength (d - e.1.1.val - 1) := by
        simpa [lengthAt, hh] using base_le_length M c.gap c.baseLength (d - e.1.1.val) hM
      omega
  unfold edgeStar edgeLength
  omega

theorem sibling_starts {M d : ℕ} (c : RoutingTemplate M d) (v : InternalNode M d)
    (i j : Fin M) (h : i.val ≤ j.val) :
    edgeStart c ⟨v, j⟩ = edgeStart c ⟨v, i⟩ +
      (j.val - i.val) * (blockSpan M c.gap c.baseLength (d - v.1.val) + c.gap)
      := by
  change nodeStart c v + j.val * _ = nodeStart c v + i.val * _ + _
  have heq : j.val = i.val + (j.val - i.val) := by omega
  calc
    _ = nodeStart c v + (i.val + (j.val - i.val)) *
        (blockSpan M c.gap c.baseLength (d - v.1.val) + c.gap) :=
      congrArg (fun n => nodeStart c v + n *
        (blockSpan M c.gap c.baseLength (d - v.1.val) + c.gap)) heq
    _ = _ := by ring

def lengthCoefficient (M : ℕ) : ℕ → ℕ
  | 0 => 0
  | h + 1 => if h = 0 then M else 2 * M * lengthCoefficient M h

def gapCoefficient (M : ℕ) : ℕ → ℕ
  | 0 => 0
  | h + 1 => if h = 0 then M - 1 else 2 * M * (1 + gapCoefficient M h) + (M - 1)

/-- Exact affine dependence needed by the noncircular logarithmic schedule. -/
theorem span_affine (M g L h : ℕ) :
    span M g L h = lengthCoefficient M h * L + gapCoefficient M h * g := by
  induction h with
  | zero => simp [lengthCoefficient, gapCoefficient]
  | succ h ih =>
    by_cases hh : h = 0
    · subst h; simp [lengthCoefficient, gapCoefficient]
    · rw [span, lengthCoefficient, gapCoefficient, if_neg hh, if_neg hh, if_neg hh, ih]
      ring

theorem total_span_affine {M d : ℕ} (c : RoutingTemplate M d) :
    span M c.gap c.baseLength d =
      lengthCoefficient M d * c.baseLength + (gapCoefficient M d * c.gap) :=
  span_affine M c.gap c.baseLength d

end RoutingTemplate

/-- Exact finite per-table address types, agreed with the probability lane. -/
abbrev SelectorAddress {M d : ℕ} (c : RoutingTemplate M d) :=
  Σ e : SelectorEdge M d, Fin (2 ^ (c.selectorEnd e + 3))

abbrev TerminalAddress {M d : ℕ} (c : RoutingTemplate M d) (hd : 0 < d) :=
  Σ p : RoutingLeaf M d, Fin (2 ^ (c.leafEnd hd p + 3))

end ErdosSimilarityGrowingGaps
