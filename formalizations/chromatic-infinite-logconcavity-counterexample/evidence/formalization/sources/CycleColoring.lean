import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

namespace ChromaticC17
open SimpleGraph

abbrev C17 := cycleGraph 17

/-- Each successor edge is an edge of the actual mathlib cycle graph. -/
theorem cycle_succ_adj (i : Fin 17) : C17.Adj i (i + 1) := by
  fin_cases i <;> decide

theorem proper_of_successor {α : Type*} (f : Fin 17 → α)
    (h : ∀ i, f i ≠ f (i + 1)) : ∀ {i j}, C17.Adj i j → f i ≠ f j := by
  intro i j hij
  rw [cycleGraph_adj] at hij
  rcases hij with hij | hij
  · have he : i = j + 1 := by simpa [add_comm] using (sub_eq_iff_eq_add).mp hij
    simpa [he] using (h j).symm
  · have he : j = i + 1 := by simpa [add_comm] using (sub_eq_iff_eq_add).mp hij
    simpa [he] using h i

/-- A proper coloring gives a closed length-17 walk in the complete color graph. -/
def coloringWalk {α : Type*} (c : C17.Coloring α) :
    (completeGraph α).Walk (c 0) (c 0) :=
  .cons (c.valid (by decide : C17.Adj 0 1)) (
  .cons (c.valid (by decide : C17.Adj 1 2)) (
  .cons (c.valid (by decide : C17.Adj 2 3)) (
  .cons (c.valid (by decide : C17.Adj 3 4)) (
  .cons (c.valid (by decide : C17.Adj 4 5)) (
  .cons (c.valid (by decide : C17.Adj 5 6)) (
  .cons (c.valid (by decide : C17.Adj 6 7)) (
  .cons (c.valid (by decide : C17.Adj 7 8)) (
  .cons (c.valid (by decide : C17.Adj 8 9)) (
  .cons (c.valid (by decide : C17.Adj 9 10)) (
  .cons (c.valid (by decide : C17.Adj 10 11)) (
  .cons (c.valid (by decide : C17.Adj 11 12)) (
  .cons (c.valid (by decide : C17.Adj 12 13)) (
  .cons (c.valid (by decide : C17.Adj 13 14)) (
  .cons (c.valid (by decide : C17.Adj 14 15)) (
  .cons (c.valid (by decide : C17.Adj 15 16)) (
  .cons (c.valid (by decide : C17.Adj 16 0)) (
  .nil
  )
  )
  )
  )
  )
  )
  )
  )
  )
  )
  )
  )
  )
  )
  )
  )
  )

theorem coloringWalk_length {α : Type*} (c : C17.Coloring α) :
    (coloringWalk c).length = 17 := rfl

abbrev ColorLoops (α : Type*) :=
  Σ a : α, {p : (completeGraph α).Walk a a // p.length = 17}

def loopColoring {α : Type*} (p : ColorLoops α) : C17.Coloring α :=
  Coloring.mk (fun i => p.2.1.getVert i.val) (proper_of_successor (fun i : Fin 17 => p.2.1.getVert i.val) (by
    intro i
    have h := p.2.1.adj_getVert_succ (show i.val < p.2.1.length by rw [p.2.2]; exact i.isLt)
    change p.2.1.getVert i.val ≠ p.2.1.getVert (i.val + 1) at h
    by_cases hi : i.val = 16
    · have he : i = 16 := Fin.ext hi
      have hlast : p.2.1.getVert 17 = p.1 := by
        simpa [p.2.2] using p.2.1.getVert_length
      simpa [he, hlast] using h
    · have hv : ((i + 1 : Fin 17) : ℕ) = i.val + 1 := by
        apply Fin.val_add_one_of_lt'
        omega
      simpa only [hv] using h))

/-- Bijection with genuine graph colorings; no formula for their number is assumed. -/
def coloringEquivLoops (α : Type*) : C17.Coloring α ≃ ColorLoops α where
  toFun c := ⟨c 0, ⟨coloringWalk c, coloringWalk_length c⟩⟩
  invFun := loopColoring
  left_inv c := by
    ext i
    fin_cases i <;> rfl
  right_inv := by
    rintro ⟨a, ⟨p, hp⟩⟩
    cases p with
    | nil => simp at hp
    | cons h0 p =>
      cases p with
      | nil => simp at hp
      | cons h1 p =>
        cases p with
        | nil => simp at hp
        | cons h2 p =>
          cases p with
          | nil => simp at hp
          | cons h3 p =>
            cases p with
            | nil => simp at hp
            | cons h4 p =>
              cases p with
              | nil => simp at hp
              | cons h5 p =>
                cases p with
                | nil => simp at hp
                | cons h6 p =>
                  cases p with
                  | nil => simp at hp
                  | cons h7 p =>
                    cases p with
                    | nil => simp at hp
                    | cons h8 p =>
                      cases p with
                      | nil => simp at hp
                      | cons h9 p =>
                        cases p with
                        | nil => simp at hp
                        | cons h10 p =>
                          cases p with
                          | nil => simp at hp
                          | cons h11 p =>
                            cases p with
                            | nil => simp at hp
                            | cons h12 p =>
                              cases p with
                              | nil => simp at hp
                              | cons h13 p =>
                                cases p with
                                | nil => simp at hp
                                | cons h14 p =>
                                  cases p with
                                  | nil => simp at hp
                                  | cons h15 p =>
                                    cases p with
                                    | nil => simp at hp
                                    | cons h16 p =>
                                      cases p with
                                      | nil => rfl
                                      | cons h17 p =>
                                        simp only [Walk.length_cons] at hp
                                        omega

/-- Counting all proper q-colorings equals the trace of a complete-graph adjacency power. -/
theorem coloring_card_eq_trace (q : ℕ) :
    (Fintype.card (C17.Coloring (Fin q)) : ℤ) =
      Matrix.trace ((completeGraph (Fin q)).adjMatrix ℤ ^ 17) := by
  rw [Fintype.card_congr (coloringEquivLoops (Fin q)), Fintype.card_sigma]
  simp only [Nat.cast_sum, Matrix.trace, Matrix.diag]
  apply Finset.sum_congr rfl
  intro a ha
  exact ((completeGraph (Fin q)).adjMatrix_pow_apply_eq_card_walk 17 a a).symm

end ChromaticC17
