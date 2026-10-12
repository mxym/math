import ChromaticCyclesAllN.CyclePolynomialAll
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.List.ChainOfFn
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace ChromaticCycleAll
open SimpleGraph

theorem cycleGraph_adj_succ_iff (n : ℕ) [NeZero n] (hn : 3 ≤ n) (i j : Fin n) :
    (cycleGraph n).Adj i j ↔ i = j + 1 ∨ j = i + 1 := by
  rw [cycleGraph_adj']
  constructor
  · rintro (h | h)
    · left
      have ht : i - j = (1 : Fin n) := by
        apply Fin.ext
        simpa [Fin.val_one, Nat.mod_eq_of_lt (show 1 < n by omega)] using h
      have hsum : i = (i-j)+j := by simp
      rw [ht] at hsum
      simpa [add_comm] using hsum
    · right
      have ht : j - i = (1 : Fin n) := by
        apply Fin.ext
        simpa [Fin.val_one, Nat.mod_eq_of_lt (show 1 < n by omega)] using h
      have hsum : j = (j-i)+i := by simp
      rw [ht] at hsum
      simpa [add_comm] using hsum
  · rintro (h | h)
    · left
      rw [h]
      simpa [Nat.mod_eq_of_lt (show 1 < n by omega)]
    · right
      rw [h]
      simpa [Nat.mod_eq_of_lt (show 1 < n by omega)]

theorem cycle_succ_adj (n : ℕ) [NeZero n] (hn : 3 ≤ n) (i : Fin n) :
    (cycleGraph n).Adj i (i + 1) :=
  (cycleGraph_adj_succ_iff n hn i (i+1)).2 (Or.inr rfl)

theorem proper_of_successor (n : ℕ) [NeZero n] (hn : 3 ≤ n)
    {α : Type*} (f : Fin n → α)
    (h : ∀ i, f i ≠ f (i + 1)) :
    ∀ {i j}, (cycleGraph n).Adj i j → f i ≠ f j := by
  intro i j hij
  rcases (cycleGraph_adj_succ_iff n hn i j).1 hij with he | he
  · subst i
    exact (h j).symm
  · subst j
    exact h i

theorem proper_successor_iff (n : ℕ) [NeZero n] (hn : 3 ≤ n)
    {α : Type*} (f : Fin n → α) :
    (∀ {i j}, (cycleGraph n).Adj i j → f i ≠ f j) ↔
      (∀ i, f i ≠ f (i + 1)) := by
  constructor
  · intro h i
    exact h (cycle_succ_adj n hn i)
  · exact proper_of_successor n hn f

end ChromaticCycleAll
