import Mxym.StochasticRigidity
import Mathlib.Tactic.FinCases

open scoped BigOperators
open Mxym.StochasticRigidity

namespace StochasticChecks

def swap : Matrix (Fin 2) (Fin 2) ℝ := fun i j => if i = j then 0 else 1

def signed : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = 0 then (if j = 0 then 2 else 1) else (if j = 0 then -1 else 0)

def scaled : Matrix (Fin 2) (Fin 2) ℝ := fun i j => if i = j then 2 else 0

noncomputable def half : Matrix (Fin 2) (Fin 2) ℝ := fun _ _ => 1 / 2

-- A determinant of minus one tests the absolute value and row/column orientation.
example : swap.det = -1 := by norm_num [Matrix.det_fin_two, swap]
example : ∃ σ : Equiv.Perm (Fin 2), ∀ i j, swap i j = if i = σ j then 1 else 0 := by
  apply exact_permutation
  · intro i j; simp only [swap]; split <;> norm_num
  · intro j; fin_cases j <;> norm_num [swap, Fin.sum_univ_succ]
  · norm_num [Matrix.det_fin_two, swap]

-- The stated smallness boundary is admitted by the actual theorem.
example (W : Matrix (Fin 2) (Fin 2) ℝ) (hn : ∀ i j, 0 ≤ W i j)
    (hs : ∀ j, ∑ i, W i j = 1) (hd : 7 / 8 ≤ |W.det|) :
    ∃ σ : Equiv.Perm (Fin 2), ∀ j,
      3 / 4 ≤ W (σ j) j ∧ (∑ i, |W i j - if i = σ j then 1 else 0|) ≤ 1 / 2 := by
  convert near_permutation W hn hs (1 / 8) (by norm_num) (by norm_num) (by linarith) using 1; norm_num

-- The empty and singleton finite types are both included without hidden cardinality assumptions.
example (W : Matrix (Fin 0) (Fin 0) ℝ) :
    ∃ σ : Equiv.Perm (Fin 0), ∀ i j, W i j = if i = σ j then 1 else 0 := by
  refine ⟨Equiv.refl _, ?_⟩
  intro i; exact Fin.elim0 i
example (W : Matrix (Fin 1) (Fin 1) ℝ) (hn : ∀ i j, 0 ≤ W i j)
    (hs : ∀ j, ∑ i, W i j = 1) (hd : 1 ≤ |W.det|) :
    ∃ σ : Equiv.Perm (Fin 1), ∀ i j, W i j = if i = σ j then 1 else 0 :=
  exact_permutation W hn hs hd

-- These are kernel-checked counterexamples to dropping mathematical assumptions.
example : (∀ j, ∑ i, signed i j = 1) ∧ 1 ≤ |signed.det| := by
  constructor
  · intro j; fin_cases j <;> norm_num [signed, Fin.sum_univ_succ]
  · norm_num [Matrix.det_fin_two, signed]
example : (∀ i j, 0 ≤ scaled i j) ∧ 1 ≤ |scaled.det| := by
  constructor
  · intro i j; simp only [scaled]; split <;> norm_num
  · norm_num [Matrix.det_fin_two, scaled]
example : (∀ i j, 0 ≤ half i j) ∧ (∀ j, ∑ i, half i j = 1) := by
  constructor
  · intro i j; norm_num [half]
  · intro j; change (∑ _ : Fin 2, (1 / 2 : ℝ)) = 1; norm_num

private theorem impossible_entry (W : Matrix (Fin 2) (Fin 2) ℝ)
    (h : W 0 0 ≠ 0 ∧ W 0 0 ≠ 1) :
    ¬ ∃ σ : Equiv.Perm (Fin 2), ∀ i j, W i j = if i = σ j then 1 else 0 := by
  rintro ⟨σ, hσ⟩
  have he := hσ 0 0
  by_cases hs : (0 : Fin 2) = σ 0
  · simp only [ite_eq_left hs] at he
    exact h.2 he
  · simp only [ite_eq_right hs] at he
    exact h.1 he

example : ¬ ∃ σ : Equiv.Perm (Fin 2), ∀ i j, signed i j = if i = σ j then 1 else 0 :=
  impossible_entry signed (by norm_num [signed])
example : ¬ ∃ σ : Equiv.Perm (Fin 2), ∀ i j, scaled i j = if i = σ j then 1 else 0 :=
  impossible_entry scaled (by norm_num [scaled])
example : ¬ ∃ σ : Equiv.Perm (Fin 2), ∀ i j, half i j = if i = σ j then 1 else 0 :=
  impossible_entry half (by norm_num [half])

end StochasticChecks
