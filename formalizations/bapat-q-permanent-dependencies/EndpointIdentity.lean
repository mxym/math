import Mathlib.Tactic.Ring
import QDefinitions
import MinorPermanent

open scoped BigOperators
open Finset
namespace Bapat

 theorem row_inversion_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    {i j : Fin n} (hij : i < j) :
    (∑ σ : Equiv.Perm (Fin n), if σ j < σ i then permutationWeight A σ else 0) =
      ∑ k : Fin n, ∑ l : Fin n,
        if k < l then A i l * A j k * minorPermanent A i j k l else 0 := by
  calc
    _ = ∑ σ : Equiv.Perm (Fin n), ∑ k : Fin n, ∑ l : Fin n,
        if k < l then
          if σ i = l ∧ σ j = k then permutationWeight A σ else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro σ hσ
      have ht (k l : Fin n) :
          (if k < l then
            if σ i = l ∧ σ j = k then permutationWeight A σ else 0 else 0) =
          if σ j = k then if σ i = l then
            if k < l then permutationWeight A σ else 0 else 0 else 0 := by
        by_cases h1 : k < l <;> by_cases h2 : σ i = l <;>
          by_cases h3 : σ j = k <;> simp [h1,h2,h3]
      simp_rw [ht]
      simp
    _ = ∑ k : Fin n, ∑ l : Fin n, ∑ σ : Equiv.Perm (Fin n),
        if k < l then
          if σ i = l ∧ σ j = k then permutationWeight A σ else 0 else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      by_cases hkl : k < l
      · simp only [hkl, ite_true]
        simp only [permutationWeight]
        rw [prescribed_sum_ite A (ne_of_lt hij) (ne_of_gt hkl)]
        rw [minorPermanent_swap_cols]
      · simp [hkl]

/-- The exact two-row/two-column deleted-minor formula for the endpoint derivative. -/
 theorem endpointDerivative_minor_formula {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    endpointDerivative A = ∑ i : Fin n, ∑ j : Fin n,
      if i < j then ∑ k : Fin n, ∑ l : Fin n,
        if k < l then A i l * A j k * minorPermanent A i j k l else 0 else 0 := by
  rw [endpointDerivative_pairs]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i < j
  · simp only [hij, ite_true]
    exact row_inversion_sum A hij
  · simp [hij]

end Bapat

namespace Bapat
 theorem sum_distinct_pairs {n : ℕ} (f : Fin n → Fin n → ℂ) :
    (∑ k : Fin n, ∑ l : Fin n, if k ≠ l then f k l else 0) =
      ∑ k : Fin n, ∑ l : Fin n, if k < l then f k l + f l k else 0 := by
  have hs (k l : Fin n) :
      (if k ≠ l then f k l else 0) =
        (if k < l then f k l else 0) + (if l < k then f k l else 0) := by
    rcases lt_trichotomy k l with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge (le_of_lt h)]
    · subst l; simp
    · simp [h, ne_of_gt h, not_lt_of_ge (le_of_lt h)]
  simp_rw [hs, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun k l : Fin n => if l < k then f k l else 0)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases h : k < l <;> simp [h]

 theorem permanent_two_rows {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    {i j : Fin n} (hij : i ≠ j) :
    A.permanent = ∑ k : Fin n, ∑ l : Fin n, if k < l then
      (A i k * A j l + A i l * A j k) * minorPermanent A i j k l else 0 := by
  have hweight : A.permanent = ∑ σ : Equiv.Perm (Fin n), permutationWeight A σ := by
    rw [← qPermanent_one]
    simp [qPermanent]
  rw [hweight]
  calc
    _ = ∑ σ : Equiv.Perm (Fin n), ∑ k : Fin n, ∑ l : Fin n,
        if σ i = k ∧ σ j = l then permutationWeight A σ else 0 := by
      apply Finset.sum_congr rfl
      intro σ hσ
      simp [ite_and]
    _ = ∑ k : Fin n, ∑ l : Fin n, ∑ σ : Equiv.Perm (Fin n),
        if σ i = k ∧ σ j = l then permutationWeight A σ else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]
    _ = ∑ k : Fin n, ∑ l : Fin n, if k ≠ l then
        A i k * A j l * minorPermanent A i j k l else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      by_cases hkl : k ≠ l
      · change (∑ σ : Equiv.Perm (Fin n),
          if σ i = k ∧ σ j = l then ∏ r : Fin n, A r (σ r) else 0) =
          if k ≠ l then A i k * A j l * minorPermanent A i j k l else 0
        rw [ite_eq_left hkl]
        exact prescribed_sum_ite A hij hkl
      · have heq : k = l := not_ne_iff.mp hkl
        subst l
        have hnone (σ : Equiv.Perm (Fin n)) : ¬(σ i = k ∧ σ j = k) := by
          intro h; exact hij (σ.injective (h.1.trans h.2.symm))
        simp [hnone]
    _ = _ := by
      rw [sum_distinct_pairs]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      by_cases hkl : k < l
      · simp only [hkl, ite_true]
        rw [minorPermanent_swap_cols]
        ring
      · simp [hkl]
end Bapat
