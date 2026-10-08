import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Data.Fintype.BigOperators

open scoped BigOperators
open Finset
namespace Bapat

/-- The actual number of inverted pairs of a permutation. -/
def inversionCount {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  ∑ i : Fin n, ∑ j : Fin n, if i < j ∧ σ j < σ i then 1 else 0

/-- The row-to-column product in the definition of the permanent. -/
def permutationWeight {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (σ : Equiv.Perm (Fin n)) : ℂ := ∏ i, A i (σ i)

/-- Bapat's inversion-weighted permanent, as an actual polynomial function. -/
def qPermanent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (q : ℂ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n), q ^ inversionCount σ * permutationWeight A σ

/-- The endpoint derivative, not a proxy for it. -/
def endpointDerivative {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n), (inversionCount σ : ℂ) * permutationWeight A σ

 theorem qPermanent_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    qPermanent A 1 = A.permanent := by
  simp only [qPermanent, one_pow, one_mul, permutationWeight]
  rw [← Matrix.permanent_transpose]
  rfl

 theorem endpointDerivative_pairs {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    endpointDerivative A = ∑ i : Fin n, ∑ j : Fin n,
      if i < j then ∑ σ : Equiv.Perm (Fin n),
        if σ j < σ i then permutationWeight A σ else 0 else 0 := by
  unfold endpointDerivative inversionCount
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i < j
  · simp [hij]
  · simp [hij]

 theorem inversionCount_inverse {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    inversionCount σ.symm = inversionCount σ := by
  unfold inversionCount
  calc
    _ = ∑ i : Fin n, ∑ j : Fin n,
        if σ i < σ j ∧ j < i then 1 else 0 := by
      rw [← Equiv.sum_comp σ]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Equiv.sum_comp σ]
      simp
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [and_comm]

end Bapat
