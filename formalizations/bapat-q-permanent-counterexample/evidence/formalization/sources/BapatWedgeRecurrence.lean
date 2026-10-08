import BapatRankTwoIdentity
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false

open scoped BigOperators Nat
open Polynomial Finset

namespace BapatRankTwo

noncomputable section

def linearFactor (a b : ℕ → ℂ) (i : ℕ) : ℂ[X] := C (a i) + C (b i) * X

def natF (a b : ℕ → ℂ) (n : ℕ) : ℂ[X] :=
  ∏ i ∈ range n, linearFactor a b i

def natRemaining (a b : ℕ → ℂ) (n i j : ℕ) : ℂ[X] :=
  ∏ k ∈ range n, if k = i ∨ k = j then 1 else linearFactor a b k

def natSingleRemaining (a b : ℕ → ℂ) (n i : ℕ) : ℂ[X] :=
  ∏ k ∈ range n, if k = i then 1 else linearFactor a b k

def natS (a b : ℕ → ℂ) (n : ℕ) : ℂ[X] :=
  ∑ i ∈ range n, ∑ j ∈ range n, if i < j then
    C (a i * b j - b i * a j) * natRemaining a b n i j else 0

theorem prod_erase_as_ite {ι M : Type*} [DecidableEq ι] [CommMonoid M]
    (s : Finset ι) (f : ι → M) (i : ι) :
    (∏ k ∈ s.erase i, f k) = ∏ k ∈ s, if k = i then 1 else f k := by
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul]
  apply Finset.prod_congr
  · ext k
    simp [and_comm]
  · intro k _
    rfl

theorem prod_erase_two_as_ite {ι M : Type*} [DecidableEq ι] [CommMonoid M]
    (s : Finset ι) (f : ι → M) (i j : ι) :
    (∏ k ∈ (s.erase i).erase j, f k) =
      ∏ k ∈ s, if k = i ∨ k = j then 1 else f k := by
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul]
  apply Finset.prod_congr
  · ext k
    simp [not_or, and_assoc, and_left_comm, and_comm]
  · intro k _
    rfl

theorem natSingleRemaining_eq_erase (a b : ℕ → ℂ) (n i : ℕ) :
    natSingleRemaining a b n i =
      ∏ k ∈ (range n).erase i, linearFactor a b k :=
  (prod_erase_as_ite _ _ _).symm

theorem natF_zero (a b : ℕ → ℂ) : natF a b 0 = 1 := by simp [natF]

theorem natF_succ (a b : ℕ → ℂ) (n : ℕ) :
    natF a b (n + 1) = linearFactor a b n * natF a b n := by
  simp [natF, Finset.prod_range_succ, mul_comm]

theorem natS_zero (a b : ℕ → ℂ) : natS a b 0 = 0 := by simp [natS]

theorem natF_derivative (a b : ℕ → ℂ) (n : ℕ) :
    (natF a b n).derivative =
      ∑ i ∈ range n, C (b i) * natSingleRemaining a b n i := by
  unfold natF
  rw [Polynomial.derivative_prod_finset]
  apply Finset.sum_congr rfl
  intro i _
  rw [natSingleRemaining_eq_erase]
  simp only [linearFactor, derivative_add, derivative_C, derivative_mul,
    derivative_X, zero_add, add_zero, zero_mul, mul_zero, mul_one]
  ring

theorem natF_euler (a b : ℕ → ℂ) (n : ℕ) :
    (∑ i ∈ range n, C (a i) * natSingleRemaining a b n i) =
      C (n : ℂ) * natF a b n - X * (natF a b n).derivative := by
  have ht :
      (∑ i ∈ range n, (C (a i) * natSingleRemaining a b n i +
        X * (C (b i) * natSingleRemaining a b n i))) =
      ∑ _i ∈ range n, natF a b n := by
    apply Finset.sum_congr rfl
    intro i hi
    calc
      _ = linearFactor a b i * natSingleRemaining a b n i := by
        unfold linearFactor
        ring
      _ = natF a b n := by
        rw [natSingleRemaining_eq_erase]
        exact Finset.mul_prod_erase _ _ hi
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul] at ht
  rw [← natF_derivative] at ht
  simp only [map_natCast]
  linear_combination ht

theorem natRemaining_succ_old (a b : ℕ → ℂ) {n i j : ℕ}
    (hi : i < n) (hj : j < n) :
    natRemaining a b (n + 1) i j =
      linearFactor a b n * natRemaining a b n i j := by
  simp [natRemaining, Finset.prod_range_succ, ne_of_gt hi, ne_of_gt hj, mul_comm]

theorem natRemaining_succ_last (a b : ℕ → ℂ) (n i : ℕ) :
    natRemaining a b (n + 1) i n = natSingleRemaining a b n i := by
  simp only [natRemaining, Finset.prod_range_succ, eq_self_iff_true, or_true,
    if_true, mul_one, natSingleRemaining]
  apply Finset.prod_congr rfl
  intro k hk
  have hkn : k ≠ n := ne_of_lt (Finset.mem_range.mp hk)
  simp [hkn]

theorem natS_succ_split (a b : ℕ → ℂ) (n : ℕ) :
    natS a b (n + 1) = linearFactor a b n * natS a b n +
      ∑ i ∈ range n, C (a i * b n - b i * a n) * natSingleRemaining a b n i := by
  unfold natS
  rw [Finset.sum_range_succ]
  have hz : (∑ j ∈ range (n + 1), if n < j then
      C (a n * b j - b n * a j) * natRemaining a b (n + 1) n j else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjn : ¬ n < j := by have := Finset.mem_range.mp hj; omega
    simp [hjn]
  rw [hz, add_zero]
  simp_rw [Finset.sum_range_succ]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i < j
    · simp only [hij, if_true]
      rw [natRemaining_succ_old a b (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)]
      ring
    · simp [hij]
  · apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range.mp hi, if_true, natRemaining_succ_last]

theorem natS_succ (a b : ℕ → ℂ) (n : ℕ) :
    natS a b (n + 1) = linearFactor a b n * natS a b n +
      C (b n) * (C (n : ℂ) * natF a b n - X * (natF a b n).derivative) -
        C (a n) * (natF a b n).derivative := by
  rw [natS_succ_split, ← natF_euler, natF_derivative]
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [add_sub_assoc, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_sub, map_mul]
  ring

noncomputable def FSeq (a b : ℕ → ℂ) : ℕ → ℂ[X]
  | 0 => 1
  | n + 1 => linearFactor a b n * FSeq a b n

noncomputable def SSeq (a b : ℕ → ℂ) : ℕ → ℂ[X]
  | 0 => 0
  | n + 1 => linearFactor a b n * SSeq a b n +
      C (b n) * (C (n : ℂ) * FSeq a b n - X * (FSeq a b n).derivative) -
        C (a n) * (FSeq a b n).derivative

theorem FSeq_eq_natF (a b : ℕ → ℂ) (n : ℕ) : FSeq a b n = natF a b n := by
  induction n with
  | zero => simp [FSeq, natF_zero]
  | succ n ih => rw [FSeq, ih, natF_succ]

theorem SSeq_eq_natS (a b : ℕ → ℂ) (n : ℕ) : SSeq a b n = natS a b n := by
  induction n with
  | zero => simp [SSeq, natS_zero]
  | succ n ih => rw [SSeq, ih, FSeq_eq_natF, natS_succ]

theorem twoColorProduct_fin_eq_natF (a b : ℕ → ℂ) (n : ℕ) :
    BapatFischer.twoColorProduct (fun i : Fin n => a i.val) (fun i : Fin n => b i.val) =
      natF a b n := by
  unfold BapatFischer.twoColorProduct natF
  exact Fin.prod_univ_eq_prod_range (linearFactor a b) n

theorem remainingPolynomial_fin_eq_natRemaining (a b : ℕ → ℂ) (n : ℕ) (i j : Fin n) :
    remainingPolynomial (fun k : Fin n => a k.val) (fun k : Fin n => b k.val) i j =
      natRemaining a b n i.val j.val := by
  rw [remainingPolynomial_eq_erased_product, prod_erase_two_as_ite]
  unfold natRemaining
  rw [← Fin.prod_univ_eq_prod_range]
  apply Finset.prod_congr rfl
  intro k _
  simp only [Fin.ext_iff, linearFactor]

theorem wedgePolynomial_fin_eq_natS (a b : ℕ → ℂ) (n : ℕ) :
    wedgePolynomial (fun i : Fin n => a i.val) (fun i : Fin n => b i.val) = natS a b n := by
  unfold wedgePolynomial MarkedInversions.originalPairs
  rw [Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]
  simp only [wedge, remainingPolynomial_fin_eq_natRemaining]
  change (∑ i : Fin n, ∑ j : Fin n, if i.val < j.val then
    C (a i.val * b j.val - b i.val * a j.val) * natRemaining a b n i.val j.val else 0) = _
  calc
    _ = ∑ i : Fin n, ∑ j ∈ range n, if i.val < j then
        C (a i.val * b j - b i.val * a j) * natRemaining a b n i.val j else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      exact Fin.sum_univ_eq_sum_range (fun j : ℕ => if i.val < j then
        C (a i.val * b j - b i.val * a j) * natRemaining a b n i.val j else 0) n
    _ = natS a b n :=
      Fin.sum_univ_eq_sum_range (fun i : ℕ => ∑ j ∈ range n, if i < j then
        C (a i * b j - b i * a j) * natRemaining a b n i j else 0) n

theorem FSeq_eq_twoColorProduct (a b : ℕ → ℂ) (n : ℕ) :
    FSeq a b n =
      BapatFischer.twoColorProduct (fun i : Fin n => a i.val) (fun i : Fin n => b i.val) := by
  rw [FSeq_eq_natF, twoColorProduct_fin_eq_natF]

theorem SSeq_eq_wedgePolynomial (a b : ℕ → ℂ) (n : ℕ) :
    SSeq a b n = wedgePolynomial (fun i : Fin n => a i.val) (fun i : Fin n => b i.val) := by
  rw [SSeq_eq_natS, wedgePolynomial_fin_eq_natS]

end

end BapatRankTwo
