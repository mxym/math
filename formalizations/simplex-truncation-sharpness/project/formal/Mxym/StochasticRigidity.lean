import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The stochastic determinant conversion in the integrated simplex stability proof.
All bounds below are derived from nonnegativity, column sums and the determinant.
No geometric identity, Hadamard bound or probability estimate is assumed. -/
namespace Mxym.StochasticRigidity
open scoped BigOperators
open Finset

set_option maxHeartbeats 2000000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem injection_sum_le {α β : Type*} [Fintype α] [Fintype β]
    (e : α → β) (he : Function.Injective e) (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    (∑ a, f (e a)) ≤ ∑ b, f b := by
  classical
  rw [← Finset.sum_image (fun a _ b _ h => he h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun b _ _ => hf b)

private theorem sign_abs_real (σ : Equiv.Perm ι) :
    |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
  exact_mod_cast Equiv.Perm.sign_abs σ

/-- An elementary determinant bound by the product of column l1 norms. -/
theorem abs_det_le_column_l1_product (A : Matrix ι ι ℝ) :
    |A.det| ≤ ∏ j, ∑ i, |A i j| := by
  classical
  rw [Matrix.det_apply']
  calc
    |∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ j, A (σ j) j| ≤
        ∑ σ : Equiv.Perm ι, |((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ j, A (σ j) j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm ι, ∏ j, |A (σ j) j| := by
      simp only [abs_mul, sign_abs_real, one_mul, Finset.abs_prod]
    _ ≤ ∑ f : ι → ι, ∏ j, |A (f j) j| :=
      injection_sum_le (fun σ : Equiv.Perm ι => (σ : ι → ι))
        (fun σ τ h => Equiv.ext (congrFun h)) (fun f : ι → ι => ∏ j, |A (f j) j|)
        (fun f => Finset.prod_nonneg (fun j _ => abs_nonneg _))
    _ = ∏ j, ∑ i, |A i j| := (Fintype.prod_sum (fun (j : ι) (i : ι) => |A i j|)).symm

omit [Fintype ι] in
private theorem restriction_injective (j : ι) :
    Function.Injective (fun σ : Equiv.Perm ι => fun k : {k : ι // k ≠ j} => σ k) := by
  intro σ τ h
  apply Equiv.ext
  intro k
  by_cases hkj : k = j
  · subst k
    obtain ⟨l, hl⟩ := τ.surjective (σ j)
    by_cases hlj : l = j
    · simpa [hlj] using hl.symm
    · have hsame : σ l = τ l := congrFun h ⟨l, hlj⟩
      have : l = j := σ.injective (hsame.trans hl)
      exact (hlj this).elim
  · exact congrFun h ⟨k, hkj⟩

/-- For a nonnegative column-stochastic matrix, the determinant is bounded
by the largest entry in each chosen column. This avoids a Hadamard premise. -/
theorem abs_det_le_column_max (W : Matrix ι ι ℝ)
    (hnonneg : ∀ i j, 0 ≤ W i j) (hsum : ∀ j, ∑ i, W i j = 1)
    (j : ι) (m : ℝ) (hmax : ∀ i, W i j ≤ m) : |W.det| ≤ m := by
  classical
  have hm : 0 ≤ m := (hnonneg j j).trans (hmax j)
  have hpartial : (∑ σ : Equiv.Perm ι, ∏ k : {k : ι // k ≠ j}, W (σ k) k) ≤ 1 := by
    calc
      _ ≤ ∑ f : {k : ι // k ≠ j} → ι, ∏ k, W (f k) k :=
        injection_sum_le _ (restriction_injective j) _
          (fun f => Finset.prod_nonneg (fun k _ => hnonneg _ _))
      _ = ∏ k : {k : ι // k ≠ j}, ∑ i, W i k := (Fintype.prod_sum (fun (k : {k : ι // k ≠ j}) (i : ι) => W i k)).symm
      _ = 1 := by simp only [hsum, Finset.prod_const_one]
  rw [Matrix.det_apply']
  calc
    _ ≤ ∑ σ : Equiv.Perm ι, |((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ k, W (σ k) k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm ι, ∏ k, W (σ k) k := by
      simp only [abs_mul, sign_abs_real, one_mul, Finset.abs_prod, abs_of_nonneg (hnonneg _ _)]
    _ = ∑ σ : Equiv.Perm ι, W (σ j) j * ∏ k : {k : ι // k ≠ j}, W (σ k) k := by
      apply Finset.sum_congr rfl
      intro σ _
      exact Fintype.prod_eq_mul_prod_subtype_ne (fun k => W (σ k) k) j
    _ ≤ ∑ σ : Equiv.Perm ι, m * ∏ k : {k : ι // k ≠ j}, W (σ k) k := by
      exact Finset.sum_le_sum (fun σ _ => mul_le_mul_of_nonneg_right (hmax _)
        (Finset.prod_nonneg (fun k _ => hnonneg _ _)))
    _ = m * ∑ σ : Equiv.Perm ι, ∏ k : {k : ι // k ≠ j}, W (σ k) k := by rw [Finset.mul_sum]
    _ ≤ m * 1 := mul_le_mul_of_nonneg_left hpartial hm
    _ = m := mul_one m

/-- The exact l1 distance between a stochastic column and a coordinate vector. -/
theorem column_l1_distance (W : Matrix ι ι ℝ)
    (hnonneg : ∀ i j, 0 ≤ W i j) (hsum : ∀ j, ∑ i, W i j = 1)
    (i j : ι) :
    (∑ r, |W r j - if r = i then 1 else 0|) = 2 * (1 - W i j) := by
  have hupper : W i j ≤ 1 :=
    (Finset.single_le_sum (fun r _ => hnonneg r j) (Finset.mem_univ i)).trans_eq (hsum j)
  calc
    _ = ∑ r, (W r j + if r = i then 1 - 2 * W i j else 0) := by
      apply Finset.sum_congr rfl
      intro r _
      by_cases hri : r = i
      · subst r
        simp only [ite_true, abs_of_nonpos (sub_nonpos.mpr hupper)]
        ring
      · simp [hri, abs_of_nonneg (hnonneg r j)]
    _ = 2 * (1 - W i j) := by
      rw [Finset.sum_add_distrib, hsum]
      simp
      ring

/-- Two columns concentrated at the same row force a small determinant. -/
theorem abs_det_le_of_shared_row (W : Matrix ι ι ℝ)
    (hnonneg : ∀ i j, 0 ≤ W i j) (hsum : ∀ j, ∑ i, W i j = 1)
    (i j k : ι) (hjk : j ≠ k) (δ : ℝ)
    (hj : 1 - δ ≤ W i j) (hk : 1 - δ ≤ W i k) : |W.det| ≤ 4 * δ := by
  classical
  let D := W.updateCol j (fun r => W r j - W r k)
  have hdet : D.det = W.det := by
    simpa [D, sub_eq_add_neg] using Matrix.det_updateCol_add_smul_self W hjk (-1 : ℝ)
  have hprod : (∏ c, ∑ r, |D r c|) = ∑ r, |W r j - W r k| := by
    rw [Finset.prod_eq_single j]
    · simp [D]
    · intro c _ hc
      simpa [D, Matrix.updateCol_ne hc, abs_of_nonneg (hnonneg _ _)] using hsum c
    · simp
  have hdist : (∑ r, |W r j - W r k|) ≤ 4 * δ := by
    calc
      _ ≤ ∑ r, (|W r j - if r = i then 1 else 0| +
          |W r k - if r = i then 1 else 0|) := by
        apply Finset.sum_le_sum
        intro r _
        simpa only [abs_sub_comm (if r = i then 1 else 0) (W r k)] using
          abs_sub_le (W r j) (if r = i then 1 else 0) (W r k)
      _ = 2 * (1 - W i j) + 2 * (1 - W i k) := by
        rw [Finset.sum_add_distrib, column_l1_distance W hnonneg hsum,
          column_l1_distance W hnonneg hsum]
      _ ≤ 4 * δ := by linarith
  rw [← hdet]
  exact (abs_det_le_column_l1_product D).trans (hprod ▸ hdist)

/-- Sharp algebraic version: each matched entry is at least 1-δ, and its
column l1 distance from the matched coordinate vector is at most 2δ. -/
theorem near_permutation_sharp (W : Matrix ι ι ℝ)
    (hnonneg : ∀ i j, 0 ≤ W i j) (hsum : ∀ j, ∑ i, W i j = 1)
    (δ : ℝ) (_hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 8) (hdet : 1 - δ ≤ |W.det|) :
    ∃ σ : Equiv.Perm ι, ∀ j,
      1 - δ ≤ W (σ j) j ∧ (∑ i, |W i j - if i = σ j then 1 else 0|) ≤ 2 * δ := by
  classical
  have heach : ∀ j, ∃ i, 1 - δ ≤ W i j := by
    intro j
    obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => W i j)
      ⟨j, Finset.mem_univ j⟩
    exact ⟨i, hdet.trans (abs_det_le_column_max W hnonneg hsum j (W i j)
      (fun r => hi r (Finset.mem_univ r)))⟩
  choose f hf using heach
  have hinj : Function.Injective f := by
    intro j k hsame
    by_contra hjk
    have hsmall := abs_det_le_of_shared_row W hnonneg hsum (f j) j k hjk δ
      (hf j) (hsame ▸ hf k)
    linarith
  let σ : Equiv.Perm ι := Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩
  refine ⟨σ, fun j => ⟨hf j, ?_⟩⟩
  rw [column_l1_distance W hnonneg hsum]
  have hj : 1 - δ ≤ W (σ j) j := hf j
  linarith

/-- The constants used in the paper's prescribed-simplex conversion. -/
theorem near_permutation (W : Matrix ι ι ℝ)
    (hnonneg : ∀ i j, 0 ≤ W i j) (hsum : ∀ j, ∑ i, W i j = 1)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 8) (hdet : 1 - δ ≤ |W.det|) :
    ∃ σ : Equiv.Perm ι, ∀ j,
      1 - 2 * δ ≤ W (σ j) j ∧ (∑ i, |W i j - if i = σ j then 1 else 0|) ≤ 4 * δ := by
  obtain ⟨σ, hσ⟩ := near_permutation_sharp W hnonneg hsum δ hδ0 hδ hdet
  refine ⟨σ, fun j => ?_⟩
  obtain ⟨hentry, hdist⟩ := hσ j
  constructor <;> linarith

/-- Exact endpoint: determinant magnitude at least one forces a permutation matrix. -/
theorem exact_permutation (W : Matrix ι ι ℝ)
    (hnonneg : ∀ i j, 0 ≤ W i j) (hsum : ∀ j, ∑ i, W i j = 1)
    (hdet : 1 ≤ |W.det|) :
    ∃ σ : Equiv.Perm ι, ∀ i j, W i j = if i = σ j then 1 else 0 := by
  obtain ⟨σ, hσ⟩ := near_permutation_sharp W hnonneg hsum 0 (le_refl 0)
    (by norm_num) (by simpa using hdet)
  refine ⟨σ, fun i j => ?_⟩
  have hdist : (∑ r, |W r j - if r = σ j then 1 else 0|) ≤ 0 := by
    simpa using (hσ j).2
  have hzero : (∑ r, |W r j - if r = σ j then 1 else 0|) = 0 :=
    le_antisymm hdist (Finset.sum_nonneg (fun r _ => abs_nonneg _))
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun r _ =>
    abs_nonneg (W r j - if r = σ j then 1 else 0))).mp hzero i (Finset.mem_univ i)
  exact sub_eq_zero.mp (abs_eq_zero.mp hterm)

end Mxym.StochasticRigidity
