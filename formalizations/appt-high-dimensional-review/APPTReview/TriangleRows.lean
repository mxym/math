import APPTReview.PairGraph
import Mathlib.Order.Interval.Finset.Fin

open scoped BigOperators
open Matrix
namespace APPTReview

def RowMajorAntitone {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  ∀ i j k l, i<j → k<l → i.val*m+j.val ≤ k.val*m+l.val → A k l ≤ A i j

def rowEnergy {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (i : Fin m) : ℝ :=
  ∑ j ∈ Finset.Ioi i, (A i j)^2

theorem sum_except_real {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (c : ℝ) :
    (∑ j, if j=i then 0 else c) = ((Fintype.card ι : ℝ)-1)*c := by
  calc
    _ = (∑ _j : ι, c)-∑ j, if j=i then c else 0 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp
    _ = _ := by simp; ring

/-- Every non-diagonal entry in a row dominates that row's last entry. -/
theorem row_reference_le {h : ℕ} (A : Matrix (Fin (h+1)) (Fin (h+1)) ℝ)
    (hsym : ∀ i j, A i j=A j i) (hord : RowMajorAntitone A)
    (i : Fin h) (j : Fin (h+1)) (hj : j≠i.castSucc) :
    A i.castSucc (Fin.last h) ≤ A i.castSucc j := by
  have hil : i.castSucc < Fin.last h := by change i.val<h; exact i.isLt
  by_cases hij : i.castSucc < j
  · apply hord i.castSucc j i.castSucc (Fin.last h) hij hil
    change i.val*(h+1)+j.val ≤ i.val*(h+1)+h
    have hjb := j.isLt
    omega
  · have hji : j < i.castSucc := lt_of_le_of_ne (le_of_not_gt hij) hj
    rw [hsym i.castSucc j]
    apply hord j i.castSucc i.castSucc (Fin.last h) hji hil
    change j.val*(h+1)+i.val ≤ i.val*(h+1)+h
    have hjv : j.val < i.val := hji
    have hib := i.isLt
    nlinarith

theorem reference_degree_bound {h : ℕ} (A : Matrix (Fin (h+1)) (Fin (h+1)) ℝ)
    (hn : ∀ i j, 0≤A i j) (hsym : ∀ i j, A i j=A j i)
    (hord : RowMajorAntitone A) (i : Fin h) :
    (h : ℝ)*A i.castSucc (Fin.last h) ≤ ∑ j, A i.castSucc j := by
  calc
    _ = ∑ j : Fin (h+1), if j=i.castSucc then 0 else A i.castSucc (Fin.last h) := by
      rw [sum_except_real]
      simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      split_ifs with hj
      · exact hn _ _
      · exact row_reference_le A hsym hord i j hj

theorem next_row_energy_bound {h : ℕ} (A : Matrix (Fin (h+1)) (Fin (h+1)) ℝ)
    (hn : ∀ i j, 0≤A i j) (hord : RowMajorAntitone A) (i : Fin h) :
    rowEnergy A i.succ ≤ ((h-(i.val+1) : ℕ) : ℝ)*(A i.castSucc (Fin.last h))^2 := by
  have href : i.castSucc < Fin.last h := by change i.val<h; exact i.isLt
  have hsum : rowEnergy A i.succ ≤ ∑ _j ∈ Finset.Ioi i.succ,
      (A i.castSucc (Fin.last h))^2 := by
    apply Finset.sum_le_sum
    intro j hj
    have hij : i.succ<j := Finset.mem_Ioi.mp hj
    have hb : A i.succ j ≤ A i.castSucc (Fin.last h) := by
      apply hord i.castSucc (Fin.last h) i.succ j href hij
      change i.val*(h+1)+h ≤ (i.val+1)*(h+1)+j.val
      nlinarith
    exact pow_le_pow_left₀ (hn _ _) hb 2
  simpa [Fin.card_Ioi, Fin.val_succ] using hsum

theorem next_row_degree_square {h : ℕ} (A : Matrix (Fin (h+1)) (Fin (h+1)) ℝ)
    (hn : ∀ i j, 0≤A i j) (hsym : ∀ i j, A i j=A j i)
    (hord : RowMajorAntitone A) (i : Fin h) :
    ((h+1 : ℕ) : ℝ)*rowEnergy A i.succ ≤ (∑ j, A i.castSucc j)^2 := by
  have he := next_row_energy_bound A hn hord i
  have hd := reference_degree_bound A hn hsym hord i
  have hnat : (h+1)*(h-(i.val+1)) ≤ h^2 := by
    have hi := i.isLt
    have hsub : h-(i.val+1)+(i.val+1)=h := Nat.sub_add_cancel (by omega)
    nlinarith
  have hreal : ((h+1 : ℕ) : ℝ)*((h-(i.val+1) : ℕ) : ℝ) ≤ (h : ℝ)^2 := by
    exact_mod_cast hnat
  calc
    _ ≤ ((h+1 : ℕ) : ℝ)*(((h-(i.val+1) : ℕ) : ℝ)*(A i.castSucc (Fin.last h))^2) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = (((h+1 : ℕ) : ℝ)*((h-(i.val+1) : ℕ) : ℝ))*(A i.castSucc (Fin.last h))^2 := by ring
    _ ≤ (h : ℝ)^2*(A i.castSucc (Fin.last h))^2 :=
      mul_le_mul_of_nonneg_right hreal (sq_nonneg _)
    _ = ((h : ℝ)*A i.castSucc (Fin.last h))^2 := by ring
    _ ≤ _ := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (hn _ _)) hd 2

/-- The exact triangular degree inequality for every row-major ordered nonnegative matrix. -/
theorem triangular_degree_square {h : ℕ} (A : Matrix (Fin (h+1)) (Fin (h+1)) ℝ)
    (hn : ∀ i j, 0≤A i j) (hsym : ∀ i j, A i j=A j i)
    (hord : RowMajorAntitone A) :
    ((h+1 : ℕ) : ℝ)*(∑ i : Fin h, rowEnergy A i.succ) ≤
      ∑ i, (∑ j, A i j)^2 := by
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ i : Fin h, (∑ j, A i.castSucc j)^2 :=
      Finset.sum_le_sum (fun i _ => next_row_degree_square A hn hsym hord i)
    _ ≤ _ := by
      rw [Fin.sum_univ_castSucc]
      exact le_add_of_nonneg_right (sq_nonneg _)

end APPTReview
