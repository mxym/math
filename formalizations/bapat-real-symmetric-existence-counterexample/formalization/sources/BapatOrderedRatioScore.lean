import BapatEmpiricalRatioGap
import Mathlib.Data.Fin.Tuple.Sort

set_option autoImplicit false
open BapatFiniteRank BapatRankTwo.MarkedInversions

namespace BapatRealExistence
noncomputable section

def realPairScore {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ p ∈ originalPairs (ι := Fin n), |x p.2-x p.1|

theorem realPairScore_nonneg {n : ℕ} (x : Fin n → ℝ) : 0≤realPairScore x := by
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem realPairScore_double {n : ℕ} (x : Fin n → ℝ) :
    (∑ i, ∑ j, |x j-x i|) = 2*realPairScore x := by
  rw [sum_pairing (fun i j => |x j-x i|) (by intro i; simp)]
  unfold realPairScore
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [abs_sub_comm (x p.1) (x p.2)]
  ring

theorem realPairScore_perm {n : ℕ} (x : Fin n → ℝ) (e : Equiv.Perm (Fin n)) :
    realPairScore (x ∘ e)=realPairScore x := by
  have h : (∑ i, ∑ j, |x (e j)-x (e i)|) = ∑ i, ∑ j, |x j-x i| := by
    calc
      _ = ∑ i, ∑ j, |x j-x (e i)| := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Equiv.sum_comp e (fun j => |x j-x (e i)|)
      _ = _ := Equiv.sum_comp e (fun i => ∑ j, |x j-x i|)
  have h₁ := realPairScore_double (x ∘ e)
  have h₂ := realPairScore_double x
  dsimp only [Function.comp_def] at h₁
  change realPairScore (fun i => x (e i))=realPairScore x
  linarith

theorem realPairScore_append_le {n m : ℕ} (x : Fin n → ℝ) (y : Fin m → ℝ) :
    realPairScore x≤realPairScore (Fin.append x y) := by
  have h : (∑ i : Fin n, ∑ j : Fin n, |x j-x i|) ≤
      ∑ i : Fin (n+m), ∑ j : Fin (n+m), |Fin.append x y j-Fin.append x y i| := by
    simp_rw [Fin.sum_univ_add]
    simp only [Fin.append_left,Fin.append_right,Finset.sum_add_distrib]
    have h₁ : 0≤∑ i : Fin n, ∑ j : Fin m, |y j-x i| := by positivity
    have h₂ : 0≤∑ i : Fin m, ∑ j : Fin n, |x j-y i| := by positivity
    have h₃ : 0≤∑ i : Fin m, ∑ j : Fin m, |y j-y i| := by positivity
    linarith
  rw [realPairScore_double,realPairScore_double] at h
  linarith

/-- The sorted real part of the complex ratio difference sum equals the score. -/
theorem sorted_ratio_difference_re {n : ℕ} (z : Fin n → ℂ)
    (hz : Monotone (fun i => (z i).re)) :
    (∑ p ∈ originalPairs (ι := Fin n), (z p.2-z p.1)).re = realPairScore (fun i => (z i).re) := by
  simp only [Complex.re_sum,Complex.sub_re,realPairScore]
  apply Finset.sum_congr rfl
  intro p hp
  have h := (Finset.mem_filter.mp hp).2
  rw [abs_of_nonneg (sub_nonneg.mpr (hz h.le))]

theorem empirical_pair_sum {K : Type*} (u : ℕ → K) {n : ℕ} (hn : n≠0) (f : K → ℝ) :
    (n:ℝ)^2*empiricalAverage u n (fun x => empiricalAverage u n (fun y => |f y-f x|)) =
      2*realPairScore (fun i : Fin n => f (u i.val)) := by
  rw [← realPairScore_double]
  have hi (i : ℕ) := Fin.sum_univ_eq_sum_range (fun j => |f (u j)-f (u i)|) n
  simp_rw [hi]
  rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ Finset.range n, |f (u j)-f (u i)|) n]
  unfold empiricalAverage
  simp_rw [Finset.mul_sum]
  have hn' : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr hn
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  field_simp

end
end BapatRealExistence
