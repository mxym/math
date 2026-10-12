import CholletNoncycleBlock

/-! Removing the vanishing third trace improves the coefficient to 5/8.
This will close the remaining degree-two blocks without enumerating cycles. -/
set_option autoImplicit false
open scoped BigOperators
namespace Chollet
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section

lemma half_trace_tail_coefficients (N : ℕ) :
    (∑ k ∈ Finset.range N,(1/2 : ℝ)^(k+2)/(k+4 : ℕ)) ≤ 1/8 := by
  calc
    _ ≤ ∑ k ∈ Finset.range N,(1/4 : ℝ)*(1/2 : ℝ)^(k+2) := by
      apply Finset.sum_le_sum
      intro k _
      have hd : (4 : ℝ) ≤ (k+4 : ℕ) := by exact_mod_cast (show 4 ≤ k+4 by omega)
      have hp : 0 ≤ (1/2 : ℝ)^(k+2) := by positivity
      have h := div_le_div_of_nonneg_left hp (by norm_num : (0 : ℝ) < 4) hd
      convert h using 1 <;> ring
    _ = (1/4 : ℝ)*(∑ k ∈ Finset.range N,(1/2 : ℝ)^(k+2)) := by rw [Finset.mul_sum]
    _ ≤ (1/4 : ℝ)*(1/2) := mul_le_mul_of_nonneg_left (half_geometric_tail N) (by norm_num)
    _ = _ := by norm_num

lemma finite_half_trace_coefficients_skip_three (N : ℕ) :
    (∑ k ∈ Finset.range N,if k=1 then 0 else (1/2 : ℝ)^k/(k+2 : ℕ)) ≤ 5/8 := by
  cases N with
  | zero => norm_num
  | succ N =>
    cases N with
    | zero => norm_num [Finset.sum_range_succ]
    | succ N =>
      rw [show N+1+1=2+N by omega,Finset.sum_range_add]
      have ht : (∑ k ∈ Finset.range N,if 2+k=1 then 0 else
          (1/2 : ℝ)^(2+k)/(2+k+2 : ℕ)) ≤ 1/8 := by
        convert half_trace_tail_coefficients N using 1
        apply Finset.sum_congr rfl
        intro k _
        simp [show 2+k ≠ 1 by omega,show 2+k=k+2 by omega,show 2+k+2=k+4 by omega] <;> ring
      norm_num [Finset.sum_range_succ] at *
      linarith

theorem finite_trace_series_upper_skip_three (C : Matrix V V ℝ)
    (hc : ∀ i j,0 ≤ C i j) (hs : ∀ i j,C i j = C j i)
    (hrow : ∀ i,(∑ j,C i j) ≤ 1/2) (hthree : (C^3).trace=0) (N : ℕ) :
    (∑ k ∈ Finset.range N,(C^(k+2)).trace/(k+2 : ℕ)) ≤
      (5/8 : ℝ)*(C^2).trace := by
  have ht : 0 ≤ (C^2).trace := by
    rw [trace_square_eq_frobeniusSquare C hs]
    exact frobeniusSquare_nonneg C
  calc
    _ ≤ ∑ k ∈ Finset.range N,
        (if k=1 then 0 else (1/2 : ℝ)^k/(k+2 : ℕ)) * (C^2).trace := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : k=1
      · subst k
        simp [hthree]
      · simp only [if_neg hk]
        have h := div_le_div_of_nonneg_right
          (trace_pow_le_row_sum C (1/2) (by norm_num) hc hs hrow k)
          (show (0 : ℝ) ≤ (k+2 : ℕ) by positivity)
        convert h using 1 <;> ring
    _ = (∑ k ∈ Finset.range N,if k=1 then 0 else (1/2 : ℝ)^k/(k+2 : ℕ)) *
        (C^2).trace := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (finite_half_trace_coefficients_skip_three N) ht

theorem log_permanent_one_add_upper_skip_three (C : Matrix V V ℝ)
    (hc : ∀ i j,0 ≤ C i j) (hs : ∀ i j,C i j = C j i)
    (hd : ∀ i,C i i = 0) (hrow : ∀ i,(∑ j,C i j) ≤ 1/2)
    (hthree : (C^3).trace=0) :
    Real.log (1+C).permanent ≤ (5/8 : ℝ)*(C^2).trace := by
  have hunit : ∀ i,(1+C) i i = 1 := by intro i; simp [hd,Matrix.add_apply]
  have hnonneg : ∀ i j,0 ≤ (1+C) i j := by
    intro i j
    simp only [Matrix.add_apply,Matrix.one_apply]
    split_ifs <;> linarith [hc i j]
  calc
    _ ≤ ∑ σ ∈ allCycles,cycleWeight (1+C) σ :=
      log_permanent_le_cycle_sum (1+C) hunit hnonneg
    _ = ∑ σ ∈ allCycles,cycleWeight C σ := by simp only [cycleWeight_one_add]
    _ ≤ ∑ k ∈ Finset.range (Fintype.card V),(C^(k+2)).trace/(k+2 : ℕ) :=
      cycle_weight_sum_le_trace_series C hc hs
    _ ≤ _ := finite_trace_series_upper_skip_three C hc hs hrow hthree _

end
end Chollet
