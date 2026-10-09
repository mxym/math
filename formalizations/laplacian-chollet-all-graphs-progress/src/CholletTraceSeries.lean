import CholletTraceContraction

/-! Exact finite trace-series estimate, retaining the constants of the
general graph argument. This bounds genuine matrix powers at all orders. -/
set_option autoImplicit false
open scoped BigOperators
namespace Chollet
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section

lemma half_geometric_sum (N : ℕ) :
    (∑ k ∈ Finset.range N,(1/2:ℝ)^k) = 2*(1-(1/2:ℝ)^N) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ,ih,pow_succ]; ring

lemma half_geometric_tail (N : ℕ) :
    (∑ k ∈ Finset.range N,(1/2:ℝ)^(k+2)) ≤ 1/2 := by
  simp_rw [pow_add]
  rw [← Finset.sum_mul,half_geometric_sum]
  have hp : 0 ≤ (1/2:ℝ)^N := by positivity
  nlinarith

lemma finite_half_trace_coefficients (N : ℕ) :
    (∑ k ∈ Finset.range N,(1/2:ℝ)^k/(k+2:ℕ)) ≤ 19/24 := by
  cases N with
  | zero => norm_num
  | succ N =>
    cases N with
    | zero => norm_num [Finset.sum_range_succ]
    | succ N =>
      rw [show N+1+1=2+N by omega,Finset.sum_range_add]
      have ht : (∑ k ∈ Finset.range N,(1/2:ℝ)^(2+k)/(2+k+2:ℕ)) ≤ 1/8 := by
        calc
          _ ≤ ∑ k ∈ Finset.range N,(1/4:ℝ)*(1/2:ℝ)^(k+2) := by
            apply Finset.sum_le_sum
            intro k _
            have hd : (4:ℝ) ≤ ((2+k+2:ℕ):ℝ) := by exact_mod_cast (show 4 ≤ 2+k+2 by omega)
            have hp : 0 ≤ (1/2:ℝ)^(k+2) := by positivity
            rw [show 2+k=k+2 by omega]
            have h := div_le_div_of_nonneg_left hp (by norm_num : (0:ℝ)<4) hd
            convert h using 1 <;> ring
          _ = (1/4:ℝ)*(∑ k ∈ Finset.range N,(1/2:ℝ)^(k+2)) := by rw [Finset.mul_sum]
          _ ≤ (1/4:ℝ)*(1/2) := mul_le_mul_of_nonneg_left (half_geometric_tail N) (by norm_num)
          _ = _ := by norm_num
      norm_num [Finset.sum_range_succ] at *
      linarith

/-- The finite version of Σ_{k≥2} tr(C^k)/k ≤ (19/24) tr(C²),
with no infinite summation or unchecked eigenvalue estimate. -/
theorem finite_trace_series_upper (C : Matrix V V ℝ)
    (hc : ∀ i j,0 ≤ C i j) (hs : ∀ i j,C i j=C j i)
    (hrow : ∀ i,(∑ j,C i j) ≤ 1/2) (N : ℕ) :
    (∑ k ∈ Finset.range N,(C^(k+2)).trace/(k+2:ℕ)) ≤
      (19/24:ℝ)*(C^2).trace := by
  have htrace : 0 ≤ (C^2).trace := by
    rw [trace_square_eq_frobeniusSquare C hs]
    exact frobeniusSquare_nonneg C
  calc
    _ ≤ ∑ k ∈ Finset.range N,((1/2:ℝ)^k/(k+2:ℕ))*(C^2).trace := by
      apply Finset.sum_le_sum
      intro k _
      have h := div_le_div_of_nonneg_right
        (trace_pow_le_row_sum C (1/2) (by norm_num) hc hs hrow k)
        (show (0:ℝ) ≤ (k+2:ℕ) by positivity)
      convert h using 1 <;> ring
    _ = (∑ k ∈ Finset.range N,(1/2:ℝ)^k/(k+2:ℕ))*(C^2).trace := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (finite_half_trace_coefficients N) htrace

end
end Chollet
