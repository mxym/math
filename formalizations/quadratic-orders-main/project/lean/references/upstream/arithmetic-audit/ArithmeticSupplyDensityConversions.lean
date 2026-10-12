import ArithmeticSupplyPNT

/-! Analytic conversion lemmas. The count function and its natural density
are explicit inputs; these results do not assert a splitting density. -/
set_option autoImplicit false
open scoped Topology
open Filter

namespace Entry002

theorem arithmeticSupply_normalized_count_of_relative_density
    (F : ℝ → ℝ) (ρ : ℝ)
    (hF : Tendsto (fun x => F x / (Nat.primeCounting ⌊x⌋₊ : ℝ)) atTop (nhds ρ)) :
    Tendsto (fun x => F x / (x / Real.log x)) atTop (nhds ρ) := by
  have h := hF.mul arithmeticSupply_prime_counting_ratio_tendsto
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hxnat : 2 ≤ ⌊x⌋₊ := Nat.le_floor hx
  have hcount : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≠ 0 := by
    exact_mod_cast (show Nat.primeCounting ⌊x⌋₊ ≠ 0 from
      fun hzero => by have := Nat.primeCounting_eq_zero_iff.mp hzero; omega)
  field_simp

theorem arithmeticSupply_dyadic_normalizer_ratio :
    Tendsto (fun x : ℝ => ((2*x) / Real.log (2*x)) / (x / Real.log x))
      atTop (nhds 2) := by
  have hsmall : Tendsto (fun x : ℝ => Real.log 2 / Real.log x) atTop (nhds 0) :=
    Real.isLittleO_const_log_atTop.tendsto_div_nhds_zero
  have h := ((tendsto_const_nhds.add hsmall).inv₀
    (by norm_num : (1 : ℝ) + 0 ≠ 0)).const_mul 2
  norm_num only [add_zero, inv_one, mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hlog2 : Real.log (2*x) ≠ 0 :=
    (Real.log_pos (by linarith : (1 : ℝ) < 2*x)).ne'
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx0] at hlog2 ⊢
  have hrew : 1 + Real.log 2 / Real.log x =
      (Real.log 2 + Real.log x) / Real.log x := by
    rw [add_div, div_self hlog, add_comm]
  rw [hrew, inv_div]
  field_simp [hlog2]

theorem arithmeticSupply_dyadic_difference_ratio_tendsto
    (F : ℝ → ℝ) (ρ : ℝ)
    (hF : Tendsto (fun x => F x / (x / Real.log x)) atTop (nhds ρ)) :
    Tendsto (fun x => (F (2*x) - F x) / (x / Real.log x)) atTop (nhds ρ) := by
  have htwice := hF.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have h := (htwice.mul arithmeticSupply_dyadic_normalizer_ratio).sub hF
  have hlim : ρ * 2 - ρ = ρ := by ring
  rw [hlim] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hlog2 : Real.log (2*x) ≠ 0 :=
    (Real.log_pos (by linarith : (1 : ℝ) < 2*x)).ne'
  dsimp only [Function.comp_def, id]
  field_simp

end Entry002
