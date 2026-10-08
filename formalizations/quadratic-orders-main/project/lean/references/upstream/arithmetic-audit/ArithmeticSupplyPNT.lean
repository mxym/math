import PrimeNumberTheoremAnd.Wiener
import Mathlib.Analysis.SpecificLimits.Basic

/-! The actual rational PNT counting limit, adapted from OpenAI/math at
adc7f1241b42e322a6451854ab7e4b4c146bf78a, under its Apache-2.0 license.
The pinned external dependency and exact upstream compatibility patch are
compiled and audited in references/upstream/arithmetic-audit. -/

set_option autoImplicit false
noncomputable section
open scoped Topology
open Filter Asymptotics
namespace Entry002

lemma arithmeticSupply_psi_nat_ratio_tendsto :
    Tendsto (fun n : ℕ => Chebyshev.psi n/(n : ℝ)) atTop (nhds 1) := by
  have he (n : ℕ) : Chebyshev.psi n=cumsum ArithmeticFunction.vonMangoldt n+
      ArithmeticFunction.vonMangoldt n := by
    rw [Chebyshev.psi_eq_sum_Icc,Nat.floor_natCast,← Nat.range_succ_eq_Icc_zero,
      Finset.sum_range_succ]
    rfl
  have hsmall : Tendsto (fun n : ℕ => ArithmeticFunction.vonMangoldt n/(n : ℝ))
      atTop (nhds 0) := by
    apply squeeze_zero
    · intro n
      exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
    · intro n
      exact div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (Nat.cast_nonneg _)
    · exact Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have ht := WeakPNT.add hsmall
  simpa only [he,add_div,add_zero] using ht

lemma arithmeticSupply_psi_real_ratio_tendsto :
    Tendsto (fun x : ℝ => Chebyshev.psi x/x) atTop (nhds 1) := by
  have h := (arithmeticSupply_psi_nat_ratio_tendsto.comp tendsto_nat_floor_atTop).mul
    (tendsto_nat_floor_div_atTop : Tendsto (fun x : ℝ => (⌊x⌋₊ : ℝ)/x) atTop (nhds 1))
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hf : (⌊x⌋₊ : ℝ)≠0 := by
    exact_mod_cast (Nat.floor_pos.mpr hx).ne'
  have hpsi : Chebyshev.psi (⌊x⌋₊ : ℝ)=Chebyshev.psi x := by simp [Chebyshev.psi]
  dsimp only [Function.comp_def]
  rw [hpsi]
  field_simp

lemma arithmeticSupply_theta_real_ratio_tendsto :
    Tendsto (fun x : ℝ => Chebyshev.theta x/x) atTop (nhds 1) := by
  have hs : (fun x : ℝ => Real.sqrt x)=o[atTop](fun x => x) := by
    apply (isLittleO_iff_tendsto' (by filter_upwards [] with x hx; simp [hx])).mpr
    apply (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/2)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.sqrt_eq_rpow]
    calc
      x^(-(1/2 : ℝ)) = x^((1/2 : ℝ)-1) := by congr 1; norm_num
      _ = x^(1/2 : ℝ)/x^((1 : ℝ)) := Real.rpow_sub hx _ _
      _ = _ := by rw [Real.rpow_one]
  have he := (Chebyshev.isBigO_psi_sub_theta_sqrt.trans_isLittleO hs).tendsto_div_nhds_zero
  have ht := arithmeticSupply_psi_real_ratio_tendsto.sub he
  convert ht using 1
  · ext x
    simp only [Pi.sub_apply]
    ring
  · simp

lemma arithmeticSupply_prime_counting_ratio_tendsto :
    Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)/(x/Real.log x)) atTop (nhds 1) := by
  have hi := Chebyshev.integral_theta_div_log_sq_isLittleO.tendsto_div_nhds_zero
  have ht := arithmeticSupply_theta_real_ratio_tendsto.add hi
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
  rw [Chebyshev.primeCounting_eq_theta_div_log_add_integral hx.le]
  have hx0 : x≠0 := ne_of_gt (by linarith : (0 : ℝ)<x)
  have hl : Real.log x≠0 := (Real.log_pos (by linarith : (1 : ℝ)<x)).ne'
  field_simp


end Entry002
