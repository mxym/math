import CircuitRecursion.Yield
import Mathlib.Analysis.Asymptotics.Defs

open scoped Topology
open CircuitCompletion
namespace CircuitRecursion

theorem extractionCircuit_real_bound (k : ℕ) (hk : 1≤k) :
    ((extractionCircuit k).length : ℝ)≤
      (20480*3^6*14^2+100 : ℝ)*(k : ℝ)^7*
        (Real.logb 2 ((k : ℝ)+3))^2 := by
  have hk' : (1 : ℝ)≤k := by exact_mod_cast hk
  have hL : 1≤Real.logb 2 ((k : ℝ)+3) := by
    apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ)<2) (by positivity)).mpr
    norm_num
    linarith
  have hceil : (Nat.clog 2 (k+3) : ℝ)≤Real.logb 2 ((k : ℝ)+3)+1 := by
    have ht := Nat.ceil_lt_add_one (le_trans (by norm_num : (0 : ℝ)≤1) hL)
    have he : ⌈Real.logb 2 ((k : ℝ)+3)⌉₊=Nat.clog 2 (k+3) := by
      simpa only [Nat.cast_add,Nat.cast_ofNat] using Real.natCeil_logb_natCast 2 (k+3)
    rw [he] at ht
    exact ht.le
  have hc : 6*(Nat.clog 2 (k+3) : ℝ)+2≤14*Real.logb 2 ((k : ℝ)+3) := by linarith
  have hx : (k : ℝ)+2≤3*k := by linarith
  have hkpow : (k : ℝ)^2≤(k : ℝ)^7 := by
    have hp : (1 : ℝ)≤(k : ℝ)^5 := one_le_pow₀ hk'
    nlinarith [mul_nonneg (sq_nonneg (k : ℝ)) (sub_nonneg.mpr hp)]
  have htail : (k : ℝ)^2≤(k : ℝ)^7*(Real.logb 2 ((k : ℝ)+3))^2 :=
    hkpow.trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL))
  have hb : ((extractionCircuit k).length : ℝ)≤
      20480*(k : ℝ)*(k+2)^6*(6*(Nat.clog 2 (k+3) : ℝ)+2)^2+100*(k : ℝ)^2 := by
    exact_mod_cast extractionCircuit_polynomial_bound k
  calc
    _ ≤ 20480*(k : ℝ)*(k+2)^6*(6*(Nat.clog 2 (k+3) : ℝ)+2)^2+100*(k : ℝ)^2 := hb
    _ ≤ 20480*(k : ℝ)*(3*k)^6*(14*Real.logb 2 ((k : ℝ)+3))^2+
        100*((k : ℝ)^7*(Real.logb 2 ((k : ℝ)+3))^2) := by
      apply add_le_add
      · gcongr
      · exact mul_le_mul_of_nonneg_left htail (by norm_num)
    _ = _ := by ring

/-- The same complete actual circuit family has the manuscript's stated
O(k^7 log²(k+3)) elementary gate complexity. -/
theorem extractionCircuit_isBigO :
    (fun k : ℕ => ((extractionCircuit k).length : ℝ)) =O[Filter.atTop]
      (fun k : ℕ => (k : ℝ)^7*(Real.logb 2 ((k : ℝ)+3))^2) := by
  apply Asymptotics.IsBigO.of_bound (20480*3^6*14^2+100 : ℝ)
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with k hk
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (by positivity)]
  simpa only [mul_assoc] using extractionCircuit_real_bound k hk

end CircuitRecursion
