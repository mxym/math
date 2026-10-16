import Deviation.RoundedTarget
import OperationalCompletion.GridLimit

open scoped Topology
open Filter ExtractionDeviation
namespace OperationalCompletion
noncomputable section

theorem nat_mul_log_rate (c : ℕ) (hc : 0<c) (K : ℕ → ℕ) (hK : ∀ k,0<K k)
    (R : ℝ) (hR : Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R)) :
    Tendsto (fun k : ℕ => Real.log ((c*K k:ℕ):ℝ)/k) atTop (nhds R) := by
  have hh : Tendsto (fun k : ℕ => Real.log c/k) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h := hh.add hR
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards with k
  rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast Nat.ne_of_gt hc)
    (by exact_mod_cast Nat.ne_of_gt (hK k)),add_div]

theorem nat_eventually_le_of_log_rates (d K : ℕ → ℕ) (hd : ∀ k,0<d k) (hK : ∀ k,0<K k)
    (b R : ℝ) (hb : Tendsto (fun k : ℕ => Real.log (d k)/k) atTop (nhds b))
    (hR : Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R)) (hbR : b<R) :
    ∀ᶠ k : ℕ in atTop,d k≤K k := by
  filter_upwards [hb.eventually_lt_const (show b<(b+R)/2 by linarith),
    hR.eventually_const_lt (show (b+R)/2<R by linarith),eventually_gt_atTop 0] with k hblo hRhi hkpos
  have hk : Real.log (d k)/k<Real.log (K k)/k := hblo.trans hRhi
  have hlogs : Real.log (d k)<Real.log (K k) :=
    (div_lt_div_iff_of_pos_right (Nat.cast_pos.mpr hkpos)).mp hk
  have hlt : (d k:ℝ)<(K k:ℝ) := (Real.log_lt_log_iff
    (Nat.cast_pos.mpr (hd k)) (Nat.cast_pos.mpr (hK k))).mp hlogs
  exact_mod_cast hlt.le

theorem nat_ratio_eventual_lower (d K : ℕ → ℕ) (hd : ∀ k,0<d k) (hK : ∀ k,0<K k)
    (b R : ℝ) (hb : Tendsto (fun k : ℕ => Real.log (d k)/k) atTop (nhds b))
    (hR : Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R)) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop,Real.exp ((k:ℝ)*(b-R-ε))≤(d k:ℝ)/K k := by
  have h := (hb.sub hR).eventually_const_lt (show b-R-ε<b-R by linarith)
  filter_upwards [h,eventually_gt_atTop 0] with k hk hkpos
  have hdR : (0:ℝ)<d k := Nat.cast_pos.mpr (hd k)
  have hKR : (0:ℝ)<K k := Nat.cast_pos.mpr (hK k)
  have hlo : (k:ℝ)*(b-R-ε)≤Real.log ((d k:ℝ)/K k) := by
    rw [Real.log_div (ne_of_gt hdR) (ne_of_gt hKR)]
    have hh := (lt_div_iff₀ (Nat.cast_pos.mpr hkpos)).mp (by simpa only [←sub_div] using hk)
    nlinarith
  exact (Real.exp_le_exp.mpr hlo).trans_eq (Real.exp_log (div_pos hdR hKR))

theorem roundedTarget_rate (b : ℝ) (hb : 0<b) :
    Tendsto (fun k : ℕ => Real.log (roundedTarget b 0 k)/k) atTop (nhds b) :=
  secondOrder_rate _ b 0 (roundedTarget_secondOrder b 0 hb)

theorem roundedTarget_rate_nonneg (b : ℝ) (hb : 0≤b) :
    Tendsto (fun k : ℕ => Real.log (roundedTarget b 0 k)/k) atTop (nhds b) := by
  by_cases hz : b=0
  · subst b
    simpa only [roundedTarget,mul_zero,zero_mul,add_zero,zero_add,Real.exp_zero,Nat.ceil_one,
      Nat.cast_one,Real.log_one,zero_div] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (nhds 0))
  · exact roundedTarget_rate b (lt_of_le_of_ne hb (Ne.symm hz))

end
end OperationalCompletion
