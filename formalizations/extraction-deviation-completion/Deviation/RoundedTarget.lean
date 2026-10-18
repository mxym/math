import Deviation.InformationQuantile

open scoped Topology
open Filter

namespace ExtractionDeviation
noncomputable section

def roundedTarget (C z : ℝ) (k : ℕ) : ℕ := ⌈Real.exp (k*C+z*Real.sqrt k)⌉₊

theorem roundedTarget_pos (C z : ℝ) (k : ℕ) : 0 < roundedTarget C z k :=
  Nat.ceil_pos.mpr (Real.exp_pos _)

theorem log_natCeil_exp_bounds (x : ℝ) (hx : 0 ≤ x) :
    x ≤ Real.log (⌈Real.exp x⌉₊:ℝ) ∧
      Real.log (⌈Real.exp x⌉₊:ℝ) ≤ x+Real.log 2 := by
  have hpos : (0:ℝ) < ⌈Real.exp x⌉₊ := by exact_mod_cast Nat.ceil_pos.mpr (Real.exp_pos x)
  constructor
  · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos x) (Nat.le_ceil (Real.exp x))
  · have he : 1 ≤ Real.exp x := Real.one_le_exp_iff.mpr hx
    have hc : (⌈Real.exp x⌉₊:ℝ) ≤ 2*Real.exp x := by
      have h := (Nat.ceil_lt_add_one (Real.exp_pos x).le).le
      linarith
    have h := Real.log_le_log hpos hc
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (Real.exp_ne_zero x), Real.log_exp] at h
    linarith

theorem natSqrt_inv_tendsto_zero :
    Tendsto (fun k : ℕ => (Real.sqrt k)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

theorem secondOrderExponent_rate (C z : ℝ) :
    Tendsto (fun k : ℕ => (k*C+z*Real.sqrt k)/k) atTop (𝓝 C) := by
  have h := tendsto_const_nhds (x := C) |>.add (natSqrt_inv_tendsto_zero.const_mul z)
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hkR : (k:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have hsR : Real.sqrt (k:ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hk)
  have he := Real.sq_sqrt (Nat.cast_nonneg k)
  field_simp
  nlinarith [congrArg (fun t : ℝ => z*t) he]

theorem secondOrderExponent_eventually_nonneg (C z : ℝ) (hC : 0 < C) :
    ∀ᶠ k : ℕ in atTop, 0 ≤ k*C+z*Real.sqrt k := by
  have h := (secondOrderExponent_rate C z).eventually (Ioi_mem_nhds hC)
  filter_upwards [h,eventually_gt_atTop 0] with k hk hkpos
  have hkR : (0:ℝ) < k := Nat.cast_pos.mpr hkpos
  exact ((div_pos_iff_of_pos_right hkR).mp hk).le

theorem roundedTarget_secondOrder (C z : ℝ) (hC : 0 < C) :
    Tendsto (fun k : ℕ => (Real.log (roundedTarget C z k)-k*C)/Real.sqrt k)
      atTop (𝓝 z) := by
  have hbound : Tendsto (fun k : ℕ => Real.log 2 / Real.sqrt k) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have herror : Tendsto (fun k : ℕ =>
      (Real.log (roundedTarget C z k)-(k*C+z*Real.sqrt k))/Real.sqrt k)
      atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hbound
    · filter_upwards [secondOrderExponent_eventually_nonneg C z hC] with k hk
      exact div_nonneg (sub_nonneg.mpr (log_natCeil_exp_bounds _ hk).1) (Real.sqrt_nonneg _)
    · filter_upwards [secondOrderExponent_eventually_nonneg C z hC] with k hk
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
      have h := (log_natCeil_exp_bounds _ hk).2
      change Real.log (roundedTarget C z k) ≤ _ at h
      linarith
  have h := herror.add_const z
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hs : Real.sqrt (k:ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hk)
  field_simp
  ring

theorem secondOrder_rate_limit (K : ℕ → ℕ) (C z : ℝ)
    (hsecond : Tendsto (fun k : ℕ => (Real.log (K k)-k*C)/Real.sqrt k)
      atTop (𝓝 z)) :
    Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (𝓝 C) := by
  have h := (hsecond.mul natSqrt_inv_tendsto_zero).add_const C
  simp only [mul_zero, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with k hk
  change (Real.log (K k)-k*C)/Real.sqrt k/Real.sqrt k+C = _
  rw [div_div, ← pow_two, Real.sq_sqrt (Nat.cast_nonneg k)]
  have hkR : (k:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  field_simp
  ring

theorem roundedTarget_eventually_le_power (C z : ℝ) (hC : 0 < C)
    (m : ℕ) (hm : 0 < m) (hcap : C < Real.log m) :
    ∀ᶠ k : ℕ in atTop, roundedTarget C z k ≤ m^k := by
  have hrate := secondOrder_rate_limit (roundedTarget C z) C z (roundedTarget_secondOrder C z hC)
  have h := hrate.eventually (Iio_mem_nhds hcap)
  filter_upwards [h,eventually_gt_atTop 0] with k hk hkpos
  have hkR : (0:ℝ) < k := Nat.cast_pos.mpr hkpos
  have hlog : Real.log (roundedTarget C z k) ≤ Real.log ((m:ℝ)^k) := by
    rw [Real.log_pow]
    simpa only [mul_comm] using ((div_lt_iff₀ hkR).mp hk).le
  have hp : (0:ℝ) < roundedTarget C z k := by exact_mod_cast roundedTarget_pos C z k
  have hpow : (0:ℝ) < (m:ℝ)^k := pow_pos (Nat.cast_pos.mpr hm) k
  have he := (Real.log_le_log_iff hp hpow).mp hlog
  exact_mod_cast he

/-- Capping the finitely many early integer targets makes every block feasible.
Under a strict local-dimension gap the cap is eventually inactive. -/
def cappedTarget (m n : ℕ) (C z : ℝ) (k : ℕ) : ℕ :=
  min (roundedTarget C z k) (min (m^k) (n^k))

theorem cappedTarget_pos (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (C z : ℝ) (k : ℕ) :
    0 < cappedTarget m n C z k :=
  lt_min (roundedTarget_pos C z k) (lt_min (Nat.pow_pos hm) (Nat.pow_pos hn))

theorem cappedTarget_secondOrder (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (C z : ℝ) (hC : 0 < C) (hCa : C < Real.log m) (hCb : C < Real.log n) :
    Tendsto (fun k : ℕ => (Real.log (cappedTarget m n C z k)-k*C)/Real.sqrt k)
      atTop (𝓝 z) := by
  apply (roundedTarget_secondOrder C z hC).congr'
  filter_upwards [roundedTarget_eventually_le_power C z hC m hm hCa,
    roundedTarget_eventually_le_power C z hC n hn hCb] with k hka hkb
  rw [cappedTarget, min_eq_left (le_min hka hkb)]

end
end ExtractionDeviation
