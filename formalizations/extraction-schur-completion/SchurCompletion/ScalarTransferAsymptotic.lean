import SchurCompletion.ScalarPowerTransfer
import Mathlib.Algebra.Order.Floor.Semifield

open scoped BigOperators Topology
open Matrix MeasureTheory Filter Asymptotics

namespace ExtractionSchur
noncomputable section

theorem nat_div_ratio_limit (b : ℕ) (hb : 0 < b) :
    Tendsto (fun k : ℕ => ((k/b : ℕ) : ℝ)/(k : ℝ)) atTop (𝓝 (1/(b : ℝ))) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_mod_div_atTop_nhds_zero_nat hb)
  have hh := h.div_const (b : ℝ)
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have he : ((k/b : ℕ) : ℝ)*(b : ℝ)+((k%b : ℕ) : ℝ) = (k : ℝ) := by
    exact_mod_cast (by simpa only [Nat.mul_comm] using Nat.div_add_mod k b)
  field_simp
  nlinarith

theorem nat_ceil_ratio_limit (s : ℕ) (hs : 0 < s) :
    Tendsto (fun k : ℕ => (⌈(k : ℝ)/(s : ℝ)⌉₊ : ℝ)/(k : ℝ)) atTop
      (𝓝 (1/(s : ℝ))) := by
  have h := (tendsto_nat_ceil_mul_div_atTop (R := ℝ)
    (show 0 ≤ (s : ℝ)⁻¹ by positivity)).comp tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def, div_eq_mul_inv, mul_comm, mul_one] using h

/-- Reindexing a proved power asymptotic along indices of positive linear size. -/
theorem power_moment_reindex_limit (g : ℕ) (M : ℕ → ℝ) (A c : ℝ)
    (hM : Tendsto (fun k : ℕ => (k : ℝ)^g*M k) atTop (𝓝 A))
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (hc : Tendsto (fun k : ℕ => (m k : ℝ)/(k : ℝ)) atTop (𝓝 c)) (hc0 : c ≠ 0) :
    Tendsto (fun k : ℕ => (k : ℝ)^g*M (m k)) atTop (𝓝 (A/c^g)) := by
  have h := (hM.comp hm).div (hc.pow g) (pow_ne_zero _ hc0)
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1, hm.eventually (eventually_ge_atTop 1)] with k hk hmk
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hmR : (m k : ℝ) ≠ 0 := by exact_mod_cast (by omega : m k ≠ 0)
  dsimp
  rw [div_pow]
  field_simp

theorem geometric_floor_tail_limit (g b : ℕ) (hb : 0 < b) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (fun k : ℕ => (k : ℝ)^g*r^(b*(k/b))) atTop (𝓝 0) := by
  have hq0 : 0 ≤ r^b := pow_nonneg hr0 _
  have hq1 : r^b < 1 := pow_lt_one₀ hr0 hr1 hb.ne'
  have h := power_moment_reindex_limit g (fun j => (r^b)^j) 0 (1/(b : ℝ))
    (tendsto_pow_const_mul_const_pow_of_lt_one g hq0 hq1)
    (fun k => k/b) (Nat.tendsto_div_const_atTop hb.ne') (nat_div_ratio_limit b hb)
    (by positivity)
  simpa only [zero_div, pow_mul] using h

/-- An upper family with constants approaching the lower constant suffices;
no uniform convergence in the auxiliary parameter is assumed. -/
theorem tendsto_of_parameter_squeeze (F L : ℕ → ℝ) (U : ℕ → ℕ → ℝ)
    (C : ℝ) (B : ℕ → ℝ) (hL : Tendsto L atTop (𝓝 C))
    (hU : ∀ N, 0 < N → Tendsto (U N) atTop (𝓝 (B N)))
    (hB : Tendsto B atTop (𝓝 C))
    (hlo : ∀ k, L k ≤ F k) (hup : ∀ N, 0 < N → ∀ k, F k ≤ U N k) :
    Tendsto F atTop (𝓝 C) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [(tendsto_order.1 hL).1 a ha] with k hk
    exact hk.trans_le (hlo k)
  · intro a ha
    obtain ⟨N, hN, hNa⟩ := ((eventually_ge_atTop 1).and
      ((tendsto_order.1 hB).2 a ha)).exists
    filter_upwards [(tendsto_order.1 (hU N (by omega))).2 a hNa] with k hk
    exact (hup N (by omega) k).trans_lt hk

end
end ExtractionSchur
