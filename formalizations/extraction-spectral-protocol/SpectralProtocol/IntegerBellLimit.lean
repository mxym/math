import SpectralProtocol.GeneralRankBell
import RankSupport.FirstOrder

open Filter
open scoped Topology
namespace SpectralProtocol

theorem integerBellYield_log_bounds (k r : ℕ) (hr : 0 < r) (hrdim : r ≤ 4^k) :
    (integerBellYield k r:ℝ) ≤ (k:ℝ)-Real.log (r:ℝ)/Real.log 4 ∧
      (k:ℝ)-Real.log (r:ℝ)/Real.log 4 < (integerBellYield k r:ℝ)+1 := by
  have hfour : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hu := Real.log_le_log hrR (show (r:ℝ) ≤ (4:ℝ)^k by exact_mod_cast hrdim)
  rw [Real.log_pow] at hu
  have hx : 0 ≤ (k:ℝ)-Real.log (r:ℝ)/Real.log 4 := by
    exact sub_nonneg.mpr ((div_le_iff₀ hfour).mpr hu)
  rw [integerBellYield_eq_real_floor k r hr hrdim]
  exact ⟨Nat.floor_le hx,Nat.lt_floor_add_one _⟩

/-- An actual integer Bell optimum has the corresponding first-order rate,
with its strict integer-floor loss bounded internally by one Bell pair. -/
theorem integerBellYield_per_copy_limit (r : ℕ → ℕ)
    (hr : ∀ k,0 < r k) (hrdim : ∀ k,r k ≤ 4^k)
    (L : ℝ) (hlog : Tendsto (fun k : ℕ => Real.log (r k:ℝ)/(k:ℝ)) atTop (𝓝 L)) :
    Tendsto (fun k : ℕ => (integerBellYield k (r k):ℝ)/(k:ℝ))
      atTop (𝓝 (1-L/Real.log 4)) := by
  have hmain : Tendsto (fun k : ℕ => 1-(Real.log (r k:ℝ)/(k:ℝ))/Real.log 4)
      atTop (𝓝 (1-L/Real.log 4)) := tendsto_const_nhds.sub (hlog.div_const _)
  have hzero : Tendsto (fun k : ℕ => 1/(k:ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hlowlim := hmain.sub hzero
  simp only [sub_zero] at hlowlim
  have hlow : ∀ᶠ k : ℕ in atTop,
      1-(Real.log (r k:ℝ)/(k:ℝ))/Real.log 4-1/(k:ℝ) ≤
        (integerBellYield k (r k):ℝ)/(k:ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hkR : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hb := (integerBellYield_log_bounds k (r k) (hr k) (hrdim k)).2.le
    have h := div_le_div_of_nonneg_right (show (k:ℝ)-Real.log (r k:ℝ)/Real.log 4-1 ≤
      (integerBellYield k (r k):ℝ) by linarith) hkR.le
    convert h using 1 <;> field_simp
  have hupp : ∀ᶠ k : ℕ in atTop,
      (integerBellYield k (r k):ℝ)/(k:ℝ) ≤
        1-(Real.log (r k:ℝ)/(k:ℝ))/Real.log 4 := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hkR : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have h := div_le_div_of_nonneg_right
      (integerBellYield_log_bounds k (r k) (hr k) (hrdim k)).1 hkR.le
    convert h using 1 <;> field_simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowlim hmain hlow hupp

/-- The finite rank-s optimum has an exact zero-error first-order Bell rate.
The proof uses the intrinsic rank's exponential rate, not a Weyl formula. -/
theorem rankBounded_iid_integerBell_per_copy_limit (s : ℕ) (hs : 0 < s) (hs4 : s ≤ 4) :
    Tendsto (fun k : ℕ => (integerBellYield k (twoQubitRankBudgetRank k s):ℝ)/(k:ℝ))
      atTop (𝓝 (1-Real.log (s:ℝ)/Real.log 4)) := by
  apply integerBellYield_per_copy_limit (fun k => twoQubitRankBudgetRank k s)
    (fun k => twoQubitRankBudgetRank_pos k s hs) (fun k => twoQubitRankBudgetRank_le k s)
  exact ExtractionRankSupport.rankBudgetProjector_log_rank_per_copy_limit 4 s hs hs4

end SpectralProtocol