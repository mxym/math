import RankSupport.ExponentialLower
import SymmetricSupport.PackingGrowth
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open scoped BigOperators Topology
open Filter Asymptotics

namespace ExtractionRankSupport

open SymmetricSupport

/-- The explicit symmetric polynomial overhead is subexponential. This lemma
uses the already proved exact rank asymptotic, not a supplied logarithmic bound. -/
theorem symmetric_log_rank_per_copy_limit (E : ℕ) (hE : 0 < E) :
    Tendsto (fun k : ℕ => Real.log ((symmetricProjector E k).rank : ℝ) / (k : ℝ))
      atTop (𝓝 0) := by
  have hnat : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun k : ℕ => (k : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hnat
  have hlog : Tendsto (fun k : ℕ => Real.log (k : ℝ) / (k : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, Function.comp_def] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero.comp hnat
  have hfconst : Tendsto (fun _ : ℕ => Real.log ((E - 1).factorial : ℝ))
      atTop (𝓝 (Real.log ((E - 1).factorial : ℝ))) := tendsto_const_nhds
  have h := (((symmetricProjector_log_rank_limit E hE).mul hinv).add
    (hlog.const_mul ((E - 1 : ℕ) : ℝ))).sub
      (hfconst.mul hinv)
  simp only [zero_mul, mul_zero, add_zero, sub_zero] at h
  convert h using 1
  ext k
  ring

theorem rankBudgetProjector_rank_div_geometric_limit (D s : ℕ)
    (hD : 0 < D) (hs : 0 < s) (b : ℝ) (hb : (s : ℝ) < b) :
    Tendsto (fun k : ℕ => ((rankBudgetProjector D k s).rank : ℝ) / b ^ k)
      atTop (𝓝 0) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hb0 : 0 < b := hsR.trans hb
  have hE : 0 < D*s := Nat.mul_pos hD hs
  have hq : |(s : ℝ) / b| < 1 := by
    rw [abs_of_pos (div_pos hsR hb0), div_lt_one hb0]
    exact hb
  have hlim := symmetricProjector_rank_mul_geometric_limit (D*s) hE ((s : ℝ)/b) hq
  apply squeeze_zero (fun k => div_nonneg (Nat.cast_nonneg _) (pow_nonneg hb0.le _))
    (fun k => ?_) hlim
  have hu : ((rankBudgetProjector D k s).rank : ℝ) ≤
      (s : ℝ) ^ k * ((symmetricProjector (D*s) k).rank : ℝ) := by
    rw [symmetricProjector_rank_choose]
    exact_mod_cast rankBudgetProjector_rank_le_polynomial D k s
  calc
    _ ≤ ((s : ℝ)^k * ((symmetricProjector (D*s) k).rank : ℝ)) / b^k :=
      div_le_div_of_nonneg_right hu (pow_nonneg hb0.le _)
    _ = _ := by rw [div_pow]; ring

theorem rankBudgetProjector_sqrt_rank_div_geometric_limit (D s : ℕ)
    (hD : 0 < D) (hs : 0 < s) (b : ℝ) (hb : 0 < b) (hbudget : (s : ℝ) < b^2) :
    Tendsto (fun k : ℕ => Real.sqrt ((rankBudgetProjector D k s).rank : ℝ) / b^k)
      atTop (𝓝 0) := by
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp
    (rankBudgetProjector_rank_div_geometric_limit D s hD hs (b^2) hbudget)
  simp only [Real.sqrt_zero] at h
  apply h.congr'
  filter_upwards [] with k
  dsimp only [Function.comp_apply]
  rw [Real.sqrt_div (Nat.cast_nonneg _)]
  have he : (b^2)^k = (b^k)^2 := by
    rw [← pow_mul, mul_comm (2 : ℕ) k, pow_mul]
  rw [he, Real.sqrt_sq_eq_abs, abs_of_pos (pow_pos hb _)]

theorem rankBudgetProjector_geometric_div_sqrt_rank_atTop (D s : ℕ)
    (hD : 0 < D) (hs : 0 < s) (b : ℝ) (hb : 0 < b) (hbudget : (s : ℝ) < b^2) :
    Tendsto (fun k : ℕ => b^k / Real.sqrt ((rankBudgetProjector D k s).rank : ℝ))
      atTop atTop := by
  have h0 := rankBudgetProjector_sqrt_rank_div_geometric_limit D s hD hs b hb hbudget
  have hp : ∀ᶠ k : ℕ in atTop,
      (0 : ℝ) < Real.sqrt ((rankBudgetProjector D k s).rank : ℝ) / b^k := by
    apply Filter.Eventually.of_forall
    intro k
    have hr : (0 : ℝ) < (rankBudgetProjector D k s).rank := by
      exact_mod_cast rankBudgetProjector_rank_pos D k s hD hs
    exact div_pos (Real.sqrt_pos.mpr hr) (pow_pos hb _)
  have h : Tendsto (fun k : ℕ => Real.sqrt ((rankBudgetProjector D k s).rank : ℝ) / b^k)
      atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨h0, hp⟩
  have hh := h.inv_tendsto_nhdsGT_zero
  change Tendsto (fun k : ℕ =>
    (Real.sqrt ((rankBudgetProjector D k s).rank : ℝ) / b^k)⁻¹) atTop atTop at hh
  simpa only [inv_div] using hh

/-- The actual intrinsic common-support rank has exponential rate log(s).
This is weaker than the manuscript's sharp polynomial Schur asymptotic. -/
theorem rankBudgetProjector_log_rank_per_copy_limit (D s : ℕ)
    (hs : 0 < s) (hsD : s ≤ D) :
    Tendsto (fun k : ℕ => Real.log ((rankBudgetProjector D k s).rank : ℝ) / (k : ℝ))
      atTop (𝓝 (Real.log (s : ℝ))) := by
  have hD : 0 < D := hs.trans_le hsD
  have hE : 0 < D*s := Nat.mul_pos hD hs
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hlow : ∀ᶠ k : ℕ in atTop,
      0 ≤ Real.log ((rankBudgetProjector D k s).rank : ℝ) / (k : ℝ) - Real.log (s : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hpow : (s : ℝ)^k ≤ ((rankBudgetProjector D k s).rank : ℝ) := by
      exact_mod_cast rankBudgetProjector_rank_ge_power D k s hsD
    have hlog := Real.log_le_log (pow_pos hsR _) hpow
    rw [Real.log_pow] at hlog
    have hdiv : Real.log (s : ℝ) ≤
        Real.log ((rankBudgetProjector D k s).rank : ℝ) / (k : ℝ) :=
      (le_div_iff₀ hkR).mpr (by nlinarith only [hlog])
    linarith
  have hupp : ∀ᶠ k : ℕ in atTop,
      Real.log ((rankBudgetProjector D k s).rank : ℝ) / (k : ℝ) - Real.log (s : ℝ) ≤
        Real.log ((symmetricProjector (D*s) k).rank : ℝ) / (k : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hr : (0 : ℝ) < (rankBudgetProjector D k s).rank := by
      exact_mod_cast rankBudgetProjector_rank_pos D k s hD hs
    have hp : (0 : ℝ) < (symmetricProjector (D*s) k).rank := by
      exact_mod_cast symmetricProjector_rank_pos (D*s) k hE
    have hu : ((rankBudgetProjector D k s).rank : ℝ) ≤
        (s : ℝ)^k * ((symmetricProjector (D*s) k).rank : ℝ) := by
      rw [symmetricProjector_rank_choose]
      exact_mod_cast rankBudgetProjector_rank_le_polynomial D k s
    have hlog := Real.log_le_log hr hu
    rw [Real.log_mul (pow_ne_zero _ hsR.ne') hp.ne', Real.log_pow] at hlog
    apply sub_le_iff_le_add.mpr
    apply (div_le_iff₀ hkR).mpr
    rw [add_mul, div_mul_cancel₀ _ hkR.ne']
    nlinarith only [hlog]
  have hz := squeeze_zero' hlow hupp (symmetric_log_rank_per_copy_limit (D*s) hE)
  have h := hz.add_const (Real.log (s : ℝ))
  simpa only [zero_add, sub_add_cancel] using h

end ExtractionRankSupport
