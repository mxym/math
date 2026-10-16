import SymmetricSupport.RankAsymptotic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Order.Field

open scoped Topology
open Filter

namespace SymmetricSupport

theorem symmetricProjector_rank_div_geometric_limit (D : ℕ) (hD : 0 < D)
    (b : ℝ) (hb : 1 < b) :
    Tendsto (fun k : ℕ => ((symmetricProjector D k).rank : ℝ) / b ^ k) atTop (𝓝 0) := by
  have h := (symmetricProjector_rank_scaled_limit D hD).mul
    (tendsto_pow_const_div_const_pow_of_one_lt (D - 1) hb)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  field_simp

theorem symmetricProjector_rank_mul_geometric_limit (D : ℕ) (hD : 0 < D)
    (q : ℝ) (hq : |q| < 1) :
    Tendsto (fun k : ℕ => ((symmetricProjector D k).rank : ℝ) * q ^ k) atTop (𝓝 0) := by
  have h := (symmetricProjector_rank_scaled_limit D hD).mul
    (tendsto_pow_const_mul_const_pow_of_abs_lt_one (D - 1) hq)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  field_simp

theorem symmetricProjector_sqrt_rank_div_geometric_limit (D : ℕ) (hD : 0 < D)
    (b : ℝ) (hb : 1 < b) :
    Tendsto (fun k : ℕ => Real.sqrt ((symmetricProjector D k).rank : ℝ) / b ^ k)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun k => div_nonneg (Real.sqrt_nonneg _) (pow_nonneg (by linarith) _))
    (fun k => ?_) (symmetricProjector_rank_div_geometric_limit D hD b hb)
  apply div_le_div_of_nonneg_right _ (pow_nonneg (by linarith) _)
  apply Real.sqrt_le_self_iff.mpr
  right
  exact_mod_cast symmetricProjector_rank_pos D k hD

theorem symmetricProjector_geometric_div_sqrt_rank_atTop (D : ℕ) (hD : 0 < D)
    (b : ℝ) (hb : 1 < b) :
    Tendsto (fun k : ℕ => b ^ k / Real.sqrt ((symmetricProjector D k).rank : ℝ))
      atTop atTop := by
  have h0 := symmetricProjector_sqrt_rank_div_geometric_limit D hD b hb
  have hp : ∀ᶠ k : ℕ in atTop,
      (0 : ℝ) < Real.sqrt ((symmetricProjector D k).rank : ℝ) / b ^ k := by
    apply Filter.Eventually.of_forall
    intro k
    have hr : (0 : ℝ) < ((symmetricProjector D k).rank : ℝ) := by
      exact_mod_cast symmetricProjector_rank_pos D k hD
    exact div_pos (Real.sqrt_pos.mpr hr) (pow_pos (by linarith) _)
  have h : Tendsto (fun k : ℕ => Real.sqrt ((symmetricProjector D k).rank : ℝ) / b ^ k)
      atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨h0, hp⟩
  have hh := h.inv_tendsto_nhdsGT_zero
  change Tendsto (fun k : ℕ =>
    (Real.sqrt ((symmetricProjector D k).rank : ℝ) / b ^ k)⁻¹) atTop atTop at hh
  simpa only [inv_div] using hh

theorem symmetricProjector_rank_atTop (D : ℕ) (hD : 2 ≤ D) :
    Tendsto (fun k : ℕ => ((symmetricProjector D k).rank : ℝ)) atTop atTop := by
  have hDpos : 0 < D := by omega
  have hc : (0 : ℝ) < 1 / ((D - 1).factorial : ℝ) := by positivity
  have hk : Tendsto (fun k : ℕ => (k : ℝ) ^ (D - 1)) atTop atTop :=
    (tendsto_pow_atTop (by omega : D - 1 ≠ 0)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := Filter.Tendsto.pos_mul_atTop hc (symmetricProjector_rank_scaled_limit D hDpos) hk
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  field_simp

theorem symmetricProjector_rectangular_cap_ratio_limit (D m n : ℕ) (hD : 0 < D)
    (hm : 0 < m) (hmn : m < n) :
    Tendsto (fun k : ℕ => ((symmetricProjector D k).rank : ℝ) * ((m : ℝ) / n) ^ k)
      atTop (𝓝 0) := by
  apply symmetricProjector_rank_mul_geometric_limit D hD
  have hn : (0 : ℝ) < n := by exact_mod_cast lt_trans hm hmn
  rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hn.le), div_lt_one hn]
  exact_mod_cast hmn

end SymmetricSupport
