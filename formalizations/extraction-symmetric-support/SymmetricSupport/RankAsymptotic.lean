import SymmetricSupport.Occupation
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators Topology
open Asymptotics Filter

namespace SymmetricSupport

theorem shifted_natCast_isEquivalent (g : ℕ) :
    (fun k : ℕ => ((k + g : ℕ) : ℝ)) ~[atTop] (fun k : ℕ => (k : ℝ)) := by
  apply IsEquivalent.symm
  have hz : ∀ᶠ k : ℕ in atTop, ((k + g : ℕ) : ℝ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    exact_mod_cast (by omega : k + g ≠ 0)
  rw [isEquivalent_iff_tendsto_one hz]
  change Tendsto (fun k : ℕ => (k : ℝ) / ((k + g : ℕ) : ℝ)) atTop (𝓝 1)
  simpa only [Nat.cast_add, Pi.div_apply] using tendsto_natCast_div_add_atTop (g : ℝ)

/-- The actual symmetric projection rank has its claimed fixed-D polynomial asymptotic. -/
theorem symmetricProjector_rank_isEquivalent (D : ℕ) (hD : 0 < D) :
    (fun k : ℕ => ((symmetricProjector D k).rank : ℝ)) ~[atTop]
      (fun k : ℕ => (k : ℝ) ^ (D - 1) / ((D - 1).factorial : ℝ)) := by
  have hc := (isEquivalent_choose (D - 1)).comp_tendsto (tendsto_add_atTop_nat (D - 1))
  have hl := (shifted_natCast_isEquivalent (D - 1)).pow (D - 1)
  have hd := hl.div (IsEquivalent.refl (u := fun _ : ℕ => ((D - 1).factorial : ℝ)))
  have h := hc.trans hd
  convert h using 1
  ext k
  rw [symmetricProjector_rank_choose_complement D k hD]
  congr 2
  dsimp
  omega

theorem symmetricProjector_rank_scaled_limit (D : ℕ) (hD : 0 < D) :
    Tendsto (fun k : ℕ => ((symmetricProjector D k).rank : ℝ) / (k : ℝ) ^ (D - 1))
      atTop (𝓝 (1 / ((D - 1).factorial : ℝ))) := by
  have h := (symmetricProjector_rank_isEquivalent D hD).div
    (IsEquivalent.refl (u := fun k : ℕ => (k : ℝ) ^ (D - 1)))
  have he : (fun k : ℕ => ((k : ℝ) ^ (D - 1) / ((D - 1).factorial : ℝ)) /
        (k : ℝ) ^ (D - 1)) =ᶠ[atTop] (fun _ => 1 / ((D - 1).factorial : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    field_simp
  exact (h.trans he.isEquivalent).tendsto_nhds_iff.mpr tendsto_const_nhds

theorem symmetricProjector_rank_pos (D k : ℕ) (hD : 0 < D) :
    0 < (symmetricProjector D k).rank := by
  rw [symmetricProjector_rank_choose_complement D k hD]
  exact Nat.choose_pos (by omega)

/-- The leading constant in the balanced pure-input full-output fidelity scale. -/
theorem symmetricProjector_inverse_sqrt_rank_scaled_limit (D : ℕ) (hD : 0 < D) :
    Tendsto (fun k : ℕ => Real.sqrt ((k : ℝ) ^ (D - 1)) /
        Real.sqrt ((symmetricProjector D k).rank : ℝ))
      atTop (𝓝 (Real.sqrt ((D - 1).factorial : ℝ))) := by
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp
    (symmetricProjector_rank_scaled_limit D hD)
  have hf : (0 : ℝ) < ((D - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have h := hs.inv₀ (by positivity)
  simp only [one_div, Real.sqrt_inv, inv_inv] at h
  apply h.congr'
  filter_upwards [] with k
  dsimp only [Function.comp_apply]
  rw [Real.sqrt_div (Nat.cast_nonneg _) _, inv_div]

/-- The exact logarithmic rank overhead, including its constant term. -/
theorem symmetricProjector_log_rank_limit (D : ℕ) (hD : 0 < D) :
    Tendsto (fun k : ℕ => Real.log ((symmetricProjector D k).rank : ℝ) -
        ((D - 1 : ℕ) : ℝ) * Real.log (k : ℝ) +
        Real.log ((D - 1).factorial : ℝ))
      atTop (𝓝 0) := by
  have hf : (0 : ℝ) < ((D - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have h := ((Real.continuousAt_log (by positivity :
    (1 / ((D - 1).factorial : ℝ)) ≠ 0)).tendsto.comp
      (symmetricProjector_rank_scaled_limit D hD)).add_const
        (Real.log ((D - 1).factorial : ℝ))
  simp only [one_div, Real.log_inv, neg_add_cancel] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hr : ((symmetricProjector D k).rank : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (symmetricProjector_rank_pos D k hD)
  dsimp only [Function.comp_apply]
  rw [Real.log_div hr (pow_ne_zero _ hk'), Real.log_pow]

end SymmetricSupport
