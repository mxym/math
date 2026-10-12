import CofactorGeometricEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The exact geometric entropy/product estimate used in the signed ring lower construction. -/
set_option autoImplicit false
open scoped BigOperators
namespace CofactorSpectral
noncomputable section

def entropyConstant (b : ℝ) : ℝ := b ^ (b/(b-1)) / (b-1)

theorem entropyConstant_pos (b : ℝ) (hb : 1 < b) : 0 < entropyConstant b :=
  div_pos (Real.rpow_pos_of_pos (by linarith) _) (sub_pos.mpr hb)

theorem geometricEntropyBound_eq_log (b : ℝ) (hb : 1 < b) :
    geometricEntropyBound b = Real.log (entropyConstant b) := by
  have hb0 : 0 < b := by linarith
  have hb1 : 0 < b-1 := sub_pos.mpr hb
  have he : 1-b⁻¹ = (b-1)/b := by field_simp
  unfold geometricEntropyBound entropyConstant
  rw [he,Real.log_div (ne_of_gt hb1) (ne_of_gt hb0),
    Real.log_div (ne_of_gt (Real.rpow_pos_of_pos hb0 _)) (ne_of_gt hb1),Real.log_rpow hb0]
  field_simp
  ring

theorem geometric_separation_product_bound (n : ℕ) (b : ℝ) (hb : 1 < b)
    (d : Fin (n+1) → ℝ) (hd : ∀ i, 0 < d i)
    (hsep : ∀ i : Fin n, b*d i.succ ≤ d i.castSucc) :
    (∑ i, d i) ^ (∑ i, d i) / (∏ i, d i ^ d i) ≤
      (entropyConstant b) ^ (∑ i, d i) := by
  classical
  let J : ℝ := ∑ i, d i
  have hJ : 0 < J := Finset.sum_pos (fun i _ => hd i) Finset.univ_nonempty
  let p : Fin (n+1) → ℝ := fun i => d i/J
  have hp : ∀ i, 0 < p i := fun i => div_pos (hd i) hJ
  have hs : ∑ i, p i = 1 := by
    change (∑ i, d i/J) = 1
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hJ)
  have hps : ∀ i : Fin n, b*p i.succ ≤ p i.castSucc := by
    intro i
    change b*(d i.succ/J) ≤ d i.castSucc/J
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (hsep i) hJ.le
  have h := geometrically_separated_entropy_bound n b hb p hp hs hps
  rw [geometricEntropyBound_eq_log b hb] at h
  have ht : ∀ i, J * (p i * Real.log (p i)) =
      d i * Real.log (d i) - d i * Real.log J := by
    intro i
    dsimp [p]
    rw [Real.log_div (ne_of_gt (hd i)) (ne_of_gt hJ)]
    field_simp [ne_of_gt hJ]
  have hscaled : J * (-(∑ i, p i * Real.log (p i))) =
      J*Real.log J - ∑ i, d i*Real.log (d i) := by
    rw [mul_neg,Finset.mul_sum]
    simp_rw [ht,Finset.sum_sub_distrib,← Finset.sum_mul]
    change -( (∑ i, d i*Real.log (d i)) - J*Real.log J) = _
    ring
  have hbound := mul_le_mul_of_nonneg_left h hJ.le
  rw [hscaled] at hbound
  have hprod : 0 < ∏ i, d i ^ d i :=
    Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (hd i) _)
  apply (Real.log_le_log_iff (div_pos (Real.rpow_pos_of_pos hJ _) hprod)
    (Real.rpow_pos_of_pos (entropyConstant_pos b hb) _)).mp
  rw [Real.log_div (ne_of_gt (Real.rpow_pos_of_pos hJ _)) (ne_of_gt hprod),
    Real.log_rpow hJ,Real.log_prod (fun i _ => ne_of_gt (Real.rpow_pos_of_pos (hd i) _))]
  simp_rw [Real.log_rpow (hd _)]
  rw [Real.log_rpow (entropyConstant_pos b hb)]
  exact hbound

end
end CofactorSpectral
