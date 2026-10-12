import CofactorGeometricMean

/-! Entropy of a positive finite geometrically separated distribution. -/
set_option autoImplicit false
open scoped BigOperators
namespace CofactorSpectral
noncomputable section

def geometricEntropyBound (b : ℝ) : ℝ := -Real.log (1-b⁻¹) + Real.log b/(b-1)

theorem geometrically_separated_entropy_bound (n : ℕ) (b : ℝ) (hb : 1 < b)
    (p : Fin (n+1) → ℝ) (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1)
    (hsep : ∀ i : Fin n, b * p i.succ ≤ p i.castSucc) :
    -(∑ i, p i * Real.log (p i)) ≤ geometricEntropyBound b := by
  have hb0 : 0 < b := by linarith
  have hr : 0 < b⁻¹ := inv_pos.mpr hb0
  have hr1 : b⁻¹ < 1 := by
    have h : 1/b < 1 := (div_lt_iff₀ hb0).mpr (by linarith)
    simpa only [one_div] using h
  have hq : 0 < 1-b⁻¹ := sub_pos.mpr hr1
  let g : Fin (n+1) → ℝ := fun i => (1-b⁻¹) * (b⁻¹)^i.val
  have hg : ∀ i, 0 < g i := fun i => mul_pos hq (pow_pos hr _)
  have hgs : (∑ i, g i) ≤ 1 := by
    change (∑ i : Fin (n+1), (1-b⁻¹) * (b⁻¹)^i.val) ≤ 1
    rw [finite_geometric_mass]
    exact sub_le_self _ (pow_nonneg hr.le _)
  have hglog : ∀ i, Real.log (g i) = Real.log (1-b⁻¹)-(i.val : ℝ)*Real.log b := by
    intro i
    dsimp [g]
    rw [Real.log_mul (ne_of_gt hq) (pow_ne_zero _ (ne_of_gt hr)),Real.log_pow,Real.log_inv]
    ring
  have hcross : -(∑ i, p i * Real.log (g i)) = -Real.log (1-b⁻¹) +
      (∑ i, (i.val : ℝ)*p i) * Real.log b := by
    have ht : (∑ i, p i * ((i.val : ℝ)*Real.log b)) =
        (∑ i, (i.val : ℝ)*p i) * Real.log b := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    simp_rw [hglog,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul]
    rw [hs,ht]
    ring
  have h := finite_gibbs_inequality p g hp hg hs hgs
  rw [hcross] at h
  have hm := geometrically_separated_mean_bound n b hb p (fun i => (hp i).le) hs hsep
  have hmul := mul_le_mul_of_nonneg_right hm (Real.log_pos hb).le
  unfold geometricEntropyBound
  have he : (1/(b-1))*Real.log b = Real.log b/(b-1) := by ring
  rw [he] at hmul
  linarith

end
end CofactorSpectral
