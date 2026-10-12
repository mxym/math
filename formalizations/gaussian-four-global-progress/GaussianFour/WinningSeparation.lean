import GaussianFour.SeparatedMoments

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace
open GaussianMeasureBridge

namespace GaussianFour

variable {d k : ℕ} [NeZero k]

/-- Two equally massive strict winning cells have uniformly separated actual
Bochner moments, in the direction of their score difference. -/
theorem winning_moment_separation (v : Fin k → Space d) (b : Fin k → ℝ)
    (hv : Function.Injective v) (i j : Fin k) (hij : i ≠ j) (p : ℝ)
    (hi : (gaussian d).real (winningCell v b i) = p)
    (hj : (gaussian d).real (winningCell v b j) = p) :
    p^2/densityBound ≤
      ⟪‖v i-v j‖⁻¹ • (v i-v j),
        (winningPartition v b hv).moment i - (winningPartition v b hv).moment j⟫ := by
  let n : Space d := ‖v i-v j‖⁻¹ • (v i-v j)
  let t : ℝ := (b i-b j)/‖v i-v j‖
  have hdiff : v i-v j ≠ 0 := sub_ne_zero.mpr (fun h => hij (hv h))
  have hnorm : 0 < ‖v i-v j‖ := norm_pos_iff.mpr hdiff
  have hn : ‖n‖ = 1 := by
    simp only [n, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm)]
    exact inv_mul_cancel₀ hnorm.ne'
  have hsi : ∀ᵐ x ∂gaussian d,
      0 < (winningPartition v b hv).labels i x → t ≤ ⟪n,x⟫ := by
    apply ae_of_all
    intro x hx
    have hmem : x ∈ winningCell v b i := by
      by_contra hh
      simp [winningPartition, hh] at hx
    have hwin := hmem j hij.symm
    have hineq : b i-b j ≤ ⟪v i,x⟫-⟪v j,x⟫ := by linarith
    have h := div_le_div_of_nonneg_right hineq hnorm.le
    simpa only [n,t,real_inner_smul_left,inner_sub_left,div_eq_mul_inv,mul_comm] using h
  have hsj : ∀ᵐ x ∂gaussian d,
      0 < (winningPartition v b hv).labels j x → ⟪n,x⟫ ≤ t := by
    apply ae_of_all
    intro x hx
    have hmem : x ∈ winningCell v b j := by
      by_contra hh
      simp [winningPartition, hh] at hx
    have hwin := hmem i hij
    have hineq : ⟪v i,x⟫-⟪v j,x⟫ ≤ b i-b j := by linarith
    have h := div_le_div_of_nonneg_right hineq hnorm.le
    simpa only [n,t,real_inner_smul_left,inner_sub_left,div_eq_mul_inv,mul_comm] using h
  exact separated_moments (winningPartition v b hv) i j hij n hn p t
    ((winningPartition_mass v b hv i).trans hi)
    ((winningPartition_mass v b hv j).trans hj) hsi hsj

/-- The four-cell paper's exact constant `1/(16 φ(0))`, with φ(0) evaluated. -/
theorem balanced_four_winning_moment_separation
    (v : Fin 4 → Space d) (b : Fin 4 → ℝ) (hv : Function.Injective v)
    (hmass : ∀ i, (gaussian d).real (winningCell v b i) = 1/4)
    (i j : Fin 4) (hij : i ≠ j) :
    Real.sqrt (2*Real.pi)/16 ≤
      ⟪‖v i-v j‖⁻¹ • (v i-v j),
        (winningPartition v b hv).moment i - (winningPartition v b hv).moment j⟫ := by
  have h := winning_moment_separation v b hv i j hij (1/4) (hmass i) (hmass j)
  have hc : (1/4:ℝ)^2/densityBound = Real.sqrt (2*Real.pi)/16 := by
    unfold densityBound
    simp only [div_eq_mul_inv, inv_inv]
    ring
  rwa [hc] at h

/-- A uniform norm separation; in particular, balanced winning-cell moments
cannot coalesce in a convergent family, including rank-deficient limits. -/
theorem balanced_four_winning_moment_norm_separation
    (v : Fin 4 → Space d) (b : Fin 4 → ℝ) (hv : Function.Injective v)
    (hmass : ∀ i, (gaussian d).real (winningCell v b i) = 1/4)
    (i j : Fin 4) (hij : i ≠ j) :
    Real.sqrt (2*Real.pi)/16 ≤
      ‖(winningPartition v b hv).moment i - (winningPartition v b hv).moment j‖ := by
  have hd : v i-v j ≠ 0 := sub_ne_zero.mpr (fun h => hij (hv h))
  have hn : ‖‖v i-v j‖⁻¹ • (v i-v j)‖ = 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hd))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hd)
  have h := real_inner_le_norm (‖v i-v j‖⁻¹ • (v i-v j))
    ((winningPartition v b hv).moment i - (winningPartition v b hv).moment j)
  rw [hn,one_mul] at h
  exact (balanced_four_winning_moment_separation v b hv hmass i j hij).trans h

end GaussianFour
