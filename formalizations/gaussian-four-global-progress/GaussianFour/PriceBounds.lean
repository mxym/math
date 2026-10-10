import GaussianFour.Profile
import GaussianFour.TripleTie
import GaussianOneCell

/-! Quantitative control of actual balanced Gaussian prices, including singular
score configurations. No covariance regularity or geometric lower bound is assumed. -/
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace
open GaussianMeasureBridge
namespace GaussianFour
variable {d k : ℕ}

/-- Positive masses of all strict winning cells imply distinct inducing vectors. -/
theorem injective_scores_of_positive_winning_masses
    (v : Fin k → Space d) (b : Fin k → ℝ)
    (hmass : ∀ i, 0 < (gaussian d).real (winningCell v b i)) :
    Function.Injective v := by
  intro i j he
  by_contra hij
  obtain ⟨x, hx⟩ := winning_nonempty_of_mass_pos v b i (hmass i)
  obtain ⟨y, hy⟩ := winning_nonempty_of_mass_pos v b j (hmass j)
  have hi := hx j (Ne.symm hij)
  have hj := hy i hij
  rw [he] at hi hj
  linarith

/-- A winning cell is contained in its normalized pairwise winning halfspace. -/
theorem winning_mass_le_pair_tail (v : Fin k → Space d) (b : Fin k → ℝ)
    (i j : Fin k) (hij : i ≠ j) (hv : v i ≠ v j) :
    (gaussian d).real (winningCell v b i) ≤
      gaussianTail ((b i - b j) / ‖v i - v j‖) := by
  let n : Space d := ‖v i - v j‖⁻¹ • (v i - v j)
  let t := (b i - b j) / ‖v i - v j‖
  have hnorm : 0 < ‖v i - v j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hv)
  have hn : ‖n‖ = 1 := by
    simp only [n, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm)]
    exact inv_mul_cancel₀ hnorm.ne'
  have hs : winningCell v b i ⊆ {x : Space d | t < ⟪n, x⟫} := by
    intro x hx
    have hw := hx j (Ne.symm hij)
    have hd : b i - b j < ⟪v i, x⟫ - ⟪v j, x⟫ := by linarith
    have h := (div_lt_div_iff_of_pos_right hnorm).mpr hd
    simpa only [t, n, real_inner_smul_left, inner_sub_left,
      div_eq_mul_inv, mul_comm, mem_setOf_eq] using h
  exact (measureReal_mono hs).trans_eq (gaussian_unit_halfspace_mass n hn t)

/-- Manuscript equation (10), for actual four-cell winning masses, all pairs,
and every ambient dimension. Distinctness is derived, not postulated. -/
theorem balanced_four_price_difference_bound
    (v : Fin 4 → Space d) (b : Fin 4 → ℝ)
    (hmass : ∀ i, (gaussian d).real (winningCell v b i) = 1 / 4)
    (i j : Fin 4) :
    |b i - b j| ≤ quarterQuantile * ‖v i - v j‖ := by
  have hv := injective_scores_of_positive_winning_masses v b (fun i => by
    rw [hmass i]; norm_num)
  have upper : ∀ i j : Fin 4, b i - b j ≤ quarterQuantile * ‖v i - v j‖ := by
    intro i j
    by_cases he : i = j
    · subst j; simp
    have hn : 0 < ‖v i - v j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hv.ne he))
    have hm := winning_mass_le_pair_tail v b i j he (hv.ne he)
    rw [hmass i] at hm
    have ht : (b i - b j) / ‖v i - v j‖ ≤ quarterQuantile := by
      by_contra h
      have hh := gaussianTail_strictAnti (lt_of_not_ge h)
      rw [quarterQuantile_tail] at hh
      linarith
    exact (div_le_iff₀ hn).mp ht
  apply abs_le.mpr
  constructor
  · have h := upper j i
    rw [norm_sub_rev] at h
    linarith
  · exact upper i j

end GaussianFour
