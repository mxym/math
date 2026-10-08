import GaussianMomentSymmetry

/-! Exact first moments and attained energy of the actual regular-simplex
winning partition, for every number of labels. This proves attainability
independently of the remaining universal upper bound. -/
open MeasureTheory ProbabilityTheory Set Matrix
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {k : ℕ} [NeZero k]

lemma standardMoment_diagonal_value (i : Fin k) :
    (k : ℝ) * standardMoment k i i = expectedGaussianMaximum k := by
  have h := standardMoment_trace (k := k)
  have he : (∑ j : Fin k, standardMoment k j j) = (k : ℝ) * standardMoment k i i := by
    simp_rw [standardMoment_diagonal (k := k) _ i]
    simp
  rwa [he] at h

lemma standardMoment_row_sum (i : Fin k) : ∑ j : Fin k, standardMoment k i j = 0 := by
  have h := congrArg (fun x : Space k => x i) (standardMoment_sum (k := k))
  simpa [standardMoment_symmetric (k := k) i] using h

lemma standardMoment_offdiagonal_value (i j : Fin k) (hij : i ≠ j) :
    ((k : ℝ) - 1) * standardMoment k i j = -standardMoment k i i := by
  have he (l : Fin k) : standardMoment k i l =
      (if l = i then standardMoment k i i - standardMoment k i j else 0) +
      standardMoment k i j := by
    by_cases hli : l = i
    · subst l; simp
    · rw [if_neg hli, zero_add]
      exact standardMoment_offdiagonal_row i l j (Ne.symm hli) hij
  have h := standardMoment_row_sum (k := k) i
  rw [Finset.sum_congr rfl (fun l _ => he l), Finset.sum_add_distrib] at h
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  linarith

/-- Actual Gaussian moments of the coordinate-maximum cells, obtained by
permutation symmetry and zero Gaussian mean. -/
theorem standardMoment_formula (hk : 2 ≤ k) (i : Fin k) :
    standardMoment k i =
      (expectedGaussianMaximum k / ((k : ℝ) - 1)) • centeredStandardRows k i := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne k)
  have hk1 : (k : ℝ) - 1 ≠ 0 := by
    have hh : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  ext j
  have hd := standardMoment_diagonal_value (k := k) i
  change standardMoment k i j =
    (expectedGaussianMaximum k / ((k : ℝ) - 1)) *
      (standardRows k i j - standardMean k j)
  have hs : standardRows k i j = if i = j then 1 else 0 := by
    simp [standardRows, EuclideanSpace.basisFun_apply, eq_comm]
  rw [hs]
  change _ = (expectedGaussianMaximum k / ((k : ℝ) - 1)) *
    ((if i = j then 1 else 0) - (k : ℝ)⁻¹)
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    field_simp
    nlinarith
  · rw [if_neg hij]
    have ho := standardMoment_offdiagonal_value i j hij
    field_simp
    nlinarith

lemma regularRows_injective (hk : 2 ≤ k) : Function.Injective (regularRows k) := by
  have hn : (Real.sqrt ((k - 1 : ℕ) : ℝ))⁻¹ ≠ 0 := by
    apply inv_ne_zero
    apply Real.sqrt_ne_zero'.mpr
    exact_mod_cast (show 0 < k - 1 by omega)
  intro i j h
  apply standardRows_injective
  have he : centeredStandardRows k i = centeredStandardRows k j :=
    (smul_right_injective _ hn) h
  exact sub_left_inj.mp he

lemma winningCell_regular_zero (hk : 2 ≤ k) (i : Fin k) :
    winningCell (regularRows k) 0 i = winningCell (standardRows k) 0 i := by
  have hn : 0 < (Real.sqrt ((k - 1 : ℕ) : ℝ))⁻¹ := by
    apply inv_pos.mpr
    apply Real.sqrt_pos.mpr
    exact_mod_cast (show 0 < k - 1 by omega)
  ext x
  simp only [winningCell, mem_setOf_eq, regularRows, Pi.smul_apply,
    centeredStandardRows, Pi.zero_apply, sub_zero, real_inner_smul_left, inner_sub_left,
    mul_lt_mul_iff_right₀ hn, sub_lt_sub_iff_right]

noncomputable def regularWinningPartition (hk : 2 ≤ k) : FractionalPartition k k :=
  winningPartition (regularRows k) 0 (regularRows_injective hk)

theorem regularWinningPartition_balanced (hk : 2 ≤ k) (i : Fin k) :
    (regularWinningPartition hk).mass i = uniformMass k i := by
  rw [regularWinningPartition, winningPartition_mass, winningCell_regular_zero hk]
  have h := canonicalPrices_balanced (standardRows k) standardRows_injective i
  rwa [canonicalPrices_standard] at h

theorem regularWinningPartition_moment (hk : 2 ≤ k) (i : Fin k) :
    (regularWinningPartition hk).moment i = simplexConstant k • regularRows k i := by
  rw [regularWinningPartition, ← rawWinningMoment_eq]
  unfold rawWinningMoment
  rw [winningCell_regular_zero hk]
  change standardMoment k i = _
  rw [standardMoment_formula hk, regularRows, Pi.smul_apply, smul_smul]
  congr 1
  have hn : Real.sqrt ((k - 1 : ℕ) : ℝ) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by exact_mod_cast (show 0 < k - 1 by omega))
  have hc : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_one]
  rw [simplexConstant, div_eq_mul_inv, div_eq_mul_inv, mul_assoc,
    ← mul_inv, ← pow_two, Real.sq_sqrt (Nat.cast_nonneg (k-1)), hc]

/-- The actual regular winning partition attains the proposed constant for
all k≥2. No universal comparison theorem is used in this assertion. -/
theorem regularWinningPartition_energy (hk : 2 ≤ k) :
    (regularWinningPartition hk).momentEnergy = simplexConstant k ^ 2 := by
  rw [← FractionalPartition.trace_scoreGram_moment]
  have hm : (regularWinningPartition hk).moment = simplexConstant k • regularRows k := by
    funext i; exact regularWinningPartition_moment hk i
  rw [hm, scoreGram_smul, Matrix.trace_smul]
  change simplexConstant k ^ 2 * (regularCovariance k).trace = _
  rw [(regularCovariance_normalized hk).2.2, mul_one]

end GaussianMeasureBridge
