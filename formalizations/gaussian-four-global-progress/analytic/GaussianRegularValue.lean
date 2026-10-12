import GaussianScoreSymmetry
import GaussianMomentCovariance

open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace GaussianMeasureBridge
variable {d k : ℕ} [NeZero k]

lemma scoreMax_add_common (v : Fin k → Space d) (u : Space d)
    (b : Fin k → ℝ) (x : Space d) :
    scoreMax (fun i => v i + u) b x = scoreMax v b x + ⟪u, x⟫ := by
  apply le_antisymm
  · unfold scoreMax
    refine Finset.sup'_le _ _ fun i _ => ?_
    change ⟪v i + u, x⟫ - b i ≤ scoreMax v b x + ⟪u, x⟫
    rw [inner_add_left]
    have h := le_scoreMax v b x i
    linarith
  · have h : scoreMax v b x ≤ scoreMax (fun i => v i + u) b x - ⟪u, x⟫ := by
      unfold scoreMax
      refine Finset.sup'_le _ _ fun i _ => ?_
      change ⟪v i, x⟫ - b i ≤ scoreMax (fun i => v i + u) b x - ⟪u, x⟫
      have h := le_scoreMax (fun i => v i + u) b x i
      rw [inner_add_left] at h
      linarith
    linarith

lemma expectedScore_add_common (v : Fin k → Space d) (u : Space d) (b : Fin k → ℝ) :
    expectedScore (fun i => v i + u) b = expectedScore v b := by
  have hi : Integrable (fun x : Space d => ⟪u, x⟫) (gaussian d) := by
    simpa using integrable_score u 0
  have hz : (∫ x : Space d, ⟪u, x⟫ ∂gaussian d) = 0 := by
    simpa using integral_score u 0
  unfold expectedScore
  simp_rw [scoreMax_add_common]
  rw [integral_add (integrable_scoreMax v b) hi, hz, add_zero]

/-- A common translation of all scores has zero contribution because the
actual Gaussian is centered. -/
theorem equalMassValue_add_common (v : Fin k → Space d) (u : Space d) :
    equalMassValue (fun i => v i + u) = equalMassValue v := by
  unfold equalMassValue balancedValue priceObjective
  simp_rw [expectedScore_add_common]

noncomputable def standardMean (k : ℕ) : Space k :=
  WithLp.toLp 2 (fun _ => (k : ℝ)⁻¹)

noncomputable def centeredStandardRows (k : ℕ) : Fin k → Space k :=
  fun i => standardRows k i - standardMean k

noncomputable def regularRows (k : ℕ) : Fin k → Space k :=
  (Real.sqrt ((k - 1 : ℕ) : ℝ))⁻¹ • centeredStandardRows k

noncomputable def regularCovariance (k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  scoreGram (regularRows k)

noncomputable def simplexConstant (k : ℕ) [NeZero k] : ℝ :=
  expectedGaussianMaximum k / Real.sqrt ((k - 1 : ℕ) : ℝ)

lemma inner_standard_mean (i : Fin k) : ⟪standardRows k i, standardMean k⟫ = (k : ℝ)⁻¹ := by
  simp [standardRows, standardMean, PiLp.inner_apply]

lemma inner_mean_self : ⟪standardMean k, standardMean k⟫ = (k : ℝ)⁻¹ := by
  have hk : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne k)
  simp only [standardMean, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  change (∑ _i : Fin k, (k : ℝ)⁻¹ * (k : ℝ)⁻¹) = (k : ℝ)⁻¹
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

lemma scoreGram_centeredStandardRows (i j : Fin k) :
    scoreGram (centeredStandardRows k) i j = (if i = j then 1 else 0) - (k : ℝ)⁻¹ := by
  have hm : ⟪standardMean k, standardRows k j⟫ = (k : ℝ)⁻¹ := by
    rw [real_inner_comm]
    exact inner_standard_mean j
  unfold scoreGram centeredStandardRows
  rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_standard_mean,
    hm, inner_mean_self]
  have h : ⟪standardRows k i, standardRows k j⟫ = if i = j then 1 else 0 := by
    change scoreGram (standardRows k) i j = _
    rw [scoreGram_standardRows]
    rfl
  rw [h]
  ring

lemma centeredStandardRows_sum : ∑ i : Fin k, centeredStandardRows k i = 0 := by
  ext j
  simp [centeredStandardRows, standardRows, standardMean, PiLp.sub_apply,
    ne_of_gt (Nat.cast_pos.mpr (NeZero.pos k) : (0 : ℝ) < k)]

lemma regularRows_sum : ∑ i : Fin k, regularRows k i = 0 := by
  unfold regularRows
  simp only [Pi.smul_apply, ← Finset.smul_sum, centeredStandardRows_sum, smul_zero]

lemma regularCovariance_apply (i j : Fin k) :
    regularCovariance k i j = ((k - 1 : ℕ) : ℝ)⁻¹ *
      ((if i = j then 1 else 0) - (k : ℝ)⁻¹) := by
  unfold regularCovariance regularRows
  rw [scoreGram_smul, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  change ((k - 1 : ℕ) : ℝ)⁻¹ * scoreGram (centeredStandardRows k) i j = _
  rw [scoreGram_centeredStandardRows]

/-- This is exactly P/(k-1), centered, positive semidefinite and trace one. -/
theorem regularCovariance_normalized (hk : 2 ≤ k) : NormalizedCovariance (regularCovariance k) := by
  refine ⟨scoreGram_posSemidef _, ?_, ?_⟩
  · intro i
    change (∑ j, ⟪regularRows k i, regularRows k j⟫) = 0
    rw [← inner_sum, regularRows_sum, inner_zero_right]
  · have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne k)
    have hk1 : ((k - 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    unfold Matrix.trace Matrix.diag
    simp only [regularCovariance_apply, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_one]
    rw [hcast] at hk1 ⊢
    field_simp
    <;> ring

/-- Exact value at the regular covariance for all k≥2 (the formula itself is
also consistently defined at k=1). -/
theorem covarianceValue_regular : covarianceValue (regularCovariance k) = simplexConstant k := by
  rw [regularCovariance, covarianceValue_scoreGram, regularRows,
    equalMassValue_smul _ _ (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  have h : equalMassValue (centeredStandardRows k) = equalMassValue (standardRows k) := by
    change equalMassValue (fun i => standardRows k i + -standardMean k) = _
    exact equalMassValue_add_common (standardRows k) (-standardMean k)
  rw [h, equalMassValue_standardRows]
  simp only [simplexConstant, div_eq_mul_inv, mul_comm]

lemma simplexConstant_nonneg : 0 ≤ simplexConstant k := by
  rw [← covarianceValue_regular, regularCovariance, covarianceValue_scoreGram]
  exact balancedValue_nonneg _ _ uniformMass_pos sum_uniformMass

end GaussianMeasureBridge
