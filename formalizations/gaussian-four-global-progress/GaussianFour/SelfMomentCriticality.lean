import GaussianFour.CovarianceCriticality

/-! Actual Gaussian masses and self-moments at full-rank local extrema.
This is not a global comparison theorem or a perimeter theorem. -/
open MeasureTheory ProbabilityTheory Set Module Matrix Filter
open scoped RealInnerProductSpace Topology
open GaussianMeasureBridge
namespace GaussianFour

lemma offdiagonal_flux_of_scalar_laplacian
    (w : Fin 4 → Fin 4 → ℝ) (μ : ℝ)
    (hL : facetLaplacian w = μ • fourCentering)
    (i j : Fin 4) (hij : i ≠ j) : w i j = μ / 4 := by
  have h := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A i j) hL
  simp [facetLaplacian, fourCentering, Matrix.diagonal_apply, Matrix.one_apply,
    hij, smul_eq_mul] at h
  linarith

lemma centered_scalar_flux_self_moment {d : ℕ}
    (r m : Fin 4 → Space d) (w : Fin 4 → Fin 4 → ℝ) (μ : ℝ)
    (hz : ∑ i, r i = 0) (hL : facetLaplacian w = μ • fourCentering)
    (hf : ∀ i, m i = ∑ j, w i j • (r i-r j)) :
    ∀ i, m i = μ • r i := by
  intro i
  rw [hf i]
  have ht (j : Fin 4) : w i j • (r i-r j) = (μ / 4) • (r i-r j) := by
    by_cases hij : i = j
    · subst j; simp
    · rw [offdiagonal_flux_of_scalar_laplacian w μ hL i j hij]
  simp_rw [ht]
  rw [← Finset.smul_sum, Finset.sum_sub_distrib, hz, sub_zero]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  module

lemma balancedMoment_eq_setIntegral {d k : ℕ} [NeZero k]
    (v : Fin k → Space d) (i : Fin k) :
    balancedMoment v i = ∫ x in winningCell v (canonicalPrices v) i, x ∂gaussian d := by
  unfold balancedMoment rawWinningMoment
  rw [integral_indicator (measurableSet_winningCell _ _ _)]

/-- Every full-rank local extremum of the actual covariance objective induces
balanced Gaussian cells with moments C(Q) times the inducing vectors.
The multiplier is derived, positive, and not supplied as a hypothesis. -/
theorem actual_four_local_extremum_self_moments
    (Q : Matrix (Fin 4) (Fin 4) ℝ)
    (hQ : NormalizedCovariance Q) (hp : (principalCovariance Q).PosDef)
    (hlocal : IsLocalExtrOn covarianceValue
      {A : Matrix (Fin 4) (Fin 4) ℝ | NormalizedCovariance A} Q) :
    0 < covarianceValue Q ∧
    ∃ r : Fin 4 → Space 3, ∃ w : Fin 4 → Fin 4 → ℝ,
      AffineIndependent ℝ r ∧ scoreGram r = Q ∧ (∑ i, r i = 0) ∧
      (∀ i, (gaussian 3).real (winningCell r (canonicalPrices r) i) = 1/4) ∧
      (∀ i, (∫ x in winningCell r (canonicalPrices r) i, x ∂gaussian 3) =
        covarianceValue Q • r i) ∧
      (∀ i j, i ≠ j → w i j = covarianceValue Q / 4) ∧
      facetLaplacian w = covarianceValue Q • fourCentering := by
  obtain ⟨r,w,hr,hg,hwd,hwp,hws,hw,hL⟩ :=
    actual_four_covariance_local_extremum_flux Q hQ hp hlocal
  let μ : ℝ := (facetLaplacian w).trace / 3
  have hz : ∑ i, r i = 0 := sum_scores_zero_of_centered_gram r
    (by simpa only [hg] using hQ.2.1)
  have hm := centered_scalar_flux_self_moment r (balancedMoment r) w μ hz hL hw
  have hμ : 0 < μ := by
    have hpos := hwp 0 1 (by decide)
    rw [offdiagonal_flux_of_scalar_laplacian w μ hL 0 1 (by decide)] at hpos
    linarith
  have ht : (∑ i, ‖r i‖^2) = 1 := by
    have htr : (scoreGram r).trace = 1 := by rw [hg, hQ.2.2]
    simpa only [Matrix.trace, Matrix.diag_apply, scoreGram, real_inner_self_eq_norm_sq] using htr
  have heval : equalMassValue r = μ := by
    rw [← balancedMoment_value r hr.injective]
    simp_rw [hm, real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [← Finset.mul_sum, ht, mul_one]
  have hv : covarianceValue Q = μ := by
    rw [← hg, covarianceValue_scoreGram, heval]
  refine ⟨by rwa [hv], r, w, hr, hg, hz, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa [uniformMass] using canonicalPrices_balanced r hr.injective i
  · intro i
    rw [← balancedMoment_eq_setIntegral, hv]
    exact hm i
  · intro i j hij
    rw [hv]
    exact offdiagonal_flux_of_scalar_laplacian w μ hL i j hij
  · rw [hv]; exact hL

end GaussianFour
