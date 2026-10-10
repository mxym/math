import GaussianFour.FixedCovarianceDifferential
import GaussianFour.CenteredSpectral
import Mathlib.Analysis.Calculus.LocalExtr.LineDeriv

/-! First-order stationarity of actual four-cell Gaussian covariance extrema.
No perimeter comparison, Hessian, or global sharp inequality is assumed. -/
open MeasureTheory ProbabilityTheory Set Module Matrix Filter
open scoped RealInnerProductSpace Topology
open GaussianMeasureBridge
namespace GaussianFour

/-- Every centered trace-zero direction is genuinely feasible on a two-sided
neighborhood at a covariance with positive principal block. -/
theorem centered_trace_direction_eventually_feasible
    (Q D : Matrix (Fin 4) (Fin 4) ℝ)
    (hQ : NormalizedCovariance Q) (hp : (principalCovariance Q).PosDef)
    (hD : D.IsHermitian) (hzD : ∀ i, (∑ j, D i j) = 0) (htD : D.trace = 0) :
    ∀ᶠ t : ℝ in 𝓝 0, NormalizedCovariance (Q+t•D) := by
  obtain ⟨v,h,hd,hv,hg,he⟩ := centered_affine_covariance_score_lift
    Q D hQ.1.isHermitian hD hQ.2.1 hzD hp
  filter_upwards [he] with t ht
  refine ⟨?_, ?_, ?_⟩
  · rw [← ht]; exact scoreGram_posSemidef (v t)
  · intro i
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum, hQ.2.1, hzD, mul_zero, add_zero]
  · rw [Matrix.trace_add, Matrix.trace_smul, hQ.2.2, htD]
    simp

/-- Fermat's theorem on the actual normalized Gaussian covariance set. -/
theorem covariance_local_extremum_direction_zero
    (Q D : Matrix (Fin 4) (Fin 4) ℝ)
    (hQ : NormalizedCovariance Q) (hp : (principalCovariance Q).PosDef)
    (hlocal : IsLocalExtrOn covarianceValue
      {A : Matrix (Fin 4) (Fin 4) ℝ | NormalizedCovariance A} Q)
    (hD : D.IsHermitian) (hzD : ∀ i, (∑ j, D i j) = 0) (htD : D.trace = 0)
    (c : ℝ) (hc : HasDerivAt (fun t : ℝ => covarianceValue (Q+t•D)) c 0) : c = 0 := by
  have he := centered_trace_direction_eventually_feasible Q D hQ hp hD hzD htD
  have ht : Tendsto (fun t : ℝ => Q+t•D) (𝓝 0)
      (𝓝[{A : Matrix (Fin 4) (Fin 4) ℝ | NormalizedCovariance A}] Q) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,he⟩
    simpa using (show ContinuousAt (fun t : ℝ => Q+t•D) 0 by fun_prop).tendsto
  exact IsExtrFilter.hasLineDerivAt_eq_zero hlocal hc ht

/-- One fixed actual winning-moment flux family satisfies the centered spectral
stationarity equation at every full-rank local extremum of the original value. -/
theorem actual_four_covariance_local_extremum_flux
    (Q : Matrix (Fin 4) (Fin 4) ℝ)
    (hQ : NormalizedCovariance Q) (hp : (principalCovariance Q).PosDef)
    (hlocal : IsLocalExtrOn covarianceValue
      {A : Matrix (Fin 4) (Fin 4) ℝ | NormalizedCovariance A} Q) :
    ∃ r : Fin 4 → Space 3, ∃ w : Fin 4 → Fin 4 → ℝ,
      AffineIndependent ℝ r ∧ scoreGram r = Q ∧
      (∀ i, w i i = 0) ∧ (∀ i j, i ≠ j → 0 < w i j) ∧
      (∀ i j, w i j = w j i) ∧
      (∀ i, balancedMoment r i = ∑ j, w i j • (r i-r j)) ∧
      facetLaplacian w = ((facetLaplacian w).trace / 3) • fourCentering := by
  obtain ⟨r,w,hr,hg,hwd,hwp,hws,hw,hvalue,hderiv⟩ :=
    actual_centered_covariance_fixed_differential Q hQ.1.isHermitian hQ.2.1 hp
  refine ⟨r,w,hr,hg,hwd,hwp,hws,hw,?_⟩
  apply centered_trace_stationary_eq_scalar (facetLaplacian w)
    (facetLaplacian_symmetric w hws) (facetLaplacian_row_sum w)
  intro D hD hzD htD
  have h := covariance_local_extremum_direction_zero Q D hQ hp hlocal hD hzD htD
    _ (hderiv D hD hzD)
  linarith

end GaussianFour
