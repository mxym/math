import GaussianFour.FluxUniqueness

/-! One actual Gaussian flux matrix for every centered covariance direction.
The coefficient family is chosen before the universally quantified direction. -/
open MeasureTheory ProbabilityTheory Set Module Matrix Filter
open scoped RealInnerProductSpace Topology
open GaussianMeasureBridge
namespace GaussianFour
variable {d : ℕ}

theorem actual_centered_covariance_fixed_differential
    (Q : Matrix (Fin (d+2)) (Fin (d+2)) ℝ)
    (hQ : Q.IsHermitian) (hzQ : ∀ i, (∑ j, Q i j) = 0)
    (hp : (principalCovariance Q).PosDef) :
    ∃ r : Fin (d+2) → Space (d+1), ∃ w : Fin (d+2) → Fin (d+2) → ℝ,
      AffineIndependent ℝ r ∧ scoreGram r = Q ∧
      (∀ i, w i i = 0) ∧ (∀ i j, i ≠ j → 0 < w i j) ∧
      (∀ i j, w i j = w j i) ∧
      (∀ i, balancedMoment r i = ∑ j, w i j • (r i-r j)) ∧
      covarianceValue Q = (∑ i, ∑ j, w i j * ‖r i-r j‖^2) / 2 ∧
      ∀ D : Matrix (Fin (d+2)) (Fin (d+2)) ℝ,
        D.IsHermitian → (∀ i, (∑ j, D i j) = 0) →
        HasDerivAt (fun t : ℝ => covarianceValue (Q+t•D))
          ((facetLaplacian w*D).trace / 2) 0 := by
  obtain ⟨r,w,hr,hg,hwd,hwp,hws,hw,hval,_⟩ :=
    actual_centered_covariance_differential Q 0 hQ (by simp) hzQ (by simp) hp
  refine ⟨r,w,hr,hg,hwd,hwp,hws,hw,hval,?_⟩
  intro D hD hzD
  obtain ⟨u,z,hu,hgu,hzd,hzp,hzs,hz,hvalz,hderiv⟩ :=
    actual_centered_covariance_differential Q D hQ hD hzQ hzD hp
  have hrz : ∑ i, r i = 0 :=
    sum_scores_zero_of_centered_gram r (by simpa only [hg] using hzQ)
  have huz : ∑ i, u i = 0 :=
    sum_scores_zero_of_centered_gram u (by simpa only [hgu] using hzQ)
  have he : w = z := balanced_flux_eq_of_gram_eq r u hr hu hrz huz
    (hg.trans hgu.symm) w z hwd hzd hws hzs hw hz
  simpa only [← he] using hderiv

end GaussianFour
