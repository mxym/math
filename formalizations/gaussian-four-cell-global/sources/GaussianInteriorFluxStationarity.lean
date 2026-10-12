import GaussianCovarianceDifferential
import GaussianGramMomentTransport
import GaussianCovarianceStationarity
import GaussianRegularFlux
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option maxHeartbeats 10000000

/-!
First-order stationarity data at a full-rank covariance.

The covariance differential module originally returned a facet-weight matrix
existentially for each direction.  Here we pin the weights to one actual
balanced score realization.  Gram-isometric transport of the genuine Gaussian
moments and uniqueness of coefficients in a simplicial normal basis show that
the same weights work for every centered Hermitian direction.

This is an unconditional analytic lemma.  It does not assert that a
stationary covariance is regular; that classification is a separate global
problem.
-/

open MeasureTheory ProbabilityTheory Set Module Matrix Filter
open scoped RealInnerProductSpace Topology

namespace GaussianMeasureBridge

variable {d : ℕ}

def FixedFluxDerivative (d : ℕ)
    (Q : Matrix (Fin (d+2)) (Fin (d+2)) ℝ)
    (w : Fin (d+2) → Fin (d+2) → ℝ) : Prop :=
  ∀ D : Matrix (Fin (d+2)) (Fin (d+2)) ℝ,
    D.IsHermitian → (∀ i, (∑ j, D i j) = 0) →
    HasDerivAt (fun t : ℝ => covarianceValue (Q+t•D))
      ((facetLaplacian w*D).trace/2) 0

def FixedFluxSpec (d : ℕ)
    (Q : Matrix (Fin (d+2)) (Fin (d+2)) ℝ) : Prop :=
  ∃ r : Fin (d+2) → Space (d+1),
    ∃ w : Fin (d+2) → Fin (d+2) → ℝ,
    AffineIndependent ℝ r ∧ scoreGram r = Q ∧
    (∀ i, w i i = 0) ∧
    (∀ i j, i ≠ j → 0 < w i j) ∧
    (∀ i j, w i j = w j i) ∧
    (∀ i, balancedMoment r i = ∑ j, w i j • (r i-r j)) ∧
    FixedFluxDerivative d Q w

def CenteredDirectionalLocalMax (d : ℕ)
    (Q : Matrix (Fin (d+2)) (Fin (d+2)) ℝ) : Prop :=
  ∀ D : Matrix (Fin (d+2)) (Fin (d+2)) ℝ,
    D.IsHermitian → (∀ i, (∑ j, D i j) = 0) → D.trace = 0 →
    IsLocalMax (fun t : ℝ => covarianceValue (Q+t•D)) 0

theorem centered_covariance_fixed_flux_differential
    (Q : Matrix (Fin (d+2)) (Fin (d+2)) ℝ)
    (hQ : Q.IsHermitian)
    (hzQ : ∀ i, (∑ j, Q i j) = 0)
    (hprincipal : (principalCovariance Q).PosDef) :
    FixedFluxSpec d Q := by
  unfold FixedFluxSpec
  obtain ⟨r,hder,hderiv,hr,hg, _⟩ := centered_affine_covariance_score_lift Q 0
    hQ (by simp) hzQ (by simp) hprincipal
  obtain ⟨w,hw,hwp,w_sym,hf,_⟩ := actual_balanced_flux_energy (r 0) hr
  refine ⟨r 0,w,hr,hg,hw,hwp,w_sym,hf,?_⟩
  intro D hD hzD
  obtain ⟨u,hu0,huderiv,hu,hug,hugram⟩ := centered_affine_covariance_score_lift Q D
    hQ hD hzQ hzD hprincipal
  have hugram' : (fun t : ℝ => scoreGram (u t)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t : ℝ => scoreGram (u 0) + t • D) := by
    filter_upwards [hugram] with t ht
    rw [hug]
    exact ht
  obtain ⟨z,hz0,hzp,hzs,hzf,hzd⟩ := actual_affine_covariance_lift_derivative
    u hu0 hu huderiv D hugram'
  have hspan : ∀ i, balancedMoment (u 0) i = ∑ j,z i j • (u 0 i-u 0 j) := hzf
  obtain ⟨T,hTr,hTm⟩ := balancedMoment_gram_embedding (r 0) (u 0) hr
    (sum_rows_zero_of_gram_centered (r 0) (by simpa only [hg] using hzQ))
    (sum_rows_zero_of_gram_centered (u 0) (by simpa only [hug] using hzQ))
    (hg.trans hug.symm)
  have hcoeff : ∀ i j, i ≠ j → w i j = z i j := by
    intro i j hij
    apply (simplicial_flux_coefficients_unique (r 0) hr w z ?_) i j hij
    intro l
    have he := hf l
    have hz' := hzf l
    have hmapz : T (∑ j, z l j • (r 0 l-r 0 j)) =
        ∑ j, z l j • (u 0 l-u 0 j) := by
      rw [map_sum]
      simp only [map_smul, map_sub, hTr]
    have heq : T (∑ j, w l j • (r 0 l-r 0 j)) =
        T (∑ j, z l j • (r 0 l-r 0 j)) := by
      calc
        T (∑ j, w l j • (r 0 l-r 0 j)) = T (balancedMoment (r 0) l) := by rw [he]
        _ = balancedMoment (u 0) l := hTm l
        _ = ∑ j, z l j • (u 0 l-u 0 j) := hz'
        _ = T (∑ j, z l j • (r 0 l-r 0 j)) := hmapz.symm
    exact T.injective heq
  have hzw : z = w := by
    funext i j
    by_cases hij : i=j
    · subst j
      exact (hz0 i).trans (hw i).symm
    · exact (hcoeff i j hij).symm
  rw [hug] at hzd
  simpa only [hzw] using hzd

theorem centered_local_max_flux_stationary
    (Q : Matrix (Fin (d+2)) (Fin (d+2)) ℝ)
    (hQ : Q.IsHermitian)
    (hzQ : ∀ i, (∑ j, Q i j) = 0)
    (hprincipal : (principalCovariance Q).PosDef)
    (hmax : CenteredDirectionalLocalMax d Q) :
    ∃ w : Fin (d+2) → Fin (d+2) → ℝ,
      (∀ i, w i i = 0) ∧
      (∀ i j, i ≠ j → 0 < w i j) ∧
      (∀ i j, w i j = w j i) ∧
      ∀ D : Matrix (Fin (d+2)) (Fin (d+2)) ℝ,
        D.IsHermitian → (∀ i, (∑ j, D i j) = 0) → D.trace = 0 →
        (facetLaplacian w*D).trace = 0 := by
  obtain ⟨r,w,hr,hg,hw,hp,hs,_,hder⟩ :=
    centered_covariance_fixed_flux_differential Q hQ hzQ hprincipal
  refine ⟨w,hw,hp,hs,?_⟩
  intro D hD hzD htD
  have hloc := hmax D hD hzD htD
  have hzero : deriv (fun t : ℝ => covarianceValue (Q+t•D)) 0 = 0 :=
    hloc.deriv_eq_zero
  have hd := hder D hD hzD
  rw [hd.deriv] at hzero
  linarith

end GaussianMeasureBridge
