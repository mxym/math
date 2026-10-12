import GaussianCenteredAffineLift
import GaussianAffineLiftDerivative

/-! The full actual covariance differential on the centered positive cone.
The differentiable lift exists by theorem, and every coefficient is derived
from actual balanced Gaussian winning moments. -/
open MeasureTheory ProbabilityTheory Set Module Matrix Filter
open scoped RealInnerProductSpace Topology
namespace GaussianMeasureBridge
variable {d : ℕ}

theorem actual_centered_covariance_differential
    (Q D : Matrix (Fin (d+2)) (Fin (d+2)) ℝ)
    (hQ : Q.IsHermitian) (hD : D.IsHermitian)
    (hzQ : ∀ i, (∑ j,Q i j) = 0) (hzD : ∀ i, (∑ j,D i j) = 0)
    (hp : (principalCovariance Q).PosDef) :
    ∃ r : Fin (d+2) → Space (d+1), ∃ w : Fin (d+2) → Fin (d+2) → ℝ,
      AffineIndependent ℝ r ∧ scoreGram r = Q ∧
      (∀ i, w i i = 0) ∧ (∀ i j, i ≠ j → 0 < w i j) ∧
      (∀ i j, w i j = w j i) ∧
      (∀ i, balancedMoment r i = ∑ j, w i j • (r i-r j)) ∧
      covarianceValue Q = (∑ i,∑ j,w i j*‖r i-r j‖^2)/2 ∧
      HasDerivAt (fun t : ℝ => covarianceValue (Q+t•D)) ((facetLaplacian w*D).trace/2) 0 := by
  obtain ⟨v,h,hd,hv,hg,ht⟩ := centered_affine_covariance_score_lift Q D hQ hD hzQ hzD hp
  have ht' : (fun t : ℝ => scoreGram (v t)) =ᶠ[𝓝 (0:ℝ)]
      (fun t : ℝ => scoreGram (v 0)+t•D) := by simpa only [hg] using ht
  obtain ⟨w,hw,hp,hs,hf,hc⟩ := actual_affine_covariance_lift_derivative v h hv hd D ht'
  refine ⟨v 0,w,hv,hg,hw,hp,hs,hf,?_,?_⟩
  · calc
      covarianceValue Q = equalMassValue (v 0) := by rw [← hg,covarianceValue_scoreGram]
      _ = (∑ i,∑ j,w i j*‖v 0 i-v 0 j‖^2)/2 := by
        rw [← balancedMoment_value (v 0) hv.injective]
        exact symmetric_flux_energy _ _ w hs hf
  · simpa only [hg] using hc

end GaussianMeasureBridge
