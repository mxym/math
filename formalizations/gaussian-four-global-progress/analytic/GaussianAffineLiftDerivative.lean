import GaussianFacetLaplacian

/-! The full Laplacian covariance differential for an actual differentiable
lift of an affine covariance path. The conclusion is about covarianceValue;
the lift and its Gram identity are explicitly required and checked. -/
open MeasureTheory ProbabilityTheory Set Module Matrix Filter
open scoped RealInnerProductSpace Topology
namespace GaussianMeasureBridge
variable {d : ℕ}

theorem actual_affine_covariance_lift_derivative
    (v : ℝ → Fin (d+2) → Space (d+1)) (h : Fin (d+2) → Space (d+1))
    (hv : AffineIndependent ℝ (v 0)) (hd : HasDerivAt v h 0)
    (D : Matrix (Fin (d+2)) (Fin (d+2)) ℝ)
    (hgram : (fun t : ℝ => scoreGram (v t)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t : ℝ => scoreGram (v 0) + t • D)) :
    ∃ w : Fin (d+2) → Fin (d+2) → ℝ,
      (∀ i, w i i = 0) ∧ (∀ i j, i ≠ j → 0 < w i j) ∧
      (∀ i j, w i j = w j i) ∧
      (∀ i, balancedMoment (v 0) i = ∑ j, w i j • (v 0 i - v 0 j)) ∧
      HasDerivAt (fun t : ℝ => covarianceValue (scoreGram (v 0) + t • D))
        ((facetLaplacian w * D).trace / 2) 0 := by
  obtain ⟨w,hw,hp,hs,hf,hc⟩ := actual_covariance_score_path_derivative v 0 h hv hd
  have he : scoreGramVelocity (v 0) h = D := by
    ext i j
    have hg : HasDerivAt (fun t : ℝ => scoreGram (v 0) i j + t * D i j) (D i j) 0 := by
      convert ((hasDerivAt_id (0 : ℝ)).mul_const (D i j)).const_add (scoreGram (v 0) i j) using 1
      · rfl
      · ring
    have heq : (fun t : ℝ => ⟪v t i,v t j⟫) =ᶠ[𝓝 (0:ℝ)]
        (fun t : ℝ => scoreGram (v 0) i j + t * D i j) := by
      filter_upwards [hgram] with t ht
      exact congrArg (fun A => A i j) ht
    exact ((hasDerivAt_pi.mp hd i).inner ℝ (hasDerivAt_pi.mp hd j)).unique
      (hg.congr_of_eventuallyEq heq)
  rw [he,fluxCovarianceDifferential_eq_trace w hs D] at hc
  refine ⟨w,hw,hp,hs,hf,?_⟩
  apply hc.congr_of_eventuallyEq
  exact hgram.mono fun t ht => congrArg covarianceValue ht.symm

end GaussianMeasureBridge
