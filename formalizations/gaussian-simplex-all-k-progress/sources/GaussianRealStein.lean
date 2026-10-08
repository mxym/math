import GaussianWeightedHalflineFlux

/-! The genuine whole-line Gaussian Stein identity for compact C1 tests.
It is derived from compact-support calculus, not used as a distributional axiom. -/
open MeasureTheory ProbabilityTheory
namespace GaussianMeasureBridge

theorem gaussianReal_stein_integral_zero
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    (∫ x,deriv f x-x*f x ∂gaussianReal 0 1) = 0 := by
  let g : ℝ → ℝ := fun x => f x*standardDensity x
  have hg : ContDiff ℝ 1 g := hf.mul standardDensity_contDiff
  have hsg : HasCompactSupport g := hs.mul_right
  have hi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hsg
  have hid : Integrable (deriv g) :=
    (hg.continuous_deriv le_rfl).integrable_of_hasCompactSupport hsg.deriv
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable
    (fun x => (hg.differentiable one_ne_zero x).hasDerivAt) hid hi
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  have he : (fun x : ℝ => gaussianPDFReal 0 1 x • (deriv f x-x*f x)) = deriv g := by
    funext x
    have hd := ((hf.differentiable one_ne_zero x).hasDerivAt.mul
      (standardDensity_hasDerivAt x)).deriv
    change standardDensity x*(deriv f x-x*f x) = deriv (f*standardDensity) x
    rw [hd]
    ring
  rw [he]
  exact hz

end GaussianMeasureBridge
