import GaussianHalflineFlux
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Weighted Gaussian boundary flux for genuine C1 compactly supported test
functions. This is the integration-by-parts base for intrinsic BV perimeter
and first variations, extending the earlier constant-test moment formula. -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace GaussianMeasureBridge

lemma standardDensity_contDiff : ContDiff ℝ 1 standardDensity := by
  have he : standardDensity = (fun x : ℝ =>
      (Real.sqrt (2*Real.pi))⁻¹*Real.exp (-(x^2)/2)) := funext standardDensity_eq
  rw [he]
  fun_prop

theorem gaussianReal_halfline_weighted_flux
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) (a : ℝ) :
    (∫ x in Ioi a,deriv f x-x*f x ∂gaussianReal 0 1) = -standardDensity a*f a := by
  have hprod : ContDiff ℝ 1 (fun x => f x*standardDensity x) := hf.mul standardDensity_contDiff
  have hsupport : HasCompactSupport (fun x => f x*standardDensity x) := hs.mul_right
  have hder (x : ℝ) : deriv (fun y => f y*standardDensity y) x =
      standardDensity x*(deriv f x-x*f x) := by
    have he := ((hf.differentiable one_ne_zero x).hasDerivAt.mul
      (standardDensity_hasDerivAt x)).deriv
    change deriv (f*standardDensity) x = _
    rw [he]
    ring
  rw [← integral_indicator measurableSet_Ioi,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  have hi : (fun x : ℝ => gaussianPDFReal 0 1 x •
      (Ioi a).indicator (fun x => deriv f x-x*f x) x) =
      (Ioi a).indicator (fun x => deriv (fun y => f y*standardDensity y) x) := by
    funext x
    by_cases hx : x ∈ Ioi a
    · simp only [Set.indicator_of_mem hx,smul_eq_mul]
      exact (hder x).symm
    · simp only [Set.indicator_of_notMem hx,smul_zero]
  rw [hi,integral_indicator measurableSet_Ioi,hsupport.integral_Ioi_deriv_eq hprod a]
  ring

end GaussianMeasureBridge
