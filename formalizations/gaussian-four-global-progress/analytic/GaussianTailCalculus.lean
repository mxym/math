import GaussianPolyhedralGraphFlux
import GaussianTail
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue

/-! Calculus of actual Gaussian tail probabilities. This supports a slicing
proof of price sensitivities for polyhedral cells. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace GaussianMeasureBridge

noncomputable def standardTail (a : ℝ) : ℝ := (gaussianReal 0 1).real (Ioi a)

lemma standardTail_eq_integral (a : ℝ) :
    standardTail a = ∫ x in Ioi a, standardDensity x := by
  have h : (∫ x : ℝ, (Ioi a).indicator (fun _ => (1 : ℝ)) x ∂gaussianReal 0 1) =
      standardTail a := by
    simpa [standardTail] using integral_indicator_const (μ := gaussianReal 0 1)
      (1 : ℝ) (measurableSet_Ioi (a := a))
  rw [← h, integral_gaussianReal_eq_integral_smul one_ne_zero]
  have he : (fun x : ℝ => gaussianPDFReal 0 1 x • (Ioi a).indicator (fun _ => (1 : ℝ)) x) =
      (Ioi a).indicator standardDensity := by
    ext x
    by_cases hx : x ∈ Ioi a <;> simp [hx, standardDensity]
  rw [he, integral_indicator measurableSet_Ioi]

lemma standardTail_eq_primitive (a : ℝ) :
    standardTail a = standardTail 0 - ∫ x in (0 : ℝ)..a, standardDensity x := by
  have hi : Integrable standardDensity := integrable_gaussianPDFReal 0 1
  have h := intervalIntegral.integral_Ioi_sub_Ioi'
    (a := (0 : ℝ)) (b := a) hi.integrableOn hi.integrableOn
  rw [← standardTail_eq_integral, ← standardTail_eq_integral] at h
  linarith

/-- Derivative of the actual upper-tail probability at every real boundary. -/
theorem standardTail_hasDerivAt (a : ℝ) :
    HasDerivAt standardTail (-standardDensity a) a := by
  have hd := intervalIntegral.integral_hasDerivAt_right
    (continuous_standardDensity.intervalIntegrable (0 : ℝ) a)
    continuous_standardDensity.stronglyMeasurable.stronglyMeasurableAtFilter
    continuous_standardDensity.continuousAt
  convert hd.const_sub (standardTail 0) using 1
  · exact funext standardTail_eq_primitive

theorem standardTail_lipschitz : LipschitzWith ⟨standardDensity 0, (standardDensity_pos 0).le⟩
    standardTail := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun a => (standardTail_hasDerivAt a).differentiableAt)
  intro a
  rw [(standardTail_hasDerivAt a).deriv]
  change ‖-standardDensity a‖ ≤ standardDensity 0
  rw [norm_neg, Real.norm_eq_abs, abs_of_pos (standardDensity_pos a)]
  exact standardDensity_le_zero a

end GaussianMeasureBridge
