import GaussianPartition
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Actual Gaussian boundary flux on a half-line. This is a base case for
polyhedral flux; it does not assert an unproved multidimensional divergence theorem. -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace GaussianMeasureBridge

noncomputable def standardDensity (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

lemma standardDensity_eq (x : ℝ) :
    standardDensity x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) := by
  simp [standardDensity, gaussianPDFReal]

lemma standardDensity_pos (x : ℝ) : 0 < standardDensity x :=
  gaussianPDFReal_pos 0 1 x one_ne_zero

lemma standardDensity_hasDerivAt (x : ℝ) :
    HasDerivAt standardDensity (-x * standardDensity x) x := by
  convert (((hasDerivAt_id x).pow 2).neg.div_const 2).exp.const_mul
    (Real.sqrt (2 * Real.pi))⁻¹ using 1
  · ext y
    simp [standardDensity_eq]
  · simp only [Pi.neg_apply, Pi.pow_apply, id_eq]
    rw [standardDensity_eq]
    ring

lemma standardDensity_tendsto_zero : Tendsto standardDensity atTop (𝓝 0) := by
  have hsq : Tendsto (fun x : ℝ => x ^ 2) atTop atTop :=
    tendsto_pow_atTop (by decide : 2 ≠ 0)
  have harg : Tendsto (fun x : ℝ => -(x ^ 2) / 2) atTop atBot := by
    exact (tendsto_neg_atTop_atBot.comp hsq).atBot_div_const (by norm_num : (0 : ℝ) < 2)
  have h := (Real.tendsto_exp_atBot.comp harg).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  have he : standardDensity = (fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2)) :=
    funext standardDensity_eq
  rw [he]
  simpa only [mul_zero, Function.comp_apply] using h

lemma integrable_mul_standardDensity : Integrable (fun x : ℝ => x * standardDensity x) := by
  have h := (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  convert h using 1
  ext x
  rw [standardDensity_eq]
  have he : -(1 / 2 : ℝ) * x ^ 2 = -(x ^ 2) / 2 := by ring
  rw [he]
  ring

/-- The Euclidean-density half-line flux identity, including arbitrary real
boundary location. -/
theorem integral_Ioi_mul_standardDensity (a : ℝ) :
    (∫ x in Ioi a, x * standardDensity x) = standardDensity a := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := a) (f := standardDensity) (f' := fun x => -x * standardDensity x)
    (fun x _ => standardDensity_hasDerivAt x)
    (by
      convert integrable_mul_standardDensity.neg.integrableOn using 1
      funext x
      simp only [Pi.neg_apply, neg_mul])
    standardDensity_tendsto_zero
  simp only [neg_mul, integral_neg, zero_sub] at h
  linarith

/-- The same identity for the actual Gaussian probability measure. -/
theorem gaussianReal_halfline_firstMoment (a : ℝ) :
    (∫ x in Ioi a, x ∂gaussianReal 0 1) = standardDensity a := by
  rw [← integral_indicator measurableSet_Ioi,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  have he : (fun x : ℝ => gaussianPDFReal 0 1 x • (Ioi a).indicator (fun x => x) x) =
      (Ioi a).indicator (fun x => x * standardDensity x) := by
    ext x
    by_cases hx : x ∈ Ioi a <;> simp [hx, standardDensity, mul_comm]
  rw [he, integral_indicator measurableSet_Ioi, integral_Ioi_mul_standardDensity]

end GaussianMeasureBridge
