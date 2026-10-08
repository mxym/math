import GaussianHalflineFlux
import GaussianCoordinateSplit
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! The explicit smooth positive Euclidean Gaussian density, with actual
derivative and uniform lower bounds on bounded sets. These analytic facts
prepare the local Gaussian-to-Lebesgue BV comparison. -/
open MeasureTheory ProbabilityTheory Module Set Filter
open scoped Topology ENNReal ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

noncomputable def gaussianLebesgueDensity (d : ℕ) (x : Space d) : ℝ :=
  (Real.sqrt (2*Real.pi))⁻¹ ^ d * Real.exp (-‖x‖^2/2)

lemma gaussianDensity_constant_pos (d : ℕ) :
    0 < (Real.sqrt (2*Real.pi))⁻¹ ^ d := by
  exact pow_pos (inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))) _

lemma gaussianLebesgueDensity_pos (x : Space d) : 0 < gaussianLebesgueDensity d x :=
  mul_pos (gaussianDensity_constant_pos d) (Real.exp_pos _)

lemma gaussianLebesgueDensity_contDiff (d : ℕ) : ContDiff ℝ ∞ (gaussianLebesgueDensity d) := by
  unfold gaussianLebesgueDensity
  have hn : ContDiff ℝ ∞ (fun x : Space d => ‖x‖^2) := contDiff_norm_sq ℝ
  fun_prop

lemma gaussianLebesgueDensity_product (x : Space d) :
    (∏ i : Fin d,standardDensity (x i))=gaussianLebesgueDensity d x := by
  simp_rw [standardDensity_eq]
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    ← Real.exp_sum]
  unfold gaussianLebesgueDensity
  congr 2
  rw [← Finset.sum_div,Finset.sum_neg_distrib,EuclideanSpace.real_norm_sq_eq]

lemma gaussianLebesgueDensity_hasFDerivAt (x : Space d) :
    HasFDerivAt (gaussianLebesgueDensity d) (-gaussianLebesgueDensity d x • innerSL ℝ x) x := by
  have hn := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have ha : HasFDerivAt (fun y : Space d => -‖y‖^2/2) (-innerSL ℝ x) x := by
    convert hn.const_smul (-1/2 : ℝ) using 1
    · funext y
      simp only [Pi.smul_apply,smul_eq_mul]
      ring
    · ext u
      simp only [neg_apply,smul_apply,smul_eq_mul]
      ring
  have hh := ha.exp.const_smul ((Real.sqrt (2*Real.pi))⁻¹ ^ d)
  convert hh using 1
  · funext y
    simp only [Pi.smul_apply,smul_eq_mul,gaussianLebesgueDensity]
  · ext u
    simp only [smul_apply,neg_apply,smul_eq_mul,gaussianLebesgueDensity]
    ring

lemma gaussianLebesgueDensity_fderiv (x : Space d) :
    fderiv ℝ (gaussianLebesgueDensity d) x = -gaussianLebesgueDensity d x • innerSL ℝ x :=
  (gaussianLebesgueDensity_hasFDerivAt x).fderiv

lemma gaussianLebesgueDensity_lower_on_ball (R : ℝ) (hR : 0 ≤ R)
    (x : Space d) (hx : ‖x‖ ≤ R) :
    (Real.sqrt (2*Real.pi))⁻¹ ^ d * Real.exp (-R^2/2) ≤ gaussianLebesgueDensity d x := by
  unfold gaussianLebesgueDensity
  apply mul_le_mul_of_nonneg_left _ (gaussianDensity_constant_pos d).le
  apply Real.exp_le_exp.mpr
  nlinarith [norm_nonneg x]

lemma gaussianLebesgueDensity_upper (x : Space d) :
    gaussianLebesgueDensity d x ≤ (Real.sqrt (2*Real.pi))⁻¹ ^ d := by
  unfold gaussianLebesgueDensity
  apply mul_le_of_le_one_right (gaussianDensity_constant_pos d).le
  exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖x‖])

end GaussianMeasureBridge
