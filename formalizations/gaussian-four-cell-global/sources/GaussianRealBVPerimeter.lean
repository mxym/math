import GaussianWeightedHalflineFlux
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! The classical variational Gaussian perimeter on the real line.
Compact smooth test fields give its exact half-line value; the lower bound
uses an actual smooth bump equal to one at the boundary. -/
open MeasureTheory ProbabilityTheory Set Metric
open scoped Topology ENNReal ContDiff
namespace GaussianMeasureBridge

structure GaussianRealTestField where
  toFun : ℝ → ℝ
  smooth : ContDiff ℝ ∞ toFun
  compact : HasCompactSupport toFun
  norm_le : ∀ x,‖toFun x‖ ≤ 1

instance : CoeFun GaussianRealTestField (fun _ => ℝ → ℝ) := ⟨GaussianRealTestField.toFun⟩

noncomputable def gaussianRealBVPerimeter (S : Set ℝ) : ℝ≥0∞ :=
  ⨆ X : GaussianRealTestField,ENNReal.ofReal (∫ x in S,deriv X x-x*X x ∂gaussianReal 0 1)

theorem gaussianRealBVPerimeter_halfline (a : ℝ) :
    gaussianRealBVPerimeter (Ioi a) = ENNReal.ofReal (standardDensity a) := by
  apply le_antisymm
  · apply iSup_le
    intro X
    apply ENNReal.ofReal_le_ofReal
    rw [gaussianReal_halfline_weighted_flux X (X.smooth.of_le (by simp)) X.compact a]
    have hx : -X a ≤ 1 := (neg_le_abs _).trans (by simpa only [Real.norm_eq_abs] using X.norm_le a)
    have hp := standardDensity_pos a
    nlinarith
  · let f : ContDiffBump a := ⟨1,2,by norm_num,by norm_num⟩
    let X : GaussianRealTestField :=
      { toFun := fun x => -f x
        smooth := f.contDiff.neg
        compact := f.hasCompactSupport.neg
        norm_le := fun x => by
          rw [norm_neg,Real.norm_eq_abs,abs_of_nonneg f.nonneg]
          exact f.le_one }
    have hx : X a = -1 := by
      change -f a = -1
      rw [f.one_of_mem_closedBall (by simp [f])]
    have he := gaussianReal_halfline_weighted_flux X (X.smooth.of_le (by simp)) X.compact a
    rw [hx] at he
    simp only [mul_neg,neg_neg,mul_one] at he
    rw [gaussianRealBVPerimeter]
    have hi := le_iSup (fun Y : GaussianRealTestField =>
      ENNReal.ofReal (∫ x in Ioi a,deriv Y x-x*Y x ∂gaussianReal 0 1)) X
    simpa only [he] using hi

end GaussianMeasureBridge
