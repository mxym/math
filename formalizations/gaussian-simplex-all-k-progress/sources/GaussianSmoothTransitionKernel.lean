import GaussianSmoothWinningApproximation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The explicit transition derivative used by the cell approximants is a
continuous, nonnegative, compactly supported normalized kernel. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff
namespace GaussianMeasureBridge

lemma smoothTransition_deriv_continuous : Continuous (deriv Real.smoothTransition) :=
  (Real.smoothTransition.contDiff (n := 1)).continuous_deriv (by simp)

lemma smoothTransition_deriv_nonneg (x : ℝ) : 0 ≤ deriv Real.smoothTransition x :=
  Real.smoothTransition.monotone.deriv_nonneg

lemma smoothTransition_deriv_support_subset :
    Function.support (deriv Real.smoothTransition) ⊆ Icc (0 : ℝ) 1 := by
  intro x hx
  by_contra he
  have hcases : x<0 ∨ 1<x := by simpa only [mem_Icc,not_and_or,not_le] using he
  have hz : deriv Real.smoothTransition x=0 := by
    rcases hcases with hneg | hpos
    · have heq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
        filter_upwards [eventually_lt_nhds hneg] with y hy
        exact Real.smoothTransition.zero_of_nonpos hy.le
      exact ((hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq heq).deriv
    · have heq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
        filter_upwards [eventually_gt_nhds hpos] with y hy
        exact Real.smoothTransition.one_of_one_le hy.le
      exact ((hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq heq).deriv
  exact hx hz

lemma smoothTransition_deriv_compact : HasCompactSupport (deriv Real.smoothTransition) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc smoothTransition_deriv_support_subset

lemma smoothTransition_deriv_bounded :
    ∃ M : ℝ,0 ≤ M ∧ ∀ x,‖deriv Real.smoothTransition x‖ ≤ M := by
  obtain ⟨M,hM⟩ := smoothTransition_deriv_compact.exists_bound_of_continuous
    smoothTransition_deriv_continuous
  exact ⟨M,(norm_nonneg _).trans (hM 0),hM⟩

lemma smoothTransition_kernel_normalized :
    (∫ t in (0 : ℝ)..1,deriv Real.smoothTransition t) = 1 := by
  have hd (x : ℝ) : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition x) x :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero x).hasDerivAt
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun x _ => hd x)
    (smoothTransition_deriv_continuous.intervalIntegrable 0 1)
  simpa only [Real.smoothTransition.one,Real.smoothTransition.zero,sub_zero] using he

end GaussianMeasureBridge
