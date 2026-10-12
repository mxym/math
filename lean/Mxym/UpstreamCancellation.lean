import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! Exact theorem and proof extracted from openai/math ProjectionCoefficients.lean.
Only the import block and surrounding namespaces have been narrowed. -/
namespace OAI.Paper092
universe uι
open scoped BigOperators

theorem twice_sum_negative_eq_sum_abs {ι : Type uι} [Fintype ι] (v : ι → ℝ)
    (hv : ∑ i, v i = 0) :
    2 * (∑ i : {i // v i < 0}, -v i.val) = ∑ i, |v i| := by
  classical
  have hpoint (i : ι) : 2 * (if v i < 0 then -v i else 0) = |v i| - v i := by
    by_cases hi : v i < 0
    · simp [hi, abs_of_neg hi]
      ring
    · simp [hi, abs_of_nonneg (le_of_not_gt hi)]
  have hsum := congrArg (fun f : ι → ℝ => ∑ i, f i) (funext hpoint)
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, hv, sub_zero] at hsum
  convert hsum using 1
  congr 1
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter (fun i => v i < 0)) (by simp)
    (fun i => -v i)).symm

end OAI.Paper092
