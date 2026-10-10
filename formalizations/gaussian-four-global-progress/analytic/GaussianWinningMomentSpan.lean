import GaussianMomentSymmetry
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-! Winning-cell moments lie in the actual score span. Orthogonal reflection
fixes every score and its cell, so it fixes its genuine Gaussian moment. -/
open MeasureTheory ProbabilityTheory Module Set
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d k : ℕ} [NeZero k]

theorem rawWinningMoment_mem_score_span (v : Fin k → Space d) (b : Fin k → ℝ) (i : Fin k) :
    rawWinningMoment v b i ∈ Submodule.span ℝ (range v) := by
  let K := Submodule.span ℝ (range v)
  have hv (j : Fin k) : K.reflection (v j) = v j :=
    Submodule.reflection_mem_subspace_eq_self (Submodule.subset_span (mem_range_self j))
  have he := rawWinningMoment_isometry v b K.reflection i
  simp only [hv] at he
  exact (Submodule.reflection_eq_self_iff _).mp he.symm

theorem balancedMoment_mem_score_span (v : Fin k → Space d) (i : Fin k) :
    balancedMoment v i ∈ Submodule.span ℝ (range v) :=
  rawWinningMoment_mem_score_span v (canonicalPrices v) i

end GaussianMeasureBridge
