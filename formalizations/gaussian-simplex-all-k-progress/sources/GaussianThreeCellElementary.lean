import GaussianMinimalCovarianceRows
import GaussianScoreSymmetry
import GaussianHalfspaceFlux
import Mathlib.Tactic

/-!
A direct three-label route to the *unconditional* sharp Gaussian first-moment
comparison, avoiding the geometric Gaussian multi-bubble theorem. For any
centrally symmetric three-score law, the mean maximum is one quarter of the
sum of expected pairwise absolute differences. In the Gaussian case those
differences scale with Euclidean edge lengths, whose sum is maximized by
the trace-one equilateral triangle.

This development is independent of the existing k=2 project and of any
unproved Gaussian perimeter lower bound.
-/

open MeasureTheory ProbabilityTheory Set Matrix Module
open scoped RealInnerProductSpace Topology

namespace GaussianMeasureBridge

/-- Elementary symmetrized range identity for three real numbers.
No probabilistic or geometric assumption occurs here. -/
theorem triple_max_symmetrized (a b c : ℝ) :
    2 * (max a (max b c) + max (-a) (max (-b) (-c))) =
      |a-b| + |a-c| + |b-c| := by
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

/-- The actual finite-label score maximum specializes to an ordinary
maximum of three Gaussian linear scores. -/
theorem scoreMax_zero_three {d : ℕ} (v : Fin 3 → Space d) (x : Space d) :
    scoreMax v 0 x =
      max ⟪v 0,x⟫ (max ⟪v 1,x⟫ ⟪v 2,x⟫) := by
  apply le_antisymm
  · unfold scoreMax
    refine Finset.sup'_le _ _ (fun i _ => ?_)
    fin_cases i <;> simp
  · apply max_le
    · simpa using le_scoreMax v 0 x (0 : Fin 3)
    · apply max_le
      · simpa using le_scoreMax v 0 x (1 : Fin 3)
      · simpa using le_scoreMax v 0 x (2 : Fin 3)

/-- Integrand-level identity: three Gaussian scores and their simultaneous
negatives sum to their complete pairwise absolute edge distances. -/
theorem scoreMax_three_symmetrized {d : ℕ} (v : Fin 3 → Space d)
    (x : Space d) :
    2*(scoreMax v 0 x + scoreMax (fun i => -v i) 0 x) =
      |⟪v 0-v 1,x⟫| + |⟪v 0-v 2,x⟫| + |⟪v 1-v 2,x⟫| := by
  rw [scoreMax_zero_three v x,scoreMax_zero_three (fun i => -v i) x]
  simpa only [inner_neg_left,inner_sub_left] using
    triple_max_symmetrized (⟪v 0,x⟫) (⟪v 1,x⟫) (⟪v 2,x⟫)

/-- Sign reversal preserves the actual Gaussian score expectation because
it preserves its Gram covariance matrix. -/
theorem expectedScore_three_neg {d : ℕ} (v : Fin 3 → Space d) :
    expectedScore v 0 = expectedScore (fun i => -v i) 0 := by
  have hGram : scoreGram v = scoreGram (fun i => -v i) := by
    ext i j
    simp [scoreGram]
  exact expectedScore_eq_of_gram_eq v _ hGram 0

#print axioms triple_max_symmetrized
#print axioms scoreMax_zero_three
#print axioms scoreMax_three_symmetrized
#print axioms expectedScore_three_neg

end GaussianMeasureBridge
