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


namespace GaussianMeasureBridge
variable {d : ℕ}

/-- Gaussian integral of the pointwise symmetrized three-score maximum.
This identity is valid in every ambient dimension, with no rank condition. -/
theorem expectedScore_three_abs_edges (v : Fin 3 → Space d) :
    4 * expectedScore v 0 =
      (∫ x, |⟪v 0 - v 1,x⟫| ∂gaussian d) +
      (∫ x, |⟪v 0 - v 2,x⟫| ∂gaussian d) +
      (∫ x, |⟪v 1 - v 2,x⟫| ∂gaussian d) := by
  have hi (u : Space d) :
      Integrable (fun x : Space d => |⟪u,x⟫|) (gaussian d) := by
    simpa only [Real.norm_eq_abs] using (integrable_gaussian_inner u).norm
  have hpoint :
      (∫ x, 2*(scoreMax v 0 x + scoreMax (fun i => -v i) 0 x) ∂gaussian d) =
      (∫ x, |⟪v 0 - v 1,x⟫| + |⟪v 0 - v 2,x⟫| +
        |⟪v 1 - v 2,x⟫| ∂gaussian d) := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => scoreMax_three_symmetrized v x
  rw [integral_const_mul,
    integral_add (integrable_scoreMax v 0)
      (integrable_scoreMax (fun i => -v i) 0)] at hpoint
  rw [integral_add ((hi (v 0-v 1)).add (hi (v 0-v 2)))
    (hi (v 1-v 2)), integral_add (hi (v 0-v 1)) (hi (v 0-v 2))] at hpoint
  change 2*(expectedScore v 0 + expectedScore (fun i => -v i) 0) = _ at hpoint
  rw [← expectedScore_three_neg v] at hpoint
  linarith

/-- The actual first absolute moment of a standard normal real random
variable, defined by integration, not by an external numerical constant. -/
noncomputable def gaussianAbsOne : ℝ :=
  ∫ z : ℝ, |z| ∂gaussianReal 0 1

lemma gaussianAbsOne_nonneg : 0 ≤ gaussianAbsOne := by
  unfold gaussianAbsOne
  exact integral_nonneg fun _ => abs_nonneg _

/-- The actual Gaussian absolute moment in an arbitrary Euclidean direction
is homogeneous in its length, including zero directions. -/
theorem gaussian_abs_inner (u : Space d) :
    (∫ x, |⟪u,x⟫| ∂gaussian d) = ‖u‖ * gaussianAbsOne := by
  by_cases hu : u = 0
  · subst u
    simp only [inner_zero_left, abs_zero, integral_zero, norm_zero, zero_mul]
  let e : Space d := ‖u‖⁻¹ • u
  have hu0 : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hu1 : 0 ≤ ‖u‖ := norm_nonneg u
  have heUnit : ‖e‖ = 1 := by
    dsimp only [e]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hu1)]
    exact inv_mul_cancel₀ hu0
  have he : ‖u‖ • e = u := by
    dsimp only [e]
    rw [smul_smul, mul_inv_cancel₀ hu0, one_smul]
  have hlin (x : Space d) : |⟪u,x⟫| = ‖u‖ * |⟪e,x⟫| := by
    rw [← he, real_inner_smul_left, abs_mul, abs_of_nonneg hu1]
  simp_rw [hlin]
  rw [integral_const_mul]
  congr 1
  unfold gaussianAbsOne
  rw [← gaussian_unit_inner_law e heUnit,
    integral_map (by fun_prop) (by fun_prop)]

/-- Exact three-score Gaussian mean-maximum/edge-length identity. -/
theorem expectedScore_three_edges (v : Fin 3 → Space d) :
    4 * expectedScore v 0 =
      gaussianAbsOne * (‖v 0-v 1‖ + ‖v 0-v 2‖ + ‖v 1-v 2‖) := by
  rw [expectedScore_three_abs_edges v]
  rw [gaussian_abs_inner, gaussian_abs_inner, gaussian_abs_inner]
  ring

#print axioms expectedScore_three_abs_edges
#print axioms gaussian_abs_inner
#print axioms expectedScore_three_edges
end GaussianMeasureBridge
