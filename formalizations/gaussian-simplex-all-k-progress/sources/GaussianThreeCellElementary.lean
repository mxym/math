import GaussianMinimalCovarianceRows
import GaussianScoreSymmetry
import GaussianHalfspaceFlux
import GaussianRegularPerimeter
import GaussianRegularStationarity
import GaussianEquidistantRigidity
import GaussianMomentCovariance
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
  have hR :
      (∫ x, |⟪v 0-v 1,x⟫| + |⟪v 0-v 2,x⟫| +
        |⟪v 1-v 2,x⟫| ∂gaussian d) =
      (∫ x, |⟪v 0-v 1,x⟫| ∂gaussian d) +
      (∫ x, |⟪v 0-v 2,x⟫| ∂gaussian d) +
      (∫ x, |⟪v 1-v 2,x⟫| ∂gaussian d) := by
    have hAB :
        (∫ x, |⟪v 0-v 1,x⟫| + |⟪v 0-v 2,x⟫| ∂gaussian d) =
          (∫ x, |⟪v 0-v 1,x⟫| ∂gaussian d) +
          (∫ x, |⟪v 0-v 2,x⟫| ∂gaussian d) := by
      simpa only [Pi.add_apply] using
        (integral_add (hi (v 0-v 1)) (hi (v 0-v 2)))
    have hABC :
        (∫ x, |⟪v 0-v 1,x⟫| + |⟪v 0-v 2,x⟫| +
          |⟪v 1-v 2,x⟫| ∂gaussian d) =
        (∫ x, |⟪v 0-v 1,x⟫| + |⟪v 0-v 2,x⟫| ∂gaussian d) +
          (∫ x, |⟪v 1-v 2,x⟫| ∂gaussian d) := by
      simpa only [Pi.add_apply] using
        (integral_add ((hi (v 0-v 1)).add (hi (v 0-v 2)))
          (hi (v 1-v 2)))
    rw [hABC, hAB]
  rw [hR] at hpoint
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
    calc
      _ = |⟪‖u‖ • e,x⟫| := congrArg (fun z => |⟪z,x⟫|) he.symm
      _ = _ := by rw [real_inner_smul_left, abs_mul, abs_of_nonneg hu1]
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


namespace GaussianMeasureBridge

/-- In a trace-one centered triple, all three squared edge lengths sum to
three. This is a purely Euclidean identity, with no nonsingularity premise. -/
theorem centered_three_squared_edges {d : ℕ} (v : Fin 3 → Space d)
    (hz : ∑ i, v i = 0) (ht : ∑ i, ‖v i‖ ^ 2 = 1) :
    ‖v 0-v 1‖ ^ 2 + ‖v 0-v 2‖ ^ 2 + ‖v 1-v 2‖ ^ 2 = 3 := by
  have hz3 : v 0 + v 1 + v 2 = 0 := by
    simpa [Fin.sum_univ_succ, Fin.sum_univ_two, add_assoc] using hz
  have ht3 : ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 + ‖v 2‖ ^ 2 = 1 := by
    simpa [Fin.sum_univ_succ, Fin.sum_univ_two, add_assoc] using ht
  have hzero : ⟪v 0+v 1+v 2, v 0+v 1+v 2⟫ = 0 := by
    rw [hz3]
    simp
  simp only [inner_add_left, inner_add_right, real_inner_self_eq_norm_sq] at hzero
  have hs01 : ⟪v 1,v 0⟫ = ⟪v 0,v 1⟫ := real_inner_comm _ _
  have hs02 : ⟪v 2,v 0⟫ = ⟪v 0,v 2⟫ := real_inner_comm _ _
  have hs12 : ⟪v 2,v 1⟫ = ⟪v 1,v 2⟫ := real_inner_comm _ _
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_sub_sq_real]
  nlinarith [hzero, ht3, hs01, hs02, hs12]

/-- Exactly the three-term Cauchy bound for trace-one centered Gaussian score
vectors. Equality can hold only for an equilateral score triangle. -/
theorem centered_three_edge_sum_le_three {d : ℕ} (v : Fin 3 → Space d)
    (hz : ∑ i, v i = 0) (ht : ∑ i, ‖v i‖ ^ 2 = 1) :
    ‖v 0-v 1‖ + ‖v 0-v 2‖ + ‖v 1-v 2‖ ≤ 3 := by
  have hs := centered_three_squared_edges v hz ht
  let a : ℝ := ‖v 0-v 1‖
  let b : ℝ := ‖v 0-v 2‖
  let c : ℝ := ‖v 1-v 2‖
  have hab : 0 ≤ a := norm_nonneg _
  have hbb : 0 ≤ b := norm_nonneg _
  have hcb : 0 ≤ c := norm_nonneg _
  have hs' : a^2+b^2+c^2=3 := hs
  have hcauchy : (a+b+c)^2 ≤ 3*(a^2+b^2+c^2) := by
    nlinarith [sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (b-c)]
  change a+b+c ≤ 3
  nlinarith [hcauchy]

/-- At the regular trace-one three-score model, the zero-price objective
equals the exact balanced-value sharp constant. -/
theorem expectedScore_regular_three :
    expectedScore (regularRows 3) 0 = simplexConstant 3 := by
  have hp : canonicalPrices (regularRows 3) = 0 :=
    canonicalPrices_regular (k := 3) (by norm_num : 2 ≤ 3)
  calc
    expectedScore (regularRows 3) 0 =
      priceObjective (regularRows 3) (uniformMass 3) 0 := by
        simp [priceObjective]
    _ = equalMassValue (regularRows 3) := by
      rw [← hp, canonicalPrices_value]
    _ = simplexConstant 3 := by
      rw [← covarianceValue_scoreGram]
      change covarianceValue (regularCovariance 3) = simplexConstant 3
      exact covarianceValue_regular

/-- Model calibration by actual standard Gaussian integrals. No use of any
numerical evaluation of sqrt(pi), Gaussian perimeter, or multibubble theorem. -/
theorem exact_three_gaussian_model :
    4 * simplexConstant 3 = 3 * gaussianAbsOne := by
  have hedge (i j : Fin 3) (hij : i ≠ j) :
      ‖regularRows 3 i - regularRows 3 j‖ = 1 := by
    have hh := regular_gram_edge_squared (d := 1) (e := 3)
      (regularRows 3) (show scoreGram (regularRows 3) = regularCovariance 3 by rfl)
      i j hij
    norm_num at hh
    rcases hh with hpos | hneg
    · exact hpos
    · exfalso
      linarith [norm_nonneg (regularRows 3 i - regularRows 3 j)]
  have he := expectedScore_three_edges (regularRows 3)
  rw [expectedScore_regular_three,
      hedge 0 1 (by decide), hedge 0 2 (by decide),
      hedge 1 2 (by decide)] at he
  norm_num at he
  nlinarith

/-- **Unconditional sharp three-cell covariance comparison.**
The proof uses only actual Gaussian score expectations, three Euclidean
pairwise distances and finite Cauchy: it needs no geometric perimeter input. -/
theorem covarianceValue_three_le_sharp
    (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQ : NormalizedCovariance Q) :
    covarianceValue Q ≤ simplexConstant 3 := by
  let v : Fin 3 → Space 2 := minimalCovarianceRows Q
  have hz : ∑ i, v i = 0 := minimalCovarianceRows_sum Q
  have hg : scoreGram v = Q := scoreGram_minimalCovarianceRows Q hQ.1 hQ.2.1
  have ht : ∑ i, ‖v i‖ ^ 2 = 1 := by
    rw [← hQ.2.2, ← hg]
    simp only [Matrix.trace, Matrix.diag, scoreGram, real_inner_self_eq_norm_sq]
  have hl := centered_three_edge_sum_le_three v hz ht
  have he := expectedScore_three_edges v
  have hm := exact_three_gaussian_model
  have hmul : gaussianAbsOne *
      (‖v 0-v 1‖ + ‖v 0-v 2‖ + ‖v 1-v 2‖) ≤ gaussianAbsOne*3 :=
    mul_le_mul_of_nonneg_left hl gaussianAbsOne_nonneg
  have hbound : expectedScore v 0 ≤ simplexConstant 3 := by
    nlinarith [he, hm, hmul]
  calc
    covarianceValue Q = equalMassValue v :=
      covarianceValue_minimal_rows Q hQ.1 hQ.2.1
    _ ≤ priceObjective v (uniformMass 3) 0 :=
      balancedValue_le_objective v (uniformMass 3) 0 uniformMass_pos sum_uniformMass
    _ = expectedScore v 0 := by simp [priceObjective]
    _ ≤ simplexConstant 3 := hbound

/-- Unconditional sharp squared first-moment inequality for **every actual
equal-mass Gaussian fractional 3-partition in every ambient dimension**.
This is the original Gaussian three-label problem, not a proxy objective. -/
theorem three_cell_sharp_first_moment {d : ℕ} (F : FractionalPartition d 3)
    (hF : ∀ i, F.mass i = uniformMass 3 i) :
    F.momentEnergy ≤ simplexConstant 3 ^ 2 := by
  exact F.momentEnergy_bound_of_normalized_covariance_bound hF (simplexConstant 3)
    simplexConstant_nonneg (fun Q hQ => covarianceValue_three_le_sharp Q hQ)

#print axioms centered_three_squared_edges
#print axioms centered_three_edge_sum_le_three
#print axioms expectedScore_regular_three
#print axioms exact_three_gaussian_model
#print axioms covarianceValue_three_le_sharp
#print axioms three_cell_sharp_first_moment
end GaussianMeasureBridge
