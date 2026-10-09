import GaussianThreeScoreAlgebra

/-!
Exact Gaussian width formula for the maximum of three centered Gaussian
linear scores.  It is valid even when the three scores are repeated,
linearly dependent, or embedded in lower dimensions.

The argument uses the centered Gaussian symmetry, the three-point range
identity, and the unit-projection Gaussian law. No multi-bubble theorem.
-/

open MeasureTheory ProbabilityTheory Module Set Filter Matrix
open scoped RealInnerProductSpace

namespace GaussianMeasureBridge

noncomputable def gaussianAbsOne : ℝ :=
  ∫ t : ℝ, |t| ∂gaussianReal 0 1

lemma gaussianAbsOne_nonneg : 0 ≤ gaussianAbsOne := by
  unfold gaussianAbsOne
  exact integral_nonneg fun t => abs_nonneg t

/-- The absolute Gaussian linear functional scales exactly with the
Euclidean norm of its coefficient, including the zero coefficient. -/
theorem gaussian_integral_abs_inner {d : ℕ} (w : Space d) :
    (∫ x : Space d, |⟪w,x⟫| ∂gaussian d) = ‖w‖ * gaussianAbsOne := by
  by_cases hw : w = 0
  · subst w
    simp [gaussianAbsOne]
  · have hp : 0 < ‖w‖ := norm_pos_iff.mpr hw
    let u : Space d := ‖w‖⁻¹ • w
    have hu : ‖u‖ = 1 := by
      rw [show u = ‖w‖⁻¹ • w from rfl, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hp.le)]
      exact inv_mul_cancel₀ hp.ne'
    have hwu : w = ‖w‖ • u := by
      dsimp [u]
      rw [smul_smul, mul_inv_cancel₀ hp.ne', one_smul]
    have hm : AEStronglyMeasurable (fun t : ℝ => |t|)
        ((gaussian d).map (fun x : Space d => ⟪u,x⟫)) :=
      continuous_abs.aestronglyMeasurable
    have hlaw : (∫ x : Space d, |⟪u,x⟫| ∂gaussian d) =
        gaussianAbsOne := by
      unfold gaussianAbsOne
      rw [← gaussian_unit_inner_law u hu,
        integral_map (by fun_prop) hm]
    calc
      (∫ x : Space d, |⟪w,x⟫| ∂gaussian d) =
          ∫ x : Space d, ‖w‖ * |⟪u,x⟫| ∂gaussian d := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => by
          rw [hwu, real_inner_smul_left, abs_mul,
            abs_of_nonneg (norm_nonneg w)]
      _ = ‖w‖ * (∫ x : Space d, |⟪u,x⟫| ∂gaussian d) :=
        integral_const_mul _ _
      _ = _ := by rw [hlaw]

theorem scoreMax_three_pair_abs {d : ℕ}
    (v : Fin 3 → Space d) (x : Space d) :
    scoreMax v 0 x + scoreMax (fun i => -v i) 0 x =
      (|⟪v 0-v 1,x⟫| + |⟪v 0-v 2,x⟫| +
          |⟪v 1-v 2,x⟫|)/2 := by
  rw [scoreMax_three_zero v x, scoreMax_three_zero (fun i => -v i) x]
  simp only [real_inner_neg_left]
  simpa only [inner_sub_left] using
    max_three_plus_negative (⟪v 0,x⟫) (⟪v 1,x⟫) (⟪v 2,x⟫)

/-- For any Gaussian score triple, with absolutely no rank hypotheses,
the expected maximum is one quarter of the sum of the three pairwise
absolute projection expectations. -/
theorem expectedScore_three_abs_pair_sum {d : ℕ}
    (v : Fin 3 → Space d) :
    expectedScore v 0 =
      ((∫ x : Space d, |⟪v 0-v 1,x⟫| ∂gaussian d) +
       (∫ x : Space d, |⟪v 0-v 2,x⟫| ∂gaussian d) +
       (∫ x : Space d, |⟪v 1-v 2,x⟫| ∂gaussian d))/4 := by
  let f := fun x : Space d => |⟪v 0-v 1,x⟫|
  let g := fun x : Space d => |⟪v 0-v 2,x⟫|
  let h := fun x : Space d => |⟪v 1-v 2,x⟫|
  have hf : Integrable f (gaussian d) := (integrable_gaussian_inner _).abs
  have hg : Integrable g (gaussian d) := (integrable_gaussian_inner _).abs
  have hh : Integrable h (gaussian d) := (integrable_gaussian_inner _).abs
  have hsum : (∫ x, (f x + g x + h x)/2 ∂gaussian d) =
      ((∫ x,f x ∂gaussian d)+(∫ x,g x ∂gaussian d)+
        (∫ x,h x ∂gaussian d))/2 := by
    simp only [div_eq_mul_inv]
    rw [integral_mul_const, integral_add (hf.add hg) hh, integral_add hf hg]
  have hpoint : (∫ x,scoreMax v 0 x+scoreMax (fun i => -v i) 0 x ∂gaussian d) =
      ∫ x,(f x+g x+h x)/2 ∂gaussian d := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => scoreMax_three_pair_abs v x
  rw [integral_add (integrable_scoreMax v 0)
    (integrable_scoreMax (fun i => -v i) 0)] at hpoint
  have hneg := expectedScore_three_neg_invariant v
  change (∫ x, scoreMax (fun i => -v i) 0 x ∂gaussian d) =
    (∫ x,scoreMax v 0 x ∂gaussian d) at hneg
  rw [hneg,hsum] at hpoint
  change (∫ x,scoreMax v 0 x ∂gaussian d) = _
  dsimp only [f,g,h] at hpoint
  unfold expectedScore
  linarith

/-- Exact three-score Gaussian width formula, with universal coefficient
equal to the actual absolute moment of one standard normal. -/
theorem expectedScore_three_width {d : ℕ} (v : Fin 3 → Space d) :
    expectedScore v 0 =
      gaussianAbsOne/4 *
        (‖v 0-v 1‖ + ‖v 0-v 2‖ + ‖v 1-v 2‖) := by
  rw [expectedScore_three_abs_pair_sum,
    gaussian_integral_abs_inner,gaussian_integral_abs_inner,
    gaussian_integral_abs_inner]
  ring

#print axioms gaussian_integral_abs_inner
#print axioms expectedScore_three_abs_pair_sum
#print axioms expectedScore_three_width

end GaussianMeasureBridge
