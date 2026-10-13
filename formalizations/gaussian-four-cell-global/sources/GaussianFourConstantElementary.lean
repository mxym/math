import GaussianRegularPerimeter

set_option maxHeartbeats 1000000

/-!
Elementary exact identities for the angular constant in the regular four-cell
calculation.  These lemmas deliberately do not identify the Gaussian
order-statistic integral; they isolate the exact one-dimensional arctangent
integral which occurs after the (separate) polar-coordinate reduction.
-/

open MeasureTheory Set
open scoped Interval

namespace GaussianMeasureBridge

noncomputable def tetrahedralAngle : ℝ := Real.arctan (Real.sqrt 2)

lemma tetrahedralAngle_pos : 0 < tetrahedralAngle := by
  unfold tetrahedralAngle
  exact Real.arctan_pos.mpr (by positivity)

lemma tetrahedralAngle_lt_pi_div_two :
    tetrahedralAngle < Real.pi / 2 := by
  unfold tetrahedralAngle
  exact Real.arctan_lt_pi_div_two _

lemma tetrahedralAngle_tan : Real.tan tetrahedralAngle = Real.sqrt 2 := by
  unfold tetrahedralAngle
  exact Real.tan_arctan _

lemma tetrahedralAngle_ne_zero : tetrahedralAngle ≠ 0 :=
  ne_of_gt tetrahedralAngle_pos

lemma integral_inv_one_add_sq_symmetric_sqrt_two :
    (∫ x : ℝ in -Real.sqrt 2..Real.sqrt 2, (1 + x ^ 2)⁻¹) =
      2 * tetrahedralAngle := by
  rw [integral_inv_one_add_sq]
  unfold tetrahedralAngle
  rw [Real.arctan_neg]
  ring

lemma tetrahedralAngularRatio :
    ((∫ x : ℝ in -Real.sqrt 2..Real.sqrt 2, (1 + x ^ 2)⁻¹) / (2 * Real.pi)) =
      tetrahedralAngle / Real.pi := by
  rw [integral_inv_one_add_sq_symmetric_sqrt_two]
  ring

lemma regular_four_target_positive :
    0 < 12 * tetrahedralAngle ^ 2 / Real.pi ^ 3 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have ht : 0 < tetrahedralAngle ^ 2 := sq_pos_of_pos tetrahedralAngle_pos
  positivity

end GaussianMeasureBridge
