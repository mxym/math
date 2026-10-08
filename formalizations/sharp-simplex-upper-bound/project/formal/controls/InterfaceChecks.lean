import Entry005.SimplexVolumeInterface
import Mathlib.Tactic.FinCases

noncomputable section
open scoped BigOperators
open MeasureTheory
open Entry005

namespace InterfaceChecks

private def point (r : ℝ) : Space 1 := WithLp.toLp 2 (fun _ : Fin 1 => r)

private def segment (a b : ℝ) (hab : a ≠ b) : Affine.Simplex ℝ (Space 1) 1 :=
  ⟨![point a, point b], affineIndependent_of_ne ℝ (fun h => hab
    (congrArg (fun x : Space 1 => x 0) h))⟩

private theorem augmented_segment (a b : ℝ) (hab : a ≠ b) :
    augmentedVertices (segment a b hab).points = !![1, 1; a, b] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private def unitSegment := segment 0 1 (by norm_num)
private def reversed := segment 1 0 (by norm_num)
private def outside := segment 0 2 (by norm_num)
private def translatedP := segment 2 4 (by norm_num)
private def translatedS := segment 2 3 (by norm_num)

private theorem reverse_inside : simplexSet reversed ⊆ simplexSet unitSegment := by
  apply convexHull_mono
  rintro x ⟨i, rfl⟩
  fin_cases i
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩

private theorem translated_inside : simplexSet translatedS ⊆ simplexSet translatedP := by
  apply convexHull_min
  · rintro x ⟨i, rfl⟩
    fin_cases i
    · exact subset_convexHull ℝ _ ⟨0, rfl⟩
    · have h0 : point 2 ∈ simplexSet translatedP := subset_convexHull ℝ _ ⟨0, rfl⟩
      have h1 : point 4 ∈ simplexSet translatedP := subset_convexHull ℝ _ ⟨1, rfl⟩
      have hm := convex_convexHull ℝ (Set.range translatedP.points) h0 h1
        (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num)
      have he : (1 / 2 : ℝ) • point 2 + (1 / 2 : ℝ) • point 4 = point 3 := by
        ext k
        norm_num [point]
      rw [he] at hm
      exact hm
  · exact convex_convexHull ℝ _

private theorem reversed_det : (simplexBarycentricMatrix unitSegment reversed).det = -1 := by
  norm_num [simplexBarycentricMatrix, unitSegment, reversed, augmented_segment,
    Matrix.inv_def, Matrix.det_fin_two, Matrix.adjugate_fin_two, Matrix.mul_apply,
    Fin.sum_univ_succ, Ring.inverse_eq_inv]
  rw [Matrix.det_fin_two]
  norm_num

private theorem translated_det : (simplexBarycentricMatrix translatedP translatedS).det = 1 / 2 := by
  norm_num [simplexBarycentricMatrix, translatedP, translatedS, augmented_segment,
    Matrix.inv_def, Matrix.det_fin_two, Matrix.adjugate_fin_two, Matrix.mul_apply,
    Fin.sum_univ_succ, Ring.inverse_eq_inv]
  rw [Matrix.det_fin_two]
  norm_num

-- The d=1 boundary, reversed orientation and actual volume ratio all use the full exact goal.
example : (volume (simplexSet reversed)).toReal / (volume (simplexSet unitSegment)).toReal = 1 := by
  have h := (simplexMatrixVolumeInterface 1 (le_refl 1) unitSegment reversed reverse_inside).2.2.2.2.2.2.2
  simpa [reversed_det] using h.symm

-- Translation does not contaminate the determinant, and image scaling is direct, not inverse.
example : (volume (simplexSet translatedS)).toReal / (volume (simplexSet translatedP)).toReal = 1 / 2 := by
  have h := (simplexMatrixVolumeInterface 1 (le_refl 1) translatedP translatedS translated_inside).2.2.2.2.2.2.2
  simpa [translated_det] using h.symm

-- The reciprocal preimage factor would assert 2 instead of the actual image ratio 1/2.
example : (volume (simplexSet translatedS)).toReal / (volume (simplexSet translatedP)).toReal ≠ 2 := by
  have h := (simplexMatrixVolumeInterface 1 (le_refl 1) translatedP translatedS translated_inside).2.2.2.2.2.2.2
  have hv : (volume (simplexSet translatedS)).toReal / (volume (simplexSet translatedP)).toReal = 1 / 2 := by
    simpa [translated_det] using h.symm
  rw [hv]
  norm_num

-- The equal-simplex endpoint gives the identity matrix and strictly positive actual volume.
example (P : Affine.Simplex ℝ (Space 1) 1) : simplexBarycentricMatrix P P = 1 := by
  have hp := (simplexMatrixVolumeInterface 1 (le_refl 1) P P (Set.Subset.refl _)).1
  exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hp)
example (P : Affine.Simplex ℝ (Space 1) 1) : 0 < (volume (simplexSet P)).toReal :=
  (simplexMatrixVolumeInterface 1 (le_refl 1) P P (Set.Subset.refl _)).2.2.2.1

-- Omitting inclusion is false, even for genuine one-dimensional simplices.
example : simplexBarycentricMatrix unitSegment outside 0 1 = -1 := by
  norm_num [simplexBarycentricMatrix, unitSegment, outside, augmented_segment,
    Matrix.inv_def, Matrix.det_fin_two, Matrix.adjugate_fin_two, Matrix.mul_apply,
    Fin.sum_univ_succ, Ring.inverse_eq_inv]
example : ¬ ∀ i j, 0 ≤ simplexBarycentricMatrix unitSegment outside i j := by
  intro h
  have hn := h 0 1
  norm_num [simplexBarycentricMatrix, unitSegment, outside, augmented_segment,
    Matrix.inv_def, Matrix.det_fin_two, Matrix.adjugate_fin_two, Matrix.mul_apply,
    Fin.sum_univ_succ, Ring.inverse_eq_inv] at hn

-- Removing the absolute value is false under the actual inclusion hypotheses.
example : (simplexBarycentricMatrix unitSegment reversed).det ≠
    (volume (simplexSet reversed)).toReal / (volume (simplexSet unitSegment)).toReal := by
  have hn : 0 ≤ (volume (simplexSet reversed)).toReal / (volume (simplexSet unitSegment)).toReal :=
    div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  rw [reversed_det]
  linarith

-- Discarding genuine affine independence admits a collapsed vertex tuple with zero determinant.
example : (augmentedVertices (fun _ : Fin 2 => (0 : Space 1))).det = 0 := by
  change (Matrix.det (!![1, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)) = 0
  norm_num [Matrix.det_fin_two]
example : volume (convexHull ℝ (Set.range (fun _ : Fin 2 => (0 : Space 1)))) = 0 := by
  simp [Set.range_const]

end InterfaceChecks
