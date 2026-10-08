import Entry005.TruncationMaximum
import Entry005.TruncationVolume

noncomputable section
open MeasureTheory

namespace Entry005

/-- The actual chosen maximum's Euclidean volume, not an assumed determinant
normalization or a scalar substitute for simplex volume. -/
theorem truncation_simplex_actual_volume {d : ℕ} (hd : 0 < d) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t < 1) (i : Fin d) :
    (volume (simplexSet (truncationSimplex t i (by linarith)))).toReal =
      (1 - t) / (d.factorial : ℝ) := by
  let P := truncationSimplex 0 i (by norm_num)
  let S := truncationSimplex t i (by linarith)
  have hsubset : simplexSet S ⊆ simplexSet P := by
    rw [truncationSimplex_zero_set i]
    intro x hx
    have ht := truncationSimplex_subset t i (by linarith) ht0 ht1.le hx
    exact ⟨ht.1, Finset.sum_nonneg (fun j _ => ht.1 j), ht.2.2⟩
  have hi := simplexMatrixVolumeInterface d (Nat.succ_le_of_lt hd) P S hsubset
  have hP : (augmentedVertices P.points).det = 1 := by
    simpa only [P, truncationSimplex_points, sub_zero] using truncationSimplex_augmented_det 0 i
  have hdet : |(simplexBarycentricMatrix P S).det| = 1 - t := by
    simp only [simplexBarycentricMatrix, Matrix.det_mul, Matrix.det_nonsing_inv,
      hP, Ring.inverse_eq_inv, inv_one, one_mul]
    change |(augmentedVertices (truncationSimplexPoints t i)).det| = 1 - t
    rw [truncationSimplex_augmented_det, abs_of_pos (by linarith : 0 < 1 - t)]
  have hPV : (volume (simplexSet P)).toReal = 1 / (d.factorial : ℝ) := by
    rw [truncationSimplex_zero_set i]
    simpa only [zero_pow hd.ne', sub_zero] using
      truncation_actual_volume hd 0 (by norm_num) (by norm_num)
  have hr := hi.2.2.2.2.2.2.2
  rw [hdet, hPV] at hr
  have hfac : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  change (volume (simplexSet S)).toReal = _
  field_simp [hfac] at hr ⊢
  nlinarith [hr]

end Entry005
