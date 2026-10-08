import Entry005.SelectedAnchorSimplex

noncomputable section
open scoped BigOperators Matrix

namespace Entry005

theorem selected_anchor_det_ne_zero_of_raw_affineIndependent {d : ℕ}
    (w : Fin (d + 1) → Fin d → ℝ) (hw : AffineIndependent ℝ w) :
    (anchorMatrix w).det ≠ 0 := by
  have hlin : LinearIndependent ℝ (anchorMatrix w).col := by
    apply Fintype.linearIndependent_iff.mpr
    intro a ha
    have hsum : ∑ i, a i = 0 := by
      have h := congrFun ha 0
      simpa [Matrix.col, anchor_matrix_entry] using h
    have hvec : ∑ i, a i • w i = 0 := by
      ext k
      have h := congrFun ha k.succ
      simpa [Matrix.col, anchor_matrix_entry, Finset.sum_apply, Pi.smul_apply] using h
    intro i
    exact hw.eq_zero_of_sum_eq_zero hsum hvec i (Finset.mem_univ i)
  have hunit := Matrix.linearIndependent_cols_iff_isUnit.mp hlin
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det (anchorMatrix w)).mp hunit)

theorem selected_anchor_det_ne_zero_of_affineIndependent {d : ℕ}
    (w : Fin (d + 1) → Fin d → ℝ)
    (hw : AffineIndependent ℝ (fun i => WithLp.toLp 2 (w i))) :
    (anchorMatrix w).det ≠ 0 := by
  let e := (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm.toAffineEquiv
  apply selected_anchor_det_ne_zero_of_raw_affineIndependent w
  exact e.affineIndependent_iff.mp hw

theorem selected_anchor_affineIndependent_iff_det_ne_zero {d : ℕ}
    (w : Fin (d + 1) → Fin d → ℝ) :
    AffineIndependent ℝ (fun i => WithLp.toLp 2 (w i)) ↔ (anchorMatrix w).det ≠ 0 :=
  ⟨selected_anchor_det_ne_zero_of_affineIndependent w, selected_anchor_affineIndependent w⟩

end Entry005
