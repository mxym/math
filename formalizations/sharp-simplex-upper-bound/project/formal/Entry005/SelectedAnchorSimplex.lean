import Entry005.AnchorCoordinates
import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
open scoped BigOperators Matrix

namespace Entry005

theorem selected_anchor_raw_affineIndependent {d : ℕ}
    (w : Fin (d + 1) → Fin d → ℝ) (hdet : (anchorMatrix w).det ≠ 0) :
    AffineIndependent ℝ w := by
  have hlin := Matrix.linearIndependent_cols_of_det_ne_zero hdet
  rw [affineIndependent_iff]
  intro s a hsum hs
  have hcols : ∑ i ∈ s, a i • (anchorMatrix w).col i = 0 := by
    ext r
    induction r using Fin.cases with
    | zero => simpa [Matrix.col, anchor_matrix_entry] using hsum
    | succ r =>
      have hr := congrFun hs r
      simpa [Matrix.col, anchor_matrix_entry, Finset.sum_apply, Pi.smul_apply] using hr
  exact linearIndependent_iff'.mp hlin s a hcols

theorem selected_anchor_affineIndependent {d : ℕ}
    (w : Fin (d + 1) → Fin d → ℝ) (hdet : (anchorMatrix w).det ≠ 0) :
    AffineIndependent ℝ (fun i => WithLp.toLp 2 (w i)) := by
  let e := (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm.toAffineEquiv
  exact (e.affineIndependent_iff).2 (selected_anchor_raw_affineIndependent w hdet)

def selectedAnchorSimplex {d : ℕ} (w : Fin (d + 1) → Fin d → ℝ)
    (hdet : (anchorMatrix w).det ≠ 0) :
    Affine.Simplex ℝ (EuclideanSpace ℝ (Fin d)) d where
  points := fun i => WithLp.toLp 2 (w i)
  independent := selected_anchor_affineIndependent w hdet

@[simp] theorem selectedAnchorSimplex_points {d : ℕ}
    (w : Fin (d + 1) → Fin d → ℝ) (hdet : (anchorMatrix w).det ≠ 0)
    (i : Fin (d + 1)) :
    (selectedAnchorSimplex w hdet).points i = WithLp.toLp 2 (w i) := rfl

end Entry005
