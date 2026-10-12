import FourRowCompleteEquality
open scoped BigOperators
open FourRowTradeoff

example : IsFlatRankOne flatMatrix := by
  apply subcritical_equality_only flatMatrix
    (fun i => ⟨0, by norm_num [flatMatrix]⟩) 0 (by norm_num)
  norm_num [flat_permanent, flat_det, flat_rowProduct, sharpConstant]

example : IsMonomial (1 : Mat) := by
  apply supercritical_equality_only (1 : Mat)
    (fun i => ⟨i, by simp⟩) 1 (by norm_num)
  norm_num [one_rowProduct, sharpConstant]

example : ‖(0 : Mat).permanent‖ + (2 : ℝ)*‖(0 : Mat).det‖ =
    sharpConstant 2 * rowProduct (0 : Mat) := by
  exact (matrix_equality_iff (0 : Mat) 2 (by norm_num)).mpr
    (Or.inl ⟨0, by simp⟩)
