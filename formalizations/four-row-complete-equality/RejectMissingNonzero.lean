import FourRowCompleteEquality
open FourRowTradeoff
-- Deliberately invalid: the zero-row case cannot be discarded.
example : IsFlatRankOne (0 : Mat) ∨ IsMonomial (0 : Mat) := by
  apply critical_equality_only (0 : Mat)
  · simp [NonzeroRows]
  · norm_num [rowProduct,rowNorm,rowSq]
