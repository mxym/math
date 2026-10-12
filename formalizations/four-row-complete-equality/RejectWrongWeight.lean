import FourRowCompleteEquality
open FourRowTradeoff
-- Deliberately invalid: the flat matrix does not attain the weight-one bound.
example : ‖flatMatrix.permanent‖ + ‖flatMatrix.det‖ = 2 * rowProduct flatMatrix := by
  norm_num [flat_permanent,flat_det,flat_rowProduct]
