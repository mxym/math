import VariableTree

-- This file MUST fail: suppressing the gap contribution is unsound.
example : GrowingGap.span 2 1 0 1 ≤ 0 := by
  norm_num [GrowingGap.span]
