import ContinuumRemainder.FinalProof
open Set ContinuumGeometric ContinuumRemainder
set_option autoImplicit false
example : (1 : ℝ) * (1/4 : ℝ) ^ (2+4 : ℝ) ≤ errorRadius 1 0 4 1 3 := by
  norm_num [errorRadius, Real.rpow_neg, Real.rpow_natCast]
