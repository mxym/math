import ContinuumRemainder.FinalProof
open Set ContinuumGeometric ContinuumRemainder
set_option autoImplicit false
example : (1 : ℝ) * (4 : ℝ) ^ (1+6 : ℝ) ≤ errorRadius 1 0 6 3 (-3) := by
  norm_num [errorRadius, Real.rpow_neg, Real.rpow_natCast]
