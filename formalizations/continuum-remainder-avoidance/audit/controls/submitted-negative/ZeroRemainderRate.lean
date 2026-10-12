import ContinuumRemainder.FinalProof
open Set ContinuumGeometric ContinuumRemainder
set_option autoImplicit false
example : 4 * ((2 ^ (0+0+2) : ℕ) : ℝ) * errorRadius 1 0 0 1 0 < 1 := by
  norm_num [errorRadius]
