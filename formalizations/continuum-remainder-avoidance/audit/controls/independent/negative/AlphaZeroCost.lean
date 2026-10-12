import ContinuumRemainder.ErrorDomination
open ContinuumRemainder
example : 4 * (2 : ℝ)^(20+2 : ℕ) * errorRadius 1 0 0 1 20 < 1 := by
  norm_num [errorRadius, Real.rpow_natCast, Real.rpow_neg]
