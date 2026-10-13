import GaussianHomogeneity
open GaussianMeasureBridge GaussianFourGlobal
-- Deliberately false: the zero-score value is zero, not one.
example : balancedValue (0 : Fin 4 → Space 3) = 1 := by
  rw [balancedValue_zero]
  norm_num
