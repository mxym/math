import APPT.Core
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators
namespace APPT.Uniform

noncomputable def spectrum (g : Fin 9 → ℝ) : Fin 9 → ℝ :=
  ![(((g 0 + g 1) + (g 2 + g 3)) + ((g 4 + g 5) + (g 6 + (g 7 + g 8)))), (((g 1 + g 2) + (g 3 + g 4)) + ((g 5 + g 6) + (g 7 + g 8))), ((g 2 + (g 3 + g 4)) + ((g 5 + g 6) + (g 7 + g 8))), ((g 3 + (g 4 + g 5)) + (g 6 + (g 7 + g 8))), ((g 4 + g 5) + (g 6 + (g 7 + g 8))), ((g 5 + g 6) + (g 7 + g 8)), (g 6 + (g 7 + g 8)), (g 7 + g 8), g 8]
noncomputable def outer (g : Fin 9 → ℝ) : Fin 9 → ℝ :=
  ![spectrum g 0, spectrum g 1, spectrum g 2, spectrum g 3, spectrum g 4, spectrum g 5, spectrum g 6, spectrum g 7, spectrum g 8]
noncomputable def total (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (∑ i, spectrum g i) + t*outer g 2 + z*outer g 3
noncomputable def squareTotal (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (∑ i, (spectrum g i)^2) + t*(outer g 2)^2 + z*(outer g 3)^2
noncomputable def mix (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := t*outer g 2-z*outer g 3
noncomputable def score (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := 9*total g t z-4*(9+t+z)*(outer g 2+outer g 3)
end APPT.Uniform
