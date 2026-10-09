import APPT.CoefficientMerge
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
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

theorem ratio_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) : 0 ≤ ratio (outer g) := by
  have hq := quadA_nonneg (outer g) hA ![1,1,1]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  simp [ratio, quadA, matA, Matrix.mulVec, dotProduct, outer, spectrum, Fin.sum_univ_succ] at hq ⊢
  linarith

noncomputable def scale : ℝ := 31507789656333080410718713123872213089045937377022794310110381275404396384846329699207061362533534184810586849231407590814708260061184000
theorem scale_pos : (0 : ℝ) < scale := by norm_num [scale]

noncomputable def monomial (g : Fin 9 → ℝ) (t z : ℝ) (k : Nat) : ℝ :=
  (g 0)^(k / 1 % 4) * (g 1)^(k / 4 % 4) * (g 2)^(k / 16 % 4) * (g 3)^(k / 64 % 4) * (g 4)^(k / 256 % 4) * (g 5)^(k / 1024 % 4) * (g 6)^(k / 4096 % 4) * (g 7)^(k / 16384 % 4) * (g 8)^(k / 65536 % 4) * t^(k / 262144 % 4) * z^(k / 1048576 % 4)

end APPT.Uniform
