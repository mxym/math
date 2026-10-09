import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff0745 : CoefficientMerge.Poly :=
  [(1118212, 1)]
noncomputable def atom0745 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (z) ^ 1)
theorem atom0745_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0745 g t z = CoefficientMerge.eval (monomial g t z) coeff0745 := by
  norm_num [atom0745, coeff0745, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0745_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0745 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0745]
  positivity
theorem weighted0745_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (8699011487806134488316037376330224986451548165790049411900591297781818535627276314900924008706984933736395097952450195375374386961885158400 : Int) coeff0745) := by
  rw [CoefficientMerge.eval_scale, ← atom0745_identity]
  exact mul_nonneg (by norm_num) (atom0745_nonneg g t z hg hA hB ht hz hw)

def coeff0746 : CoefficientMerge.Poly :=
  [(81924, 1)]
noncomputable def atom0746 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1)
theorem atom0746_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0746 g t z = CoefficientMerge.eval (monomial g t z) coeff0746 := by
  norm_num [atom0746, coeff0746, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0746_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0746 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0746]
  positivity
theorem weighted0746_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (17632770787975592762140217481479326241221922205358721380277559499508401821407699321944347730534210149476074632053762253914534404322689843200 : Int) coeff0746) := by
  rw [CoefficientMerge.eval_scale, ← atom0746_identity]
  exact mul_nonneg (by norm_num) (atom0746_nonneg g t z hg hA hB ht hz hw)

def coeff0747 : CoefficientMerge.Poly :=
  [(131076, 1)]
noncomputable def atom0747 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 8) ^ 2)
theorem atom0747_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0747 g t z = CoefficientMerge.eval (monomial g t z) coeff0747 := by
  norm_num [atom0747, coeff0747, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0747_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0747 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0747]
  positivity
theorem weighted0747_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (7631166972755906145666323723810804481325386982200035938829520411358665976277513986300501984980282596238882865078592653960291040898566553600 : Int) coeff0747) := by
  rw [CoefficientMerge.eval_scale, ← atom0747_identity]
  exact mul_nonneg (by norm_num) (atom0747_nonneg g t z hg hA hB ht hz hw)

def coeff0748 : CoefficientMerge.Poly :=
  [(344068, 1)]
noncomputable def atom0748 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (t) ^ 1)
theorem atom0748_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0748 g t z = CoefficientMerge.eval (monomial g t z) coeff0748 := by
  norm_num [atom0748, coeff0748, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0748_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0748 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0748]
  positivity
theorem weighted0748_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5121513732867389529353554909742250223570897957640403766125714571946422841176597915939441115645262649404533970435055774353707543941801420800 : Int) coeff0748) := by
  rw [CoefficientMerge.eval_scale, ← atom0748_identity]
  exact mul_nonneg (by norm_num) (atom0748_nonneg g t z hg hA hB ht hz hw)

def coeff0749 : CoefficientMerge.Poly :=
  [(393220, 1)]
noncomputable def atom0749 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 8) ^ 2 * (t) ^ 1)
theorem atom0749_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0749 g t z = CoefficientMerge.eval (monomial g t z) coeff0749 := by
  norm_num [atom0749, coeff0749, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0749_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0749 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0749]
  positivity
theorem weighted0749_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2447193611724690499889724748756699613221233988914533468240501804201299732998148794601326689717519269466482345242956869270751899037043916800 : Int) coeff0749) := by
  rw [CoefficientMerge.eval_scale, ← atom0749_identity]
  exact mul_nonneg (by norm_num) (atom0749_nonneg g t z hg hA hB ht hz hw)

def coeff0750 : CoefficientMerge.Poly :=
  [(1130500, 1)]
noncomputable def atom0750 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (z) ^ 1)
theorem atom0750_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0750 g t z = CoefficientMerge.eval (monomial g t z) coeff0750 := by
  norm_num [atom0750, coeff0750, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0750_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0750 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0750]
  positivity
theorem weighted0750_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5711457983758524312986445041244820302660011840720622791176483490100814532567639232865656954286356255776001801472951885938542451195699686400 : Int) coeff0750) := by
  rw [CoefficientMerge.eval_scale, ← atom0750_identity]
  exact mul_nonneg (by norm_num) (atom0750_nonneg g t z hg hA hB ht hz hw)

def coeff0751 : CoefficientMerge.Poly :=
  [(1179652, 1)]
noncomputable def atom0751 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 8) ^ 2 * (z) ^ 1)
theorem atom0751_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0751 g t z = CoefficientMerge.eval (monomial g t z) coeff0751 := by
  norm_num [atom0751, coeff0751, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0751_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0751 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0751]
  positivity
theorem weighted0751_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2447193611724690499889724748756699613221233988914533468240501804201299732998148794601326689717519269466482345242956869270751899037043916800 : Int) coeff0751) := by
  rw [CoefficientMerge.eval_scale, ← atom0751_identity]
  exact mul_nonneg (by norm_num) (atom0751_nonneg g t z hg hA hB ht hz hw)

def coeff0752 : CoefficientMerge.Poly :=
  [(524372, 1)]
noncomputable def atom0752 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 3) ^ 1 * (t) ^ 2)
theorem atom0752_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0752 g t z = CoefficientMerge.eval (monomial g t z) coeff0752 := by
  norm_num [atom0752, coeff0752, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0752_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0752 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0752]
  positivity
theorem weighted0752_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (840731337404685991284701152775079101675309148544474198783190750623035507247615912642137023622276473697563913427166981361628833933173575680 : Int) coeff0752) := by
  rw [CoefficientMerge.eval_scale, ← atom0752_identity]
  exact mul_nonneg (by norm_num) (atom0752_nonneg g t z hg hA hB ht hz hw)

def coeff0753 : CoefficientMerge.Poly :=
  [(524564, 1)]
noncomputable def atom0753 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 4) ^ 1 * (t) ^ 2)
theorem atom0753_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0753 g t z = CoefficientMerge.eval (monomial g t z) coeff0753 := by
  norm_num [atom0753, coeff0753, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0753_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0753 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0753]
  positivity
theorem weighted0753_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1052277044817555216972417531124989973321672025128946273540709039935063210787210133942453314737454949831018744632130099210809514985165952000 : Int) coeff0753) := by
  rw [CoefficientMerge.eval_scale, ← atom0753_identity]
  exact mul_nonneg (by norm_num) (atom0753_nonneg g t z hg hA hB ht hz hw)

def coeff0754 : CoefficientMerge.Poly :=
  [(525332, 1)]
noncomputable def atom0754 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 5) ^ 1 * (t) ^ 2)
theorem atom0754_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0754 g t z = CoefficientMerge.eval (monomial g t z) coeff0754 := by
  norm_num [atom0754, coeff0754, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0754_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0754 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0754]
  positivity
theorem weighted0754_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1158525179062951079936591152975480473731362110431780620680116843482141992104772921256170270895245168865980760218113444113743718237145856000 : Int) coeff0754) := by
  rw [CoefficientMerge.eval_scale, ← atom0754_identity]
  exact mul_nonneg (by norm_num) (atom0754_nonneg g t z hg hA hB ht hz hw)

def coeff0755 : CoefficientMerge.Poly :=
  [(528404, 1)]
noncomputable def atom0755 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 6) ^ 1 * (t) ^ 2)
theorem atom0755_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0755 g t z = CoefficientMerge.eval (monomial g t z) coeff0755 := by
  norm_num [atom0755, coeff0755, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0755_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0755 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0755]
  positivity
theorem weighted0755_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1346243173096813481938016300010588545043728269881584134754065237140674951024523993559562085382288842989250485841027575792806426071993507840 : Int) coeff0755) := by
  rw [CoefficientMerge.eval_scale, ← atom0755_identity]
  exact mul_nonneg (by norm_num) (atom0755_nonneg g t z hg hA hB ht hz hw)

def coeff0756 : CoefficientMerge.Poly :=
  [(540692, 1)]
noncomputable def atom0756 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 7) ^ 1 * (t) ^ 2)
theorem atom0756_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0756 g t z = CoefficientMerge.eval (monomial g t z) coeff0756 := by
  norm_num [atom0756, coeff0756, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0756_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0756 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0756]
  positivity
theorem weighted0756_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1634098291465849719737093925490885662318290505540532992501169929543368250198959991759960622993668864686570147240881362689057302775996098560 : Int) coeff0756) := by
  rw [CoefficientMerge.eval_scale, ← atom0756_identity]
  exact mul_nonneg (by norm_num) (atom0756_nonneg g t z hg hA hB ht hz hw)

def coeff0757 : CoefficientMerge.Poly :=
  [(589844, 1)]
noncomputable def atom0757 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 8) ^ 1 * (t) ^ 2)
theorem atom0757_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0757 g t z = CoefficientMerge.eval (monomial g t z) coeff0757 := by
  norm_num [atom0757, coeff0757, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0757_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0757 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0757]
  positivity
theorem weighted0757_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2752877278610608011851374816859544542027265743331034192160079870745391382908037588818104307318335266783413888290177346549123754867520358400 : Int) coeff0757) := by
  rw [CoefficientMerge.eval_scale, ← atom0757_identity]
  exact mul_nonneg (by norm_num) (atom0757_nonneg g t z hg hA hB ht hz hw)

def coeff0758 : CoefficientMerge.Poly :=
  [(1310804, 1)]
noncomputable def atom0758 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 3) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0758_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0758 g t z = CoefficientMerge.eval (monomial g t z) coeff0758 := by
  norm_num [atom0758, coeff0758, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0758_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0758 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0758]
  positivity
theorem weighted0758_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1536673871793707338813764874156903543078854513465980943136569230814281160074369627322657975871888891733006883868502508113037264453777782784 : Int) coeff0758) := by
  rw [CoefficientMerge.eval_scale, ← atom0758_identity]
  exact mul_nonneg (by norm_num) (atom0758_nonneg g t z hg hA hB ht hz hw)

def coeff0759 : CoefficientMerge.Poly :=
  [(1310996, 1)]
noncomputable def atom0759 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 4) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0759_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0759 g t z = CoefficientMerge.eval (monomial g t z) coeff0759 := by
  norm_num [atom0759, coeff0759, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0759_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0759 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0759]
  positivity
theorem weighted0759_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2564982984954843563823835549750568330593324913415564947790204060226775701972916430051945173627904024866110354841830857883852812438750119040 : Int) coeff0759) := by
  rw [CoefficientMerge.eval_scale, ← atom0759_identity]
  exact mul_nonneg (by norm_num) (atom0759_nonneg g t z hg hA hB ht hz hw)

def coeff0760 : CoefficientMerge.Poly :=
  [(1311764, 1)]
noncomputable def atom0760 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 5) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0760_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0760 g t z = CoefficientMerge.eval (monomial g t z) coeff0760 := by
  norm_num [atom0760, coeff0760, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0760_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0760 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0760]
  positivity
theorem weighted0760_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2839026449064747949126759052508847372290275715824132704110197232387972391161219754972034067696662424325692576986383487838753777892326754176 : Int) coeff0760) := by
  rw [CoefficientMerge.eval_scale, ← atom0760_identity]
  exact mul_nonneg (by norm_num) (atom0760_nonneg g t z hg hA hB ht hz hw)

def coeff0761 : CoefficientMerge.Poly :=
  [(1314836, 1)]
noncomputable def atom0761 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0761_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0761 g t z = CoefficientMerge.eval (monomial g t z) coeff0761 := by
  norm_num [atom0761, coeff0761, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0761_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0761 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0761]
  positivity
theorem weighted0761_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1903867711300000775505122374973348139221505653154763914987384743755410212293033072787269242657361787515990529587231072682606059137391703040 : Int) coeff0761) := by
  rw [CoefficientMerge.eval_scale, ← atom0761_identity]
  exact mul_nonneg (by norm_num) (atom0761_nonneg g t z hg hA hB ht hz hw)

def coeff0762 : CoefficientMerge.Poly :=
  [(1327124, 1)]
noncomputable def atom0762 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0762_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0762 g t z = CoefficientMerge.eval (monomial g t z) coeff0762 := by
  norm_num [atom0762, coeff0762, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0762_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0762 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0762]
  positivity
theorem weighted0762_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2148205971222125983825296268690073423619454195202810798886554806908493045911912716868191049806037626207950324168284432464395874220203473920 : Int) coeff0762) := by
  rw [CoefficientMerge.eval_scale, ← atom0762_identity]
  exact mul_nonneg (by norm_num) (atom0762_nonneg g t z hg hA hB ht hz hw)

def coeff0763 : CoefficientMerge.Poly :=
  [(1376276, 1)]
noncomputable def atom0763 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0763_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0763 g t z = CoefficientMerge.eval (monomial g t z) coeff0763 := by
  norm_num [atom0763, coeff0763, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0763_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0763 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0763]
  positivity
theorem weighted0763_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2874763045131983875813818247203299019936473517151774686512598077471863058327337296572107276913829291805928278458382639828052045929065948160 : Int) coeff0763) := by
  rw [CoefficientMerge.eval_scale, ← atom0763_identity]
  exact mul_nonneg (by norm_num) (atom0763_nonneg g t z hg hA hB ht hz hw)

def coeff0764 : CoefficientMerge.Poly :=
  [(524420, 1)]
noncomputable def atom0764 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 2 * (t) ^ 2)
theorem atom0764_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0764 g t z = CoefficientMerge.eval (monomial g t z) coeff0764 := by
  norm_num [atom0764, coeff0764, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0764_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0764 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0764]
  positivity
theorem weighted0764_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1077889684632518474685952392870561089157606138491221443231463959747639023645945421989041954646772166010412194313170688189430586157892485120 : Int) coeff0764) := by
  rw [CoefficientMerge.eval_scale, ← atom0764_identity]
  exact mul_nonneg (by norm_num) (atom0764_nonneg g t z hg hA hB ht hz hw)

def sparseBlock069 : CoefficientMerge.Poly :=
  [(81924, 17632770787975592762140217481479326241221922205358721380277559499508401821407699321944347730534210149476074632053762253914534404322689843200), (131076, 7631166972755906145666323723810804481325386982200035938829520411358665976277513986300501984980282596238882865078592653960291040898566553600), (344068, 5121513732867389529353554909742250223570897957640403766125714571946422841176597915939441115645262649404533970435055774353707543941801420800), (393220, 2447193611724690499889724748756699613221233988914533468240501804201299732998148794601326689717519269466482345242956869270751899037043916800), (524372, 840731337404685991284701152775079101675309148544474198783190750623035507247615912642137023622276473697563913427166981361628833933173575680), (524420, 1077889684632518474685952392870561089157606138491221443231463959747639023645945421989041954646772166010412194313170688189430586157892485120), (524564, 1052277044817555216972417531124989973321672025128946273540709039935063210787210133942453314737454949831018744632130099210809514985165952000), (525332, 1158525179062951079936591152975480473731362110431780620680116843482141992104772921256170270895245168865980760218113444113743718237145856000), (528404, 1346243173096813481938016300010588545043728269881584134754065237140674951024523993559562085382288842989250485841027575792806426071993507840), (540692, 1634098291465849719737093925490885662318290505540532992501169929543368250198959991759960622993668864686570147240881362689057302775996098560), (589844, 2752877278610608011851374816859544542027265743331034192160079870745391382908037588818104307318335266783413888290177346549123754867520358400), (1118212, 8699011487806134488316037376330224986451548165790049411900591297781818535627276314900924008706984933736395097952450195375374386961885158400), (1130500, 5711457983758524312986445041244820302660011840720622791176483490100814532567639232865656954286356255776001801472951885938542451195699686400), (1179652, 2447193611724690499889724748756699613221233988914533468240501804201299732998148794601326689717519269466482345242956869270751899037043916800), (1310804, 1536673871793707338813764874156903543078854513465980943136569230814281160074369627322657975871888891733006883868502508113037264453777782784), (1310996, 2564982984954843563823835549750568330593324913415564947790204060226775701972916430051945173627904024866110354841830857883852812438750119040), (1311764, 2839026449064747949126759052508847372290275715824132704110197232387972391161219754972034067696662424325692576986383487838753777892326754176), (1314836, 1903867711300000775505122374973348139221505653154763914987384743755410212293033072787269242657361787515990529587231072682606059137391703040), (1327124, 2148205971222125983825296268690073423619454195202810798886554806908493045911912716868191049806037626207950324168284432464395874220203473920), (1376276, 2874763045131983875813818247203299019936473517151774686512598077471863058327337296572107276913829291805928278458382639828052045929065948160)]
theorem sparseBlock069_data : sparseBlock069 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (8699011487806134488316037376330224986451548165790049411900591297781818535627276314900924008706984933736395097952450195375374386961885158400 : Int) coeff0745) (CoefficientMerge.scale (17632770787975592762140217481479326241221922205358721380277559499508401821407699321944347730534210149476074632053762253914534404322689843200 : Int) coeff0746)) (CoefficientMerge.merge (CoefficientMerge.scale (7631166972755906145666323723810804481325386982200035938829520411358665976277513986300501984980282596238882865078592653960291040898566553600 : Int) coeff0747) (CoefficientMerge.merge (CoefficientMerge.scale (5121513732867389529353554909742250223570897957640403766125714571946422841176597915939441115645262649404533970435055774353707543941801420800 : Int) coeff0748) (CoefficientMerge.scale (2447193611724690499889724748756699613221233988914533468240501804201299732998148794601326689717519269466482345242956869270751899037043916800 : Int) coeff0749)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (5711457983758524312986445041244820302660011840720622791176483490100814532567639232865656954286356255776001801472951885938542451195699686400 : Int) coeff0750) (CoefficientMerge.scale (2447193611724690499889724748756699613221233988914533468240501804201299732998148794601326689717519269466482345242956869270751899037043916800 : Int) coeff0751)) (CoefficientMerge.merge (CoefficientMerge.scale (840731337404685991284701152775079101675309148544474198783190750623035507247615912642137023622276473697563913427166981361628833933173575680 : Int) coeff0752) (CoefficientMerge.merge (CoefficientMerge.scale (1052277044817555216972417531124989973321672025128946273540709039935063210787210133942453314737454949831018744632130099210809514985165952000 : Int) coeff0753) (CoefficientMerge.scale (1158525179062951079936591152975480473731362110431780620680116843482141992104772921256170270895245168865980760218113444113743718237145856000 : Int) coeff0754))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1346243173096813481938016300010588545043728269881584134754065237140674951024523993559562085382288842989250485841027575792806426071993507840 : Int) coeff0755) (CoefficientMerge.scale (1634098291465849719737093925490885662318290505540532992501169929543368250198959991759960622993668864686570147240881362689057302775996098560 : Int) coeff0756)) (CoefficientMerge.merge (CoefficientMerge.scale (2752877278610608011851374816859544542027265743331034192160079870745391382908037588818104307318335266783413888290177346549123754867520358400 : Int) coeff0757) (CoefficientMerge.merge (CoefficientMerge.scale (1536673871793707338813764874156903543078854513465980943136569230814281160074369627322657975871888891733006883868502508113037264453777782784 : Int) coeff0758) (CoefficientMerge.scale (2564982984954843563823835549750568330593324913415564947790204060226775701972916430051945173627904024866110354841830857883852812438750119040 : Int) coeff0759)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (2839026449064747949126759052508847372290275715824132704110197232387972391161219754972034067696662424325692576986383487838753777892326754176 : Int) coeff0760) (CoefficientMerge.scale (1903867711300000775505122374973348139221505653154763914987384743755410212293033072787269242657361787515990529587231072682606059137391703040 : Int) coeff0761)) (CoefficientMerge.merge (CoefficientMerge.scale (2148205971222125983825296268690073423619454195202810798886554806908493045911912716868191049806037626207950324168284432464395874220203473920 : Int) coeff0762) (CoefficientMerge.merge (CoefficientMerge.scale (2874763045131983875813818247203299019936473517151774686512598077471863058327337296572107276913829291805928278458382639828052045929065948160 : Int) coeff0763) (CoefficientMerge.scale (1077889684632518474685952392870561089157606138491221443231463959747639023645945421989041954646772166010412194313170688189430586157892485120 : Int) coeff0764)))))) := by decide +kernel
theorem sparseBlock069_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock069 := by
  rw [sparseBlock069_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted0745_nonneg g t z hg hA hB ht hz hw) (weighted0746_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0747_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0748_nonneg g t z hg hA hB ht hz hw) (weighted0749_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0750_nonneg g t z hg hA hB ht hz hw) (weighted0751_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0752_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0753_nonneg g t z hg hA hB ht hz hw) (weighted0754_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted0755_nonneg g t z hg hA hB ht hz hw) (weighted0756_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0757_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0758_nonneg g t z hg hA hB ht hz hw) (weighted0759_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0760_nonneg g t z hg hA hB ht hz hw) (weighted0761_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0762_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0763_nonneg g t z hg hA hB ht hz hw) (weighted0764_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
