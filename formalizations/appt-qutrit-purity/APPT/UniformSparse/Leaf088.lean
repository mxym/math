import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff1125 : CoefficientMerge.Poly :=
  [(786816, 1)]
noncomputable def atom1125 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 2 * (g 4) ^ 1 * (t) ^ 3)
theorem atom1125_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1125 g t z = CoefficientMerge.eval (monomial g t z) coeff1125 := by
  norm_num [atom1125, coeff1125, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1125_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1125 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1125]
  positivity
theorem weighted1125_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (34965315040072701360766864405053209750483426263981471579979245140620628163671539684840526901481039264574138557180829260863685669654630400 : Int) coeff1125) := by
  rw [CoefficientMerge.eval_scale, ← atom1125_identity]
  exact mul_nonneg (by norm_num) (atom1125_nonneg g t z hg hA hB ht hz hw)

def coeff1126 : CoefficientMerge.Poly :=
  [(787584, 1)]
noncomputable def atom1126 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 2 * (g 5) ^ 1 * (t) ^ 3)
theorem atom1126_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1126 g t z = CoefficientMerge.eval (monomial g t z) coeff1126 := by
  norm_num [atom1126, coeff1126, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1126_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1126 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1126]
  positivity
theorem weighted1126_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (90175177652616240573789291862766445399383454955238938773329515196800168161535540996444269171824427402622590232124081653098844782086112000 : Int) coeff1126) := by
  rw [CoefficientMerge.eval_scale, ← atom1126_identity]
  exact mul_nonneg (by norm_num) (atom1126_nonneg g t z hg hA hB ht hz hw)

def coeff1127 : CoefficientMerge.Poly :=
  [(790656, 1)]
noncomputable def atom1127 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 2 * (g 6) ^ 1 * (t) ^ 3)
theorem atom1127_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1127 g t z = CoefficientMerge.eval (monomial g t z) coeff1127 := by
  norm_num [atom1127, coeff1127, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1127_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1127 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1127]
  positivity
theorem weighted1127_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (77139394980189994081120110778887838319494041174088978888555721436645207491243927571286765583744564698686328622944464795904094242704950400 : Int) coeff1127) := by
  rw [CoefficientMerge.eval_scale, ← atom1127_identity]
  exact mul_nonneg (by norm_num) (atom1127_nonneg g t z hg hA hB ht hz hw)

def coeff1128 : CoefficientMerge.Poly :=
  [(802944, 1)]
noncomputable def atom1128 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 2 * (g 7) ^ 1 * (t) ^ 3)
theorem atom1128_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1128 g t z = CoefficientMerge.eval (monomial g t z) coeff1128 := by
  norm_num [atom1128, coeff1128, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1128_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1128 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1128]
  positivity
theorem weighted1128_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (68173698105828324582634890997851312535587574327243786338672840677900935386094338250082465158827772893513935029617937458325139770573468800 : Int) coeff1128) := by
  rw [CoefficientMerge.eval_scale, ← atom1128_identity]
  exact mul_nonneg (by norm_num) (atom1128_nonneg g t z hg hA hB ht hz hw)

def coeff1129 : CoefficientMerge.Poly :=
  [(852096, 1)]
noncomputable def atom1129 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 2 * (g 8) ^ 1 * (t) ^ 3)
theorem atom1129_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1129 g t z = CoefficientMerge.eval (monomial g t z) coeff1129 := by
  norm_num [atom1129, coeff1129, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1129_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1129 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1129]
  positivity
theorem weighted1129_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (52277458121403620658735037400833254855024686370756210620860433320377518481667688211391146741442162313518403794895882773326147312589161600 : Int) coeff1129) := by
  rw [CoefficientMerge.eval_scale, ← atom1129_identity]
  exact mul_nonneg (by norm_num) (atom1129_nonneg g t z hg hA hB ht hz hw)

def coeff1130 : CoefficientMerge.Poly :=
  [(1573056, 1)]
noncomputable def atom1130 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 3 * (t) ^ 2 * (z) ^ 1)
theorem atom1130_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1130 g t z = CoefficientMerge.eval (monomial g t z) coeff1130 := by
  norm_num [atom1130, coeff1130, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1130_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1130 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1130]
  positivity
theorem weighted1130_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (21113894009412530202118464962260631775644527603756139048541883141275076821902132649309506768637508540909592648653217811990639488252928000 : Int) coeff1130) := by
  rw [CoefficientMerge.eval_scale, ← atom1130_identity]
  exact mul_nonneg (by norm_num) (atom1130_nonneg g t z hg hA hB ht hz hw)

def coeff1131 : CoefficientMerge.Poly :=
  [(1573248, 1)]
noncomputable def atom1131 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 2 * (g 4) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1131_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1131 g t z = CoefficientMerge.eval (monomial g t z) coeff1131 := by
  norm_num [atom1131, coeff1131, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1131_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1131 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1131]
  positivity
theorem weighted1131_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (111215520076111809829291672828877345551284930113548731062985181550123807652051214721905955368230263685731418129334867581389309933147485440 : Int) coeff1131) := by
  rw [CoefficientMerge.eval_scale, ← atom1131_identity]
  exact mul_nonneg (by norm_num) (atom1131_nonneg g t z hg hA hB ht hz hw)

def coeff1132 : CoefficientMerge.Poly :=
  [(1574016, 1)]
noncomputable def atom1132 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 2 * (g 5) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1132_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1132 g t z = CoefficientMerge.eval (monomial g t z) coeff1132 := by
  norm_num [atom1132, coeff1132, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1132_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1132 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1132]
  positivity
theorem weighted1132_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (241093953495245018256233227803225016427314651015476271857253178440153935009474507371536103741151742359526438390851339218710768501559752800 : Int) coeff1132) := by
  rw [CoefficientMerge.eval_scale, ← atom1132_identity]
  exact mul_nonneg (by norm_num) (atom1132_nonneg g t z hg hA hB ht hz hw)

def coeff1133 : CoefficientMerge.Poly :=
  [(1577088, 1)]
noncomputable def atom1133 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 2 * (g 6) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1133_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1133 g t z = CoefficientMerge.eval (monomial g t z) coeff1133 := by
  norm_num [atom1133, coeff1133, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1133_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1133 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1133]
  positivity
theorem weighted1133_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (185233229328687706418342869475952687919147435865442646356841855908088559817080746115839484692822943573362590208999804930811518874315683920 : Int) coeff1133) := by
  rw [CoefficientMerge.eval_scale, ← atom1133_identity]
  exact mul_nonneg (by norm_num) (atom1133_nonneg g t z hg hA hB ht hz hw)

def coeff1134 : CoefficientMerge.Poly :=
  [(1589376, 1)]
noncomputable def atom1134 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 2 * (g 7) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1134_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1134 g t z = CoefficientMerge.eval (monomial g t z) coeff1134 := by
  norm_num [atom1134, coeff1134, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1134_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1134 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1134]
  positivity
theorem weighted1134_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (172910426063444666416825167928998773159032462310900356538893504609063810199377888861038979416177639734382599632147799784900280170746285520 : Int) coeff1134) := by
  rw [CoefficientMerge.eval_scale, ← atom1134_identity]
  exact mul_nonneg (by norm_num) (atom1134_nonneg g t z hg hA hB ht hz hw)

def coeff1135 : CoefficientMerge.Poly :=
  [(1638528, 1)]
noncomputable def atom1135 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 2 * (g 8) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1135_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1135 g t z = CoefficientMerge.eval (monomial g t z) coeff1135 := by
  norm_num [atom1135, coeff1135, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1135_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1135 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1135]
  positivity
theorem weighted1135_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (113433779618877771025785003134067070722621706202585294893624073928718892081668711485499054505303413889900343932741593530560546004073786320 : Int) coeff1135) := by
  rw [CoefficientMerge.eval_scale, ← atom1135_identity]
  exact mul_nonneg (by norm_num) (atom1135_nonneg g t z hg hA hB ht hz hw)

def coeff1136 : CoefficientMerge.Poly :=
  [(787008, 1)]
noncomputable def atom1136 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 2 * (t) ^ 3)
theorem atom1136_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1136 g t z = CoefficientMerge.eval (monomial g t z) coeff1136 := by
  norm_num [atom1136, coeff1136, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1136_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1136 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1136]
  positivity
theorem weighted1136_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (31265597298559211630276377573900246965131783635918281131017721137091232465583521755430599149918952019090399788147476227395603855196364800 : Int) coeff1136) := by
  rw [CoefficientMerge.eval_scale, ← atom1136_identity]
  exact mul_nonneg (by norm_num) (atom1136_nonneg g t z hg hA hB ht hz hw)

def coeff1137 : CoefficientMerge.Poly :=
  [(787776, 1)]
noncomputable def atom1137 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 1 * (g 5) ^ 1 * (t) ^ 3)
theorem atom1137_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1137 g t z = CoefficientMerge.eval (monomial g t z) coeff1137 := by
  norm_num [atom1137, coeff1137, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1137_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1137 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1137]
  positivity
theorem weighted1137_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (184191828917048634784615480969255808529954653073089657627786117956279853798641235798251454381286383227850347111334361480132225198586905600 : Int) coeff1137) := by
  rw [CoefficientMerge.eval_scale, ← atom1137_identity]
  exact mul_nonneg (by norm_num) (atom1137_nonneg g t z hg hA hB ht hz hw)

def coeff1138 : CoefficientMerge.Poly :=
  [(790848, 1)]
noncomputable def atom1138 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (t) ^ 3)
theorem atom1138_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1138 g t z = CoefficientMerge.eval (monomial g t z) coeff1138 := by
  norm_num [atom1138, coeff1138, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1138_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1138 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1138]
  positivity
theorem weighted1138_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (105485835175553705256545799322535947818700474861589239960893273547053946197281270725530134320733807173978003131214057718398007030506800000 : Int) coeff1138) := by
  rw [CoefficientMerge.eval_scale, ← atom1138_identity]
  exact mul_nonneg (by norm_num) (atom1138_nonneg g t z hg hA hB ht hz hw)

def coeff1139 : CoefficientMerge.Poly :=
  [(803136, 1)]
noncomputable def atom1139 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (t) ^ 3)
theorem atom1139_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1139 g t z = CoefficientMerge.eval (monomial g t z) coeff1139 := by
  norm_num [atom1139, coeff1139, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1139_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1139 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1139]
  positivity
theorem weighted1139_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (81209513272479053762223381185130844961265153707994367418515606478517820637278770098171931262018021449839318722657732293333403546276233600 : Int) coeff1139) := by
  rw [CoefficientMerge.eval_scale, ← atom1139_identity]
  exact mul_nonneg (by norm_num) (atom1139_nonneg g t z hg hA hB ht hz hw)

def coeff1140 : CoefficientMerge.Poly :=
  [(852288, 1)]
noncomputable def atom1140 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (t) ^ 3)
theorem atom1140_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1140 g t z = CoefficientMerge.eval (monomial g t z) coeff1140 := by
  norm_num [atom1140, coeff1140, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1140_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1140 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1140]
  positivity
theorem weighted1140_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (31752146378158397519756054799087561560668741349813105886751145783337757065891148415305948903181354499097997877629130888473067726420432000 : Int) coeff1140) := by
  rw [CoefficientMerge.eval_scale, ← atom1140_identity]
  exact mul_nonneg (by norm_num) (atom1140_nonneg g t z hg hA hB ht hz hw)

def coeff1141 : CoefficientMerge.Poly :=
  [(1573440, 1)]
noncomputable def atom1141 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 2 * (t) ^ 2 * (z) ^ 1)
theorem atom1141_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1141 g t z = CoefficientMerge.eval (monomial g t z) coeff1141 := by
  norm_num [atom1141, coeff1141, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1141_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1141 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1141]
  positivity
theorem weighted1141_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (100534275275269911914300131997282226682772604481032236154899762394075529032668857210740322572287337219968347837004133068217169819199692800 : Int) coeff1141) := by
  rw [CoefficientMerge.eval_scale, ← atom1141_identity]
  exact mul_nonneg (by norm_num) (atom1141_nonneg g t z hg hA hB ht hz hw)

def coeff1142 : CoefficientMerge.Poly :=
  [(1574208, 1)]
noncomputable def atom1142 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 1 * (g 5) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1142_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1142 g t z = CoefficientMerge.eval (monomial g t z) coeff1142 := by
  norm_num [atom1142, coeff1142, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1142_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1142 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1142]
  positivity
theorem weighted1142_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (554414969941653629248444401757066015028895621609567859471973690346074448652415508437557532928636092301396780809625195073372750481995752576 : Int) coeff1142) := by
  rw [CoefficientMerge.eval_scale, ← atom1142_identity]
  exact mul_nonneg (by norm_num) (atom1142_nonneg g t z hg hA hB ht hz hw)

def coeff1143 : CoefficientMerge.Poly :=
  [(1577280, 1)]
noncomputable def atom1143 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1143_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1143 g t z = CoefficientMerge.eval (monomial g t z) coeff1143 := by
  norm_num [atom1143, coeff1143, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1143_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1143 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1143]
  positivity
theorem weighted1143_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (352323774514183813239844113884449291531365411423766374688751782751820651315681683388674188440288488157290241122843121526144754963809882320 : Int) coeff1143) := by
  rw [CoefficientMerge.eval_scale, ← atom1143_identity]
  exact mul_nonneg (by norm_num) (atom1143_nonneg g t z hg hA hB ht hz hw)

def coeff1144 : CoefficientMerge.Poly :=
  [(1589568, 1)]
noncomputable def atom1144 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1144_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1144 g t z = CoefficientMerge.eval (monomial g t z) coeff1144 := by
  norm_num [atom1144, coeff1144, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1144_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1144 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1144]
  positivity
theorem weighted1144_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (309481397209057918832141667551881421302382892849351685535142202010224763332339049071847424537270951778222038555298339178236085558714919120 : Int) coeff1144) := by
  rw [CoefficientMerge.eval_scale, ← atom1144_identity]
  exact mul_nonneg (by norm_num) (atom1144_nonneg g t z hg hA hB ht hz hw)

def sparseBlock088 : CoefficientMerge.Poly :=
  [(786816, 34965315040072701360766864405053209750483426263981471579979245140620628163671539684840526901481039264574138557180829260863685669654630400), (787008, 31265597298559211630276377573900246965131783635918281131017721137091232465583521755430599149918952019090399788147476227395603855196364800), (787584, 90175177652616240573789291862766445399383454955238938773329515196800168161535540996444269171824427402622590232124081653098844782086112000), (787776, 184191828917048634784615480969255808529954653073089657627786117956279853798641235798251454381286383227850347111334361480132225198586905600), (790656, 77139394980189994081120110778887838319494041174088978888555721436645207491243927571286765583744564698686328622944464795904094242704950400), (790848, 105485835175553705256545799322535947818700474861589239960893273547053946197281270725530134320733807173978003131214057718398007030506800000), (802944, 68173698105828324582634890997851312535587574327243786338672840677900935386094338250082465158827772893513935029617937458325139770573468800), (803136, 81209513272479053762223381185130844961265153707994367418515606478517820637278770098171931262018021449839318722657732293333403546276233600), (852096, 52277458121403620658735037400833254855024686370756210620860433320377518481667688211391146741442162313518403794895882773326147312589161600), (852288, 31752146378158397519756054799087561560668741349813105886751145783337757065891148415305948903181354499097997877629130888473067726420432000), (1573056, 21113894009412530202118464962260631775644527603756139048541883141275076821902132649309506768637508540909592648653217811990639488252928000), (1573248, 111215520076111809829291672828877345551284930113548731062985181550123807652051214721905955368230263685731418129334867581389309933147485440), (1573440, 100534275275269911914300131997282226682772604481032236154899762394075529032668857210740322572287337219968347837004133068217169819199692800), (1574016, 241093953495245018256233227803225016427314651015476271857253178440153935009474507371536103741151742359526438390851339218710768501559752800), (1574208, 554414969941653629248444401757066015028895621609567859471973690346074448652415508437557532928636092301396780809625195073372750481995752576), (1577088, 185233229328687706418342869475952687919147435865442646356841855908088559817080746115839484692822943573362590208999804930811518874315683920), (1577280, 352323774514183813239844113884449291531365411423766374688751782751820651315681683388674188440288488157290241122843121526144754963809882320), (1589376, 172910426063444666416825167928998773159032462310900356538893504609063810199377888861038979416177639734382599632147799784900280170746285520), (1589568, 309481397209057918832141667551881421302382892849351685535142202010224763332339049071847424537270951778222038555298339178236085558714919120), (1638528, 113433779618877771025785003134067070722621706202585294893624073928718892081668711485499054505303413889900343932741593530560546004073786320)]
theorem sparseBlock088_data : sparseBlock088 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (34965315040072701360766864405053209750483426263981471579979245140620628163671539684840526901481039264574138557180829260863685669654630400 : Int) coeff1125) (CoefficientMerge.scale (90175177652616240573789291862766445399383454955238938773329515196800168161535540996444269171824427402622590232124081653098844782086112000 : Int) coeff1126)) (CoefficientMerge.merge (CoefficientMerge.scale (77139394980189994081120110778887838319494041174088978888555721436645207491243927571286765583744564698686328622944464795904094242704950400 : Int) coeff1127) (CoefficientMerge.merge (CoefficientMerge.scale (68173698105828324582634890997851312535587574327243786338672840677900935386094338250082465158827772893513935029617937458325139770573468800 : Int) coeff1128) (CoefficientMerge.scale (52277458121403620658735037400833254855024686370756210620860433320377518481667688211391146741442162313518403794895882773326147312589161600 : Int) coeff1129)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (21113894009412530202118464962260631775644527603756139048541883141275076821902132649309506768637508540909592648653217811990639488252928000 : Int) coeff1130) (CoefficientMerge.scale (111215520076111809829291672828877345551284930113548731062985181550123807652051214721905955368230263685731418129334867581389309933147485440 : Int) coeff1131)) (CoefficientMerge.merge (CoefficientMerge.scale (241093953495245018256233227803225016427314651015476271857253178440153935009474507371536103741151742359526438390851339218710768501559752800 : Int) coeff1132) (CoefficientMerge.merge (CoefficientMerge.scale (185233229328687706418342869475952687919147435865442646356841855908088559817080746115839484692822943573362590208999804930811518874315683920 : Int) coeff1133) (CoefficientMerge.scale (172910426063444666416825167928998773159032462310900356538893504609063810199377888861038979416177639734382599632147799784900280170746285520 : Int) coeff1134))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (113433779618877771025785003134067070722621706202585294893624073928718892081668711485499054505303413889900343932741593530560546004073786320 : Int) coeff1135) (CoefficientMerge.scale (31265597298559211630276377573900246965131783635918281131017721137091232465583521755430599149918952019090399788147476227395603855196364800 : Int) coeff1136)) (CoefficientMerge.merge (CoefficientMerge.scale (184191828917048634784615480969255808529954653073089657627786117956279853798641235798251454381286383227850347111334361480132225198586905600 : Int) coeff1137) (CoefficientMerge.merge (CoefficientMerge.scale (105485835175553705256545799322535947818700474861589239960893273547053946197281270725530134320733807173978003131214057718398007030506800000 : Int) coeff1138) (CoefficientMerge.scale (81209513272479053762223381185130844961265153707994367418515606478517820637278770098171931262018021449839318722657732293333403546276233600 : Int) coeff1139)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (31752146378158397519756054799087561560668741349813105886751145783337757065891148415305948903181354499097997877629130888473067726420432000 : Int) coeff1140) (CoefficientMerge.scale (100534275275269911914300131997282226682772604481032236154899762394075529032668857210740322572287337219968347837004133068217169819199692800 : Int) coeff1141)) (CoefficientMerge.merge (CoefficientMerge.scale (554414969941653629248444401757066015028895621609567859471973690346074448652415508437557532928636092301396780809625195073372750481995752576 : Int) coeff1142) (CoefficientMerge.merge (CoefficientMerge.scale (352323774514183813239844113884449291531365411423766374688751782751820651315681683388674188440288488157290241122843121526144754963809882320 : Int) coeff1143) (CoefficientMerge.scale (309481397209057918832141667551881421302382892849351685535142202010224763332339049071847424537270951778222038555298339178236085558714919120 : Int) coeff1144)))))) := by decide +kernel
theorem sparseBlock088_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock088 := by
  rw [sparseBlock088_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted1125_nonneg g t z hg hA hB ht hz hw) (weighted1126_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1127_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1128_nonneg g t z hg hA hB ht hz hw) (weighted1129_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1130_nonneg g t z hg hA hB ht hz hw) (weighted1131_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1132_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1133_nonneg g t z hg hA hB ht hz hw) (weighted1134_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted1135_nonneg g t z hg hA hB ht hz hw) (weighted1136_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1137_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1138_nonneg g t z hg hA hB ht hz hw) (weighted1139_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1140_nonneg g t z hg hA hB ht hz hw) (weighted1141_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1142_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1143_nonneg g t z hg hA hB ht hz hw) (weighted1144_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
