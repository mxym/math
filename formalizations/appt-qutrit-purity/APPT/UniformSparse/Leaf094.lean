import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff1245 : CoefficientMerge.Poly :=
  [(1643520, 1)]
noncomputable def atom1245 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1245_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1245 g t z = CoefficientMerge.eval (monomial g t z) coeff1245 := by
  norm_num [atom1245, coeff1245, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1245_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1245 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1245]
  positivity
theorem weighted1245_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (444085250767951166849119114536522201166000278509677197232695433967497620147300905344388918957263073481799869098849268583471912431504829440 : Int) coeff1245) := by
  rw [CoefficientMerge.eval_scale, ← atom1245_identity]
  exact mul_nonneg (by norm_num) (atom1245_nonneg g t z hg hA hB ht hz hw)

def coeff1246 : CoefficientMerge.Poly :=
  [(820224, 1)]
noncomputable def atom1246 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 7) ^ 2 * (t) ^ 3)
theorem atom1246_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1246 g t z = CoefficientMerge.eval (monomial g t z) coeff1246 := by
  norm_num [atom1246, coeff1246, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1246_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1246 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1246]
  positivity
theorem weighted1246_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (72189669598950592478294913695992406669652242859735852416924922547879682250344130668829703173462156809377465707683691514102272294683500800 : Int) coeff1246) := by
  rw [CoefficientMerge.eval_scale, ← atom1246_identity]
  exact mul_nonneg (by norm_num) (atom1246_nonneg g t z hg hA hB ht hz hw)

def coeff1247 : CoefficientMerge.Poly :=
  [(869376, 1)]
noncomputable def atom1247 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (t) ^ 3)
theorem atom1247_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1247 g t z = CoefficientMerge.eval (monomial g t z) coeff1247 := by
  norm_num [atom1247, coeff1247, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1247_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1247 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1247]
  positivity
theorem weighted1247_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (100772571401485800748381144006499217059627053454704041514273626185997990175682123553280292571305396209857083388264653650153385284542969600 : Int) coeff1247) := by
  rw [CoefficientMerge.eval_scale, ← atom1247_identity]
  exact mul_nonneg (by norm_num) (atom1247_nonneg g t z hg hA hB ht hz hw)

def coeff1248 : CoefficientMerge.Poly :=
  [(1606656, 1)]
noncomputable def atom1248 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 7) ^ 2 * (t) ^ 2 * (z) ^ 1)
theorem atom1248_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1248 g t z = CoefficientMerge.eval (monomial g t z) coeff1248 := by
  norm_num [atom1248, coeff1248, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1248_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1248 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1248]
  positivity
theorem weighted1248_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (247100031989048429793574623198401537711797534642370742928112335871239013957698187371279165073751263338924467712319440404783513344679177600 : Int) coeff1248) := by
  rw [CoefficientMerge.eval_scale, ← atom1248_identity]
  exact mul_nonneg (by norm_num) (atom1248_nonneg g t z hg hA hB ht hz hw)

def coeff1249 : CoefficientMerge.Poly :=
  [(1655808, 1)]
noncomputable def atom1249 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1249_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1249 g t z = CoefficientMerge.eval (monomial g t z) coeff1249 := by
  norm_num [atom1249, coeff1249, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1249_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1249 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1249]
  positivity
theorem weighted1249_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (342130470624201860099820796054511439315911719802540901393287740252705843647126969448266844853459786692405932369003215553766926707768496000 : Int) coeff1249) := by
  rw [CoefficientMerge.eval_scale, ← atom1249_identity]
  exact mul_nonneg (by norm_num) (atom1249_nonneg g t z hg hA hB ht hz hw)

def coeff1250 : CoefficientMerge.Poly :=
  [(918528, 1)]
noncomputable def atom1250 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 8) ^ 2 * (t) ^ 3)
theorem atom1250_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1250 g t z = CoefficientMerge.eval (monomial g t z) coeff1250 := by
  norm_num [atom1250, coeff1250, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1250_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1250 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1250]
  positivity
theorem weighted1250_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (41054992699737930127338047949124860101703015196899675325331918908736219624381756026154186811773862583514199167581585258086879023613696000 : Int) coeff1250) := by
  rw [CoefficientMerge.eval_scale, ← atom1250_identity]
  exact mul_nonneg (by norm_num) (atom1250_nonneg g t z hg hA hB ht hz hw)

def coeff1251 : CoefficientMerge.Poly :=
  [(1704960, 1)]
noncomputable def atom1251 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 8) ^ 2 * (t) ^ 2 * (z) ^ 1)
theorem atom1251_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1251 g t z = CoefficientMerge.eval (monomial g t z) coeff1251 := by
  norm_num [atom1251, coeff1251, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1251_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1251 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1251]
  positivity
theorem weighted1251_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (143025325656966574707412942349612381341984496108988999216170136320635240926054540457379301164378872144684546287042076400017416372146910720 : Int) coeff1251) := by
  rw [CoefficientMerge.eval_scale, ← atom1251_identity]
  exact mul_nonneg (by norm_num) (atom1251_nonneg g t z hg hA hB ht hz hw)

def coeff1252 : CoefficientMerge.Poly :=
  [(2362368, 1)]
noncomputable def atom1252 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 3 * (t) ^ 1 * (z) ^ 2)
theorem atom1252_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1252 g t z = CoefficientMerge.eval (monomial g t z) coeff1252 := by
  norm_num [atom1252, coeff1252, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1252_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1252 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1252]
  positivity
theorem weighted1252_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (120865159459995171551997774880533852104514221227731965534237917803261145264384937553217331812005886114594889784145171254902154545412003840 : Int) coeff1252) := by
  rw [CoefficientMerge.eval_scale, ← atom1252_identity]
  exact mul_nonneg (by norm_num) (atom1252_nonneg g t z hg hA hB ht hz hw)

def coeff1253 : CoefficientMerge.Poly :=
  [(2365440, 1)]
noncomputable def atom1253 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 2 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1253_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1253 g t z = CoefficientMerge.eval (monomial g t z) coeff1253 := by
  norm_num [atom1253, coeff1253, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1253_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1253 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1253]
  positivity
theorem weighted1253_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (343174985157479868672147897825838115778437313811844226362267990980644406004330787539540177956740108181390262793786530413628727804835438080 : Int) coeff1253) := by
  rw [CoefficientMerge.eval_scale, ← atom1253_identity]
  exact mul_nonneg (by norm_num) (atom1253_nonneg g t z hg hA hB ht hz hw)

def coeff1254 : CoefficientMerge.Poly :=
  [(2377728, 1)]
noncomputable def atom1254 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 2 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1254_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1254 g t z = CoefficientMerge.eval (monomial g t z) coeff1254 := by
  norm_num [atom1254, coeff1254, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1254_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1254 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1254]
  positivity
theorem weighted1254_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (294734856218354745865683058061562085047632160835583141373959018260875480107681035266202946437671114451999653833149589610692483038631124480 : Int) coeff1254) := by
  rw [CoefficientMerge.eval_scale, ← atom1254_identity]
  exact mul_nonneg (by norm_num) (atom1254_nonneg g t z hg hA hB ht hz hw)

def coeff1255 : CoefficientMerge.Poly :=
  [(2426880, 1)]
noncomputable def atom1255 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 2 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1255_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1255 g t z = CoefficientMerge.eval (monomial g t z) coeff1255 := by
  norm_num [atom1255, coeff1255, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1255_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1255 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1255]
  positivity
theorem weighted1255_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (267760674680578257639517148368597952532263311344831020612401251094054648640955004408438743551108597259294226838598395733119577803153911110 : Int) coeff1255) := by
  rw [CoefficientMerge.eval_scale, ← atom1255_identity]
  exact mul_nonneg (by norm_num) (atom1255_nonneg g t z hg hA hB ht hz hw)

def coeff1256 : CoefficientMerge.Poly :=
  [(2368512, 1)]
noncomputable def atom1256 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 6) ^ 2 * (t) ^ 1 * (z) ^ 2)
theorem atom1256_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1256 g t z = CoefficientMerge.eval (monomial g t z) coeff1256 := by
  norm_num [atom1256, coeff1256, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1256_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1256 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1256]
  positivity
theorem weighted1256_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (327256667934847025696363206969184730462610431112574007841955975041709534889062194171748100812789635395468979811680216460550263326875239040 : Int) coeff1256) := by
  rw [CoefficientMerge.eval_scale, ← atom1256_identity]
  exact mul_nonneg (by norm_num) (atom1256_nonneg g t z hg hA hB ht hz hw)

def coeff1257 : CoefficientMerge.Poly :=
  [(2380800, 1)]
noncomputable def atom1257 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1257_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1257 g t z = CoefficientMerge.eval (monomial g t z) coeff1257 := by
  norm_num [atom1257, coeff1257, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1257_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1257 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1257]
  positivity
theorem weighted1257_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (549724271530298848500318501201844268698316837876163066768860557922922227749326945341692595409815886728458286749428771813667862533034627280 : Int) coeff1257) := by
  rw [CoefficientMerge.eval_scale, ← atom1257_identity]
  exact mul_nonneg (by norm_num) (atom1257_nonneg g t z hg hA hB ht hz hw)

def coeff1258 : CoefficientMerge.Poly :=
  [(2429952, 1)]
noncomputable def atom1258 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1258_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1258 g t z = CoefficientMerge.eval (monomial g t z) coeff1258 := by
  norm_num [atom1258, coeff1258, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1258_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1258 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1258]
  positivity
theorem weighted1258_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (462570686017700116041573374691434308229161523382369361710962777882232986710105560270558952264871693365814732582922481321778829637819359870 : Int) coeff1258) := by
  rw [CoefficientMerge.eval_scale, ← atom1258_identity]
  exact mul_nonneg (by norm_num) (atom1258_nonneg g t z hg hA hB ht hz hw)

def coeff1259 : CoefficientMerge.Poly :=
  [(2393088, 1)]
noncomputable def atom1259 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 7) ^ 2 * (t) ^ 1 * (z) ^ 2)
theorem atom1259_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1259 g t z = CoefficientMerge.eval (monomial g t z) coeff1259 := by
  norm_num [atom1259, coeff1259, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1259_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1259 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1259]
  positivity
theorem weighted1259_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (237459148520893671244325361741515257741831876195091459962701859899664693550074242546564310891086951443196369039898329965709999055082515200 : Int) coeff1259) := by
  rw [CoefficientMerge.eval_scale, ← atom1259_identity]
  exact mul_nonneg (by norm_num) (atom1259_nonneg g t z hg hA hB ht hz hw)

def coeff1260 : CoefficientMerge.Poly :=
  [(2442240, 1)]
noncomputable def atom1260 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1260_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1260 g t z = CoefficientMerge.eval (monomial g t z) coeff1260 := by
  norm_num [atom1260, coeff1260, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1260_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1260 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1260]
  positivity
theorem weighted1260_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (348615564152669386991368984383916776751069226520054640228055234826080607729480239296557405120286880555438492450021390333168069652298116150 : Int) coeff1260) := by
  rw [CoefficientMerge.eval_scale, ← atom1260_identity]
  exact mul_nonneg (by norm_num) (atom1260_nonneg g t z hg hA hB ht hz hw)

def coeff1261 : CoefficientMerge.Poly :=
  [(2491392, 1)]
noncomputable def atom1261 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 8) ^ 2 * (t) ^ 1 * (z) ^ 2)
theorem atom1261_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1261 g t z = CoefficientMerge.eval (monomial g t z) coeff1261 := by
  norm_num [atom1261, coeff1261, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1261_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1261 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1261]
  positivity
theorem weighted1261_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (142201404221921077366625990083464936651219365409191967721124430039415966662469271058311177639463763753692921548370194311662604784914363950 : Int) coeff1261) := by
  rw [CoefficientMerge.eval_scale, ← atom1261_identity]
  exact mul_nonneg (by norm_num) (atom1261_nonneg g t z hg hA hB ht hz hw)

def coeff1262 : CoefficientMerge.Poly :=
  [(798720, 1)]
noncomputable def atom1262 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 3 * (t) ^ 3)
theorem atom1262_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1262 g t z = CoefficientMerge.eval (monomial g t z) coeff1262 := by
  norm_num [atom1262, coeff1262, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1262_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1262 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1262]
  positivity
theorem weighted1262_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (35666496866148189799135383001914775895803634079264105265391853815570367163699076132036924436086529788297005317335088468058214674465996800 : Int) coeff1262) := by
  rw [CoefficientMerge.eval_scale, ← atom1262_identity]
  exact mul_nonneg (by norm_num) (atom1262_nonneg g t z hg hA hB ht hz hw)

def coeff1263 : CoefficientMerge.Poly :=
  [(811008, 1)]
noncomputable def atom1263 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 2 * (g 7) ^ 1 * (t) ^ 3)
theorem atom1263_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1263 g t z = CoefficientMerge.eval (monomial g t z) coeff1263 := by
  norm_num [atom1263, coeff1263, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1263_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1263 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1263]
  positivity
theorem weighted1263_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (88792689705228137864707801183782069978092780287200475623024744016007818706020696307119255244777414453750663072524417738955325373864704000 : Int) coeff1263) := by
  rw [CoefficientMerge.eval_scale, ← atom1263_identity]
  exact mul_nonneg (by norm_num) (atom1263_nonneg g t z hg hA hB ht hz hw)

def coeff1264 : CoefficientMerge.Poly :=
  [(860160, 1)]
noncomputable def atom1264 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 2 * (g 8) ^ 1 * (t) ^ 3)
theorem atom1264_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1264 g t z = CoefficientMerge.eval (monomial g t z) coeff1264 := by
  norm_num [atom1264, coeff1264, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1264_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1264 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1264]
  positivity
theorem weighted1264_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (62741944922965530022231112763385766583418882195048177284090590707246250159749702255056378772719960596347337722285236182485942776576307200 : Int) coeff1264) := by
  rw [CoefficientMerge.eval_scale, ← atom1264_identity]
  exact mul_nonneg (by norm_num) (atom1264_nonneg g t z hg hA hB ht hz hw)

def sparseBlock094 : CoefficientMerge.Poly :=
  [(798720, 35666496866148189799135383001914775895803634079264105265391853815570367163699076132036924436086529788297005317335088468058214674465996800), (811008, 88792689705228137864707801183782069978092780287200475623024744016007818706020696307119255244777414453750663072524417738955325373864704000), (820224, 72189669598950592478294913695992406669652242859735852416924922547879682250344130668829703173462156809377465707683691514102272294683500800), (860160, 62741944922965530022231112763385766583418882195048177284090590707246250159749702255056378772719960596347337722285236182485942776576307200), (869376, 100772571401485800748381144006499217059627053454704041514273626185997990175682123553280292571305396209857083388264653650153385284542969600), (918528, 41054992699737930127338047949124860101703015196899675325331918908736219624381756026154186811773862583514199167581585258086879023613696000), (1606656, 247100031989048429793574623198401537711797534642370742928112335871239013957698187371279165073751263338924467712319440404783513344679177600), (1643520, 444085250767951166849119114536522201166000278509677197232695433967497620147300905344388918957263073481799869098849268583471912431504829440), (1655808, 342130470624201860099820796054511439315911719802540901393287740252705843647126969448266844853459786692405932369003215553766926707768496000), (1704960, 143025325656966574707412942349612381341984496108988999216170136320635240926054540457379301164378872144684546287042076400017416372146910720), (2362368, 120865159459995171551997774880533852104514221227731965534237917803261145264384937553217331812005886114594889784145171254902154545412003840), (2365440, 343174985157479868672147897825838115778437313811844226362267990980644406004330787539540177956740108181390262793786530413628727804835438080), (2368512, 327256667934847025696363206969184730462610431112574007841955975041709534889062194171748100812789635395468979811680216460550263326875239040), (2377728, 294734856218354745865683058061562085047632160835583141373959018260875480107681035266202946437671114451999653833149589610692483038631124480), (2380800, 549724271530298848500318501201844268698316837876163066768860557922922227749326945341692595409815886728458286749428771813667862533034627280), (2393088, 237459148520893671244325361741515257741831876195091459962701859899664693550074242546564310891086951443196369039898329965709999055082515200), (2426880, 267760674680578257639517148368597952532263311344831020612401251094054648640955004408438743551108597259294226838598395733119577803153911110), (2429952, 462570686017700116041573374691434308229161523382369361710962777882232986710105560270558952264871693365814732582922481321778829637819359870), (2442240, 348615564152669386991368984383916776751069226520054640228055234826080607729480239296557405120286880555438492450021390333168069652298116150), (2491392, 142201404221921077366625990083464936651219365409191967721124430039415966662469271058311177639463763753692921548370194311662604784914363950)]
theorem sparseBlock094_data : sparseBlock094 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (444085250767951166849119114536522201166000278509677197232695433967497620147300905344388918957263073481799869098849268583471912431504829440 : Int) coeff1245) (CoefficientMerge.scale (72189669598950592478294913695992406669652242859735852416924922547879682250344130668829703173462156809377465707683691514102272294683500800 : Int) coeff1246)) (CoefficientMerge.merge (CoefficientMerge.scale (100772571401485800748381144006499217059627053454704041514273626185997990175682123553280292571305396209857083388264653650153385284542969600 : Int) coeff1247) (CoefficientMerge.merge (CoefficientMerge.scale (247100031989048429793574623198401537711797534642370742928112335871239013957698187371279165073751263338924467712319440404783513344679177600 : Int) coeff1248) (CoefficientMerge.scale (342130470624201860099820796054511439315911719802540901393287740252705843647126969448266844853459786692405932369003215553766926707768496000 : Int) coeff1249)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (41054992699737930127338047949124860101703015196899675325331918908736219624381756026154186811773862583514199167581585258086879023613696000 : Int) coeff1250) (CoefficientMerge.scale (143025325656966574707412942349612381341984496108988999216170136320635240926054540457379301164378872144684546287042076400017416372146910720 : Int) coeff1251)) (CoefficientMerge.merge (CoefficientMerge.scale (120865159459995171551997774880533852104514221227731965534237917803261145264384937553217331812005886114594889784145171254902154545412003840 : Int) coeff1252) (CoefficientMerge.merge (CoefficientMerge.scale (343174985157479868672147897825838115778437313811844226362267990980644406004330787539540177956740108181390262793786530413628727804835438080 : Int) coeff1253) (CoefficientMerge.scale (294734856218354745865683058061562085047632160835583141373959018260875480107681035266202946437671114451999653833149589610692483038631124480 : Int) coeff1254))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (267760674680578257639517148368597952532263311344831020612401251094054648640955004408438743551108597259294226838598395733119577803153911110 : Int) coeff1255) (CoefficientMerge.scale (327256667934847025696363206969184730462610431112574007841955975041709534889062194171748100812789635395468979811680216460550263326875239040 : Int) coeff1256)) (CoefficientMerge.merge (CoefficientMerge.scale (549724271530298848500318501201844268698316837876163066768860557922922227749326945341692595409815886728458286749428771813667862533034627280 : Int) coeff1257) (CoefficientMerge.merge (CoefficientMerge.scale (462570686017700116041573374691434308229161523382369361710962777882232986710105560270558952264871693365814732582922481321778829637819359870 : Int) coeff1258) (CoefficientMerge.scale (237459148520893671244325361741515257741831876195091459962701859899664693550074242546564310891086951443196369039898329965709999055082515200 : Int) coeff1259)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (348615564152669386991368984383916776751069226520054640228055234826080607729480239296557405120286880555438492450021390333168069652298116150 : Int) coeff1260) (CoefficientMerge.scale (142201404221921077366625990083464936651219365409191967721124430039415966662469271058311177639463763753692921548370194311662604784914363950 : Int) coeff1261)) (CoefficientMerge.merge (CoefficientMerge.scale (35666496866148189799135383001914775895803634079264105265391853815570367163699076132036924436086529788297005317335088468058214674465996800 : Int) coeff1262) (CoefficientMerge.merge (CoefficientMerge.scale (88792689705228137864707801183782069978092780287200475623024744016007818706020696307119255244777414453750663072524417738955325373864704000 : Int) coeff1263) (CoefficientMerge.scale (62741944922965530022231112763385766583418882195048177284090590707246250159749702255056378772719960596347337722285236182485942776576307200 : Int) coeff1264)))))) := by decide +kernel
theorem sparseBlock094_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock094 := by
  rw [sparseBlock094_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted1245_nonneg g t z hg hA hB ht hz hw) (weighted1246_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1247_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1248_nonneg g t z hg hA hB ht hz hw) (weighted1249_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1250_nonneg g t z hg hA hB ht hz hw) (weighted1251_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1252_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1253_nonneg g t z hg hA hB ht hz hw) (weighted1254_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted1255_nonneg g t z hg hA hB ht hz hw) (weighted1256_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1257_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1258_nonneg g t z hg hA hB ht hz hw) (weighted1259_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1260_nonneg g t z hg hA hB ht hz hw) (weighted1261_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1262_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1263_nonneg g t z hg hA hB ht hz hw) (weighted1264_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
