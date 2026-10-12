import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff1445 : CoefficientMerge.Poly :=
  [(1577025, 1)]
noncomputable def atom1445 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 6) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1445_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1445 g t z = CoefficientMerge.eval (monomial g t z) coeff1445 := by
  norm_num [atom1445, coeff1445, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1445_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1445 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1445]
  positivity
theorem weighted1445_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (14372335806813526978728868328976339152340005401249664272433092623906264040267028814310766907172760937399622938146120850405072426564418560 : Int) coeff1445) := by
  rw [CoefficientMerge.eval_scale, ← atom1445_identity]
  exact mul_nonneg (by norm_num) (atom1445_nonneg g t z hg hA hB ht hz hw)

def coeff1446 : CoefficientMerge.Poly :=
  [(2363457, 1)]
noncomputable def atom1446 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1446_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1446 g t z = CoefficientMerge.eval (monomial g t z) coeff1446 := by
  norm_num [atom1446, coeff1446, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1446_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1446 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1446]
  positivity
theorem weighted1446_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (7186167903406763489364434164488169576170002700624832136216546311953132020133514407155383453586380468699811469073060425202536213282209280 : Int) coeff1446) := by
  rw [CoefficientMerge.eval_scale, ← atom1446_identity]
  exact mul_nonneg (by norm_num) (atom1446_nonneg g t z hg hA hB ht hz hw)

def coeff1447 : CoefficientMerge.Poly :=
  [(802881, 1)]
noncomputable def atom1447 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 7) ^ 1 * (t) ^ 3)
theorem atom1447_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1447 g t z = CoefficientMerge.eval (monomial g t z) coeff1447 := by
  norm_num [atom1447, coeff1447, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1447_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1447 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1447]
  positivity
theorem weighted1447_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (9001930562405430846330385764754757353316072840299974363977203579383387605984190441809375478696387536221132777988613425447616475189762560 : Int) coeff1447) := by
  rw [CoefficientMerge.eval_scale, ← atom1447_identity]
  exact mul_nonneg (by norm_num) (atom1447_nonneg g t z hg hA hB ht hz hw)

def coeff1448 : CoefficientMerge.Poly :=
  [(1589313, 1)]
noncomputable def atom1448 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 7) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1448_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1448 g t z = CoefficientMerge.eval (monomial g t z) coeff1448 := by
  norm_num [atom1448, coeff1448, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1448_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1448 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1448]
  positivity
theorem weighted1448_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (19605152117336813839095267930724682694691491899701571022957765473230746944419302846253091537772267111327330071059683437498920453088624640 : Int) coeff1448) := by
  rw [CoefficientMerge.eval_scale, ← atom1448_identity]
  exact mul_nonneg (by norm_num) (atom1448_nonneg g t z hg hA hB ht hz hw)

def coeff1449 : CoefficientMerge.Poly :=
  [(2375745, 1)]
noncomputable def atom1449 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1449_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1449 g t z = CoefficientMerge.eval (monomial g t z) coeff1449 := by
  norm_num [atom1449, coeff1449, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1449_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1449 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1449]
  positivity
theorem weighted1449_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (14334876072727536633744318829243836984717186816318009317661307333236493120806379501216968505185973639455507325789896826408746537469900800 : Int) coeff1449) := by
  rw [CoefficientMerge.eval_scale, ← atom1449_identity]
  exact mul_nonneg (by norm_num) (atom1449_nonneg g t z hg hA hB ht hz hw)

def coeff1450 : CoefficientMerge.Poly :=
  [(852033, 1)]
noncomputable def atom1450 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 8) ^ 1 * (t) ^ 3)
theorem atom1450_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1450 g t z = CoefficientMerge.eval (monomial g t z) coeff1450 := by
  norm_num [atom1450, coeff1450, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1450_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1450 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1450]
  positivity
theorem weighted1450_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2774550075322333831775971356862508160544619770656626278802972141085606010588342007790883513066791222839250374070112755207469410625804800 : Int) coeff1450) := by
  rw [CoefficientMerge.eval_scale, ← atom1450_identity]
  exact mul_nonneg (by norm_num) (atom1450_nonneg g t z hg hA hB ht hz hw)

def coeff1451 : CoefficientMerge.Poly :=
  [(2424897, 1)]
noncomputable def atom1451 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1451_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1451 g t z = CoefficientMerge.eval (monomial g t z) coeff1451 := by
  norm_num [atom1451, coeff1451, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1451_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1451 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1451]
  positivity
theorem weighted1451_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (10009654041214484475729168755668971908211823686014510355397992650192370723048560089681530157626193598310898505318877827781879609252372480 : Int) coeff1451) := by
  rw [CoefficientMerge.eval_scale, ← atom1451_identity]
  exact mul_nonneg (by norm_num) (atom1451_nonneg g t z hg hA hB ht hz hw)

def coeff1452 : CoefficientMerge.Poly :=
  [(786945, 1)]
noncomputable def atom1452 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 2 * (t) ^ 3)
theorem atom1452_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1452 g t z = CoefficientMerge.eval (monomial g t z) coeff1452 := by
  norm_num [atom1452, coeff1452, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1452_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1452 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1452]
  positivity
theorem weighted1452_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5954660087962971782187655471567423437105104351210383724754644172829807294224744206572946886385096715889965558957407553296542543769190400 : Int) coeff1452) := by
  rw [CoefficientMerge.eval_scale, ← atom1452_identity]
  exact mul_nonneg (by norm_num) (atom1452_nonneg g t z hg hA hB ht hz hw)

def coeff1453 : CoefficientMerge.Poly :=
  [(1573377, 1)]
noncomputable def atom1453 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 2 * (t) ^ 2 * (z) ^ 1)
theorem atom1453_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1453 g t z = CoefficientMerge.eval (monomial g t z) coeff1453 := by
  norm_num [atom1453, coeff1453, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1453_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1453 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1453]
  positivity
theorem weighted1453_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (26785883808868478106025384090958085328879960227843400353742097296531756597748234136503684518920408528390287894955266381205090937216746336 : Int) coeff1453) := by
  rw [CoefficientMerge.eval_scale, ← atom1453_identity]
  exact mul_nonneg (by norm_num) (atom1453_nonneg g t z hg hA hB ht hz hw)

def coeff1454 : CoefficientMerge.Poly :=
  [(2359809, 1)]
noncomputable def atom1454 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 2 * (t) ^ 1 * (z) ^ 2)
theorem atom1454_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1454 g t z = CoefficientMerge.eval (monomial g t z) coeff1454 := by
  norm_num [atom1454, coeff1454, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1454_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1454 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1454]
  positivity
theorem weighted1454_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (35707787353848040865487801767213900346444607402055649533220262074574091312822235653288528378685526909110679113038310102520554243125921472 : Int) coeff1454) := by
  rw [CoefficientMerge.eval_scale, ← atom1454_identity]
  exact mul_nonneg (by norm_num) (atom1454_nonneg g t z hg hA hB ht hz hw)

def coeff1455 : CoefficientMerge.Poly :=
  [(787713, 1)]
noncomputable def atom1455 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 5) ^ 1 * (t) ^ 3)
theorem atom1455_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1455 g t z = CoefficientMerge.eval (monomial g t z) coeff1455 := by
  norm_num [atom1455, coeff1455, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1455_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1455 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1455]
  positivity
theorem weighted1455_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (9618480665948098593263333848107821080547500842649261251927004487888051341934955309586758148419133418893954503573919302445990110492336000 : Int) coeff1455) := by
  rw [CoefficientMerge.eval_scale, ← atom1455_identity]
  exact mul_nonneg (by norm_num) (atom1455_nonneg g t z hg hA hB ht hz hw)

def coeff1456 : CoefficientMerge.Poly :=
  [(1574145, 1)]
noncomputable def atom1456 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 5) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1456_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1456 g t z = CoefficientMerge.eval (monomial g t z) coeff1456 := by
  norm_num [atom1456, coeff1456, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1456_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1456 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1456]
  positivity
theorem weighted1456_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (33356793327064389758318383795739430335924262808688207230142970948475449935484745750298258267806351705518275304288547300388480766120597432 : Int) coeff1456) := by
  rw [CoefficientMerge.eval_scale, ← atom1456_identity]
  exact mul_nonneg (by norm_num) (atom1456_nonneg g t z hg hA hB ht hz hw)

def coeff1457 : CoefficientMerge.Poly :=
  [(2360577, 1)]
noncomputable def atom1457 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 5) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1457_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1457 g t z = CoefficientMerge.eval (monomial g t z) coeff1457 := by
  norm_num [atom1457, coeff1457, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1457_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1457 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1457]
  positivity
theorem weighted1457_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (37858144656284483736846766047155397430206023089428630704504928433286745845164625571836242090355303154354687097855336693438991200764186864 : Int) coeff1457) := by
  rw [CoefficientMerge.eval_scale, ← atom1457_identity]
  exact mul_nonneg (by norm_num) (atom1457_nonneg g t z hg hA hB ht hz hw)

def coeff1458 : CoefficientMerge.Poly :=
  [(790785, 1)]
noncomputable def atom1458 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (t) ^ 3)
theorem atom1458_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1458 g t z = CoefficientMerge.eval (monomial g t z) coeff1458 := by
  norm_num [atom1458, coeff1458, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1458_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1458 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1458]
  positivity
theorem weighted1458_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3850256069627295571298635524871630463553418110476740150468507012858529679128481615454311268277374499046884874417066526416882867022949760 : Int) coeff1458) := by
  rw [CoefficientMerge.eval_scale, ← atom1458_identity]
  exact mul_nonneg (by norm_num) (atom1458_nonneg g t z hg hA hB ht hz hw)

def coeff1459 : CoefficientMerge.Poly :=
  [(1577217, 1)]
noncomputable def atom1459 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1459_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1459 g t z = CoefficientMerge.eval (monomial g t z) coeff1459 := by
  norm_num [atom1459, coeff1459, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1459_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1459 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1459]
  positivity
theorem weighted1459_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (25327546538496100180803840377052513271055163775439055836576065722196730404868255671258096993774137244224321247222906569886613678742760440 : Int) coeff1459) := by
  rw [CoefficientMerge.eval_scale, ← atom1459_identity]
  exact mul_nonneg (by norm_num) (atom1459_nonneg g t z hg hA hB ht hz hw)

def coeff1460 : CoefficientMerge.Poly :=
  [(2363649, 1)]
noncomputable def atom1460 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1460_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1460 g t z = CoefficientMerge.eval (monomial g t z) coeff1460 := by
  norm_num [atom1460, coeff1460, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1460_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1460 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1460]
  positivity
theorem weighted1460_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (39104324868110313647711774179490135151450073219447891221746610405817871772351066496153260182716150991307987871194613560522578756416671600 : Int) coeff1460) := by
  rw [CoefficientMerge.eval_scale, ← atom1460_identity]
  exact mul_nonneg (by norm_num) (atom1460_nonneg g t z hg hA hB ht hz hw)

def coeff1461 : CoefficientMerge.Poly :=
  [(803073, 1)]
noncomputable def atom1461 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (t) ^ 3)
theorem atom1461_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1461 g t z = CoefficientMerge.eval (monomial g t z) coeff1461 := by
  norm_num [atom1461, coeff1461, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1461_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1461 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1461]
  positivity
theorem weighted1461_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (6962680819860880811344288704616780394542559712730475380903795951975330542408866488025509820519889959628666037835621262346766634331125120 : Int) coeff1461) := by
  rw [CoefficientMerge.eval_scale, ← atom1461_identity]
  exact mul_nonneg (by norm_num) (atom1461_nonneg g t z hg hA hB ht hz hw)

def coeff1462 : CoefficientMerge.Poly :=
  [(1589505, 1)]
noncomputable def atom1462 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1462_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1462 g t z = CoefficientMerge.eval (monomial g t z) coeff1462 := by
  norm_num [atom1462, coeff1462, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1462_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1462 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1462]
  positivity
theorem weighted1462_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (31201973172635499415656782796479179843646768522358444005123937742773497884499724193923568210840383782406709791326102078386142798845684920 : Int) coeff1462) := by
  rw [CoefficientMerge.eval_scale, ← atom1462_identity]
  exact mul_nonneg (by norm_num) (atom1462_nonneg g t z hg hA hB ht hz hw)

def coeff1463 : CoefficientMerge.Poly :=
  [(2375937, 1)]
noncomputable def atom1463 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1463_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1463 g t z = CoefficientMerge.eval (monomial g t z) coeff1463 := by
  norm_num [atom1463, coeff1463, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1463_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1463 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1463]
  positivity
theorem weighted1463_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (41515903885688356397280699479108018503665857906525461867536487629621004141772848923770606960121097685927421469145340369731985694697994480 : Int) coeff1463) := by
  rw [CoefficientMerge.eval_scale, ← atom1463_identity]
  exact mul_nonneg (by norm_num) (atom1463_nonneg g t z hg hA hB ht hz hw)

def coeff1464 : CoefficientMerge.Poly :=
  [(852225, 1)]
noncomputable def atom1464 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (t) ^ 3)
theorem atom1464_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1464 g t z = CoefficientMerge.eval (monomial g t z) coeff1464 := by
  norm_num [atom1464, coeff1464, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1464_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1464 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1464]
  positivity
theorem weighted1464_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (6511459637221263263489321152109930230752820057467769597787942968616580153595435615233679572591801949511148165933716961616448551477411200 : Int) coeff1464) := by
  rw [CoefficientMerge.eval_scale, ← atom1464_identity]
  exact mul_nonneg (by norm_num) (atom1464_nonneg g t z hg hA hB ht hz hw)

def sparseBlock104 : CoefficientMerge.Poly :=
  [(786945, 5954660087962971782187655471567423437105104351210383724754644172829807294224744206572946886385096715889965558957407553296542543769190400), (787713, 9618480665948098593263333848107821080547500842649261251927004487888051341934955309586758148419133418893954503573919302445990110492336000), (790785, 3850256069627295571298635524871630463553418110476740150468507012858529679128481615454311268277374499046884874417066526416882867022949760), (802881, 9001930562405430846330385764754757353316072840299974363977203579383387605984190441809375478696387536221132777988613425447616475189762560), (803073, 6962680819860880811344288704616780394542559712730475380903795951975330542408866488025509820519889959628666037835621262346766634331125120), (852033, 2774550075322333831775971356862508160544619770656626278802972141085606010588342007790883513066791222839250374070112755207469410625804800), (852225, 6511459637221263263489321152109930230752820057467769597787942968616580153595435615233679572591801949511148165933716961616448551477411200), (1573377, 26785883808868478106025384090958085328879960227843400353742097296531756597748234136503684518920408528390287894955266381205090937216746336), (1574145, 33356793327064389758318383795739430335924262808688207230142970948475449935484745750298258267806351705518275304288547300388480766120597432), (1577025, 14372335806813526978728868328976339152340005401249664272433092623906264040267028814310766907172760937399622938146120850405072426564418560), (1577217, 25327546538496100180803840377052513271055163775439055836576065722196730404868255671258096993774137244224321247222906569886613678742760440), (1589313, 19605152117336813839095267930724682694691491899701571022957765473230746944419302846253091537772267111327330071059683437498920453088624640), (1589505, 31201973172635499415656782796479179843646768522358444005123937742773497884499724193923568210840383782406709791326102078386142798845684920), (2359809, 35707787353848040865487801767213900346444607402055649533220262074574091312822235653288528378685526909110679113038310102520554243125921472), (2360577, 37858144656284483736846766047155397430206023089428630704504928433286745845164625571836242090355303154354687097855336693438991200764186864), (2363457, 7186167903406763489364434164488169576170002700624832136216546311953132020133514407155383453586380468699811469073060425202536213282209280), (2363649, 39104324868110313647711774179490135151450073219447891221746610405817871772351066496153260182716150991307987871194613560522578756416671600), (2375745, 14334876072727536633744318829243836984717186816318009317661307333236493120806379501216968505185973639455507325789896826408746537469900800), (2375937, 41515903885688356397280699479108018503665857906525461867536487629621004141772848923770606960121097685927421469145340369731985694697994480), (2424897, 10009654041214484475729168755668971908211823686014510355397992650192370723048560089681530157626193598310898505318877827781879609252372480)]
theorem sparseBlock104_data : sparseBlock104 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (14372335806813526978728868328976339152340005401249664272433092623906264040267028814310766907172760937399622938146120850405072426564418560 : Int) coeff1445) (CoefficientMerge.scale (7186167903406763489364434164488169576170002700624832136216546311953132020133514407155383453586380468699811469073060425202536213282209280 : Int) coeff1446)) (CoefficientMerge.merge (CoefficientMerge.scale (9001930562405430846330385764754757353316072840299974363977203579383387605984190441809375478696387536221132777988613425447616475189762560 : Int) coeff1447) (CoefficientMerge.merge (CoefficientMerge.scale (19605152117336813839095267930724682694691491899701571022957765473230746944419302846253091537772267111327330071059683437498920453088624640 : Int) coeff1448) (CoefficientMerge.scale (14334876072727536633744318829243836984717186816318009317661307333236493120806379501216968505185973639455507325789896826408746537469900800 : Int) coeff1449)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (2774550075322333831775971356862508160544619770656626278802972141085606010588342007790883513066791222839250374070112755207469410625804800 : Int) coeff1450) (CoefficientMerge.scale (10009654041214484475729168755668971908211823686014510355397992650192370723048560089681530157626193598310898505318877827781879609252372480 : Int) coeff1451)) (CoefficientMerge.merge (CoefficientMerge.scale (5954660087962971782187655471567423437105104351210383724754644172829807294224744206572946886385096715889965558957407553296542543769190400 : Int) coeff1452) (CoefficientMerge.merge (CoefficientMerge.scale (26785883808868478106025384090958085328879960227843400353742097296531756597748234136503684518920408528390287894955266381205090937216746336 : Int) coeff1453) (CoefficientMerge.scale (35707787353848040865487801767213900346444607402055649533220262074574091312822235653288528378685526909110679113038310102520554243125921472 : Int) coeff1454))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (9618480665948098593263333848107821080547500842649261251927004487888051341934955309586758148419133418893954503573919302445990110492336000 : Int) coeff1455) (CoefficientMerge.scale (33356793327064389758318383795739430335924262808688207230142970948475449935484745750298258267806351705518275304288547300388480766120597432 : Int) coeff1456)) (CoefficientMerge.merge (CoefficientMerge.scale (37858144656284483736846766047155397430206023089428630704504928433286745845164625571836242090355303154354687097855336693438991200764186864 : Int) coeff1457) (CoefficientMerge.merge (CoefficientMerge.scale (3850256069627295571298635524871630463553418110476740150468507012858529679128481615454311268277374499046884874417066526416882867022949760 : Int) coeff1458) (CoefficientMerge.scale (25327546538496100180803840377052513271055163775439055836576065722196730404868255671258096993774137244224321247222906569886613678742760440 : Int) coeff1459)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (39104324868110313647711774179490135151450073219447891221746610405817871772351066496153260182716150991307987871194613560522578756416671600 : Int) coeff1460) (CoefficientMerge.scale (6962680819860880811344288704616780394542559712730475380903795951975330542408866488025509820519889959628666037835621262346766634331125120 : Int) coeff1461)) (CoefficientMerge.merge (CoefficientMerge.scale (31201973172635499415656782796479179843646768522358444005123937742773497884499724193923568210840383782406709791326102078386142798845684920 : Int) coeff1462) (CoefficientMerge.merge (CoefficientMerge.scale (41515903885688356397280699479108018503665857906525461867536487629621004141772848923770606960121097685927421469145340369731985694697994480 : Int) coeff1463) (CoefficientMerge.scale (6511459637221263263489321152109930230752820057467769597787942968616580153595435615233679572591801949511148165933716961616448551477411200 : Int) coeff1464)))))) := by decide +kernel
theorem sparseBlock104_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock104 := by
  rw [sparseBlock104_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted1445_nonneg g t z hg hA hB ht hz hw) (weighted1446_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1447_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1448_nonneg g t z hg hA hB ht hz hw) (weighted1449_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1450_nonneg g t z hg hA hB ht hz hw) (weighted1451_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1452_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1453_nonneg g t z hg hA hB ht hz hw) (weighted1454_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted1455_nonneg g t z hg hA hB ht hz hw) (weighted1456_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1457_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1458_nonneg g t z hg hA hB ht hz hw) (weighted1459_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1460_nonneg g t z hg hA hB ht hz hw) (weighted1461_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1462_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1463_nonneg g t z hg hA hB ht hz hw) (weighted1464_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
