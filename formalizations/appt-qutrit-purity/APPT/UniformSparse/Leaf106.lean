import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff1485 : CoefficientMerge.Poly :=
  [(1642497, 1)]
noncomputable def atom1485 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1485_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1485 g t z = CoefficientMerge.eval (monomial g t z) coeff1485 := by
  norm_num [atom1485, coeff1485, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1485_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1485 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1485]
  positivity
theorem weighted1485_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (23090006044972520879311468087341206362375185796317910997941313627463084176467104779204644718541870907094996891122764565503780735596620800 : Int) coeff1485) := by
  rw [CoefficientMerge.eval_scale, ← atom1485_identity]
  exact mul_nonneg (by norm_num) (atom1485_nonneg g t z hg hA hB ht hz hw)

def coeff1486 : CoefficientMerge.Poly :=
  [(2428929, 1)]
noncomputable def atom1486 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1486_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1486 g t z = CoefficientMerge.eval (monomial g t z) coeff1486 := by
  norm_num [atom1486, coeff1486, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1486_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1486 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1486]
  positivity
theorem weighted1486_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (36069006905996733699949769423844481947422270010502535773948381650285571153103619027108372754947817039826697169936586096516068797252345600 : Int) coeff1486) := by
  rw [CoefficientMerge.eval_scale, ← atom1486_identity]
  exact mul_nonneg (by norm_num) (atom1486_nonneg g t z hg hA hB ht hz hw)

def coeff1487 : CoefficientMerge.Poly :=
  [(787464, 1)]
noncomputable def atom1487 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 2 * (g 5) ^ 1 * (t) ^ 3)
theorem atom1487_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1487 g t z = CoefficientMerge.eval (monomial g t z) coeff1487 := by
  norm_num [atom1487, coeff1487, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1487_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1487 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1487]
  positivity
theorem weighted1487_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (436892065806819691399234924204130885214410228234233605696032553071381297198165845487293831842240237743665702239488684674135042587033600 : Int) coeff1487) := by
  rw [CoefficientMerge.eval_scale, ← atom1487_identity]
  exact mul_nonneg (by norm_num) (atom1487_nonneg g t z hg hA hB ht hz hw)

def coeff1488 : CoefficientMerge.Poly :=
  [(786516, 1)]
noncomputable def atom1488 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 3) ^ 1 * (t) ^ 3)
theorem atom1488_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1488 g t z = CoefficientMerge.eval (monomial g t z) coeff1488 := by
  norm_num [atom1488, coeff1488, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1488_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1488 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1488]
  positivity
theorem weighted1488_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (89827690829833206031059927161851018686340464843640942761589044197327890590830636495651457908110832053018706869755950500273842828858347520 : Int) coeff1488) := by
  rw [CoefficientMerge.eval_scale, ← atom1488_identity]
  exact mul_nonneg (by norm_num) (atom1488_nonneg g t z hg hA hB ht hz hw)

def coeff1489 : CoefficientMerge.Poly :=
  [(1572948, 1)]
noncomputable def atom1489 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 3) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1489_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1489 g t z = CoefficientMerge.eval (monomial g t z) coeff1489 := by
  norm_num [atom1489, coeff1489, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1489_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1489 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1489]
  positivity
theorem weighted1489_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (263433433552611420152444568227539085704652659912489814897478091861794027860984385403604353996062883985742839499861201376641830866258342656 : Int) coeff1489) := by
  rw [CoefficientMerge.eval_scale, ← atom1489_identity]
  exact mul_nonneg (by norm_num) (atom1489_nonneg g t z hg hA hB ht hz hw)

def coeff1490 : CoefficientMerge.Poly :=
  [(2359380, 1)]
noncomputable def atom1490 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 3) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1490_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1490 g t z = CoefficientMerge.eval (monomial g t z) coeff1490 := by
  norm_num [atom1490, coeff1490, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1490_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1490 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1490]
  positivity
theorem weighted1490_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (225752163857403556352569570919798685108899422763263547067976988542523954460655142112267397954353630733707526842151328436385103455415462400 : Int) coeff1490) := by
  rw [CoefficientMerge.eval_scale, ← atom1490_identity]
  exact mul_nonneg (by norm_num) (atom1490_nonneg g t z hg hA hB ht hz hw)

def coeff1491 : CoefficientMerge.Poly :=
  [(786708, 1)]
noncomputable def atom1491 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 4) ^ 1 * (t) ^ 3)
theorem atom1491_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1491 g t z = CoefficientMerge.eval (monomial g t z) coeff1491 := by
  norm_num [atom1491, coeff1491, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1491_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1491 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1491]
  positivity
theorem weighted1491_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (94866150503159945100134173013958202493314257356901303700261731746280888666550717725515813269458465885594890305226473354198696595504947200 : Int) coeff1491) := by
  rw [CoefficientMerge.eval_scale, ← atom1491_identity]
  exact mul_nonneg (by norm_num) (atom1491_nonneg g t z hg hA hB ht hz hw)

def coeff1492 : CoefficientMerge.Poly :=
  [(1573140, 1)]
noncomputable def atom1492 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 4) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1492_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1492 g t z = CoefficientMerge.eval (monomial g t z) coeff1492 := by
  norm_num [atom1492, coeff1492, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1492_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1492 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1492]
  positivity
theorem weighted1492_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (262765087512712891264686815074028813027612728245937704647916674950917595780268643086264785379304176780122884950365814722402975432582214880 : Int) coeff1492) := by
  rw [CoefficientMerge.eval_scale, ← atom1492_identity]
  exact mul_nonneg (by norm_num) (atom1492_nonneg g t z hg hA hB ht hz hw)

def coeff1493 : CoefficientMerge.Poly :=
  [(2359572, 1)]
noncomputable def atom1493 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 4) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1493_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1493 g t z = CoefficientMerge.eval (monomial g t z) coeff1493 := by
  norm_num [atom1493, coeff1493, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1493_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1493 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1493]
  positivity
theorem weighted1493_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (224571580205381331226430867959290328491624492419884267646963529048018915297453810830606964161859758622223410926894485150780872846773750592 : Int) coeff1493) := by
  rw [CoefficientMerge.eval_scale, ← atom1493_identity]
  exact mul_nonneg (by norm_num) (atom1493_nonneg g t z hg hA hB ht hz hw)

def coeff1494 : CoefficientMerge.Poly :=
  [(787476, 1)]
noncomputable def atom1494 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 5) ^ 1 * (t) ^ 3)
theorem atom1494_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1494 g t z = CoefficientMerge.eval (monomial g t z) coeff1494 := by
  norm_num [atom1494, coeff1494, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1494_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1494 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1494]
  positivity
theorem weighted1494_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (50599342314800146121952766407889443009710300521481096794400609963010746867552540576719843344477882563734393180968114011650404658863360000 : Int) coeff1494) := by
  rw [CoefficientMerge.eval_scale, ← atom1494_identity]
  exact mul_nonneg (by norm_num) (atom1494_nonneg g t z hg hA hB ht hz hw)

def coeff1495 : CoefficientMerge.Poly :=
  [(1573908, 1)]
noncomputable def atom1495 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 5) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1495_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1495 g t z = CoefficientMerge.eval (monomial g t z) coeff1495 := by
  norm_num [atom1495, coeff1495, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1495_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1495 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1495]
  positivity
theorem weighted1495_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (197627413892972596368851340078322568911352185645606593462399521174950163060499940144968641604794988205396714937894985378205323561164891904 : Int) coeff1495) := by
  rw [CoefficientMerge.eval_scale, ← atom1495_identity]
  exact mul_nonneg (by norm_num) (atom1495_nonneg g t z hg hA hB ht hz hw)

def coeff1496 : CoefficientMerge.Poly :=
  [(2360340, 1)]
noncomputable def atom1496 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 5) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1496_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1496 g t z = CoefficientMerge.eval (monomial g t z) coeff1496 := by
  norm_num [atom1496, coeff1496, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1496_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1496 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1496]
  positivity
theorem weighted1496_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (137340998227471134732544133687848172388834958178167903768816426986584830959663599682149864826870304742777315041069583130579168182544957504 : Int) coeff1496) := by
  rw [CoefficientMerge.eval_scale, ← atom1496_identity]
  exact mul_nonneg (by norm_num) (atom1496_nonneg g t z hg hA hB ht hz hw)

def coeff1497 : CoefficientMerge.Poly :=
  [(790548, 1)]
noncomputable def atom1497 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 6) ^ 1 * (t) ^ 3)
theorem atom1497_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1497 g t z = CoefficientMerge.eval (monomial g t z) coeff1497 := by
  norm_num [atom1497, coeff1497, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1497_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1497 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1497]
  positivity
theorem weighted1497_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (70813607777013899271899153969626618920685674958262588298644677560752473002104055121580958870383590087150287529863720480567680116606302720 : Int) coeff1497) := by
  rw [CoefficientMerge.eval_scale, ← atom1497_identity]
  exact mul_nonneg (by norm_num) (atom1497_nonneg g t z hg hA hB ht hz hw)

def coeff1498 : CoefficientMerge.Poly :=
  [(1576980, 1)]
noncomputable def atom1498 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 6) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1498_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1498 g t z = CoefficientMerge.eval (monomial g t z) coeff1498 := by
  norm_num [atom1498, coeff1498, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1498_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1498 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1498]
  positivity
theorem weighted1498_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (225541792484521280204243451435560273439710323086397975704509508523069825985697580322289401958547738137731757317506670671133540588851622400 : Int) coeff1498) := by
  rw [CoefficientMerge.eval_scale, ← atom1498_identity]
  exact mul_nonneg (by norm_num) (atom1498_nonneg g t z hg hA hB ht hz hw)

def coeff1499 : CoefficientMerge.Poly :=
  [(2363412, 1)]
noncomputable def atom1499 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1499_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1499 g t z = CoefficientMerge.eval (monomial g t z) coeff1499 := by
  norm_num [atom1499, coeff1499, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1499_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1499 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1499]
  positivity
theorem weighted1499_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (160801025010048034089486893432410933463469236664241759356316352955958903315342256610721732976603252281029905101377798006563481817742707200 : Int) coeff1499) := by
  rw [CoefficientMerge.eval_scale, ← atom1499_identity]
  exact mul_nonneg (by norm_num) (atom1499_nonneg g t z hg hA hB ht hz hw)

def coeff1500 : CoefficientMerge.Poly :=
  [(802836, 1)]
noncomputable def atom1500 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 7) ^ 1 * (t) ^ 3)
theorem atom1500_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1500 g t z = CoefficientMerge.eval (monomial g t z) coeff1500 := by
  norm_num [atom1500, coeff1500, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1500_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1500 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1500]
  positivity
theorem weighted1500_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (84743518484107577185612927127656591050218581085201739747058857564447440110084923331658171551433026286177825879912237631665088287102960640 : Int) coeff1500) := by
  rw [CoefficientMerge.eval_scale, ← atom1500_identity]
  exact mul_nonneg (by norm_num) (atom1500_nonneg g t z hg hA hB ht hz hw)

def coeff1501 : CoefficientMerge.Poly :=
  [(1589268, 1)]
noncomputable def atom1501 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 7) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1501_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1501 g t z = CoefficientMerge.eval (monomial g t z) coeff1501 := by
  norm_num [atom1501, coeff1501, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1501_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1501 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1501]
  positivity
theorem weighted1501_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (237571273130267637289998875640916258388625929216248780386841111365312993224772308214520175452104386009995378675936124537547300693826705920 : Int) coeff1501) := by
  rw [CoefficientMerge.eval_scale, ← atom1501_identity]
  exact mul_nonneg (by norm_num) (atom1501_nonneg g t z hg hA hB ht hz hw)

def coeff1502 : CoefficientMerge.Poly :=
  [(2375700, 1)]
noncomputable def atom1502 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1502_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1502 g t z = CoefficientMerge.eval (monomial g t z) coeff1502 := by
  norm_num [atom1502, coeff1502, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1502_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1502 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1502]
  positivity
theorem weighted1502_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (187592344436305042350421905479257259538948305645139349794912307490990852062578932571096425291296929601530355489227888363707821292296688640 : Int) coeff1502) := by
  rw [CoefficientMerge.eval_scale, ← atom1502_identity]
  exact mul_nonneg (by norm_num) (atom1502_nonneg g t z hg hA hB ht hz hw)

def coeff1503 : CoefficientMerge.Poly :=
  [(851988, 1)]
noncomputable def atom1503 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 8) ^ 1 * (t) ^ 3)
theorem atom1503_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1503 g t z = CoefficientMerge.eval (monomial g t z) coeff1503 := by
  norm_num [atom1503, coeff1503, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1503_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1503 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1503]
  positivity
theorem weighted1503_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (52006331930336298162249243782268590244555470995857824952917997540935694023058766141269901986544485990470617715756543173855508697850060800 : Int) coeff1503) := by
  rw [CoefficientMerge.eval_scale, ← atom1503_identity]
  exact mul_nonneg (by norm_num) (atom1503_nonneg g t z hg hA hB ht hz hw)

def coeff1504 : CoefficientMerge.Poly :=
  [(1638420, 1)]
noncomputable def atom1504 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 8) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1504_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1504 g t z = CoefficientMerge.eval (monomial g t z) coeff1504 := by
  norm_num [atom1504, coeff1504, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1504_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1504 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1504]
  positivity
theorem weighted1504_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (106906261887128623699299891294927566605487163767543522297163661147419943077323755859493275973469642219907591933978098838016262846993152000 : Int) coeff1504) := by
  rw [CoefficientMerge.eval_scale, ← atom1504_identity]
  exact mul_nonneg (by norm_num) (atom1504_nonneg g t z hg hA hB ht hz hw)

def sparseBlock106 : CoefficientMerge.Poly :=
  [(786516, 89827690829833206031059927161851018686340464843640942761589044197327890590830636495651457908110832053018706869755950500273842828858347520), (786708, 94866150503159945100134173013958202493314257356901303700261731746280888666550717725515813269458465885594890305226473354198696595504947200), (787464, 436892065806819691399234924204130885214410228234233605696032553071381297198165845487293831842240237743665702239488684674135042587033600), (787476, 50599342314800146121952766407889443009710300521481096794400609963010746867552540576719843344477882563734393180968114011650404658863360000), (790548, 70813607777013899271899153969626618920685674958262588298644677560752473002104055121580958870383590087150287529863720480567680116606302720), (802836, 84743518484107577185612927127656591050218581085201739747058857564447440110084923331658171551433026286177825879912237631665088287102960640), (851988, 52006331930336298162249243782268590244555470995857824952917997540935694023058766141269901986544485990470617715756543173855508697850060800), (1572948, 263433433552611420152444568227539085704652659912489814897478091861794027860984385403604353996062883985742839499861201376641830866258342656), (1573140, 262765087512712891264686815074028813027612728245937704647916674950917595780268643086264785379304176780122884950365814722402975432582214880), (1573908, 197627413892972596368851340078322568911352185645606593462399521174950163060499940144968641604794988205396714937894985378205323561164891904), (1576980, 225541792484521280204243451435560273439710323086397975704509508523069825985697580322289401958547738137731757317506670671133540588851622400), (1589268, 237571273130267637289998875640916258388625929216248780386841111365312993224772308214520175452104386009995378675936124537547300693826705920), (1638420, 106906261887128623699299891294927566605487163767543522297163661147419943077323755859493275973469642219907591933978098838016262846993152000), (1642497, 23090006044972520879311468087341206362375185796317910997941313627463084176467104779204644718541870907094996891122764565503780735596620800), (2359380, 225752163857403556352569570919798685108899422763263547067976988542523954460655142112267397954353630733707526842151328436385103455415462400), (2359572, 224571580205381331226430867959290328491624492419884267646963529048018915297453810830606964161859758622223410926894485150780872846773750592), (2360340, 137340998227471134732544133687848172388834958178167903768816426986584830959663599682149864826870304742777315041069583130579168182544957504), (2363412, 160801025010048034089486893432410933463469236664241759356316352955958903315342256610721732976603252281029905101377798006563481817742707200), (2375700, 187592344436305042350421905479257259538948305645139349794912307490990852062578932571096425291296929601530355489227888363707821292296688640), (2428929, 36069006905996733699949769423844481947422270010502535773948381650285571153103619027108372754947817039826697169936586096516068797252345600)]
theorem sparseBlock106_data : sparseBlock106 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (23090006044972520879311468087341206362375185796317910997941313627463084176467104779204644718541870907094996891122764565503780735596620800 : Int) coeff1485) (CoefficientMerge.scale (36069006905996733699949769423844481947422270010502535773948381650285571153103619027108372754947817039826697169936586096516068797252345600 : Int) coeff1486)) (CoefficientMerge.merge (CoefficientMerge.scale (436892065806819691399234924204130885214410228234233605696032553071381297198165845487293831842240237743665702239488684674135042587033600 : Int) coeff1487) (CoefficientMerge.merge (CoefficientMerge.scale (89827690829833206031059927161851018686340464843640942761589044197327890590830636495651457908110832053018706869755950500273842828858347520 : Int) coeff1488) (CoefficientMerge.scale (263433433552611420152444568227539085704652659912489814897478091861794027860984385403604353996062883985742839499861201376641830866258342656 : Int) coeff1489)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (225752163857403556352569570919798685108899422763263547067976988542523954460655142112267397954353630733707526842151328436385103455415462400 : Int) coeff1490) (CoefficientMerge.scale (94866150503159945100134173013958202493314257356901303700261731746280888666550717725515813269458465885594890305226473354198696595504947200 : Int) coeff1491)) (CoefficientMerge.merge (CoefficientMerge.scale (262765087512712891264686815074028813027612728245937704647916674950917595780268643086264785379304176780122884950365814722402975432582214880 : Int) coeff1492) (CoefficientMerge.merge (CoefficientMerge.scale (224571580205381331226430867959290328491624492419884267646963529048018915297453810830606964161859758622223410926894485150780872846773750592 : Int) coeff1493) (CoefficientMerge.scale (50599342314800146121952766407889443009710300521481096794400609963010746867552540576719843344477882563734393180968114011650404658863360000 : Int) coeff1494))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (197627413892972596368851340078322568911352185645606593462399521174950163060499940144968641604794988205396714937894985378205323561164891904 : Int) coeff1495) (CoefficientMerge.scale (137340998227471134732544133687848172388834958178167903768816426986584830959663599682149864826870304742777315041069583130579168182544957504 : Int) coeff1496)) (CoefficientMerge.merge (CoefficientMerge.scale (70813607777013899271899153969626618920685674958262588298644677560752473002104055121580958870383590087150287529863720480567680116606302720 : Int) coeff1497) (CoefficientMerge.merge (CoefficientMerge.scale (225541792484521280204243451435560273439710323086397975704509508523069825985697580322289401958547738137731757317506670671133540588851622400 : Int) coeff1498) (CoefficientMerge.scale (160801025010048034089486893432410933463469236664241759356316352955958903315342256610721732976603252281029905101377798006563481817742707200 : Int) coeff1499)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (84743518484107577185612927127656591050218581085201739747058857564447440110084923331658171551433026286177825879912237631665088287102960640 : Int) coeff1500) (CoefficientMerge.scale (237571273130267637289998875640916258388625929216248780386841111365312993224772308214520175452104386009995378675936124537547300693826705920 : Int) coeff1501)) (CoefficientMerge.merge (CoefficientMerge.scale (187592344436305042350421905479257259538948305645139349794912307490990852062578932571096425291296929601530355489227888363707821292296688640 : Int) coeff1502) (CoefficientMerge.merge (CoefficientMerge.scale (52006331930336298162249243782268590244555470995857824952917997540935694023058766141269901986544485990470617715756543173855508697850060800 : Int) coeff1503) (CoefficientMerge.scale (106906261887128623699299891294927566605487163767543522297163661147419943077323755859493275973469642219907591933978098838016262846993152000 : Int) coeff1504)))))) := by decide +kernel
theorem sparseBlock106_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock106 := by
  rw [sparseBlock106_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted1485_nonneg g t z hg hA hB ht hz hw) (weighted1486_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1487_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1488_nonneg g t z hg hA hB ht hz hw) (weighted1489_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1490_nonneg g t z hg hA hB ht hz hw) (weighted1491_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1492_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1493_nonneg g t z hg hA hB ht hz hw) (weighted1494_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted1495_nonneg g t z hg hA hB ht hz hw) (weighted1496_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1497_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1498_nonneg g t z hg hA hB ht hz hw) (weighted1499_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1500_nonneg g t z hg hA hB ht hz hw) (weighted1501_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1502_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1503_nonneg g t z hg hA hB ht hz hw) (weighted1504_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
