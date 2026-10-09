import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff1565 : CoefficientMerge.Poly :=
  [(3162114, 1)]
noncomputable def atom1565 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 2 * (g 7) ^ 1 * (z) ^ 3)
theorem atom1565_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1565 g t z = CoefficientMerge.eval (monomial g t z) coeff1565 := by
  norm_num [atom1565, coeff1565, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1565_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1565 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1565]
  positivity
theorem weighted1565_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1047108890401221314295933645687405347705271922056637523537367565811159495467580313849928768391468910944267107719878992936913571818803200 : Int) coeff1565) := by
  rw [CoefficientMerge.eval_scale, ← atom1565_identity]
  exact mul_nonneg (by norm_num) (atom1565_nonneg g t z hg hA hB ht hz hw)

def coeff1566 : CoefficientMerge.Poly :=
  [(3145797, 1)]
noncomputable def atom1566 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 1) ^ 1 * (g 3) ^ 1 * (z) ^ 3)
theorem atom1566_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1566 g t z = CoefficientMerge.eval (monomial g t z) coeff1566 := by
  norm_num [atom1566, coeff1566, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1566_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1566 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1566]
  positivity
theorem weighted1566_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (19370507349738316340385990741277354053561775381590515587204359593518076087495142628780097180212544688687297533043199854403441269726597120 : Int) coeff1566) := by
  rw [CoefficientMerge.eval_scale, ← atom1566_identity]
  exact mul_nonneg (by norm_num) (atom1566_nonneg g t z hg hA hB ht hz hw)

def coeff1567 : CoefficientMerge.Poly :=
  [(3145989, 1)]
noncomputable def atom1567 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 1) ^ 1 * (g 4) ^ 1 * (z) ^ 3)
theorem atom1567_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1567 g t z = CoefficientMerge.eval (monomial g t z) coeff1567 := by
  norm_num [atom1567, coeff1567, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1567_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1567 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1567]
  positivity
theorem weighted1567_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (16616871837307044769960393523162058629482048578598685179788875624279226126902259012316557309515588982290165269099284652060282428544819200 : Int) coeff1567) := by
  rw [CoefficientMerge.eval_scale, ← atom1567_identity]
  exact mul_nonneg (by norm_num) (atom1567_nonneg g t z hg hA hB ht hz hw)

def coeff1568 : CoefficientMerge.Poly :=
  [(3146757, 1)]
noncomputable def atom1568 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 1) ^ 1 * (g 5) ^ 1 * (z) ^ 3)
theorem atom1568_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1568 g t z = CoefficientMerge.eval (monomial g t z) coeff1568 := by
  norm_num [atom1568, coeff1568, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1568_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1568 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1568]
  positivity
theorem weighted1568_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4924966315955911986872319189126910623401153909035650508734219317087263831053924785887511280305563991431815370598775102616621002803466240 : Int) coeff1568) := by
  rw [CoefficientMerge.eval_scale, ← atom1568_identity]
  exact mul_nonneg (by norm_num) (atom1568_nonneg g t z hg hA hB ht hz hw)

def coeff1569 : CoefficientMerge.Poly :=
  [(3149829, 1)]
noncomputable def atom1569 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 1) ^ 1 * (g 6) ^ 1 * (z) ^ 3)
theorem atom1569_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1569 g t z = CoefficientMerge.eval (monomial g t z) coeff1569 := by
  norm_num [atom1569, coeff1569, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1569_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1569 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1569]
  positivity
theorem weighted1569_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1997854923891052370156233850544743025955224222149557825796121887505244199816945270859830048779822043091799313530385094792626375727329280 : Int) coeff1569) := by
  rw [CoefficientMerge.eval_scale, ← atom1569_identity]
  exact mul_nonneg (by norm_num) (atom1569_nonneg g t z hg hA hB ht hz hw)

def coeff1570 : CoefficientMerge.Poly :=
  [(3145809, 1)]
noncomputable def atom1570 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 3) ^ 1 * (z) ^ 3)
theorem atom1570_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1570 g t z = CoefficientMerge.eval (monomial g t z) coeff1570 := by
  norm_num [atom1570, coeff1570, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1570_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1570 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1570]
  positivity
theorem weighted1570_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (46198701263458304849299666056032592867691715871329798826069266509911681816328623002032141770639204521149300192963221673842584970244588800 : Int) coeff1570) := by
  rw [CoefficientMerge.eval_scale, ← atom1570_identity]
  exact mul_nonneg (by norm_num) (atom1570_nonneg g t z hg hA hB ht hz hw)

def coeff1571 : CoefficientMerge.Poly :=
  [(3146001, 1)]
noncomputable def atom1571 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 4) ^ 1 * (z) ^ 3)
theorem atom1571_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1571 g t z = CoefficientMerge.eval (monomial g t z) coeff1571 := by
  norm_num [atom1571, coeff1571, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1571_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1571 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1571]
  positivity
theorem weighted1571_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (30802913540681008343880568491849040351060002652585124875516036798910530182554597133117652986460492534619472454250543656048855748811943872 : Int) coeff1571) := by
  rw [CoefficientMerge.eval_scale, ← atom1571_identity]
  exact mul_nonneg (by norm_num) (atom1571_nonneg g t z hg hA hB ht hz hw)

def coeff1572 : CoefficientMerge.Poly :=
  [(3146769, 1)]
noncomputable def atom1572 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 5) ^ 1 * (z) ^ 3)
theorem atom1572_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1572 g t z = CoefficientMerge.eval (monomial g t z) coeff1572 := by
  norm_num [atom1572, coeff1572, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1572_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1572 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1572]
  positivity
theorem weighted1572_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (21330599659713341979981783725006523430707862558319946494463908786679761739795560427823210287305421650901064712502378943832829197962815264 : Int) coeff1572) := by
  rw [CoefficientMerge.eval_scale, ← atom1572_identity]
  exact mul_nonneg (by norm_num) (atom1572_nonneg g t z hg hA hB ht hz hw)

def coeff1573 : CoefficientMerge.Poly :=
  [(3149841, 1)]
noncomputable def atom1573 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 6) ^ 1 * (z) ^ 3)
theorem atom1573_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1573 g t z = CoefficientMerge.eval (monomial g t z) coeff1573 := by
  norm_num [atom1573, coeff1573, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1573_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1573 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1573]
  positivity
theorem weighted1573_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (13754704568222616307490244925764138455093524854541469134445207014569076390466068257291493805699038800889871405718549946376120027838827520 : Int) coeff1573) := by
  rw [CoefficientMerge.eval_scale, ← atom1573_identity]
  exact mul_nonneg (by norm_num) (atom1573_nonneg g t z hg hA hB ht hz hw)

def coeff1574 : CoefficientMerge.Poly :=
  [(3162129, 1)]
noncomputable def atom1574 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 7) ^ 1 * (z) ^ 3)
theorem atom1574_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1574 g t z = CoefficientMerge.eval (monomial g t z) coeff1574 := by
  norm_num [atom1574, coeff1574, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1574_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1574 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1574]
  positivity
theorem weighted1574_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (18033750357185701125003146160140848644232535399551088942657890884907705576329435029936354434306614479523082719095092823576214119325616640 : Int) coeff1574) := by
  rw [CoefficientMerge.eval_scale, ← atom1574_identity]
  exact mul_nonneg (by norm_num) (atom1574_nonneg g t z hg hA hB ht hz hw)

def coeff1575 : CoefficientMerge.Poly :=
  [(3145857, 1)]
noncomputable def atom1575 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 2 * (z) ^ 3)
theorem atom1575_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1575 g t z = CoefficientMerge.eval (monomial g t z) coeff1575 := by
  norm_num [atom1575, coeff1575, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1575_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1575 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1575]
  positivity
theorem weighted1575_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (14133446397820580197428550460177137708779845815079912760451145608701465408488173485142689388038475941975494670296986803216062436413297280 : Int) coeff1575) := by
  rw [CoefficientMerge.eval_scale, ← atom1575_identity]
  exact mul_nonneg (by norm_num) (atom1575_nonneg g t z hg hA hB ht hz hw)

def coeff1576 : CoefficientMerge.Poly :=
  [(3146049, 1)]
noncomputable def atom1576 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 4) ^ 1 * (z) ^ 3)
theorem atom1576_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1576 g t z = CoefficientMerge.eval (monomial g t z) coeff1576 := by
  norm_num [atom1576, coeff1576, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1576_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1576 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1576]
  positivity
theorem weighted1576_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (20303545496241958286317811036033221183250858202875933998394691406058331694358866376469994520150037432863672066886034215808985023042965168 : Int) coeff1576) := by
  rw [CoefficientMerge.eval_scale, ← atom1576_identity]
  exact mul_nonneg (by norm_num) (atom1576_nonneg g t z hg hA hB ht hz hw)

def coeff1577 : CoefficientMerge.Poly :=
  [(3146817, 1)]
noncomputable def atom1577 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 5) ^ 1 * (z) ^ 3)
theorem atom1577_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1577 g t z = CoefficientMerge.eval (monomial g t z) coeff1577 := by
  norm_num [atom1577, coeff1577, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1577_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1577 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1577]
  positivity
theorem weighted1577_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (584164861584148472402526516722684130500523618928900939837077364088600485773985882934710690461408480185760364175061173609028961962656256 : Int) coeff1577) := by
  rw [CoefficientMerge.eval_scale, ← atom1577_identity]
  exact mul_nonneg (by norm_num) (atom1577_nonneg g t z hg hA hB ht hz hw)

def coeff1578 : CoefficientMerge.Poly :=
  [(3162177, 1)]
noncomputable def atom1578 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 7) ^ 1 * (z) ^ 3)
theorem atom1578_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1578 g t z = CoefficientMerge.eval (monomial g t z) coeff1578 := by
  norm_num [atom1578, coeff1578, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1578_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1578 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1578]
  positivity
theorem weighted1578_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3731654517796153640979436663273911643341767756916412658680745439389133782371267096773252446110094064349310032718826814357442559571038720 : Int) coeff1578) := by
  rw [CoefficientMerge.eval_scale, ← atom1578_identity]
  exact mul_nonneg (by norm_num) (atom1578_nonneg g t z hg hA hB ht hz hw)

def coeff1579 : CoefficientMerge.Poly :=
  [(3211329, 1)]
noncomputable def atom1579 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 8) ^ 1 * (z) ^ 3)
theorem atom1579_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1579 g t z = CoefficientMerge.eval (monomial g t z) coeff1579 := by
  norm_num [atom1579, coeff1579, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1579_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1579 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1579]
  positivity
theorem weighted1579_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (12784204116536818307505140112531480068756443456671136634200964791277976733636902097472413670692984821150148879388990582989349019878177280 : Int) coeff1579) := by
  rw [CoefficientMerge.eval_scale, ← atom1579_identity]
  exact mul_nonneg (by norm_num) (atom1579_nonneg g t z hg hA hB ht hz hw)

def coeff1580 : CoefficientMerge.Poly :=
  [(3146241, 1)]
noncomputable def atom1580 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 2 * (z) ^ 3)
theorem atom1580_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1580 g t z = CoefficientMerge.eval (monomial g t z) coeff1580 := by
  norm_num [atom1580, coeff1580, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1580_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1580 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1580]
  positivity
theorem weighted1580_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (14876563632942534541650073147823238454669751525422632904232808950872142009298745723357790746150215096610356777040451274612005849678365536 : Int) coeff1580) := by
  rw [CoefficientMerge.eval_scale, ← atom1580_identity]
  exact mul_nonneg (by norm_num) (atom1580_nonneg g t z hg hA hB ht hz hw)

def coeff1581 : CoefficientMerge.Poly :=
  [(3147009, 1)]
noncomputable def atom1581 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 5) ^ 1 * (z) ^ 3)
theorem atom1581_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1581 g t z = CoefficientMerge.eval (monomial g t z) coeff1581 := by
  norm_num [atom1581, coeff1581, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1581_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1581 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1581]
  positivity
theorem weighted1581_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (14119831995168192571791716099523788174829261123389684726288961972699347251614835131124741970968084867730366297140708695496500545135925432 : Int) coeff1581) := by
  rw [CoefficientMerge.eval_scale, ← atom1581_identity]
  exact mul_nonneg (by norm_num) (atom1581_nonneg g t z hg hA hB ht hz hw)

def coeff1582 : CoefficientMerge.Poly :=
  [(3150081, 1)]
noncomputable def atom1582 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (z) ^ 3)
theorem atom1582_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1582 g t z = CoefficientMerge.eval (monomial g t z) coeff1582 := by
  norm_num [atom1582, coeff1582, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1582_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1582 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1582]
  positivity
theorem weighted1582_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (17627034399241509038206569327309252343948327554485575535639051696479671046611292440349474457219388246130551498388773517052847944696860920 : Int) coeff1582) := by
  rw [CoefficientMerge.eval_scale, ← atom1582_identity]
  exact mul_nonneg (by norm_num) (atom1582_nonneg g t z hg hA hB ht hz hw)

def coeff1583 : CoefficientMerge.Poly :=
  [(3162369, 1)]
noncomputable def atom1583 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (z) ^ 3)
theorem atom1583_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1583 g t z = CoefficientMerge.eval (monomial g t z) coeff1583 := by
  norm_num [atom1583, coeff1583, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1583_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1583 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1583]
  positivity
theorem weighted1583_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (17276611532913737792968205387245619054561649096897493243316345838822836799681991217872548569800603863149377715654859553692609530183434680 : Int) coeff1583) := by
  rw [CoefficientMerge.eval_scale, ← atom1583_identity]
  exact mul_nonneg (by norm_num) (atom1583_nonneg g t z hg hA hB ht hz hw)

def coeff1584 : CoefficientMerge.Poly :=
  [(3211521, 1)]
noncomputable def atom1584 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (z) ^ 3)
theorem atom1584_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1584 g t z = CoefficientMerge.eval (monomial g t z) coeff1584 := by
  norm_num [atom1584, coeff1584, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1584_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1584 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1584]
  positivity
theorem weighted1584_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (11826925887347189856990030007317191674906745406811245961304401027819624096532655657507218266370989684980979458097129817406966361266277560 : Int) coeff1584) := by
  rw [CoefficientMerge.eval_scale, ← atom1584_identity]
  exact mul_nonneg (by norm_num) (atom1584_nonneg g t z hg hA hB ht hz hw)

def sparseBlock110 : CoefficientMerge.Poly :=
  [(3145797, 19370507349738316340385990741277354053561775381590515587204359593518076087495142628780097180212544688687297533043199854403441269726597120), (3145809, 46198701263458304849299666056032592867691715871329798826069266509911681816328623002032141770639204521149300192963221673842584970244588800), (3145857, 14133446397820580197428550460177137708779845815079912760451145608701465408488173485142689388038475941975494670296986803216062436413297280), (3145989, 16616871837307044769960393523162058629482048578598685179788875624279226126902259012316557309515588982290165269099284652060282428544819200), (3146001, 30802913540681008343880568491849040351060002652585124875516036798910530182554597133117652986460492534619472454250543656048855748811943872), (3146049, 20303545496241958286317811036033221183250858202875933998394691406058331694358866376469994520150037432863672066886034215808985023042965168), (3146241, 14876563632942534541650073147823238454669751525422632904232808950872142009298745723357790746150215096610356777040451274612005849678365536), (3146757, 4924966315955911986872319189126910623401153909035650508734219317087263831053924785887511280305563991431815370598775102616621002803466240), (3146769, 21330599659713341979981783725006523430707862558319946494463908786679761739795560427823210287305421650901064712502378943832829197962815264), (3146817, 584164861584148472402526516722684130500523618928900939837077364088600485773985882934710690461408480185760364175061173609028961962656256), (3147009, 14119831995168192571791716099523788174829261123389684726288961972699347251614835131124741970968084867730366297140708695496500545135925432), (3149829, 1997854923891052370156233850544743025955224222149557825796121887505244199816945270859830048779822043091799313530385094792626375727329280), (3149841, 13754704568222616307490244925764138455093524854541469134445207014569076390466068257291493805699038800889871405718549946376120027838827520), (3150081, 17627034399241509038206569327309252343948327554485575535639051696479671046611292440349474457219388246130551498388773517052847944696860920), (3162114, 1047108890401221314295933645687405347705271922056637523537367565811159495467580313849928768391468910944267107719878992936913571818803200), (3162129, 18033750357185701125003146160140848644232535399551088942657890884907705576329435029936354434306614479523082719095092823576214119325616640), (3162177, 3731654517796153640979436663273911643341767756916412658680745439389133782371267096773252446110094064349310032718826814357442559571038720), (3162369, 17276611532913737792968205387245619054561649096897493243316345838822836799681991217872548569800603863149377715654859553692609530183434680), (3211329, 12784204116536818307505140112531480068756443456671136634200964791277976733636902097472413670692984821150148879388990582989349019878177280), (3211521, 11826925887347189856990030007317191674906745406811245961304401027819624096532655657507218266370989684980979458097129817406966361266277560)]
theorem sparseBlock110_data : sparseBlock110 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1047108890401221314295933645687405347705271922056637523537367565811159495467580313849928768391468910944267107719878992936913571818803200 : Int) coeff1565) (CoefficientMerge.scale (19370507349738316340385990741277354053561775381590515587204359593518076087495142628780097180212544688687297533043199854403441269726597120 : Int) coeff1566)) (CoefficientMerge.merge (CoefficientMerge.scale (16616871837307044769960393523162058629482048578598685179788875624279226126902259012316557309515588982290165269099284652060282428544819200 : Int) coeff1567) (CoefficientMerge.merge (CoefficientMerge.scale (4924966315955911986872319189126910623401153909035650508734219317087263831053924785887511280305563991431815370598775102616621002803466240 : Int) coeff1568) (CoefficientMerge.scale (1997854923891052370156233850544743025955224222149557825796121887505244199816945270859830048779822043091799313530385094792626375727329280 : Int) coeff1569)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (46198701263458304849299666056032592867691715871329798826069266509911681816328623002032141770639204521149300192963221673842584970244588800 : Int) coeff1570) (CoefficientMerge.scale (30802913540681008343880568491849040351060002652585124875516036798910530182554597133117652986460492534619472454250543656048855748811943872 : Int) coeff1571)) (CoefficientMerge.merge (CoefficientMerge.scale (21330599659713341979981783725006523430707862558319946494463908786679761739795560427823210287305421650901064712502378943832829197962815264 : Int) coeff1572) (CoefficientMerge.merge (CoefficientMerge.scale (13754704568222616307490244925764138455093524854541469134445207014569076390466068257291493805699038800889871405718549946376120027838827520 : Int) coeff1573) (CoefficientMerge.scale (18033750357185701125003146160140848644232535399551088942657890884907705576329435029936354434306614479523082719095092823576214119325616640 : Int) coeff1574))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (14133446397820580197428550460177137708779845815079912760451145608701465408488173485142689388038475941975494670296986803216062436413297280 : Int) coeff1575) (CoefficientMerge.scale (20303545496241958286317811036033221183250858202875933998394691406058331694358866376469994520150037432863672066886034215808985023042965168 : Int) coeff1576)) (CoefficientMerge.merge (CoefficientMerge.scale (584164861584148472402526516722684130500523618928900939837077364088600485773985882934710690461408480185760364175061173609028961962656256 : Int) coeff1577) (CoefficientMerge.merge (CoefficientMerge.scale (3731654517796153640979436663273911643341767756916412658680745439389133782371267096773252446110094064349310032718826814357442559571038720 : Int) coeff1578) (CoefficientMerge.scale (12784204116536818307505140112531480068756443456671136634200964791277976733636902097472413670692984821150148879388990582989349019878177280 : Int) coeff1579)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (14876563632942534541650073147823238454669751525422632904232808950872142009298745723357790746150215096610356777040451274612005849678365536 : Int) coeff1580) (CoefficientMerge.scale (14119831995168192571791716099523788174829261123389684726288961972699347251614835131124741970968084867730366297140708695496500545135925432 : Int) coeff1581)) (CoefficientMerge.merge (CoefficientMerge.scale (17627034399241509038206569327309252343948327554485575535639051696479671046611292440349474457219388246130551498388773517052847944696860920 : Int) coeff1582) (CoefficientMerge.merge (CoefficientMerge.scale (17276611532913737792968205387245619054561649096897493243316345838822836799681991217872548569800603863149377715654859553692609530183434680 : Int) coeff1583) (CoefficientMerge.scale (11826925887347189856990030007317191674906745406811245961304401027819624096532655657507218266370989684980979458097129817406966361266277560 : Int) coeff1584)))))) := by decide +kernel
theorem sparseBlock110_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock110 := by
  rw [sparseBlock110_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted1565_nonneg g t z hg hA hB ht hz hw) (weighted1566_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1567_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1568_nonneg g t z hg hA hB ht hz hw) (weighted1569_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1570_nonneg g t z hg hA hB ht hz hw) (weighted1571_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1572_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1573_nonneg g t z hg hA hB ht hz hw) (weighted1574_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted1575_nonneg g t z hg hA hB ht hz hw) (weighted1576_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1577_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1578_nonneg g t z hg hA hB ht hz hw) (weighted1579_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1580_nonneg g t z hg hA hB ht hz hw) (weighted1581_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1582_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1583_nonneg g t z hg hA hB ht hz hw) (weighted1584_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
