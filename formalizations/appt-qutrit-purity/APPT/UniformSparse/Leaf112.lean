import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff1605 : CoefficientMerge.Poly :=
  [(3150084, 1)]
noncomputable def atom1605 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (z) ^ 3)
theorem atom1605_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1605 g t z = CoefficientMerge.eval (monomial g t z) coeff1605 := by
  norm_num [atom1605, coeff1605, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1605_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1605 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1605]
  positivity
theorem weighted1605_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (21379681477351758774347649865093903122186320290896322631750769132184275744923230068252799430039853503968327072992504028027142813567881920 : Int) coeff1605) := by
  rw [CoefficientMerge.eval_scale, ← atom1605_identity]
  exact mul_nonneg (by norm_num) (atom1605_nonneg g t z hg hA hB ht hz hw)

def coeff1606 : CoefficientMerge.Poly :=
  [(3162372, 1)]
noncomputable def atom1606 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (z) ^ 3)
theorem atom1606_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1606 g t z = CoefficientMerge.eval (monomial g t z) coeff1606 := by
  norm_num [atom1606, coeff1606, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1606_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1606 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1606]
  positivity
theorem weighted1606_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (25924100024495487367567880752087575700075640769607462060636968774424755979043635265726947472232356126537892574885555491967481660725731840 : Int) coeff1606) := by
  rw [CoefficientMerge.eval_scale, ← atom1606_identity]
  exact mul_nonneg (by norm_num) (atom1606_nonneg g t z hg hA hB ht hz hw)

def coeff1607 : CoefficientMerge.Poly :=
  [(3211524, 1)]
noncomputable def atom1607 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (z) ^ 3)
theorem atom1607_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1607 g t z = CoefficientMerge.eval (monomial g t z) coeff1607 := by
  norm_num [atom1607, coeff1607, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1607_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1607 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1607]
  positivity
theorem weighted1607_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (10969245442471048501983431861843176256585145834718677537162908434507811789648460819295018152900214185453001289276406245312473211614056960 : Int) coeff1607) := by
  rw [CoefficientMerge.eval_scale, ← atom1607_identity]
  exact mul_nonneg (by norm_num) (atom1607_nonneg g t z hg hA hB ht hz hw)

def coeff1608 : CoefficientMerge.Poly :=
  [(3150852, 1)]
noncomputable def atom1608 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (z) ^ 3)
theorem atom1608_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1608 g t z = CoefficientMerge.eval (monomial g t z) coeff1608 := by
  norm_num [atom1608, coeff1608, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1608_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1608 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1608]
  positivity
theorem weighted1608_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (912321092734125904252057795411370904040392641971548016891447713717502270141752299682371361872405315089387190279377797819105105705621120 : Int) coeff1608) := by
  rw [CoefficientMerge.eval_scale, ← atom1608_identity]
  exact mul_nonneg (by norm_num) (atom1608_nonneg g t z hg hA hB ht hz hw)

def coeff1609 : CoefficientMerge.Poly :=
  [(3212292, 1)]
noncomputable def atom1609 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (z) ^ 3)
theorem atom1609_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1609 g t z = CoefficientMerge.eval (monomial g t z) coeff1609 := by
  norm_num [atom1609, coeff1609, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1609_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1609 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1609]
  positivity
theorem weighted1609_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (7035759438895438540132649483657863969344875686812553145286123167007364787277538340862353224959073857025064553485913107030583788043670860 : Int) coeff1609) := by
  rw [CoefficientMerge.eval_scale, ← atom1609_identity]
  exact mul_nonneg (by norm_num) (atom1609_nonneg g t z hg hA hB ht hz hw)

def coeff1610 : CoefficientMerge.Poly :=
  [(3166212, 1)]
noncomputable def atom1610 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (z) ^ 3)
theorem atom1610_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1610 g t z = CoefficientMerge.eval (monomial g t z) coeff1610 := by
  norm_num [atom1610, coeff1610, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1610_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1610 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1610]
  positivity
theorem weighted1610_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2098724061857374993479443367226480136791712267776758241717324777148985719596532642108762360861528982752559112208505316295929827936823200 : Int) coeff1610) := by
  rw [CoefficientMerge.eval_scale, ← atom1610_identity]
  exact mul_nonneg (by norm_num) (atom1610_nonneg g t z hg hA hB ht hz hw)

def coeff1611 : CoefficientMerge.Poly :=
  [(3215364, 1)]
noncomputable def atom1611 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (z) ^ 3)
theorem atom1611_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1611 g t z = CoefficientMerge.eval (monomial g t z) coeff1611 := by
  norm_num [atom1611, coeff1611, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1611_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1611 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1611]
  positivity
theorem weighted1611_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (10077709211975016640689394702016535674411497193261108891510072073477448855178758478849033054156343424778419443999640826047796216479382400 : Int) coeff1611) := by
  rw [CoefficientMerge.eval_scale, ← atom1611_identity]
  exact mul_nonneg (by norm_num) (atom1611_nonneg g t z hg hA hB ht hz hw)

def coeff1612 : CoefficientMerge.Poly :=
  [(3146064, 1)]
noncomputable def atom1612 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 4) ^ 1 * (z) ^ 3)
theorem atom1612_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1612 g t z = CoefficientMerge.eval (monomial g t z) coeff1612 := by
  norm_num [atom1612, coeff1612, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1612_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1612 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1612]
  positivity
theorem weighted1612_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (130798856077687441292513666925595014445191838917928271470218859909599739323349559287420003422215774908826113184678910358107755191478638560 : Int) coeff1612) := by
  rw [CoefficientMerge.eval_scale, ← atom1612_identity]
  exact mul_nonneg (by norm_num) (atom1612_nonneg g t z hg hA hB ht hz hw)

def coeff1613 : CoefficientMerge.Poly :=
  [(3146832, 1)]
noncomputable def atom1613 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 5) ^ 1 * (z) ^ 3)
theorem atom1613_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1613 g t z = CoefficientMerge.eval (monomial g t z) coeff1613 := by
  norm_num [atom1613, coeff1613, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1613_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1613 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1613]
  positivity
theorem weighted1613_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (43416869057320351828052804247222189264586614236346961917526945491739488940001388395550595224012645479704031119042789986185404117017671040 : Int) coeff1613) := by
  rw [CoefficientMerge.eval_scale, ← atom1613_identity]
  exact mul_nonneg (by norm_num) (atom1613_nonneg g t z hg hA hB ht hz hw)

def coeff1614 : CoefficientMerge.Poly :=
  [(3149904, 1)]
noncomputable def atom1614 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 6) ^ 1 * (z) ^ 3)
theorem atom1614_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1614 g t z = CoefficientMerge.eval (monomial g t z) coeff1614 := by
  norm_num [atom1614, coeff1614, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1614_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1614 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1614]
  positivity
theorem weighted1614_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (39022215922240492549686504354946633895189283232263473207972210942721621091828758662944152922842811782069470658302558191110732031312094400 : Int) coeff1614) := by
  rw [CoefficientMerge.eval_scale, ← atom1614_identity]
  exact mul_nonneg (by norm_num) (atom1614_nonneg g t z hg hA hB ht hz hw)

def coeff1615 : CoefficientMerge.Poly :=
  [(3162192, 1)]
noncomputable def atom1615 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 7) ^ 1 * (z) ^ 3)
theorem atom1615_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1615 g t z = CoefficientMerge.eval (monomial g t z) coeff1615 := by
  norm_num [atom1615, coeff1615, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1615_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1615 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1615]
  positivity
theorem weighted1615_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (57932817007913575295665934133314082534288297098713717831329149016264192257591425317173283332301221691998288088869149633228973366558248000 : Int) coeff1615) := by
  rw [CoefficientMerge.eval_scale, ← atom1615_identity]
  exact mul_nonneg (by norm_num) (atom1615_nonneg g t z hg hA hB ht hz hw)

def coeff1616 : CoefficientMerge.Poly :=
  [(3147024, 1)]
noncomputable def atom1616 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 5) ^ 1 * (z) ^ 3)
theorem atom1616_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1616 g t z = CoefficientMerge.eval (monomial g t z) coeff1616 := by
  norm_num [atom1616, coeff1616, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1616_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1616 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1616]
  positivity
theorem weighted1616_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (10995542318137821120856973010700027695281616667079345730282760695753312864960230407607653857064052288101530103374256243951892434144358400 : Int) coeff1616) := by
  rw [CoefficientMerge.eval_scale, ← atom1616_identity]
  exact mul_nonneg (by norm_num) (atom1616_nonneg g t z hg hA hB ht hz hw)

def coeff1617 : CoefficientMerge.Poly :=
  [(3150096, 1)]
noncomputable def atom1617 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (z) ^ 3)
theorem atom1617_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1617 g t z = CoefficientMerge.eval (monomial g t z) coeff1617 := by
  norm_num [atom1617, coeff1617, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1617_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1617 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1617]
  positivity
theorem weighted1617_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (9548186576784428147426912699304116190816472480377964996655158115541945527380186794872314071503075066546820243051703769156689159963434480 : Int) coeff1617) := by
  rw [CoefficientMerge.eval_scale, ← atom1617_identity]
  exact mul_nonneg (by norm_num) (atom1617_nonneg g t z hg hA hB ht hz hw)

def coeff1618 : CoefficientMerge.Poly :=
  [(3162384, 1)]
noncomputable def atom1618 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (z) ^ 3)
theorem atom1618_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1618 g t z = CoefficientMerge.eval (monomial g t z) coeff1618 := by
  norm_num [atom1618, coeff1618, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1618_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1618 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1618]
  positivity
theorem weighted1618_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (25614704068375888325182574683729541974299739869196269438057764962958945801703819270839427599977612460592664185563784412059885502085241920 : Int) coeff1618) := by
  rw [CoefficientMerge.eval_scale, ← atom1618_identity]
  exact mul_nonneg (by norm_num) (atom1618_nonneg g t z hg hA hB ht hz hw)

def coeff1619 : CoefficientMerge.Poly :=
  [(3211536, 1)]
noncomputable def atom1619 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (z) ^ 3)
theorem atom1619_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1619 g t z = CoefficientMerge.eval (monomial g t z) coeff1619 := by
  norm_num [atom1619, coeff1619, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1619_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1619 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1619]
  positivity
theorem weighted1619_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (7735474099286509482304932965207193420710398039126028319401995134490585115865530112351136546739090940693519367585818530719857091017229320 : Int) coeff1619) := by
  rw [CoefficientMerge.eval_scale, ← atom1619_identity]
  exact mul_nonneg (by norm_num) (atom1619_nonneg g t z hg hA hB ht hz hw)

def coeff1620 : CoefficientMerge.Poly :=
  [(3145761, 1)]
noncomputable def atom1620 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 2 * (z) ^ 3)
theorem atom1620_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1620 g t z = CoefficientMerge.eval (monomial g t z) coeff1620 := by
  norm_num [atom1620, coeff1620, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1620_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1620 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1620]
  positivity
theorem weighted1620_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (16255785755464315773720487861917017040989836368469228919433831009055055734613886384489697174077963428991376451193592043167487975330856960 : Int) coeff1620) := by
  rw [CoefficientMerge.eval_scale, ← atom1620_identity]
  exact mul_nonneg (by norm_num) (atom1620_nonneg g t z hg hA hB ht hz hw)

def coeff1621 : CoefficientMerge.Poly :=
  [(3145764, 1)]
noncomputable def atom1621 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 2 * (z) ^ 3)
theorem atom1621_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1621 g t z = CoefficientMerge.eval (monomial g t z) coeff1621 := by
  norm_num [atom1621, coeff1621, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1621_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1621 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1621]
  positivity
theorem weighted1621_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (33838599567938550408286729665073700758718852999295468969699981940274316674116487305244403131021138749599653630968628863632854501627308032 : Int) coeff1621) := by
  rw [CoefficientMerge.eval_scale, ← atom1621_identity]
  exact mul_nonneg (by norm_num) (atom1621_nonneg g t z hg hA hB ht hz hw)

def coeff1622 : CoefficientMerge.Poly :=
  [(1654785, 1)]
noncomputable def atom1622 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1622_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1622 g t z = CoefficientMerge.eval (monomial g t z) coeff1622 := by
  norm_num [atom1622, coeff1622, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1622_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1622 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1622]
  positivity
theorem weighted1622_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5950184858777161782745236045203005819967266357827614442632511790651209282556948264102280923635847118558255034274319081564998822867123200 : Int) coeff1622) := by
  rw [CoefficientMerge.eval_scale, ← atom1622_identity]
  exact mul_nonneg (by norm_num) (atom1622_nonneg g t z hg hA hB ht hz hw)

def coeff1623 : CoefficientMerge.Poly :=
  [(2441217, 1)]
noncomputable def atom1623 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1623_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1623 g t z = CoefficientMerge.eval (monomial g t z) coeff1623 := by
  norm_num [atom1623, coeff1623, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1623_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1623 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1623]
  positivity
theorem weighted1623_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (8430951938873565571548708476792730041907280825373006773464977456172441140071095301730921824185176541743722427663641418694237865668441600 : Int) coeff1623) := by
  rw [CoefficientMerge.eval_scale, ← atom1623_identity]
  exact mul_nonneg (by norm_num) (atom1623_nonneg g t z hg hA hB ht hz hw)

def coeff1624 : CoefficientMerge.Poly :=
  [(2392065, 1)]
noncomputable def atom1624 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 7) ^ 2 * (t) ^ 1 * (z) ^ 2)
theorem atom1624_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1624 g t z = CoefficientMerge.eval (monomial g t z) coeff1624 := by
  norm_num [atom1624, coeff1624, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1624_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1624 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1624]
  positivity
theorem weighted1624_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (6757999781655786995901568218574469687769401293204547755310631170996885976016824234993310078878700304815583447156941066195075935617664000 : Int) coeff1624) := by
  rw [CoefficientMerge.eval_scale, ← atom1624_identity]
  exact mul_nonneg (by norm_num) (atom1624_nonneg g t z hg hA hB ht hz hw)

def sparseBlock112 : CoefficientMerge.Poly :=
  [(1654785, 5950184858777161782745236045203005819967266357827614442632511790651209282556948264102280923635847118558255034274319081564998822867123200), (2392065, 6757999781655786995901568218574469687769401293204547755310631170996885976016824234993310078878700304815583447156941066195075935617664000), (2441217, 8430951938873565571548708476792730041907280825373006773464977456172441140071095301730921824185176541743722427663641418694237865668441600), (3145761, 16255785755464315773720487861917017040989836368469228919433831009055055734613886384489697174077963428991376451193592043167487975330856960), (3145764, 33838599567938550408286729665073700758718852999295468969699981940274316674116487305244403131021138749599653630968628863632854501627308032), (3146064, 130798856077687441292513666925595014445191838917928271470218859909599739323349559287420003422215774908826113184678910358107755191478638560), (3146832, 43416869057320351828052804247222189264586614236346961917526945491739488940001388395550595224012645479704031119042789986185404117017671040), (3147024, 10995542318137821120856973010700027695281616667079345730282760695753312864960230407607653857064052288101530103374256243951892434144358400), (3149904, 39022215922240492549686504354946633895189283232263473207972210942721621091828758662944152922842811782069470658302558191110732031312094400), (3150084, 21379681477351758774347649865093903122186320290896322631750769132184275744923230068252799430039853503968327072992504028027142813567881920), (3150096, 9548186576784428147426912699304116190816472480377964996655158115541945527380186794872314071503075066546820243051703769156689159963434480), (3150852, 912321092734125904252057795411370904040392641971548016891447713717502270141752299682371361872405315089387190279377797819105105705621120), (3162192, 57932817007913575295665934133314082534288297098713717831329149016264192257591425317173283332301221691998288088869149633228973366558248000), (3162372, 25924100024495487367567880752087575700075640769607462060636968774424755979043635265726947472232356126537892574885555491967481660725731840), (3162384, 25614704068375888325182574683729541974299739869196269438057764962958945801703819270839427599977612460592664185563784412059885502085241920), (3166212, 2098724061857374993479443367226480136791712267776758241717324777148985719596532642108762360861528982752559112208505316295929827936823200), (3211524, 10969245442471048501983431861843176256585145834718677537162908434507811789648460819295018152900214185453001289276406245312473211614056960), (3211536, 7735474099286509482304932965207193420710398039126028319401995134490585115865530112351136546739090940693519367585818530719857091017229320), (3212292, 7035759438895438540132649483657863969344875686812553145286123167007364787277538340862353224959073857025064553485913107030583788043670860), (3215364, 10077709211975016640689394702016535674411497193261108891510072073477448855178758478849033054156343424778419443999640826047796216479382400)]
theorem sparseBlock112_data : sparseBlock112 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (21379681477351758774347649865093903122186320290896322631750769132184275744923230068252799430039853503968327072992504028027142813567881920 : Int) coeff1605) (CoefficientMerge.scale (25924100024495487367567880752087575700075640769607462060636968774424755979043635265726947472232356126537892574885555491967481660725731840 : Int) coeff1606)) (CoefficientMerge.merge (CoefficientMerge.scale (10969245442471048501983431861843176256585145834718677537162908434507811789648460819295018152900214185453001289276406245312473211614056960 : Int) coeff1607) (CoefficientMerge.merge (CoefficientMerge.scale (912321092734125904252057795411370904040392641971548016891447713717502270141752299682371361872405315089387190279377797819105105705621120 : Int) coeff1608) (CoefficientMerge.scale (7035759438895438540132649483657863969344875686812553145286123167007364787277538340862353224959073857025064553485913107030583788043670860 : Int) coeff1609)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (2098724061857374993479443367226480136791712267776758241717324777148985719596532642108762360861528982752559112208505316295929827936823200 : Int) coeff1610) (CoefficientMerge.scale (10077709211975016640689394702016535674411497193261108891510072073477448855178758478849033054156343424778419443999640826047796216479382400 : Int) coeff1611)) (CoefficientMerge.merge (CoefficientMerge.scale (130798856077687441292513666925595014445191838917928271470218859909599739323349559287420003422215774908826113184678910358107755191478638560 : Int) coeff1612) (CoefficientMerge.merge (CoefficientMerge.scale (43416869057320351828052804247222189264586614236346961917526945491739488940001388395550595224012645479704031119042789986185404117017671040 : Int) coeff1613) (CoefficientMerge.scale (39022215922240492549686504354946633895189283232263473207972210942721621091828758662944152922842811782069470658302558191110732031312094400 : Int) coeff1614))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (57932817007913575295665934133314082534288297098713717831329149016264192257591425317173283332301221691998288088869149633228973366558248000 : Int) coeff1615) (CoefficientMerge.scale (10995542318137821120856973010700027695281616667079345730282760695753312864960230407607653857064052288101530103374256243951892434144358400 : Int) coeff1616)) (CoefficientMerge.merge (CoefficientMerge.scale (9548186576784428147426912699304116190816472480377964996655158115541945527380186794872314071503075066546820243051703769156689159963434480 : Int) coeff1617) (CoefficientMerge.merge (CoefficientMerge.scale (25614704068375888325182574683729541974299739869196269438057764962958945801703819270839427599977612460592664185563784412059885502085241920 : Int) coeff1618) (CoefficientMerge.scale (7735474099286509482304932965207193420710398039126028319401995134490585115865530112351136546739090940693519367585818530719857091017229320 : Int) coeff1619)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (16255785755464315773720487861917017040989836368469228919433831009055055734613886384489697174077963428991376451193592043167487975330856960 : Int) coeff1620) (CoefficientMerge.scale (33838599567938550408286729665073700758718852999295468969699981940274316674116487305244403131021138749599653630968628863632854501627308032 : Int) coeff1621)) (CoefficientMerge.merge (CoefficientMerge.scale (5950184858777161782745236045203005819967266357827614442632511790651209282556948264102280923635847118558255034274319081564998822867123200 : Int) coeff1622) (CoefficientMerge.merge (CoefficientMerge.scale (8430951938873565571548708476792730041907280825373006773464977456172441140071095301730921824185176541743722427663641418694237865668441600 : Int) coeff1623) (CoefficientMerge.scale (6757999781655786995901568218574469687769401293204547755310631170996885976016824234993310078878700304815583447156941066195075935617664000 : Int) coeff1624)))))) := by decide +kernel
theorem sparseBlock112_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock112 := by
  rw [sparseBlock112_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted1605_nonneg g t z hg hA hB ht hz hw) (weighted1606_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1607_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1608_nonneg g t z hg hA hB ht hz hw) (weighted1609_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1610_nonneg g t z hg hA hB ht hz hw) (weighted1611_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1612_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1613_nonneg g t z hg hA hB ht hz hw) (weighted1614_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted1615_nonneg g t z hg hA hB ht hz hw) (weighted1616_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1617_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1618_nonneg g t z hg hA hB ht hz hw) (weighted1619_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1620_nonneg g t z hg hA hB ht hz hw) (weighted1621_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1622_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1623_nonneg g t z hg hA hB ht hz hw) (weighted1624_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
