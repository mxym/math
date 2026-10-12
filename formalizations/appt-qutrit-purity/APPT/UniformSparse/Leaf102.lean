import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff1405 : CoefficientMerge.Poly :=
  [(2375682, 1)]
noncomputable def atom1405 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 2 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1405_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1405 g t z = CoefficientMerge.eval (monomial g t z) coeff1405 := by
  norm_num [atom1405, coeff1405, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1405_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1405 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1405]
  positivity
theorem weighted1405_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2707201056176379969699434792451963888039664312180907400619899866884152899117439767519860904555600996411618892044231739366241230689587200 : Int) coeff1405) := by
  rw [CoefficientMerge.eval_scale, ← atom1405_identity]
  exact mul_nonneg (by norm_num) (atom1405_nonneg g t z hg hA hB ht hz hw)

def coeff1406 : CoefficientMerge.Poly :=
  [(786501, 1)]
noncomputable def atom1406 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 1) ^ 1 * (g 3) ^ 1 * (t) ^ 3)
theorem atom1406_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1406 g t z = CoefficientMerge.eval (monomial g t z) coeff1406 := by
  norm_num [atom1406, coeff1406, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1406_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1406 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1406]
  positivity
theorem weighted1406_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (21286521714872344205076281683254539033283260882768121140733864809827843517464000870431732833632623542412928328617678300806989581107793920 : Int) coeff1406) := by
  rw [CoefficientMerge.eval_scale, ← atom1406_identity]
  exact mul_nonneg (by norm_num) (atom1406_nonneg g t z hg hA hB ht hz hw)

def coeff1407 : CoefficientMerge.Poly :=
  [(1572933, 1)]
noncomputable def atom1407 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 1) ^ 1 * (g 3) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1407_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1407 g t z = CoefficientMerge.eval (monomial g t z) coeff1407 := by
  norm_num [atom1407, coeff1407, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1407_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1407 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1407]
  positivity
theorem weighted1407_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (62467227362616047588544042904730312595183095133055501974818108712014206320272583061765468865356732410775128904728546856017917367682913280 : Int) coeff1407) := by
  rw [CoefficientMerge.eval_scale, ← atom1407_identity]
  exact mul_nonneg (by norm_num) (atom1407_nonneg g t z hg hA hB ht hz hw)

def coeff1408 : CoefficientMerge.Poly :=
  [(2359365, 1)]
noncomputable def atom1408 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 1) ^ 1 * (g 3) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1408_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1408 g t z = CoefficientMerge.eval (monomial g t z) coeff1408 := by
  norm_num [atom1408, coeff1408, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1408_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1408 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1408]
  positivity
theorem weighted1408_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (60551212997482019723853751962753127615461609631877896421288603495704438890303724820113833211936653557049498109154068409614369056301716480 : Int) coeff1408) := by
  rw [CoefficientMerge.eval_scale, ← atom1408_identity]
  exact mul_nonneg (by norm_num) (atom1408_nonneg g t z hg hA hB ht hz hw)

def coeff1409 : CoefficientMerge.Poly :=
  [(786693, 1)]
noncomputable def atom1409 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 1) ^ 1 * (g 4) ^ 1 * (t) ^ 3)
theorem atom1409_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1409 g t z = CoefficientMerge.eval (monomial g t z) coeff1409 := by
  norm_num [atom1409, coeff1409, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1409_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1409 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1409]
  positivity
theorem weighted1409_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (16661526628966258571100224841224606510051040958631395345058370345224135536842606445876985123808885361103540782412493314484321034641408000 : Int) coeff1409) := by
  rw [CoefficientMerge.eval_scale, ← atom1409_identity]
  exact mul_nonneg (by norm_num) (atom1409_nonneg g t z hg hA hB ht hz hw)

def coeff1410 : CoefficientMerge.Poly :=
  [(1573125, 1)]
noncomputable def atom1410 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 1) ^ 1 * (g 4) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1410_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1410 g t z = CoefficientMerge.eval (monomial g t z) coeff1410 := by
  norm_num [atom1410, coeff1410, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1410_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1410 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1410]
  positivity
theorem weighted1410_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (49919075794180923131065351224304632318271915954775482368990967850861144977321577303797261841656148650457660277010902773128153177121817600 : Int) coeff1410) := by
  rw [CoefficientMerge.eval_scale, ← atom1410_identity]
  exact mul_nonneg (by norm_num) (atom1410_nonneg g t z hg hA hB ht hz hw)

def coeff1411 : CoefficientMerge.Poly :=
  [(2359557, 1)]
noncomputable def atom1411 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 1) ^ 1 * (g 4) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1411_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1411 g t z = CoefficientMerge.eval (monomial g t z) coeff1411 := by
  norm_num [atom1411, coeff1411, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1411_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1411 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1411]
  positivity
theorem weighted1411_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (49874421002521709329925519906242084437702923574742772203721473129916235567381229870236834027362852271644284763697694110704114571025228800 : Int) coeff1411) := by
  rw [CoefficientMerge.eval_scale, ← atom1411_identity]
  exact mul_nonneg (by norm_num) (atom1411_nonneg g t z hg hA hB ht hz hw)

def coeff1412 : CoefficientMerge.Poly :=
  [(787461, 1)]
noncomputable def atom1412 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 1) ^ 1 * (g 5) ^ 1 * (t) ^ 3)
theorem atom1412_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1412 g t z = CoefficientMerge.eval (monomial g t z) coeff1412 := by
  norm_num [atom1412, coeff1412, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1412_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1412 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1412]
  positivity
theorem weighted1412_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4922151324600314819901507566902664972199636971962031660576084859380889841525721080047822042486495471952315346682744799107030272456601600 : Int) coeff1412) := by
  rw [CoefficientMerge.eval_scale, ← atom1412_identity]
  exact mul_nonneg (by norm_num) (atom1412_nonneg g t z hg hA hB ht hz hw)

def coeff1413 : CoefficientMerge.Poly :=
  [(1573893, 1)]
noncomputable def atom1413 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 1) ^ 1 * (g 5) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1413_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1413 g t z = CoefficientMerge.eval (monomial g t z) coeff1413 := by
  norm_num [atom1413, coeff1413, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1413_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1413 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1413]
  positivity
theorem weighted1413_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (14765099104944813870456235926670912701537984944742515129703459343075773069452188025928502222183112724528528752581590999250527283575505920 : Int) coeff1413) := by
  rw [CoefficientMerge.eval_scale, ← atom1413_identity]
  exact mul_nonneg (by norm_num) (atom1413_nonneg g t z hg hA hB ht hz hw)

def coeff1414 : CoefficientMerge.Poly :=
  [(2360325, 1)]
noncomputable def atom1414 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 1) ^ 1 * (g 5) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1414_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1414 g t z = CoefficientMerge.eval (monomial g t z) coeff1414 := by
  norm_num [atom1414, coeff1414, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1414_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1414 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1414]
  positivity
theorem weighted1414_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (14767914096300411037427047548895158352739501881816133977861593800782147058980391731768191460002181244008028776497621302760118013922370560 : Int) coeff1414) := by
  rw [CoefficientMerge.eval_scale, ← atom1414_identity]
  exact mul_nonneg (by norm_num) (atom1414_nonneg g t z hg hA hB ht hz hw)

def coeff1415 : CoefficientMerge.Poly :=
  [(790533, 1)]
noncomputable def atom1415 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 1) ^ 1 * (g 6) ^ 1 * (t) ^ 3)
theorem atom1415_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1415 g t z = CoefficientMerge.eval (monomial g t z) coeff1415 := by
  norm_num [atom1415, coeff1415, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1415_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1415 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1415]
  positivity
theorem weighted1415_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1495768342222810505941757663614591821114702883787581951129917582901571977753193471732124883721601559516431766093102883556679072191283200 : Int) coeff1415) := by
  rw [CoefficientMerge.eval_scale, ← atom1415_identity]
  exact mul_nonneg (by norm_num) (atom1415_nonneg g t z hg hA hB ht hz hw)

def coeff1416 : CoefficientMerge.Poly :=
  [(1576965, 1)]
noncomputable def atom1416 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 1) ^ 1 * (g 6) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1416_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1416 g t z = CoefficientMerge.eval (monomial g t z) coeff1416 := by
  norm_num [atom1416, coeff1416, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1416_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1416 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1416]
  positivity
theorem weighted1416_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3996293936634573257244959640408773505157295736907368063360233777012824913949743546219347980654992534273956793501199876800537787304980480 : Int) coeff1416) := by
  rw [CoefficientMerge.eval_scale, ← atom1416_identity]
  exact mul_nonneg (by norm_num) (atom1416_nonneg g t z hg hA hB ht hz hw)

def coeff1417 : CoefficientMerge.Poly :=
  [(2363397, 1)]
noncomputable def atom1417 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 1) ^ 1 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1417_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1417 g t z = CoefficientMerge.eval (monomial g t z) coeff1417 := by
  norm_num [atom1417, coeff1417, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1417_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1417 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1417]
  positivity
theorem weighted1417_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3992813425466279661618628387191809292459193683520367079590319605945159853031908217255662979851079142765190062652511003335938913978408960 : Int) coeff1417) := by
  rw [CoefficientMerge.eval_scale, ← atom1417_identity]
  exact mul_nonneg (by norm_num) (atom1417_nonneg g t z hg hA hB ht hz hw)

def coeff1418 : CoefficientMerge.Poly :=
  [(786513, 1)]
noncomputable def atom1418 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 3) ^ 1 * (t) ^ 3)
theorem atom1418_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1418 g t z = CoefficientMerge.eval (monomial g t z) coeff1418 := by
  norm_num [atom1418, coeff1418, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1418_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1418 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1418]
  positivity
theorem weighted1418_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (66794453144673260507885418102198144444993060957212057975305924910564750473443041710388515214539921509657622163557003753251356008110159360 : Int) coeff1418) := by
  rw [CoefficientMerge.eval_scale, ← atom1418_identity]
  exact mul_nonneg (by norm_num) (atom1418_nonneg g t z hg hA hB ht hz hw)

def coeff1419 : CoefficientMerge.Poly :=
  [(1572945, 1)]
noncomputable def atom1419 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 3) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1419_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1419 g t z = CoefficientMerge.eval (monomial g t z) coeff1419 := by
  norm_num [atom1419, coeff1419, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1419_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1419 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1419]
  positivity
theorem weighted1419_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (206834494065562298941533216979947163534353248977743763762374592150367103108928759325956325801320551518598786322930535090567701600588550400 : Int) coeff1419) := by
  rw [CoefficientMerge.eval_scale, ← atom1419_identity]
  exact mul_nonneg (by norm_num) (atom1419_nonneg g t z hg hA hB ht hz hw)

def coeff1420 : CoefficientMerge.Poly :=
  [(2359377, 1)]
noncomputable def atom1420 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 3) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1420_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1420 g t z = CoefficientMerge.eval (monomial g t z) coeff1420 := by
  norm_num [atom1420, coeff1420, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1420_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1420 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1420]
  positivity
theorem weighted1420_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (183890276670981895475104375914375293861014476770461323836423260760854702902400546416753734594502118084751893215989044835276619084992509440 : Int) coeff1420) := by
  rw [CoefficientMerge.eval_scale, ← atom1420_identity]
  exact mul_nonneg (by norm_num) (atom1420_nonneg g t z hg hA hB ht hz hw)

def coeff1421 : CoefficientMerge.Poly :=
  [(786705, 1)]
noncomputable def atom1421 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 4) ^ 1 * (t) ^ 3)
theorem atom1421_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1421 g t z = CoefficientMerge.eval (monomial g t z) coeff1421 := by
  norm_num [atom1421, coeff1421, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1421_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1421 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1421]
  positivity
theorem weighted1421_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (67043469774497744183107192549340379626830722632604388723871458364453521568986905850812064499003494262335538690661837812845296690021891840 : Int) coeff1421) := by
  rw [CoefficientMerge.eval_scale, ← atom1421_identity]
  exact mul_nonneg (by norm_num) (atom1421_nonneg g t z hg hA hB ht hz hw)

def coeff1422 : CoefficientMerge.Poly :=
  [(1573137, 1)]
noncomputable def atom1422 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 4) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1422_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1422 g t z = CoefficientMerge.eval (monomial g t z) coeff1422 := by
  norm_num [atom1422, coeff1422, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1422_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1422 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1422]
  positivity
theorem weighted1422_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (183709354355281240662931121213867727179668260854003078908060956188842901121481088695166284350248045561843053568789032191812018849825022912 : Int) coeff1422) := by
  rw [CoefficientMerge.eval_scale, ← atom1422_identity]
  exact mul_nonneg (by norm_num) (atom1422_nonneg g t z hg hA hB ht hz hw)

def coeff1423 : CoefficientMerge.Poly :=
  [(2359569, 1)]
noncomputable def atom1423 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 4) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1423_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1423 g t z = CoefficientMerge.eval (monomial g t z) coeff1423 := by
  norm_num [atom1423, coeff1423, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1423_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1423 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1423]
  positivity
theorem weighted1423_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (148599455180278332706094320319385334842160259220531400786805316713434740712585724391929678065325037376982366883679416163632084407667231552 : Int) coeff1423) := by
  rw [CoefficientMerge.eval_scale, ← atom1423_identity]
  exact mul_nonneg (by norm_num) (atom1423_nonneg g t z hg hA hB ht hz hw)

def coeff1424 : CoefficientMerge.Poly :=
  [(787473, 1)]
noncomputable def atom1424 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 5) ^ 1 * (t) ^ 3)
theorem atom1424_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1424 g t z = CoefficientMerge.eval (monomial g t z) coeff1424 := by
  norm_num [atom1424, coeff1424, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1424_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1424 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1424]
  positivity
theorem weighted1424_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (41622344007946070373164347466878905228715441410899037687026579279046683045167616851062887573813220770233062205975705538795168154316899840 : Int) coeff1424) := by
  rw [CoefficientMerge.eval_scale, ← atom1424_identity]
  exact mul_nonneg (by norm_num) (atom1424_nonneg g t z hg hA hB ht hz hw)

def sparseBlock102 : CoefficientMerge.Poly :=
  [(786501, 21286521714872344205076281683254539033283260882768121140733864809827843517464000870431732833632623542412928328617678300806989581107793920), (786513, 66794453144673260507885418102198144444993060957212057975305924910564750473443041710388515214539921509657622163557003753251356008110159360), (786693, 16661526628966258571100224841224606510051040958631395345058370345224135536842606445876985123808885361103540782412493314484321034641408000), (786705, 67043469774497744183107192549340379626830722632604388723871458364453521568986905850812064499003494262335538690661837812845296690021891840), (787461, 4922151324600314819901507566902664972199636971962031660576084859380889841525721080047822042486495471952315346682744799107030272456601600), (787473, 41622344007946070373164347466878905228715441410899037687026579279046683045167616851062887573813220770233062205975705538795168154316899840), (790533, 1495768342222810505941757663614591821114702883787581951129917582901571977753193471732124883721601559516431766093102883556679072191283200), (1572933, 62467227362616047588544042904730312595183095133055501974818108712014206320272583061765468865356732410775128904728546856017917367682913280), (1572945, 206834494065562298941533216979947163534353248977743763762374592150367103108928759325956325801320551518598786322930535090567701600588550400), (1573125, 49919075794180923131065351224304632318271915954775482368990967850861144977321577303797261841656148650457660277010902773128153177121817600), (1573137, 183709354355281240662931121213867727179668260854003078908060956188842901121481088695166284350248045561843053568789032191812018849825022912), (1573893, 14765099104944813870456235926670912701537984944742515129703459343075773069452188025928502222183112724528528752581590999250527283575505920), (1576965, 3996293936634573257244959640408773505157295736907368063360233777012824913949743546219347980654992534273956793501199876800537787304980480), (2359365, 60551212997482019723853751962753127615461609631877896421288603495704438890303724820113833211936653557049498109154068409614369056301716480), (2359377, 183890276670981895475104375914375293861014476770461323836423260760854702902400546416753734594502118084751893215989044835276619084992509440), (2359557, 49874421002521709329925519906242084437702923574742772203721473129916235567381229870236834027362852271644284763697694110704114571025228800), (2359569, 148599455180278332706094320319385334842160259220531400786805316713434740712585724391929678065325037376982366883679416163632084407667231552), (2360325, 14767914096300411037427047548895158352739501881816133977861593800782147058980391731768191460002181244008028776497621302760118013922370560), (2363397, 3992813425466279661618628387191809292459193683520367079590319605945159853031908217255662979851079142765190062652511003335938913978408960), (2375682, 2707201056176379969699434792451963888039664312180907400619899866884152899117439767519860904555600996411618892044231739366241230689587200)]
theorem sparseBlock102_data : sparseBlock102 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (2707201056176379969699434792451963888039664312180907400619899866884152899117439767519860904555600996411618892044231739366241230689587200 : Int) coeff1405) (CoefficientMerge.scale (21286521714872344205076281683254539033283260882768121140733864809827843517464000870431732833632623542412928328617678300806989581107793920 : Int) coeff1406)) (CoefficientMerge.merge (CoefficientMerge.scale (62467227362616047588544042904730312595183095133055501974818108712014206320272583061765468865356732410775128904728546856017917367682913280 : Int) coeff1407) (CoefficientMerge.merge (CoefficientMerge.scale (60551212997482019723853751962753127615461609631877896421288603495704438890303724820113833211936653557049498109154068409614369056301716480 : Int) coeff1408) (CoefficientMerge.scale (16661526628966258571100224841224606510051040958631395345058370345224135536842606445876985123808885361103540782412493314484321034641408000 : Int) coeff1409)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (49919075794180923131065351224304632318271915954775482368990967850861144977321577303797261841656148650457660277010902773128153177121817600 : Int) coeff1410) (CoefficientMerge.scale (49874421002521709329925519906242084437702923574742772203721473129916235567381229870236834027362852271644284763697694110704114571025228800 : Int) coeff1411)) (CoefficientMerge.merge (CoefficientMerge.scale (4922151324600314819901507566902664972199636971962031660576084859380889841525721080047822042486495471952315346682744799107030272456601600 : Int) coeff1412) (CoefficientMerge.merge (CoefficientMerge.scale (14765099104944813870456235926670912701537984944742515129703459343075773069452188025928502222183112724528528752581590999250527283575505920 : Int) coeff1413) (CoefficientMerge.scale (14767914096300411037427047548895158352739501881816133977861593800782147058980391731768191460002181244008028776497621302760118013922370560 : Int) coeff1414))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1495768342222810505941757663614591821114702883787581951129917582901571977753193471732124883721601559516431766093102883556679072191283200 : Int) coeff1415) (CoefficientMerge.scale (3996293936634573257244959640408773505157295736907368063360233777012824913949743546219347980654992534273956793501199876800537787304980480 : Int) coeff1416)) (CoefficientMerge.merge (CoefficientMerge.scale (3992813425466279661618628387191809292459193683520367079590319605945159853031908217255662979851079142765190062652511003335938913978408960 : Int) coeff1417) (CoefficientMerge.merge (CoefficientMerge.scale (66794453144673260507885418102198144444993060957212057975305924910564750473443041710388515214539921509657622163557003753251356008110159360 : Int) coeff1418) (CoefficientMerge.scale (206834494065562298941533216979947163534353248977743763762374592150367103108928759325956325801320551518598786322930535090567701600588550400 : Int) coeff1419)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (183890276670981895475104375914375293861014476770461323836423260760854702902400546416753734594502118084751893215989044835276619084992509440 : Int) coeff1420) (CoefficientMerge.scale (67043469774497744183107192549340379626830722632604388723871458364453521568986905850812064499003494262335538690661837812845296690021891840 : Int) coeff1421)) (CoefficientMerge.merge (CoefficientMerge.scale (183709354355281240662931121213867727179668260854003078908060956188842901121481088695166284350248045561843053568789032191812018849825022912 : Int) coeff1422) (CoefficientMerge.merge (CoefficientMerge.scale (148599455180278332706094320319385334842160259220531400786805316713434740712585724391929678065325037376982366883679416163632084407667231552 : Int) coeff1423) (CoefficientMerge.scale (41622344007946070373164347466878905228715441410899037687026579279046683045167616851062887573813220770233062205975705538795168154316899840 : Int) coeff1424)))))) := by decide +kernel
theorem sparseBlock102_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock102 := by
  rw [sparseBlock102_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted1405_nonneg g t z hg hA hB ht hz hw) (weighted1406_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1407_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1408_nonneg g t z hg hA hB ht hz hw) (weighted1409_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1410_nonneg g t z hg hA hB ht hz hw) (weighted1411_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1412_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1413_nonneg g t z hg hA hB ht hz hw) (weighted1414_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted1415_nonneg g t z hg hA hB ht hz hw) (weighted1416_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1417_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1418_nonneg g t z hg hA hB ht hz hw) (weighted1419_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1420_nonneg g t z hg hA hB ht hz hw) (weighted1421_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1422_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1423_nonneg g t z hg hA hB ht hz hw) (weighted1424_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
