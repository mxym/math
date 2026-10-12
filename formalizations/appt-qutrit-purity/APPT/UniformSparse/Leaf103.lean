import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff1425 : CoefficientMerge.Poly :=
  [(1573905, 1)]
noncomputable def atom1425 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 5) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1425_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1425 g t z = CoefficientMerge.eval (monomial g t z) coeff1425 := by
  norm_num [atom1425, coeff1425, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1425_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1425 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1425]
  positivity
theorem weighted1425_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (141294762036727360906391295241356601691313677522670623928928878813727585707899292075590581210846067320993513488824639798646368746991983104 : Int) coeff1425) := by
  rw [CoefficientMerge.eval_scale, ← atom1425_identity]
  exact mul_nonneg (by norm_num) (atom1425_nonneg g t z hg hA hB ht hz hw)

def coeff1426 : CoefficientMerge.Poly :=
  [(2360337, 1)]
noncomputable def atom1426 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 5) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1426_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1426 g t z = CoefficientMerge.eval (monomial g t z) coeff1426 := by
  norm_num [atom1426, coeff1426, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1426_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1426 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1426]
  positivity
theorem weighted1426_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (102940359927398165361223315348560827630968400250807031935126672769827461343581711754692917503262019556920222063292919571001881136917522208 : Int) coeff1426) := by
  rw [CoefficientMerge.eval_scale, ← atom1426_identity]
  exact mul_nonneg (by norm_num) (atom1426_nonneg g t z hg hA hB ht hz hw)

def coeff1427 : CoefficientMerge.Poly :=
  [(790545, 1)]
noncomputable def atom1427 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 6) ^ 1 * (t) ^ 3)
theorem atom1427_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1427 g t z = CoefficientMerge.eval (monomial g t z) coeff1427 := by
  norm_num [atom1427, coeff1427, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1427_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1427 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1427]
  positivity
theorem weighted1427_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (42065941333891898521329146756685916520652419984039804525905236806751251541645613496044802304065364689000344787457687647684027428480097280 : Int) coeff1427) := by
  rw [CoefficientMerge.eval_scale, ← atom1427_identity]
  exact mul_nonneg (by norm_num) (atom1427_nonneg g t z hg hA hB ht hz hw)

def coeff1428 : CoefficientMerge.Poly :=
  [(1576977, 1)]
noncomputable def atom1428 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 6) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1428_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1428 g t z = CoefficientMerge.eval (monomial g t z) coeff1428 := by
  norm_num [atom1428, coeff1428, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1428_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1428 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1428]
  positivity
theorem weighted1428_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (119176422847400031379907274091198318779344230672900453444685138026794285033836798584922867409194943685946783596488134284586026112582568960 : Int) coeff1428) := by
  rw [CoefficientMerge.eval_scale, ← atom1428_identity]
  exact mul_nonneg (by norm_num) (atom1428_nonneg g t z hg hA hB ht hz hw)

def coeff1429 : CoefficientMerge.Poly :=
  [(2363409, 1)]
noncomputable def atom1429 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1429_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1429 g t z = CoefficientMerge.eval (monomial g t z) coeff1429 := by
  norm_num [atom1429, coeff1429, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1429_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1429 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1429]
  positivity
theorem weighted1429_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (76365224177389064896528067742453127588580154925588821225322203997304966792977828691701944045179452793723380994224599452984144575980840960 : Int) coeff1429) := by
  rw [CoefficientMerge.eval_scale, ← atom1429_identity]
  exact mul_nonneg (by norm_num) (atom1429_nonneg g t z hg hA hB ht hz hw)

def coeff1430 : CoefficientMerge.Poly :=
  [(802833, 1)]
noncomputable def atom1430 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 7) ^ 1 * (t) ^ 3)
theorem atom1430_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1430 g t z = CoefficientMerge.eval (monomial g t z) coeff1430 := by
  norm_num [atom1430, coeff1430, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1430_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1430 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1430]
  positivity
theorem weighted1430_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (37746473315828563069236958826037363257010180247672034611894688400304631932361837280744540515942358335354373144929234701657926489026227200 : Int) coeff1430) := by
  rw [CoefficientMerge.eval_scale, ← atom1430_identity]
  exact mul_nonneg (by norm_num) (atom1430_nonneg g t z hg hA hB ht hz hw)

def coeff1431 : CoefficientMerge.Poly :=
  [(1589265, 1)]
noncomputable def atom1431 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 7) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1431_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1431 g t z = CoefficientMerge.eval (monomial g t z) coeff1431 := by
  norm_num [atom1431, coeff1431, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1431_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1431 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1431]
  positivity
theorem weighted1431_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (85086637904454784326314709309519805917490514983862527578568188314645650978712836147494812460574673274024354341176112010279885591083904000 : Int) coeff1431) := by
  rw [CoefficientMerge.eval_scale, ← atom1431_identity]
  exact mul_nonneg (by norm_num) (atom1431_nonneg g t z hg hA hB ht hz hw)

def coeff1432 : CoefficientMerge.Poly :=
  [(2375697, 1)]
noncomputable def atom1432 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1432_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1432 g t z = CoefficientMerge.eval (monomial g t z) coeff1432 := by
  norm_num [atom1432, coeff1432, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1432_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1432 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1432]
  positivity
theorem weighted1432_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (67079266588115411857185409476743319617205442046273915544929928481944979903691269553782852360041167084251370573381764061969397815557708800 : Int) coeff1432) := by
  rw [CoefficientMerge.eval_scale, ← atom1432_identity]
  exact mul_nonneg (by norm_num) (atom1432_nonneg g t z hg hA hB ht hz hw)

def coeff1433 : CoefficientMerge.Poly :=
  [(851985, 1)]
noncomputable def atom1433 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 8) ^ 1 * (t) ^ 3)
theorem atom1433_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1433 g t z = CoefficientMerge.eval (monomial g t z) coeff1433 := by
  norm_num [atom1433, coeff1433, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1433_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1433 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1433]
  positivity
theorem weighted1433_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (13996673404699978370144399183715330810189132044693945440779762166005862424062334609780021688513423622756807876149472162921667641438126080 : Int) coeff1433) := by
  rw [CoefficientMerge.eval_scale, ← atom1433_identity]
  exact mul_nonneg (by norm_num) (atom1433_nonneg g t z hg hA hB ht hz hw)

def coeff1434 : CoefficientMerge.Poly :=
  [(1638417, 1)]
noncomputable def atom1434 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 8) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1434_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1434 g t z = CoefficientMerge.eval (monomial g t z) coeff1434 := by
  norm_num [atom1434, coeff1434, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1434_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1434 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1434]
  positivity
theorem weighted1434_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5058548719336543068089062662446585679816397404222641139099214800941591649323050165327375669904687467247460146335379558081093519761689600 : Int) coeff1434) := by
  rw [CoefficientMerge.eval_scale, ← atom1434_identity]
  exact mul_nonneg (by norm_num) (atom1434_nonneg g t z hg hA hB ht hz hw)

def coeff1435 : CoefficientMerge.Poly :=
  [(786561, 1)]
noncomputable def atom1435 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 2 * (t) ^ 3)
theorem atom1435_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1435 g t z = CoefficientMerge.eval (monomial g t z) coeff1435 := by
  norm_num [atom1435, coeff1435, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1435_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1435 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1435]
  positivity
theorem weighted1435_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (16522534395991928683638819686306146845137579806886025284122689124905874522695054747572452611177606416015832394962414322100302147027553280 : Int) coeff1435) := by
  rw [CoefficientMerge.eval_scale, ← atom1435_identity]
  exact mul_nonneg (by norm_num) (atom1435_nonneg g t z hg hA hB ht hz hw)

def coeff1436 : CoefficientMerge.Poly :=
  [(1572993, 1)]
noncomputable def atom1436 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 2 * (t) ^ 2 * (z) ^ 1)
theorem atom1436_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1436 g t z = CoefficientMerge.eval (monomial g t z) coeff1436 := by
  norm_num [atom1436, coeff1436, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1436_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1436 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1436]
  positivity
theorem weighted1436_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (47178515189804437564706189832789431399055005428851963328696523858513214453878282980287594610393688774007159460221815447416666730468403840 : Int) coeff1436) := by
  rw [CoefficientMerge.eval_scale, ← atom1436_identity]
  exact mul_nonneg (by norm_num) (atom1436_nonneg g t z hg hA hB ht hz hw)

def coeff1437 : CoefficientMerge.Poly :=
  [(2359425, 1)]
noncomputable def atom1437 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 2 * (t) ^ 1 * (z) ^ 2)
theorem atom1437_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1437 g t z = CoefficientMerge.eval (monomial g t z) coeff1437 := by
  norm_num [atom1437, coeff1437, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1437_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1437 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1437]
  positivity
theorem weighted1437_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (44789427191633089078495920606660422262697271437045850805024980342308805339671401717857831387254558299966821735556387928532427019854147840 : Int) coeff1437) := by
  rw [CoefficientMerge.eval_scale, ← atom1437_identity]
  exact mul_nonneg (by norm_num) (atom1437_nonneg g t z hg hA hB ht hz hw)

def coeff1438 : CoefficientMerge.Poly :=
  [(786753, 1)]
noncomputable def atom1438 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 4) ^ 1 * (t) ^ 3)
theorem atom1438_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1438 g t z = CoefficientMerge.eval (monomial g t z) coeff1438 := by
  norm_num [atom1438, coeff1438, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1438_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1438 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1438]
  positivity
theorem weighted1438_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (20803402870130673881035362163759657424020142193376410750151988591952116980923828048787145359894593033944389605981148470276743064473045760 : Int) coeff1438) := by
  rw [CoefficientMerge.eval_scale, ← atom1438_identity]
  exact mul_nonneg (by norm_num) (atom1438_nonneg g t z hg hA hB ht hz hw)

def coeff1439 : CoefficientMerge.Poly :=
  [(1573185, 1)]
noncomputable def atom1439 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 4) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1439_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1439 g t z = CoefficientMerge.eval (monomial g t z) coeff1439 := by
  norm_num [atom1439, coeff1439, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1439_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1439 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1439]
  positivity
theorem weighted1439_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (61910351236503306048388535363552536031291142589628755498698668589962565656206522474044285239939223500752451278848331156362471151989056688 : Int) coeff1439) := by
  rw [CoefficientMerge.eval_scale, ← atom1439_identity]
  exact mul_nonneg (by norm_num) (atom1439_nonneg g t z hg hA hB ht hz hw)

def coeff1440 : CoefficientMerge.Poly :=
  [(2359617, 1)]
noncomputable def atom1440 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 4) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1440_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1440 g t z = CoefficientMerge.eval (monomial g t z) coeff1440 := by
  norm_num [atom1440, coeff1440, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1440_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1440 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1440]
  positivity
theorem weighted1440_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (61410493862614590453670984235826099790521858599128278746941371404068780369641560801727134400194667899671733739753216901894713110558976096 : Int) coeff1440) := by
  rw [CoefficientMerge.eval_scale, ← atom1440_identity]
  exact mul_nonneg (by norm_num) (atom1440_nonneg g t z hg hA hB ht hz hw)

def coeff1441 : CoefficientMerge.Poly :=
  [(787521, 1)]
noncomputable def atom1441 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 5) ^ 1 * (t) ^ 3)
theorem atom1441_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1441 g t z = CoefficientMerge.eval (monomial g t z) coeff1441 := by
  norm_num [atom1441, coeff1441, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1441_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1441 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1441]
  positivity
theorem weighted1441_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (11584374823530138005597724769011681720920821035939961639410735174076948074151914289476224284315721519522949433302956612101003640526927360 : Int) coeff1441) := by
  rw [CoefficientMerge.eval_scale, ← atom1441_identity]
  exact mul_nonneg (by norm_num) (atom1441_nonneg g t z hg hA hB ht hz hw)

def coeff1442 : CoefficientMerge.Poly :=
  [(1573953, 1)]
noncomputable def atom1442 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 5) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1442_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1442 g t z = CoefficientMerge.eval (monomial g t z) coeff1442 := by
  norm_num [atom1442, coeff1442, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1442_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1442 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1442]
  positivity
theorem weighted1442_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (23752914508644424483597976054746047572342165690808824218658547712242496634077814461887159259092851519231659230780974397811036243016510976 : Int) coeff1442) := by
  rw [CoefficientMerge.eval_scale, ← atom1442_identity]
  exact mul_nonneg (by norm_num) (atom1442_nonneg g t z hg hA hB ht hz hw)

def coeff1443 : CoefficientMerge.Poly :=
  [(2360385, 1)]
noncomputable def atom1443 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 5) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1443_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1443 g t z = CoefficientMerge.eval (monomial g t z) coeff1443 := by
  norm_num [atom1443, coeff1443, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1443_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1443 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1443]
  positivity
theorem weighted1443_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (12752704546698434950402777802457049981921868273797763519084889902254149045699886055345645665238538479894470161653078959319061564452239872 : Int) coeff1443) := by
  rw [CoefficientMerge.eval_scale, ← atom1443_identity]
  exact mul_nonneg (by norm_num) (atom1443_nonneg g t z hg hA hB ht hz hw)

def coeff1444 : CoefficientMerge.Poly :=
  [(790593, 1)]
noncomputable def atom1444 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 6) ^ 1 * (t) ^ 3)
theorem atom1444_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1444 g t z = CoefficientMerge.eval (monomial g t z) coeff1444 := by
  norm_num [atom1444, coeff1444, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1444_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1444 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1444]
  positivity
theorem weighted1444_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (7186167903406763489364434164488169576170002700624832136216546311953132020133514407155383453586380468699811469073060425202536213282209280 : Int) coeff1444) := by
  rw [CoefficientMerge.eval_scale, ← atom1444_identity]
  exact mul_nonneg (by norm_num) (atom1444_nonneg g t z hg hA hB ht hz hw)

def sparseBlock103 : CoefficientMerge.Poly :=
  [(786561, 16522534395991928683638819686306146845137579806886025284122689124905874522695054747572452611177606416015832394962414322100302147027553280), (786753, 20803402870130673881035362163759657424020142193376410750151988591952116980923828048787145359894593033944389605981148470276743064473045760), (787521, 11584374823530138005597724769011681720920821035939961639410735174076948074151914289476224284315721519522949433302956612101003640526927360), (790545, 42065941333891898521329146756685916520652419984039804525905236806751251541645613496044802304065364689000344787457687647684027428480097280), (790593, 7186167903406763489364434164488169576170002700624832136216546311953132020133514407155383453586380468699811469073060425202536213282209280), (802833, 37746473315828563069236958826037363257010180247672034611894688400304631932361837280744540515942358335354373144929234701657926489026227200), (851985, 13996673404699978370144399183715330810189132044693945440779762166005862424062334609780021688513423622756807876149472162921667641438126080), (1572993, 47178515189804437564706189832789431399055005428851963328696523858513214453878282980287594610393688774007159460221815447416666730468403840), (1573185, 61910351236503306048388535363552536031291142589628755498698668589962565656206522474044285239939223500752451278848331156362471151989056688), (1573905, 141294762036727360906391295241356601691313677522670623928928878813727585707899292075590581210846067320993513488824639798646368746991983104), (1573953, 23752914508644424483597976054746047572342165690808824218658547712242496634077814461887159259092851519231659230780974397811036243016510976), (1576977, 119176422847400031379907274091198318779344230672900453444685138026794285033836798584922867409194943685946783596488134284586026112582568960), (1589265, 85086637904454784326314709309519805917490514983862527578568188314645650978712836147494812460574673274024354341176112010279885591083904000), (1638417, 5058548719336543068089062662446585679816397404222641139099214800941591649323050165327375669904687467247460146335379558081093519761689600), (2359425, 44789427191633089078495920606660422262697271437045850805024980342308805339671401717857831387254558299966821735556387928532427019854147840), (2359617, 61410493862614590453670984235826099790521858599128278746941371404068780369641560801727134400194667899671733739753216901894713110558976096), (2360337, 102940359927398165361223315348560827630968400250807031935126672769827461343581711754692917503262019556920222063292919571001881136917522208), (2360385, 12752704546698434950402777802457049981921868273797763519084889902254149045699886055345645665238538479894470161653078959319061564452239872), (2363409, 76365224177389064896528067742453127588580154925588821225322203997304966792977828691701944045179452793723380994224599452984144575980840960), (2375697, 67079266588115411857185409476743319617205442046273915544929928481944979903691269553782852360041167084251370573381764061969397815557708800)]
theorem sparseBlock103_data : sparseBlock103 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (141294762036727360906391295241356601691313677522670623928928878813727585707899292075590581210846067320993513488824639798646368746991983104 : Int) coeff1425) (CoefficientMerge.scale (102940359927398165361223315348560827630968400250807031935126672769827461343581711754692917503262019556920222063292919571001881136917522208 : Int) coeff1426)) (CoefficientMerge.merge (CoefficientMerge.scale (42065941333891898521329146756685916520652419984039804525905236806751251541645613496044802304065364689000344787457687647684027428480097280 : Int) coeff1427) (CoefficientMerge.merge (CoefficientMerge.scale (119176422847400031379907274091198318779344230672900453444685138026794285033836798584922867409194943685946783596488134284586026112582568960 : Int) coeff1428) (CoefficientMerge.scale (76365224177389064896528067742453127588580154925588821225322203997304966792977828691701944045179452793723380994224599452984144575980840960 : Int) coeff1429)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (37746473315828563069236958826037363257010180247672034611894688400304631932361837280744540515942358335354373144929234701657926489026227200 : Int) coeff1430) (CoefficientMerge.scale (85086637904454784326314709309519805917490514983862527578568188314645650978712836147494812460574673274024354341176112010279885591083904000 : Int) coeff1431)) (CoefficientMerge.merge (CoefficientMerge.scale (67079266588115411857185409476743319617205442046273915544929928481944979903691269553782852360041167084251370573381764061969397815557708800 : Int) coeff1432) (CoefficientMerge.merge (CoefficientMerge.scale (13996673404699978370144399183715330810189132044693945440779762166005862424062334609780021688513423622756807876149472162921667641438126080 : Int) coeff1433) (CoefficientMerge.scale (5058548719336543068089062662446585679816397404222641139099214800941591649323050165327375669904687467247460146335379558081093519761689600 : Int) coeff1434))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (16522534395991928683638819686306146845137579806886025284122689124905874522695054747572452611177606416015832394962414322100302147027553280 : Int) coeff1435) (CoefficientMerge.scale (47178515189804437564706189832789431399055005428851963328696523858513214453878282980287594610393688774007159460221815447416666730468403840 : Int) coeff1436)) (CoefficientMerge.merge (CoefficientMerge.scale (44789427191633089078495920606660422262697271437045850805024980342308805339671401717857831387254558299966821735556387928532427019854147840 : Int) coeff1437) (CoefficientMerge.merge (CoefficientMerge.scale (20803402870130673881035362163759657424020142193376410750151988591952116980923828048787145359894593033944389605981148470276743064473045760 : Int) coeff1438) (CoefficientMerge.scale (61910351236503306048388535363552536031291142589628755498698668589962565656206522474044285239939223500752451278848331156362471151989056688 : Int) coeff1439)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (61410493862614590453670984235826099790521858599128278746941371404068780369641560801727134400194667899671733739753216901894713110558976096 : Int) coeff1440) (CoefficientMerge.scale (11584374823530138005597724769011681720920821035939961639410735174076948074151914289476224284315721519522949433302956612101003640526927360 : Int) coeff1441)) (CoefficientMerge.merge (CoefficientMerge.scale (23752914508644424483597976054746047572342165690808824218658547712242496634077814461887159259092851519231659230780974397811036243016510976 : Int) coeff1442) (CoefficientMerge.merge (CoefficientMerge.scale (12752704546698434950402777802457049981921868273797763519084889902254149045699886055345645665238538479894470161653078959319061564452239872 : Int) coeff1443) (CoefficientMerge.scale (7186167903406763489364434164488169576170002700624832136216546311953132020133514407155383453586380468699811469073060425202536213282209280 : Int) coeff1444)))))) := by decide +kernel
theorem sparseBlock103_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock103 := by
  rw [sparseBlock103_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted1425_nonneg g t z hg hA hB ht hz hw) (weighted1426_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1427_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1428_nonneg g t z hg hA hB ht hz hw) (weighted1429_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1430_nonneg g t z hg hA hB ht hz hw) (weighted1431_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1432_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1433_nonneg g t z hg hA hB ht hz hw) (weighted1434_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted1435_nonneg g t z hg hA hB ht hz hw) (weighted1436_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1437_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1438_nonneg g t z hg hA hB ht hz hw) (weighted1439_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1440_nonneg g t z hg hA hB ht hz hw) (weighted1441_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1442_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1443_nonneg g t z hg hA hB ht hz hw) (weighted1444_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
