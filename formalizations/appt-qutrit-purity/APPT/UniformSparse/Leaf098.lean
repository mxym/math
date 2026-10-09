import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff1325 : CoefficientMerge.Poly :=
  [(3216384, 1)]
noncomputable def atom1325 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (z) ^ 3)
theorem atom1325_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1325 g t z = CoefficientMerge.eval (monomial g t z) coeff1325 := by
  norm_num [atom1325, coeff1325, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1325_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1325 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1325]
  positivity
theorem weighted1325_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (157345636881404191182609681782767150557791393892099552721887712715525539970441541270631548933976552016258385854306765634450841495727752830 : Int) coeff1325) := by
  rw [CoefficientMerge.eval_scale, ← atom1325_identity]
  exact mul_nonneg (by norm_num) (atom1325_nonneg g t z hg hA hB ht hz hw)

def coeff1326 : CoefficientMerge.Poly :=
  [(3179520, 1)]
noncomputable def atom1326 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 7) ^ 2 * (z) ^ 3)
theorem atom1326_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1326 g t z = CoefficientMerge.eval (monomial g t z) coeff1326 := by
  norm_num [atom1326, coeff1326, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1326_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1326 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1326]
  positivity
theorem weighted1326_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (73131831421466949673972011890689820574452326289011715476852196047526299237456266431563479790920950476666042824426950924488400959902354880 : Int) coeff1326) := by
  rw [CoefficientMerge.eval_scale, ← atom1326_identity]
  exact mul_nonneg (by norm_num) (atom1326_nonneg g t z hg hA hB ht hz hw)

def coeff1327 : CoefficientMerge.Poly :=
  [(3228672, 1)]
noncomputable def atom1327 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (z) ^ 3)
theorem atom1327_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1327 g t z = CoefficientMerge.eval (monomial g t z) coeff1327 := by
  norm_num [atom1327, coeff1327, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1327_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1327 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1327]
  positivity
theorem weighted1327_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (123741930815119910328445052877377052932504785569981796407861122155702366353897995372368222358520093385217313590463987767061289089334079670 : Int) coeff1327) := by
  rw [CoefficientMerge.eval_scale, ← atom1327_identity]
  exact mul_nonneg (by norm_num) (atom1327_nonneg g t z hg hA hB ht hz hw)

def coeff1328 : CoefficientMerge.Poly :=
  [(3277824, 1)]
noncomputable def atom1328 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 8) ^ 2 * (z) ^ 3)
theorem atom1328_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1328 g t z = CoefficientMerge.eval (monomial g t z) coeff1328 := by
  norm_num [atom1328, coeff1328, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1328_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1328 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1328]
  positivity
theorem weighted1328_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (40419006459691471621731541856365499047982931106385217929678747057842639305056857707914460097702398916397376454168455745642442661440067630 : Int) coeff1328) := by
  rw [CoefficientMerge.eval_scale, ← atom1328_identity]
  exact mul_nonneg (by norm_num) (atom1328_nonneg g t z hg hA hB ht hz hw)

def coeff1329 : CoefficientMerge.Poly :=
  [(3158016, 1)]
noncomputable def atom1329 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 3 * (z) ^ 3)
theorem atom1329_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1329 g t z = CoefficientMerge.eval (monomial g t z) coeff1329 := by
  norm_num [atom1329, coeff1329, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1329_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1329 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1329]
  positivity
theorem weighted1329_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (34114685266307136918574473581269187208482082909120708349418317391409321464539727080864079841182600285490382358102061204655535036126044800 : Int) coeff1329) := by
  rw [CoefficientMerge.eval_scale, ← atom1329_identity]
  exact mul_nonneg (by norm_num) (atom1329_nonneg g t z hg hA hB ht hz hw)

def coeff1330 : CoefficientMerge.Poly :=
  [(3170304, 1)]
noncomputable def atom1330 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 2 * (g 7) ^ 1 * (z) ^ 3)
theorem atom1330_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1330 g t z = CoefficientMerge.eval (monomial g t z) coeff1330 := by
  norm_num [atom1330, coeff1330, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1330_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1330 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1330]
  positivity
theorem weighted1330_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (83306341994613201049752248378422055333137094524084302917744078489510446872999385017634486540700690879362332050585104851540477628636365200 : Int) coeff1330) := by
  rw [CoefficientMerge.eval_scale, ← atom1330_identity]
  exact mul_nonneg (by norm_num) (atom1330_nonneg g t z hg hA hB ht hz hw)

def coeff1331 : CoefficientMerge.Poly :=
  [(3219456, 1)]
noncomputable def atom1331 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 2 * (g 8) ^ 1 * (z) ^ 3)
theorem atom1331_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1331 g t z = CoefficientMerge.eval (monomial g t z) coeff1331 := by
  norm_num [atom1331, coeff1331, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1331_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1331 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1331]
  positivity
theorem weighted1331_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (67297298723885277528296532645299540455008360355398477845290221007525268027991829510933633598218193630946936100766962761367857545423486400 : Int) coeff1331) := by
  rw [CoefficientMerge.eval_scale, ← atom1331_identity]
  exact mul_nonneg (by norm_num) (atom1331_nonneg g t z hg hA hB ht hz hw)

def coeff1332 : CoefficientMerge.Poly :=
  [(3182592, 1)]
noncomputable def atom1332 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 1 * (g 7) ^ 2 * (z) ^ 3)
theorem atom1332_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1332 g t z = CoefficientMerge.eval (monomial g t z) coeff1332 := by
  norm_num [atom1332, coeff1332, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1332_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1332 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1332]
  positivity
theorem weighted1332_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (64383525975283041534785190202408656698590487424986660452452710509131230250823213710309151625055008626115263435412117295024274506159014320 : Int) coeff1332) := by
  rw [CoefficientMerge.eval_scale, ← atom1332_identity]
  exact mul_nonneg (by norm_num) (atom1332_nonneg g t z hg hA hB ht hz hw)

def coeff1333 : CoefficientMerge.Poly :=
  [(3231744, 1)]
noncomputable def atom1333 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (z) ^ 3)
theorem atom1333_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1333 g t z = CoefficientMerge.eval (monomial g t z) coeff1333 := by
  norm_num [atom1333, coeff1333, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1333_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1333 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1333]
  positivity
theorem weighted1333_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (91114384966115261507784187028854184470672102735989139647766476464785971060685486599861467934315099784234140959460461750426248544300201040 : Int) coeff1333) := by
  rw [CoefficientMerge.eval_scale, ← atom1333_identity]
  exact mul_nonneg (by norm_num) (atom1333_nonneg g t z hg hA hB ht hz hw)

def coeff1334 : CoefficientMerge.Poly :=
  [(3280896, 1)]
noncomputable def atom1334 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 1 * (g 8) ^ 2 * (z) ^ 3)
theorem atom1334_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1334 g t z = CoefficientMerge.eval (monomial g t z) coeff1334 := by
  norm_num [atom1334, coeff1334, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1334_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1334 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1334]
  positivity
theorem weighted1334_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (23873108718009953167456060400113692396996855242190063800386086940178721999724386869088544715120861213844781346057074833706040210155540800 : Int) coeff1334) := by
  rw [CoefficientMerge.eval_scale, ← atom1334_identity]
  exact mul_nonneg (by norm_num) (atom1334_nonneg g t z hg hA hB ht hz hw)

def coeff1335 : CoefficientMerge.Poly :=
  [(3194880, 1)]
noncomputable def atom1335 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 7) ^ 3 * (z) ^ 3)
theorem atom1335_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1335 g t z = CoefficientMerge.eval (monomial g t z) coeff1335 := by
  norm_num [atom1335, coeff1335, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1335_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1335 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1335]
  positivity
theorem weighted1335_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (12155756069188520465347098617028242647202160678168190655713639130498537592140248429405647785865472996907463979537039472897394396778156160 : Int) coeff1335) := by
  rw [CoefficientMerge.eval_scale, ← atom1335_identity]
  exact mul_nonneg (by norm_num) (atom1335_nonneg g t z hg hA hB ht hz hw)

def coeff1336 : CoefficientMerge.Poly :=
  [(3244032, 1)]
noncomputable def atom1336 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 7) ^ 2 * (g 8) ^ 1 * (z) ^ 3)
theorem atom1336_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1336 g t z = CoefficientMerge.eval (monomial g t z) coeff1336 := by
  norm_num [atom1336, coeff1336, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1336_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1336 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1336]
  positivity
theorem weighted1336_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (9157118757345337967655468943888664977563304436061245041886516866139402273718258586514631882886090687257968687252461684810755495641085840 : Int) coeff1336) := by
  rw [CoefficientMerge.eval_scale, ← atom1336_identity]
  exact mul_nonneg (by norm_num) (atom1336_nonneg g t z hg hA hB ht hz hw)

def coeff1337 : CoefficientMerge.Poly :=
  [(1310978, 1)]
noncomputable def atom1337 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 2 * (g 4) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom1337_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1337 g t z = CoefficientMerge.eval (monomial g t z) coeff1337 := by
  norm_num [atom1337, coeff1337, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1337_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1337 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1337]
  positivity
theorem weighted1337_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (8775550419580163969171677749924679418796795499230782512672886411236067251056027720240150054706177549798291930729558207288210006961356800 : Int) coeff1337) := by
  rw [CoefficientMerge.eval_scale, ← atom1337_identity]
  exact mul_nonneg (by norm_num) (atom1337_nonneg g t z hg hA hB ht hz hw)

def coeff1338 : CoefficientMerge.Poly :=
  [(1311746, 1)]
noncomputable def atom1338 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 2 * (g 5) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom1338_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1338 g t z = CoefficientMerge.eval (monomial g t z) coeff1338 := by
  norm_num [atom1338, coeff1338, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1338_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1338 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1338]
  positivity
theorem weighted1338_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2107448016733986221505610917385736321116924827736587858466471710736670709791139144212970156501922809857609519497068160474959103911198720 : Int) coeff1338) := by
  rw [CoefficientMerge.eval_scale, ← atom1338_identity]
  exact mul_nonneg (by norm_num) (atom1338_nonneg g t z hg hA hB ht hz hw)

def coeff1339 : CoefficientMerge.Poly :=
  [(1314818, 1)]
noncomputable def atom1339 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 2 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom1339_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1339 g t z = CoefficientMerge.eval (monomial g t z) coeff1339 := by
  norm_num [atom1339, coeff1339, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1339_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1339 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1339]
  positivity
theorem weighted1339_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (8584846651559004551404132509367423400676764505864254505548158975344323205171145984566683281108344844435789158409324454320144392491827200 : Int) coeff1339) := by
  rw [CoefficientMerge.eval_scale, ← atom1339_identity]
  exact mul_nonneg (by norm_num) (atom1339_nonneg g t z hg hA hB ht hz hw)

def coeff1340 : CoefficientMerge.Poly :=
  [(524357, 1)]
noncomputable def atom1340 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 1) ^ 1 * (g 3) ^ 1 * (t) ^ 2)
theorem atom1340_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1340 g t z = CoefficientMerge.eval (monomial g t z) coeff1340 := by
  norm_num [atom1340, coeff1340, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1340_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1340 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1340]
  positivity
theorem weighted1340_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (245213073805647696664908950426239000812332552982462069294622464593393498067562562022105451973777399306921112908122441965980282045789675520 : Int) coeff1340) := by
  rw [CoefficientMerge.eval_scale, ← atom1340_identity]
  exact mul_nonneg (by norm_num) (atom1340_nonneg g t z hg hA hB ht hz hw)

def coeff1341 : CoefficientMerge.Poly :=
  [(1310789, 1)]
noncomputable def atom1341 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 1) ^ 1 * (g 3) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom1341_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1341 g t z = CoefficientMerge.eval (monomial g t z) coeff1341 := by
  norm_num [atom1341, coeff1341, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1341_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1341 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1341]
  positivity
theorem weighted1341_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (475860775779406291999962957106854864306710305321700262068695713243025166244061418422725330773437128754809219377646648682986453032471900160 : Int) coeff1341) := by
  rw [CoefficientMerge.eval_scale, ← atom1341_identity]
  exact mul_nonneg (by norm_num) (atom1341_nonneg g t z hg hA hB ht hz hw)

def coeff1342 : CoefficientMerge.Poly :=
  [(1314821, 1)]
noncomputable def atom1342 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 1) ^ 1 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom1342_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1342 g t z = CoefficientMerge.eval (monomial g t z) coeff1342 := by
  norm_num [atom1342, coeff1342, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1342_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1342 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1342]
  positivity
theorem weighted1342_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (8850607903391263581115448882628581011520767847140359115965620881154935254813248281223906630424137344340803535617684835730986761502300160 : Int) coeff1342) := by
  rw [CoefficientMerge.eval_scale, ← atom1342_identity]
  exact mul_nonneg (by norm_num) (atom1342_nonneg g t z hg hA hB ht hz hw)

def coeff1343 : CoefficientMerge.Poly :=
  [(525320, 1)]
noncomputable def atom1343 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 2 * (g 5) ^ 1 * (t) ^ 2)
theorem atom1343_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1343 g t z = CoefficientMerge.eval (monomial g t z) coeff1343 := by
  norm_num [atom1343, coeff1343, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1343_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1343 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1343]
  positivity
theorem weighted1343_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (20585585917712145569157374664837736537396325309722773763252332131679928878465711843551120044647341422807129160150399853709271061429043200 : Int) coeff1343) := by
  rw [CoefficientMerge.eval_scale, ← atom1343_identity]
  exact mul_nonneg (by norm_num) (atom1343_nonneg g t z hg hA hB ht hz hw)

def coeff1344 : CoefficientMerge.Poly :=
  [(1310792, 1)]
noncomputable def atom1344 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 2 * (g 3) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom1344_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1344 g t z = CoefficientMerge.eval (monomial g t z) coeff1344 := by
  norm_num [atom1344, coeff1344, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1344_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1344 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1344]
  positivity
theorem weighted1344_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (23592171553568263335558685907023067801578152324648614707585757865854590048700955656313866919480972838157947920932388972403292299699814400 : Int) coeff1344) := by
  rw [CoefficientMerge.eval_scale, ← atom1344_identity]
  exact mul_nonneg (by norm_num) (atom1344_nonneg g t z hg hA hB ht hz hw)

def sparseBlock098 : CoefficientMerge.Poly :=
  [(524357, 245213073805647696664908950426239000812332552982462069294622464593393498067562562022105451973777399306921112908122441965980282045789675520), (525320, 20585585917712145569157374664837736537396325309722773763252332131679928878465711843551120044647341422807129160150399853709271061429043200), (1310789, 475860775779406291999962957106854864306710305321700262068695713243025166244061418422725330773437128754809219377646648682986453032471900160), (1310792, 23592171553568263335558685907023067801578152324648614707585757865854590048700955656313866919480972838157947920932388972403292299699814400), (1310978, 8775550419580163969171677749924679418796795499230782512672886411236067251056027720240150054706177549798291930729558207288210006961356800), (1311746, 2107448016733986221505610917385736321116924827736587858466471710736670709791139144212970156501922809857609519497068160474959103911198720), (1314818, 8584846651559004551404132509367423400676764505864254505548158975344323205171145984566683281108344844435789158409324454320144392491827200), (1314821, 8850607903391263581115448882628581011520767847140359115965620881154935254813248281223906630424137344340803535617684835730986761502300160), (3158016, 34114685266307136918574473581269187208482082909120708349418317391409321464539727080864079841182600285490382358102061204655535036126044800), (3170304, 83306341994613201049752248378422055333137094524084302917744078489510446872999385017634486540700690879362332050585104851540477628636365200), (3179520, 73131831421466949673972011890689820574452326289011715476852196047526299237456266431563479790920950476666042824426950924488400959902354880), (3182592, 64383525975283041534785190202408656698590487424986660452452710509131230250823213710309151625055008626115263435412117295024274506159014320), (3194880, 12155756069188520465347098617028242647202160678168190655713639130498537592140248429405647785865472996907463979537039472897394396778156160), (3216384, 157345636881404191182609681782767150557791393892099552721887712715525539970441541270631548933976552016258385854306765634450841495727752830), (3219456, 67297298723885277528296532645299540455008360355398477845290221007525268027991829510933633598218193630946936100766962761367857545423486400), (3228672, 123741930815119910328445052877377052932504785569981796407861122155702366353897995372368222358520093385217313590463987767061289089334079670), (3231744, 91114384966115261507784187028854184470672102735989139647766476464785971060685486599861467934315099784234140959460461750426248544300201040), (3244032, 9157118757345337967655468943888664977563304436061245041886516866139402273718258586514631882886090687257968687252461684810755495641085840), (3277824, 40419006459691471621731541856365499047982931106385217929678747057842639305056857707914460097702398916397376454168455745642442661440067630), (3280896, 23873108718009953167456060400113692396996855242190063800386086940178721999724386869088544715120861213844781346057074833706040210155540800)]
theorem sparseBlock098_data : sparseBlock098 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (157345636881404191182609681782767150557791393892099552721887712715525539970441541270631548933976552016258385854306765634450841495727752830 : Int) coeff1325) (CoefficientMerge.scale (73131831421466949673972011890689820574452326289011715476852196047526299237456266431563479790920950476666042824426950924488400959902354880 : Int) coeff1326)) (CoefficientMerge.merge (CoefficientMerge.scale (123741930815119910328445052877377052932504785569981796407861122155702366353897995372368222358520093385217313590463987767061289089334079670 : Int) coeff1327) (CoefficientMerge.merge (CoefficientMerge.scale (40419006459691471621731541856365499047982931106385217929678747057842639305056857707914460097702398916397376454168455745642442661440067630 : Int) coeff1328) (CoefficientMerge.scale (34114685266307136918574473581269187208482082909120708349418317391409321464539727080864079841182600285490382358102061204655535036126044800 : Int) coeff1329)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (83306341994613201049752248378422055333137094524084302917744078489510446872999385017634486540700690879362332050585104851540477628636365200 : Int) coeff1330) (CoefficientMerge.scale (67297298723885277528296532645299540455008360355398477845290221007525268027991829510933633598218193630946936100766962761367857545423486400 : Int) coeff1331)) (CoefficientMerge.merge (CoefficientMerge.scale (64383525975283041534785190202408656698590487424986660452452710509131230250823213710309151625055008626115263435412117295024274506159014320 : Int) coeff1332) (CoefficientMerge.merge (CoefficientMerge.scale (91114384966115261507784187028854184470672102735989139647766476464785971060685486599861467934315099784234140959460461750426248544300201040 : Int) coeff1333) (CoefficientMerge.scale (23873108718009953167456060400113692396996855242190063800386086940178721999724386869088544715120861213844781346057074833706040210155540800 : Int) coeff1334))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (12155756069188520465347098617028242647202160678168190655713639130498537592140248429405647785865472996907463979537039472897394396778156160 : Int) coeff1335) (CoefficientMerge.scale (9157118757345337967655468943888664977563304436061245041886516866139402273718258586514631882886090687257968687252461684810755495641085840 : Int) coeff1336)) (CoefficientMerge.merge (CoefficientMerge.scale (8775550419580163969171677749924679418796795499230782512672886411236067251056027720240150054706177549798291930729558207288210006961356800 : Int) coeff1337) (CoefficientMerge.merge (CoefficientMerge.scale (2107448016733986221505610917385736321116924827736587858466471710736670709791139144212970156501922809857609519497068160474959103911198720 : Int) coeff1338) (CoefficientMerge.scale (8584846651559004551404132509367423400676764505864254505548158975344323205171145984566683281108344844435789158409324454320144392491827200 : Int) coeff1339)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (245213073805647696664908950426239000812332552982462069294622464593393498067562562022105451973777399306921112908122441965980282045789675520 : Int) coeff1340) (CoefficientMerge.scale (475860775779406291999962957106854864306710305321700262068695713243025166244061418422725330773437128754809219377646648682986453032471900160 : Int) coeff1341)) (CoefficientMerge.merge (CoefficientMerge.scale (8850607903391263581115448882628581011520767847140359115965620881154935254813248281223906630424137344340803535617684835730986761502300160 : Int) coeff1342) (CoefficientMerge.merge (CoefficientMerge.scale (20585585917712145569157374664837736537396325309722773763252332131679928878465711843551120044647341422807129160150399853709271061429043200 : Int) coeff1343) (CoefficientMerge.scale (23592171553568263335558685907023067801578152324648614707585757865854590048700955656313866919480972838157947920932388972403292299699814400 : Int) coeff1344)))))) := by decide +kernel
theorem sparseBlock098_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock098 := by
  rw [sparseBlock098_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted1325_nonneg g t z hg hA hB ht hz hw) (weighted1326_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1327_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1328_nonneg g t z hg hA hB ht hz hw) (weighted1329_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1330_nonneg g t z hg hA hB ht hz hw) (weighted1331_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1332_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1333_nonneg g t z hg hA hB ht hz hw) (weighted1334_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted1335_nonneg g t z hg hA hB ht hz hw) (weighted1336_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1337_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1338_nonneg g t z hg hA hB ht hz hw) (weighted1339_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1340_nonneg g t z hg hA hB ht hz hw) (weighted1341_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1342_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1343_nonneg g t z hg hA hB ht hz hw) (weighted1344_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
