import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff1265 : CoefficientMerge.Poly :=
  [(1585152, 1)]
noncomputable def atom1265 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 3 * (t) ^ 2 * (z) ^ 1)
theorem atom1265_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1265 g t z = CoefficientMerge.eval (monomial g t z) coeff1265 := by
  norm_num [atom1265, coeff1265, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1265_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1265 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1265]
  positivity
theorem weighted1265_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (107908982259419304395538728424803126839280427711473018531798350338486223984325542800136834521871455959241403924714413697484251413297753600 : Int) coeff1265) := by
  rw [CoefficientMerge.eval_scale, ← atom1265_identity]
  exact mul_nonneg (by norm_num) (atom1265_nonneg g t z hg hA hB ht hz hw)

def coeff1266 : CoefficientMerge.Poly :=
  [(1597440, 1)]
noncomputable def atom1266 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 2 * (g 7) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1266_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1266 g t z = CoefficientMerge.eval (monomial g t z) coeff1266 := by
  norm_num [atom1266, coeff1266, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1266_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1266 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1266]
  positivity
theorem weighted1266_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (278637429280653223103954752177918026384080849822067364606681676839963129233525840580091019556358150992163212661235776923558167734786188800 : Int) coeff1266) := by
  rw [CoefficientMerge.eval_scale, ← atom1266_identity]
  exact mul_nonneg (by norm_num) (atom1266_nonneg g t z hg hA hB ht hz hw)

def coeff1267 : CoefficientMerge.Poly :=
  [(1646592, 1)]
noncomputable def atom1267 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 2 * (g 8) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1267_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1267 g t z = CoefficientMerge.eval (monomial g t z) coeff1267 := by
  norm_num [atom1267, coeff1267, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1267_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1267 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1267]
  positivity
theorem weighted1267_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (203744635350722428670662658140952630902594686466776156132098179694763879565346399251555243325723262564146195278184315188402369389202521600 : Int) coeff1267) := by
  rw [CoefficientMerge.eval_scale, ← atom1267_identity]
  exact mul_nonneg (by norm_num) (atom1267_nonneg g t z hg hA hB ht hz hw)

def coeff1268 : CoefficientMerge.Poly :=
  [(823296, 1)]
noncomputable def atom1268 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 1 * (g 7) ^ 2 * (t) ^ 3)
theorem atom1268_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1268 g t z = CoefficientMerge.eval (monomial g t z) coeff1268 := by
  norm_num [atom1268, coeff1268, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1268_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1268 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1268]
  positivity
theorem weighted1268_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (79124871690023669368221271649289012883385961089318725298300388406319547040995048458652449746316701817391983585470389299033227792125638400 : Int) coeff1268) := by
  rw [CoefficientMerge.eval_scale, ← atom1268_identity]
  exact mul_nonneg (by norm_num) (atom1268_nonneg g t z hg hA hB ht hz hw)

def coeff1269 : CoefficientMerge.Poly :=
  [(872448, 1)]
noncomputable def atom1269 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (t) ^ 3)
theorem atom1269_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1269 g t z = CoefficientMerge.eval (monomial g t z) coeff1269 := by
  norm_num [atom1269, coeff1269, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1269_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1269 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1269]
  positivity
theorem weighted1269_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (105158649505384222712115568729585440444581037906840520194719849266572779473147558524864500775749811596774295320113603762962900833657145600 : Int) coeff1269) := by
  rw [CoefficientMerge.eval_scale, ← atom1269_identity]
  exact mul_nonneg (by norm_num) (atom1269_nonneg g t z hg hA hB ht hz hw)

def coeff1270 : CoefficientMerge.Poly :=
  [(1609728, 1)]
noncomputable def atom1270 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 1 * (g 7) ^ 2 * (t) ^ 2 * (z) ^ 1)
theorem atom1270_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1270 g t z = CoefficientMerge.eval (monomial g t z) coeff1270 := by
  norm_num [atom1270, coeff1270, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1270_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1270 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1270]
  positivity
theorem weighted1270_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (259110405863942463563460329870029079097587427775957359143959901134728666255640796323951340306684102659158291723908599004267691695249664000 : Int) coeff1270) := by
  rw [CoefficientMerge.eval_scale, ← atom1270_identity]
  exact mul_nonneg (by norm_num) (atom1270_nonneg g t z hg hA hB ht hz hw)

def coeff1271 : CoefficientMerge.Poly :=
  [(1658880, 1)]
noncomputable def atom1271 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1271_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1271 g t z = CoefficientMerge.eval (monomial g t z) coeff1271 := by
  norm_num [atom1271, coeff1271, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1271_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1271 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1271]
  positivity
theorem weighted1271_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (331190123048250712112215192238227690217711759678307569720316206752481984948475356920809041490841943593156794233940766536444140374658649600 : Int) coeff1271) := by
  rw [CoefficientMerge.eval_scale, ← atom1271_identity]
  exact mul_nonneg (by norm_num) (atom1271_nonneg g t z hg hA hB ht hz hw)

def coeff1272 : CoefficientMerge.Poly :=
  [(921600, 1)]
noncomputable def atom1272 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 1 * (g 8) ^ 2 * (t) ^ 3)
theorem atom1272_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1272 g t z = CoefficientMerge.eval (monomial g t z) coeff1272 := by
  norm_num [atom1272, coeff1272, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1272_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1272 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1272]
  positivity
theorem weighted1272_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (28549046875865974839559983474736159109502296775598605924147911748787175565433112419665865082111763482190873713391583788489344244805324800 : Int) coeff1272) := by
  rw [CoefficientMerge.eval_scale, ← atom1272_identity]
  exact mul_nonneg (by norm_num) (atom1272_nonneg g t z hg hA hB ht hz hw)

def coeff1273 : CoefficientMerge.Poly :=
  [(1708032, 1)]
noncomputable def atom1273 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 1 * (g 8) ^ 2 * (t) ^ 2 * (z) ^ 1)
theorem atom1273_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1273 g t z = CoefficientMerge.eval (monomial g t z) coeff1273 := by
  norm_num [atom1273, coeff1273, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1273_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1273 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1273]
  positivity
theorem weighted1273_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (105179431279109964628498398138264700788392521093772139381024583792826728884559551175409424430745250331332758711168467155393988367030169600 : Int) coeff1273) := by
  rw [CoefficientMerge.eval_scale, ← atom1273_identity]
  exact mul_nonneg (by norm_num) (atom1273_nonneg g t z hg hA hB ht hz hw)

def coeff1274 : CoefficientMerge.Poly :=
  [(2371584, 1)]
noncomputable def atom1274 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 3 * (t) ^ 1 * (z) ^ 2)
theorem atom1274_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1274 g t z = CoefficientMerge.eval (monomial g t z) coeff1274 := by
  norm_num [atom1274, coeff1274, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1274_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1274 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1274]
  positivity
theorem weighted1274_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (106357170659578251514977819004157538151958876541329621615824813914325178285166193748963989926967526456434780965481386434081571774957801600 : Int) coeff1274) := by
  rw [CoefficientMerge.eval_scale, ← atom1274_identity]
  exact mul_nonneg (by norm_num) (atom1274_nonneg g t z hg hA hB ht hz hw)

def coeff1275 : CoefficientMerge.Poly :=
  [(2383872, 1)]
noncomputable def atom1275 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 2 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1275_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1275 g t z = CoefficientMerge.eval (monomial g t z) coeff1275 := by
  norm_num [atom1275, coeff1275, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1275_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1275 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1275]
  positivity
theorem weighted1275_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (270411221726241333279173272594307755350481472204507951205619649445176112479488618705617713714610879546292195778560356856341884730219098000 : Int) coeff1275) := by
  rw [CoefficientMerge.eval_scale, ← atom1275_identity]
  exact mul_nonneg (by norm_num) (atom1275_nonneg g t z hg hA hB ht hz hw)

def coeff1276 : CoefficientMerge.Poly :=
  [(2433024, 1)]
noncomputable def atom1276 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 2 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1276_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1276 g t z = CoefficientMerge.eval (monomial g t z) coeff1276 := by
  norm_num [atom1276, coeff1276, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1276_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1276 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1276]
  positivity
theorem weighted1276_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (208299989151642176176728078022866404774184164627126456693297809995042897433588526507432498151221495598745793656666041767284284158049700800 : Int) coeff1276) := by
  rw [CoefficientMerge.eval_scale, ← atom1276_identity]
  exact mul_nonneg (by norm_num) (atom1276_nonneg g t z hg hA hB ht hz hw)

def coeff1277 : CoefficientMerge.Poly :=
  [(2396160, 1)]
noncomputable def atom1277 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 1 * (g 7) ^ 2 * (t) ^ 1 * (z) ^ 2)
theorem atom1277_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1277 g t z = CoefficientMerge.eval (monomial g t z) coeff1277 := by
  norm_num [atom1277, coeff1277, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1277_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1277 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1277]
  positivity
theorem weighted1277_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (231140358003298258932980488635830335657846491037585546974844834053716526426700155598543784058136864939993615948485527066216487382895294800 : Int) coeff1277) := by
  rw [CoefficientMerge.eval_scale, ← atom1277_identity]
  exact mul_nonneg (by norm_num) (atom1277_nonneg g t z hg hA hB ht hz hw)

def coeff1278 : CoefficientMerge.Poly :=
  [(2445312, 1)]
noncomputable def atom1278 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1278_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1278 g t z = CoefficientMerge.eval (monomial g t z) coeff1278 := by
  norm_num [atom1278, coeff1278, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1278_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1278 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1278]
  positivity
theorem weighted1278_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (304629092034124754240831906314821965448042933364872019039992687665336212826017305759791919142318017759669335119511730235809143500561141200 : Int) coeff1278) := by
  rw [CoefficientMerge.eval_scale, ← atom1278_identity]
  exact mul_nonneg (by norm_num) (atom1278_nonneg g t z hg hA hB ht hz hw)

def coeff1279 : CoefficientMerge.Poly :=
  [(2494464, 1)]
noncomputable def atom1279 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 1 * (g 8) ^ 2 * (t) ^ 1 * (z) ^ 2)
theorem atom1279_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1279 g t z = CoefficientMerge.eval (monomial g t z) coeff1279 := by
  norm_num [atom1279, coeff1279, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1279_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1279 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1279]
  positivity
theorem weighted1279_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (100503493121253942956394475063642234075887079560363597257262758984218275318850825624832104063754348062986666343833958200610684332380385600 : Int) coeff1279) := by
  rw [CoefficientMerge.eval_scale, ← atom1279_identity]
  exact mul_nonneg (by norm_num) (atom1279_nonneg g t z hg hA hB ht hz hw)

def coeff1280 : CoefficientMerge.Poly :=
  [(835584, 1)]
noncomputable def atom1280 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 7) ^ 3 * (t) ^ 3)
theorem atom1280_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1280 g t z = CoefficientMerge.eval (monomial g t z) coeff1280 := by
  norm_num [atom1280, coeff1280, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1280_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1280 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1280]
  positivity
theorem weighted1280_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (20895584991564552814986068513858090057133717836672333324640782770038930323456823809236045372554366747256645085528449658528413835289312000 : Int) coeff1280) := by
  rw [CoefficientMerge.eval_scale, ← atom1280_identity]
  exact mul_nonneg (by norm_num) (atom1280_nonneg g t z hg hA hB ht hz hw)

def coeff1281 : CoefficientMerge.Poly :=
  [(884736, 1)]
noncomputable def atom1281 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 7) ^ 2 * (g 8) ^ 1 * (t) ^ 3)
theorem atom1281_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1281 g t z = CoefficientMerge.eval (monomial g t z) coeff1281 := by
  norm_num [atom1281, coeff1281, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1281_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1281 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1281]
  positivity
theorem weighted1281_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (20542880564410570091103172694178903161888783237273416778342360048003141568552651073799976467648836905224379362443648373864770698053721600 : Int) coeff1281) := by
  rw [CoefficientMerge.eval_scale, ← atom1281_identity]
  exact mul_nonneg (by norm_num) (atom1281_nonneg g t z hg hA hB ht hz hw)

def coeff1282 : CoefficientMerge.Poly :=
  [(1622016, 1)]
noncomputable def atom1282 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 7) ^ 3 * (t) ^ 2 * (z) ^ 1)
theorem atom1282_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1282 g t z = CoefficientMerge.eval (monomial g t z) coeff1282 := by
  norm_num [atom1282, coeff1282, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1282_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1282 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1282]
  positivity
theorem weighted1282_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (76757304560430466979457821192007794554331022903659476117371769826289190757081924540833427945702029481857204486810473521741800682913484800 : Int) coeff1282) := by
  rw [CoefficientMerge.eval_scale, ← atom1282_identity]
  exact mul_nonneg (by norm_num) (atom1282_nonneg g t z hg hA hB ht hz hw)

def coeff1283 : CoefficientMerge.Poly :=
  [(1671168, 1)]
noncomputable def atom1283 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 7) ^ 2 * (g 8) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1283_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1283 g t z = CoefficientMerge.eval (monomial g t z) coeff1283 := by
  norm_num [atom1283, coeff1283, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1283_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1283 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1283]
  positivity
theorem weighted1283_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (70149163781275061317261452101183801408304347582052653598253569911228882913214414833170560787863233698843172499754160149718973442584550400 : Int) coeff1283) := by
  rw [CoefficientMerge.eval_scale, ← atom1283_identity]
  exact mul_nonneg (by norm_num) (atom1283_nonneg g t z hg hA hB ht hz hw)

def coeff1284 : CoefficientMerge.Poly :=
  [(2408448, 1)]
noncomputable def atom1284 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 7) ^ 3 * (t) ^ 1 * (z) ^ 2)
theorem atom1284_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1284 g t z = CoefficientMerge.eval (monomial g t z) coeff1284 := by
  norm_num [atom1284, coeff1284, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1284_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1284 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1284]
  positivity
theorem weighted1284_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (54394323808762379401502518898366856631266437096732347319531681935669558092462435456785329806562534473830407082537202958561154427848908800 : Int) coeff1284) := by
  rw [CoefficientMerge.eval_scale, ← atom1284_identity]
  exact mul_nonneg (by norm_num) (atom1284_nonneg g t z hg hA hB ht hz hw)

def sparseBlock095 : CoefficientMerge.Poly :=
  [(823296, 79124871690023669368221271649289012883385961089318725298300388406319547040995048458652449746316701817391983585470389299033227792125638400), (835584, 20895584991564552814986068513858090057133717836672333324640782770038930323456823809236045372554366747256645085528449658528413835289312000), (872448, 105158649505384222712115568729585440444581037906840520194719849266572779473147558524864500775749811596774295320113603762962900833657145600), (884736, 20542880564410570091103172694178903161888783237273416778342360048003141568552651073799976467648836905224379362443648373864770698053721600), (921600, 28549046875865974839559983474736159109502296775598605924147911748787175565433112419665865082111763482190873713391583788489344244805324800), (1585152, 107908982259419304395538728424803126839280427711473018531798350338486223984325542800136834521871455959241403924714413697484251413297753600), (1597440, 278637429280653223103954752177918026384080849822067364606681676839963129233525840580091019556358150992163212661235776923558167734786188800), (1609728, 259110405863942463563460329870029079097587427775957359143959901134728666255640796323951340306684102659158291723908599004267691695249664000), (1622016, 76757304560430466979457821192007794554331022903659476117371769826289190757081924540833427945702029481857204486810473521741800682913484800), (1646592, 203744635350722428670662658140952630902594686466776156132098179694763879565346399251555243325723262564146195278184315188402369389202521600), (1658880, 331190123048250712112215192238227690217711759678307569720316206752481984948475356920809041490841943593156794233940766536444140374658649600), (1671168, 70149163781275061317261452101183801408304347582052653598253569911228882913214414833170560787863233698843172499754160149718973442584550400), (1708032, 105179431279109964628498398138264700788392521093772139381024583792826728884559551175409424430745250331332758711168467155393988367030169600), (2371584, 106357170659578251514977819004157538151958876541329621615824813914325178285166193748963989926967526456434780965481386434081571774957801600), (2383872, 270411221726241333279173272594307755350481472204507951205619649445176112479488618705617713714610879546292195778560356856341884730219098000), (2396160, 231140358003298258932980488635830335657846491037585546974844834053716526426700155598543784058136864939993615948485527066216487382895294800), (2408448, 54394323808762379401502518898366856631266437096732347319531681935669558092462435456785329806562534473830407082537202958561154427848908800), (2433024, 208299989151642176176728078022866404774184164627126456693297809995042897433588526507432498151221495598745793656666041767284284158049700800), (2445312, 304629092034124754240831906314821965448042933364872019039992687665336212826017305759791919142318017759669335119511730235809143500561141200), (2494464, 100503493121253942956394475063642234075887079560363597257262758984218275318850825624832104063754348062986666343833958200610684332380385600)]
theorem sparseBlock095_data : sparseBlock095 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (107908982259419304395538728424803126839280427711473018531798350338486223984325542800136834521871455959241403924714413697484251413297753600 : Int) coeff1265) (CoefficientMerge.scale (278637429280653223103954752177918026384080849822067364606681676839963129233525840580091019556358150992163212661235776923558167734786188800 : Int) coeff1266)) (CoefficientMerge.merge (CoefficientMerge.scale (203744635350722428670662658140952630902594686466776156132098179694763879565346399251555243325723262564146195278184315188402369389202521600 : Int) coeff1267) (CoefficientMerge.merge (CoefficientMerge.scale (79124871690023669368221271649289012883385961089318725298300388406319547040995048458652449746316701817391983585470389299033227792125638400 : Int) coeff1268) (CoefficientMerge.scale (105158649505384222712115568729585440444581037906840520194719849266572779473147558524864500775749811596774295320113603762962900833657145600 : Int) coeff1269)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (259110405863942463563460329870029079097587427775957359143959901134728666255640796323951340306684102659158291723908599004267691695249664000 : Int) coeff1270) (CoefficientMerge.scale (331190123048250712112215192238227690217711759678307569720316206752481984948475356920809041490841943593156794233940766536444140374658649600 : Int) coeff1271)) (CoefficientMerge.merge (CoefficientMerge.scale (28549046875865974839559983474736159109502296775598605924147911748787175565433112419665865082111763482190873713391583788489344244805324800 : Int) coeff1272) (CoefficientMerge.merge (CoefficientMerge.scale (105179431279109964628498398138264700788392521093772139381024583792826728884559551175409424430745250331332758711168467155393988367030169600 : Int) coeff1273) (CoefficientMerge.scale (106357170659578251514977819004157538151958876541329621615824813914325178285166193748963989926967526456434780965481386434081571774957801600 : Int) coeff1274))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (270411221726241333279173272594307755350481472204507951205619649445176112479488618705617713714610879546292195778560356856341884730219098000 : Int) coeff1275) (CoefficientMerge.scale (208299989151642176176728078022866404774184164627126456693297809995042897433588526507432498151221495598745793656666041767284284158049700800 : Int) coeff1276)) (CoefficientMerge.merge (CoefficientMerge.scale (231140358003298258932980488635830335657846491037585546974844834053716526426700155598543784058136864939993615948485527066216487382895294800 : Int) coeff1277) (CoefficientMerge.merge (CoefficientMerge.scale (304629092034124754240831906314821965448042933364872019039992687665336212826017305759791919142318017759669335119511730235809143500561141200 : Int) coeff1278) (CoefficientMerge.scale (100503493121253942956394475063642234075887079560363597257262758984218275318850825624832104063754348062986666343833958200610684332380385600 : Int) coeff1279)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (20895584991564552814986068513858090057133717836672333324640782770038930323456823809236045372554366747256645085528449658528413835289312000 : Int) coeff1280) (CoefficientMerge.scale (20542880564410570091103172694178903161888783237273416778342360048003141568552651073799976467648836905224379362443648373864770698053721600 : Int) coeff1281)) (CoefficientMerge.merge (CoefficientMerge.scale (76757304560430466979457821192007794554331022903659476117371769826289190757081924540833427945702029481857204486810473521741800682913484800 : Int) coeff1282) (CoefficientMerge.merge (CoefficientMerge.scale (70149163781275061317261452101183801408304347582052653598253569911228882913214414833170560787863233698843172499754160149718973442584550400 : Int) coeff1283) (CoefficientMerge.scale (54394323808762379401502518898366856631266437096732347319531681935669558092462435456785329806562534473830407082537202958561154427848908800 : Int) coeff1284)))))) := by decide +kernel
theorem sparseBlock095_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock095 := by
  rw [sparseBlock095_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted1265_nonneg g t z hg hA hB ht hz hw) (weighted1266_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1267_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1268_nonneg g t z hg hA hB ht hz hw) (weighted1269_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1270_nonneg g t z hg hA hB ht hz hw) (weighted1271_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1272_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1273_nonneg g t z hg hA hB ht hz hw) (weighted1274_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted1275_nonneg g t z hg hA hB ht hz hw) (weighted1276_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1277_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1278_nonneg g t z hg hA hB ht hz hw) (weighted1279_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1280_nonneg g t z hg hA hB ht hz hw) (weighted1281_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1282_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1283_nonneg g t z hg hA hB ht hz hw) (weighted1284_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
