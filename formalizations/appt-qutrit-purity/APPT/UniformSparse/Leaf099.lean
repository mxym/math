import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff1345 : CoefficientMerge.Poly :=
  [(1311752, 1)]
noncomputable def atom1345 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 2 * (g 5) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom1345_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1345 g t z = CoefficientMerge.eval (monomial g t z) coeff1345 := by
  norm_num [atom1345, coeff1345, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1345_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1345 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1345]
  positivity
theorem weighted1345_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (54302452874180516507129111516337693913069375341320099122275083236360014034065873891592893043537161792906124126357190556593319446346547200 : Int) coeff1345) := by
  rw [CoefficientMerge.eval_scale, ← atom1345_identity]
  exact mul_nonneg (by norm_num) (atom1345_nonneg g t z hg hA hB ht hz hw)

def coeff1346 : CoefficientMerge.Poly :=
  [(2097221, 1)]
noncomputable def atom1346 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 1) ^ 1 * (g 3) ^ 1 * (z) ^ 2)
theorem atom1346_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1346 g t z = CoefficientMerge.eval (monomial g t z) coeff1346 := by
  norm_num [atom1346, coeff1346, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1346_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1346 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1346]
  positivity
theorem weighted1346_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (240599282856831063702759202954533023194431922521322622907750740918191721764089296785700483151506379480401232563840920316114553111801937920 : Int) coeff1346) := by
  rw [CoefficientMerge.eval_scale, ← atom1346_identity]
  exact mul_nonneg (by norm_num) (atom1346_nonneg g t z hg hA hB ht hz hw)

def coeff1347 : CoefficientMerge.Poly :=
  [(1048609, 1)]
noncomputable def atom1347 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 2 * (z) ^ 1)
theorem atom1347_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1347 g t z = CoefficientMerge.eval (monomial g t z) coeff1347 := by
  norm_num [atom1347, coeff1347, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1347_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1347 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1347]
  positivity
theorem weighted1347_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1866704472768630600316655088283708827246303482270590257726837250568459082532143715732630093263000982327929709207455716626221092903304314880 : Int) coeff1347) := by
  rw [CoefficientMerge.eval_scale, ← atom1347_identity]
  exact mul_nonneg (by norm_num) (atom1347_nonneg g t z hg hA hB ht hz hw)

def coeff1348 : CoefficientMerge.Poly :=
  [(1310753, 1)]
noncomputable def atom1348 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 2 * (t) ^ 1 * (z) ^ 1)
theorem atom1348_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1348 g t z = CoefficientMerge.eval (monomial g t z) coeff1348 := by
  norm_num [atom1348, coeff1348, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1348_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1348 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1348]
  positivity
theorem weighted1348_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (250486651978009537619938633968582846092827337316138938974342846547127750889387542073659156074083714250095348426406099210567659734760341504 : Int) coeff1348) := by
  rw [CoefficientMerge.eval_scale, ← atom1348_identity]
  exact mul_nonneg (by norm_num) (atom1348_nonneg g t z hg hA hB ht hz hw)

def coeff1349 : CoefficientMerge.Poly :=
  [(2162705, 1)]
noncomputable def atom1349 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 8) ^ 1 * (z) ^ 2)
theorem atom1349_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1349 g t z = CoefficientMerge.eval (monomial g t z) coeff1349 := by
  norm_num [atom1349, coeff1349, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1349_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1349 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1349]
  positivity
theorem weighted1349_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (157177979947235931140290651571915387594048947526656596232563193108231342843840169649377419643335768517508264053081497554919327600572211200 : Int) coeff1349) := by
  rw [CoefficientMerge.eval_scale, ← atom1349_identity]
  exact mul_nonneg (by norm_num) (atom1349_nonneg g t z hg hA hB ht hz hw)

def coeff1350 : CoefficientMerge.Poly :=
  [(2098184, 1)]
noncomputable def atom1350 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 2 * (g 5) ^ 1 * (z) ^ 2)
theorem atom1350_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1350 g t z = CoefficientMerge.eval (monomial g t z) coeff1350 := by
  norm_num [atom1350, coeff1350, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1350_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1350 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1350]
  positivity
theorem weighted1350_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (10124695402900107602413050944476889574094897706948710651436993238825495106899206391727906079408847531941047045274401730480756085217689600 : Int) coeff1350) := by
  rw [CoefficientMerge.eval_scale, ← atom1350_identity]
  exact mul_nonneg (by norm_num) (atom1350_nonneg g t z hg hA hB ht hz hw)

def coeff1351 : CoefficientMerge.Poly :=
  [(1048612, 1)]
noncomputable def atom1351 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 2 * (z) ^ 1)
theorem atom1351_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1351 g t z = CoefficientMerge.eval (monomial g t z) coeff1351 := by
  norm_num [atom1351, coeff1351, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1351_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1351 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1351]
  positivity
theorem weighted1351_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4338889352228544405276787779063024735732567716511547019274370157572639019798822228988823556528893826001675951790041347374109399307369431040 : Int) coeff1351) := by
  rw [CoefficientMerge.eval_scale, ← atom1351_identity]
  exact mul_nonneg (by norm_num) (atom1351_nonneg g t z hg hA hB ht hz hw)

def coeff1352 : CoefficientMerge.Poly :=
  [(2098196, 1)]
noncomputable def atom1352 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 5) ^ 1 * (z) ^ 2)
theorem atom1352_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1352 g t z = CoefficientMerge.eval (monomial g t z) coeff1352 := by
  norm_num [atom1352, coeff1352, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1352_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1352 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1352]
  positivity
theorem weighted1352_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (479490244149747768468240845611096187068325932966139669093549159912350360113966390440522242722087270613340951776756995670651758478944953088 : Int) coeff1352) := by
  rw [CoefficientMerge.eval_scale, ← atom1352_identity]
  exact mul_nonneg (by norm_num) (atom1352_nonneg g t z hg hA hB ht hz hw)

def coeff1353 : CoefficientMerge.Poly :=
  [(2162708, 1)]
noncomputable def atom1353 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 8) ^ 1 * (z) ^ 2)
theorem atom1353_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1353 g t z = CoefficientMerge.eval (monomial g t z) coeff1353 := by
  norm_num [atom1353, coeff1353, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1353_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1353 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1353]
  positivity
theorem weighted1353_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (416809866551819621718805565382101257626117604690159767447359444109922999458337470576288455643104693943736909533512852187750349214360279040 : Int) coeff1353) := by
  rw [CoefficientMerge.eval_scale, ← atom1353_identity]
  exact mul_nonneg (by norm_num) (atom1353_nonneg g t z hg hA hB ht hz hw)

def coeff1354 : CoefficientMerge.Poly :=
  [(786438, 1)]
noncomputable def atom1354 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 2 * (g 1) ^ 1 * (t) ^ 3)
theorem atom1354_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1354 g t z = CoefficientMerge.eval (monomial g t z) coeff1354 := by
  norm_num [atom1354, coeff1354, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1354_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1354 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1354]
  positivity
theorem weighted1354_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1356045130956722082148559155365556496116346070238806819588083967785751627674284765860934911178998127638452897660679579097135077722112000 : Int) coeff1354) := by
  rw [CoefficientMerge.eval_scale, ← atom1354_identity]
  exact mul_nonneg (by norm_num) (atom1354_nonneg g t z hg hA hB ht hz hw)

def coeff1355 : CoefficientMerge.Poly :=
  [(1572870, 1)]
noncomputable def atom1355 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 2 * (g 1) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1355_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1355 g t z = CoefficientMerge.eval (monomial g t z) coeff1355 := by
  norm_num [atom1355, coeff1355, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1355_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1355 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1355]
  positivity
theorem weighted1355_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4015732118695884180657418826601319718844072673821457525816937355508245576457860670515849909720588436632989036800777001031557291724410880 : Int) coeff1355) := by
  rw [CoefficientMerge.eval_scale, ← atom1355_identity]
  exact mul_nonneg (by norm_num) (atom1355_nonneg g t z hg hA hB ht hz hw)

def coeff1356 : CoefficientMerge.Poly :=
  [(2359302, 1)]
noncomputable def atom1356 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 2 * (g 1) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1356_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1356 g t z = CoefficientMerge.eval (monomial g t z) coeff1356 := by
  norm_num [atom1356, coeff1356, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1356_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1356 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1356]
  positivity
theorem weighted1356_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3980008285368513139745553772151281414388878769795289393601341578752318048505582723667507658285951333582288626150210071092326406847139840 : Int) coeff1356) := by
  rw [CoefficientMerge.eval_scale, ← atom1356_identity]
  exact mul_nonneg (by norm_num) (atom1356_nonneg g t z hg hA hB ht hz hw)

def coeff1357 : CoefficientMerge.Poly :=
  [(3145734, 1)]
noncomputable def atom1357 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 2 * (g 1) ^ 1 * (z) ^ 3)
theorem atom1357_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1357 g t z = CoefficientMerge.eval (monomial g t z) coeff1357 := by
  norm_num [atom1357, coeff1357, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1357_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1357 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1357]
  positivity
theorem weighted1357_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1320321297629351041236694100915518191661152166212638687372488191029824099722006819012592659744361024587752487010112649157904192844840960 : Int) coeff1357) := by
  rw [CoefficientMerge.eval_scale, ← atom1357_identity]
  exact mul_nonneg (by norm_num) (atom1357_nonneg g t z hg hA hB ht hz hw)

def coeff1358 : CoefficientMerge.Poly :=
  [(786450, 1)]
noncomputable def atom1358 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 2 * (g 2) ^ 1 * (t) ^ 3)
theorem atom1358_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1358 g t z = CoefficientMerge.eval (monomial g t z) coeff1358 := by
  norm_num [atom1358, coeff1358, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1358_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1358 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1358]
  positivity
theorem weighted1358_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (180324517697171470883354710487775527940055755035980114600355799121181192322860518875419629112801104158485440424087961089203115004702720 : Int) coeff1358) := by
  rw [CoefficientMerge.eval_scale, ← atom1358_identity]
  exact mul_nonneg (by norm_num) (atom1358_nonneg g t z hg hA hB ht hz hw)

def coeff1359 : CoefficientMerge.Poly :=
  [(786498, 1)]
noncomputable def atom1359 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 2 * (g 3) ^ 1 * (t) ^ 3)
theorem atom1359_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1359 g t z = CoefficientMerge.eval (monomial g t z) coeff1359 := by
  norm_num [atom1359, coeff1359, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1359_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1359 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1359]
  positivity
theorem weighted1359_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3883199951291769543472399723426042553995306164674986769871458278197359681730149446542174750918963669902260119435672791556338382864691200 : Int) coeff1359) := by
  rw [CoefficientMerge.eval_scale, ← atom1359_identity]
  exact mul_nonneg (by norm_num) (atom1359_nonneg g t z hg hA hB ht hz hw)

def coeff1360 : CoefficientMerge.Poly :=
  [(1572930, 1)]
noncomputable def atom1360 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 2 * (g 3) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1360_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1360 g t z = CoefficientMerge.eval (monomial g t z) coeff1360 := by
  norm_num [atom1360, coeff1360, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1360_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1360 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1360]
  positivity
theorem weighted1360_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (11649599853875308630417199170278127661985918494024960309614374834592079045190448339626524252756891009706780358307018374669015148594073600 : Int) coeff1360) := by
  rw [CoefficientMerge.eval_scale, ← atom1360_identity]
  exact mul_nonneg (by norm_num) (atom1360_nonneg g t z hg hA hB ht hz hw)

def coeff1361 : CoefficientMerge.Poly :=
  [(2359362, 1)]
noncomputable def atom1361 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 2 * (g 3) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1361_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1361 g t z = CoefficientMerge.eval (monomial g t z) coeff1361 := by
  norm_num [atom1361, coeff1361, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1361_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1361 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1361]
  positivity
theorem weighted1361_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (11649599853875308630417199170278127661985918494024960309614374834592079045190448339626524252756891009706780358307018374669015148594073600 : Int) coeff1361) := by
  rw [CoefficientMerge.eval_scale, ← atom1361_identity]
  exact mul_nonneg (by norm_num) (atom1361_nonneg g t z hg hA hB ht hz hw)

def coeff1362 : CoefficientMerge.Poly :=
  [(3145794, 1)]
noncomputable def atom1362 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 2 * (g 3) ^ 1 * (z) ^ 3)
theorem atom1362_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1362 g t z = CoefficientMerge.eval (monomial g t z) coeff1362 := by
  norm_num [atom1362, coeff1362, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1362_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1362 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1362]
  positivity
theorem weighted1362_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3883199951291769543472399723426042553995306164674986769871458278197359681730149446542174750918963669902260119435672791556338382864691200 : Int) coeff1362) := by
  rw [CoefficientMerge.eval_scale, ← atom1362_identity]
  exact mul_nonneg (by norm_num) (atom1362_nonneg g t z hg hA hB ht hz hw)

def coeff1363 : CoefficientMerge.Poly :=
  [(786690, 1)]
noncomputable def atom1363 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 2 * (g 4) ^ 1 * (t) ^ 3)
theorem atom1363_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1363 g t z = CoefficientMerge.eval (monomial g t z) coeff1363 := by
  norm_num [atom1363, coeff1363, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1363_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1363 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1363]
  positivity
theorem weighted1363_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2016171125873904157164730695658050262135976081696918312660939333725540763317129173722357678214877616534900554318315051329502314912952320 : Int) coeff1363) := by
  rw [CoefficientMerge.eval_scale, ← atom1363_identity]
  exact mul_nonneg (by norm_num) (atom1363_nonneg g t z hg hA hB ht hz hw)

def coeff1364 : CoefficientMerge.Poly :=
  [(1573122, 1)]
noncomputable def atom1364 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 2 * (g 4) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1364_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1364 g t z = CoefficientMerge.eval (monomial g t z) coeff1364 := by
  norm_num [atom1364, coeff1364, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1364_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1364 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1364]
  positivity
theorem weighted1364_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5749144352923734947997295206563605822683598200389479314643066403817885203362478961959096728947173121758137070982206874993685193439498240 : Int) coeff1364) := by
  rw [CoefficientMerge.eval_scale, ← atom1364_identity]
  exact mul_nonneg (by norm_num) (atom1364_nonneg g t z hg hA hB ht hz hw)

def sparseBlock099 : CoefficientMerge.Poly :=
  [(786438, 1356045130956722082148559155365556496116346070238806819588083967785751627674284765860934911178998127638452897660679579097135077722112000), (786450, 180324517697171470883354710487775527940055755035980114600355799121181192322860518875419629112801104158485440424087961089203115004702720), (786498, 3883199951291769543472399723426042553995306164674986769871458278197359681730149446542174750918963669902260119435672791556338382864691200), (786690, 2016171125873904157164730695658050262135976081696918312660939333725540763317129173722357678214877616534900554318315051329502314912952320), (1048609, 1866704472768630600316655088283708827246303482270590257726837250568459082532143715732630093263000982327929709207455716626221092903304314880), (1048612, 4338889352228544405276787779063024735732567716511547019274370157572639019798822228988823556528893826001675951790041347374109399307369431040), (1310753, 250486651978009537619938633968582846092827337316138938974342846547127750889387542073659156074083714250095348426406099210567659734760341504), (1311752, 54302452874180516507129111516337693913069375341320099122275083236360014034065873891592893043537161792906124126357190556593319446346547200), (1572870, 4015732118695884180657418826601319718844072673821457525816937355508245576457860670515849909720588436632989036800777001031557291724410880), (1572930, 11649599853875308630417199170278127661985918494024960309614374834592079045190448339626524252756891009706780358307018374669015148594073600), (1573122, 5749144352923734947997295206563605822683598200389479314643066403817885203362478961959096728947173121758137070982206874993685193439498240), (2097221, 240599282856831063702759202954533023194431922521322622907750740918191721764089296785700483151506379480401232563840920316114553111801937920), (2098184, 10124695402900107602413050944476889574094897706948710651436993238825495106899206391727906079408847531941047045274401730480756085217689600), (2098196, 479490244149747768468240845611096187068325932966139669093549159912350360113966390440522242722087270613340951776756995670651758478944953088), (2162705, 157177979947235931140290651571915387594048947526656596232563193108231342843840169649377419643335768517508264053081497554919327600572211200), (2162708, 416809866551819621718805565382101257626117604690159767447359444109922999458337470576288455643104693943736909533512852187750349214360279040), (2359302, 3980008285368513139745553772151281414388878769795289393601341578752318048505582723667507658285951333582288626150210071092326406847139840), (2359362, 11649599853875308630417199170278127661985918494024960309614374834592079045190448339626524252756891009706780358307018374669015148594073600), (3145734, 1320321297629351041236694100915518191661152166212638687372488191029824099722006819012592659744361024587752487010112649157904192844840960), (3145794, 3883199951291769543472399723426042553995306164674986769871458278197359681730149446542174750918963669902260119435672791556338382864691200)]
theorem sparseBlock099_data : sparseBlock099 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (54302452874180516507129111516337693913069375341320099122275083236360014034065873891592893043537161792906124126357190556593319446346547200 : Int) coeff1345) (CoefficientMerge.scale (240599282856831063702759202954533023194431922521322622907750740918191721764089296785700483151506379480401232563840920316114553111801937920 : Int) coeff1346)) (CoefficientMerge.merge (CoefficientMerge.scale (1866704472768630600316655088283708827246303482270590257726837250568459082532143715732630093263000982327929709207455716626221092903304314880 : Int) coeff1347) (CoefficientMerge.merge (CoefficientMerge.scale (250486651978009537619938633968582846092827337316138938974342846547127750889387542073659156074083714250095348426406099210567659734760341504 : Int) coeff1348) (CoefficientMerge.scale (157177979947235931140290651571915387594048947526656596232563193108231342843840169649377419643335768517508264053081497554919327600572211200 : Int) coeff1349)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (10124695402900107602413050944476889574094897706948710651436993238825495106899206391727906079408847531941047045274401730480756085217689600 : Int) coeff1350) (CoefficientMerge.scale (4338889352228544405276787779063024735732567716511547019274370157572639019798822228988823556528893826001675951790041347374109399307369431040 : Int) coeff1351)) (CoefficientMerge.merge (CoefficientMerge.scale (479490244149747768468240845611096187068325932966139669093549159912350360113966390440522242722087270613340951776756995670651758478944953088 : Int) coeff1352) (CoefficientMerge.merge (CoefficientMerge.scale (416809866551819621718805565382101257626117604690159767447359444109922999458337470576288455643104693943736909533512852187750349214360279040 : Int) coeff1353) (CoefficientMerge.scale (1356045130956722082148559155365556496116346070238806819588083967785751627674284765860934911178998127638452897660679579097135077722112000 : Int) coeff1354))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (4015732118695884180657418826601319718844072673821457525816937355508245576457860670515849909720588436632989036800777001031557291724410880 : Int) coeff1355) (CoefficientMerge.scale (3980008285368513139745553772151281414388878769795289393601341578752318048505582723667507658285951333582288626150210071092326406847139840 : Int) coeff1356)) (CoefficientMerge.merge (CoefficientMerge.scale (1320321297629351041236694100915518191661152166212638687372488191029824099722006819012592659744361024587752487010112649157904192844840960 : Int) coeff1357) (CoefficientMerge.merge (CoefficientMerge.scale (180324517697171470883354710487775527940055755035980114600355799121181192322860518875419629112801104158485440424087961089203115004702720 : Int) coeff1358) (CoefficientMerge.scale (3883199951291769543472399723426042553995306164674986769871458278197359681730149446542174750918963669902260119435672791556338382864691200 : Int) coeff1359)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (11649599853875308630417199170278127661985918494024960309614374834592079045190448339626524252756891009706780358307018374669015148594073600 : Int) coeff1360) (CoefficientMerge.scale (11649599853875308630417199170278127661985918494024960309614374834592079045190448339626524252756891009706780358307018374669015148594073600 : Int) coeff1361)) (CoefficientMerge.merge (CoefficientMerge.scale (3883199951291769543472399723426042553995306164674986769871458278197359681730149446542174750918963669902260119435672791556338382864691200 : Int) coeff1362) (CoefficientMerge.merge (CoefficientMerge.scale (2016171125873904157164730695658050262135976081696918312660939333725540763317129173722357678214877616534900554318315051329502314912952320 : Int) coeff1363) (CoefficientMerge.scale (5749144352923734947997295206563605822683598200389479314643066403817885203362478961959096728947173121758137070982206874993685193439498240 : Int) coeff1364)))))) := by decide +kernel
theorem sparseBlock099_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock099 := by
  rw [sparseBlock099_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted1345_nonneg g t z hg hA hB ht hz hw) (weighted1346_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1347_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1348_nonneg g t z hg hA hB ht hz hw) (weighted1349_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1350_nonneg g t z hg hA hB ht hz hw) (weighted1351_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1352_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1353_nonneg g t z hg hA hB ht hz hw) (weighted1354_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted1355_nonneg g t z hg hA hB ht hz hw) (weighted1356_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1357_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1358_nonneg g t z hg hA hB ht hz hw) (weighted1359_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1360_nonneg g t z hg hA hB ht hz hw) (weighted1361_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1362_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1363_nonneg g t z hg hA hB ht hz hw) (weighted1364_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
