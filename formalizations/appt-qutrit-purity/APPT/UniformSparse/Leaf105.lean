import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff1465 : CoefficientMerge.Poly :=
  [(1638657, 1)]
noncomputable def atom1465 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1465_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1465 g t z = CoefficientMerge.eval (monomial g t z) coeff1465 := by
  norm_num [atom1465, coeff1465, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1465_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1465 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1465]
  positivity
theorem weighted1465_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (25337375740655281048922654408755089881901096382815161963139891765677010362115528427987919081260492336769847563893983641044764020163397560 : Int) coeff1465) := by
  rw [CoefficientMerge.eval_scale, ← atom1465_identity]
  exact mul_nonneg (by norm_num) (atom1465_nonneg g t z hg hA hB ht hz hw)

def coeff1466 : CoefficientMerge.Poly :=
  [(2425089, 1)]
noncomputable def atom1466 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1466_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1466 g t z = CoefficientMerge.eval (monomial g t z) coeff1466 := by
  norm_num [atom1466, coeff1466, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1466_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1466 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1466]
  positivity
theorem weighted1466_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (30652841990781207642423363263962351326055021732158638326656349824880054305052748470261457775039680072239678856057396496835281829952263920 : Int) coeff1466) := by
  rw [CoefficientMerge.eval_scale, ← atom1466_identity]
  exact mul_nonneg (by norm_num) (atom1466_nonneg g t z hg hA hB ht hz hw)

def coeff1467 : CoefficientMerge.Poly :=
  [(788481, 1)]
noncomputable def atom1467 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 2 * (t) ^ 3)
theorem atom1467_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1467 g t z = CoefficientMerge.eval (monomial g t z) coeff1467 := by
  norm_num [atom1467, coeff1467, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1467_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1467 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1467]
  positivity
theorem weighted1467_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1960432841868859614221248246055274680217780095018556119340700150965082841938388573707843303556056516682710517068343422274608565932032000 : Int) coeff1467) := by
  rw [CoefficientMerge.eval_scale, ← atom1467_identity]
  exact mul_nonneg (by norm_num) (atom1467_nonneg g t z hg hA hB ht hz hw)

def coeff1468 : CoefficientMerge.Poly :=
  [(1574913, 1)]
noncomputable def atom1468 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 2 * (t) ^ 2 * (z) ^ 1)
theorem atom1468_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1468 g t z = CoefficientMerge.eval (monomial g t z) coeff1468 := by
  norm_num [atom1468, coeff1468, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1468_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1468 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1468]
  positivity
theorem weighted1468_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3920865683737719228442496492110549360435560190037112238681400301930165683876777147415686607112113033365421034136686844549217131864064000 : Int) coeff1468) := by
  rw [CoefficientMerge.eval_scale, ← atom1468_identity]
  exact mul_nonneg (by norm_num) (atom1468_nonneg g t z hg hA hB ht hz hw)

def coeff1469 : CoefficientMerge.Poly :=
  [(2361345, 1)]
noncomputable def atom1469 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 2 * (t) ^ 1 * (z) ^ 2)
theorem atom1469_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1469 g t z = CoefficientMerge.eval (monomial g t z) coeff1469 := by
  norm_num [atom1469, coeff1469, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1469_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1469 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1469]
  positivity
theorem weighted1469_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1960432841868859614221248246055274680217780095018556119340700150965082841938388573707843303556056516682710517068343422274608565932032000 : Int) coeff1469) := by
  rw [CoefficientMerge.eval_scale, ← atom1469_identity]
  exact mul_nonneg (by norm_num) (atom1469_nonneg g t z hg hA hB ht hz hw)

def coeff1470 : CoefficientMerge.Poly :=
  [(791553, 1)]
noncomputable def atom1470 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (t) ^ 3)
theorem atom1470_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1470 g t z = CoefficientMerge.eval (monomial g t z) coeff1470 := by
  norm_num [atom1470, coeff1470, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1470_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1470 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1470]
  positivity
theorem weighted1470_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (8177316336872466750791656798566320654854411494091655809690567156851781995173419047217047370723772280201787305542095665624535866097029120 : Int) coeff1470) := by
  rw [CoefficientMerge.eval_scale, ← atom1470_identity]
  exact mul_nonneg (by norm_num) (atom1470_nonneg g t z hg hA hB ht hz hw)

def coeff1471 : CoefficientMerge.Poly :=
  [(1577985, 1)]
noncomputable def atom1471 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1471_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1471 g t z = CoefficientMerge.eval (monomial g t z) coeff1471 := by
  norm_num [atom1471, coeff1471, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1471_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1471 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1471]
  positivity
theorem weighted1471_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (28049608976688410422633651597494353122502517517959393425496207346856591212044013498193290247661436928793685884214072537830758658599274240 : Int) coeff1471) := by
  rw [CoefficientMerge.eval_scale, ← atom1471_identity]
  exact mul_nonneg (by norm_num) (atom1471_nonneg g t z hg hA hB ht hz hw)

def coeff1472 : CoefficientMerge.Poly :=
  [(2364417, 1)]
noncomputable def atom1472 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1472_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1472 g t z = CoefficientMerge.eval (monomial g t z) coeff1472 := by
  norm_num [atom1472, coeff1472, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1472_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1472 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1472]
  positivity
theorem weighted1472_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (31567268942759420592892332799289744280441800553643819421920713223157836438567769854735438383151557016982009851801858078787909718907461120 : Int) coeff1472) := by
  rw [CoefficientMerge.eval_scale, ← atom1472_identity]
  exact mul_nonneg (by norm_num) (atom1472_nonneg g t z hg hA hB ht hz hw)

def coeff1473 : CoefficientMerge.Poly :=
  [(803841, 1)]
noncomputable def atom1473 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (t) ^ 3)
theorem atom1473_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1473 g t z = CoefficientMerge.eval (monomial g t z) coeff1473 := by
  norm_num [atom1473, coeff1473, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1473_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1473 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1473]
  positivity
theorem weighted1473_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4734685336434046268803148093537980632370562577546113596869716771635883737288846104317976135452684215124176143738620759817672960381066240 : Int) coeff1473) := by
  rw [CoefficientMerge.eval_scale, ← atom1473_identity]
  exact mul_nonneg (by norm_num) (atom1473_nonneg g t z hg hA hB ht hz hw)

def coeff1474 : CoefficientMerge.Poly :=
  [(1590273, 1)]
noncomputable def atom1474 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1474_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1474 g t z = CoefficientMerge.eval (monomial g t z) coeff1474 := by
  norm_num [atom1474, coeff1474, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1474_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1474 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1474]
  positivity
theorem weighted1474_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (9469370672868092537606296187075961264741125155092227193739433543271767474577692208635952270905368430248352287477241519635345920762132480 : Int) coeff1474) := by
  rw [CoefficientMerge.eval_scale, ← atom1474_identity]
  exact mul_nonneg (by norm_num) (atom1474_nonneg g t z hg hA hB ht hz hw)

def coeff1475 : CoefficientMerge.Poly :=
  [(2376705, 1)]
noncomputable def atom1475 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1475_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1475 g t z = CoefficientMerge.eval (monomial g t z) coeff1475 := by
  norm_num [atom1475, coeff1475, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1475_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1475 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1475]
  positivity
theorem weighted1475_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4734685336434046268803148093537980632370562577546113596869716771635883737288846104317976135452684215124176143738620759817672960381066240 : Int) coeff1475) := by
  rw [CoefficientMerge.eval_scale, ← atom1475_identity]
  exact mul_nonneg (by norm_num) (atom1475_nonneg g t z hg hA hB ht hz hw)

def coeff1476 : CoefficientMerge.Poly :=
  [(852993, 1)]
noncomputable def atom1476 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (t) ^ 3)
theorem atom1476_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1476 g t z = CoefficientMerge.eval (monomial g t z) coeff1476 := by
  norm_num [atom1476, coeff1476, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1476_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1476 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1476]
  positivity
theorem weighted1476_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3743060543023592489349377836452856727665950059868473618761120899853607868679132206835890368337540695153407588513247846013139419342950400 : Int) coeff1476) := by
  rw [CoefficientMerge.eval_scale, ← atom1476_identity]
  exact mul_nonneg (by norm_num) (atom1476_nonneg g t z hg hA hB ht hz hw)

def coeff1477 : CoefficientMerge.Poly :=
  [(1639425, 1)]
noncomputable def atom1477 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1477_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1477 g t z = CoefficientMerge.eval (monomial g t z) coeff1477 := by
  norm_num [atom1477, coeff1477, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1477_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1477 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1477]
  positivity
theorem weighted1477_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (6897851240506974228013517703639715952162986698787595558532152201706645009963049671998056787977100917547669527941174620801664797797520640 : Int) coeff1477) := by
  rw [CoefficientMerge.eval_scale, ← atom1477_identity]
  exact mul_nonneg (by norm_num) (atom1477_nonneg g t z hg hA hB ht hz hw)

def coeff1478 : CoefficientMerge.Poly :=
  [(2425857, 1)]
noncomputable def atom1478 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1478_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1478 g t z = CoefficientMerge.eval (monomial g t z) coeff1478 := by
  norm_num [atom1478, coeff1478, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1478_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1478 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1478]
  positivity
theorem weighted1478_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (8275431150403984466828672406478134108736406172144155948831830731676915160365012948295955682822827486084599253882400460948431292476717320 : Int) coeff1478) := by
  rw [CoefficientMerge.eval_scale, ← atom1478_identity]
  exact mul_nonneg (by norm_num) (atom1478_nonneg g t z hg hA hB ht hz hw)

def coeff1479 : CoefficientMerge.Poly :=
  [(794625, 1)]
noncomputable def atom1479 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 6) ^ 2 * (t) ^ 3)
theorem atom1479_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1479 g t z = CoefficientMerge.eval (monomial g t z) coeff1479 := by
  norm_num [atom1479, coeff1479, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1479_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1479 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1479]
  positivity
theorem weighted1479_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3983599054253139469190740690497205726881513700792726120719250928717015176171407876874917294145031826874274318533623850873605468543206400 : Int) coeff1479) := by
  rw [CoefficientMerge.eval_scale, ← atom1479_identity]
  exact mul_nonneg (by norm_num) (atom1479_nonneg g t z hg hA hB ht hz hw)

def coeff1480 : CoefficientMerge.Poly :=
  [(1581057, 1)]
noncomputable def atom1480 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 6) ^ 2 * (t) ^ 2 * (z) ^ 1)
theorem atom1480_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1480 g t z = CoefficientMerge.eval (monomial g t z) coeff1480 := by
  norm_num [atom1480, coeff1480, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1480_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1480 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1480]
  positivity
theorem weighted1480_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (18125581759114388879640873333831476321744421922208793510806515403413623761518598294778700148303842867301751426083430960478306703928499200 : Int) coeff1480) := by
  rw [CoefficientMerge.eval_scale, ← atom1480_identity]
  exact mul_nonneg (by norm_num) (atom1480_nonneg g t z hg hA hB ht hz hw)

def coeff1481 : CoefficientMerge.Poly :=
  [(2367489, 1)]
noncomputable def atom1481 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 6) ^ 2 * (t) ^ 1 * (z) ^ 2)
theorem atom1481_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1481 g t z = CoefficientMerge.eval (monomial g t z) coeff1481 := by
  norm_num [atom1481, coeff1481, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1481_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1481 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1481]
  positivity
theorem weighted1481_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (24998447062646454283175037494839277418256452889484957170876414302004985979953548028221528906382427050107972381652380101581414065154726400 : Int) coeff1481) := by
  rw [CoefficientMerge.eval_scale, ← atom1481_identity]
  exact mul_nonneg (by norm_num) (atom1481_nonneg g t z hg hA hB ht hz hw)

def coeff1482 : CoefficientMerge.Poly :=
  [(1593345, 1)]
noncomputable def atom1482 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1482_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1482 g t z = CoefficientMerge.eval (monomial g t z) coeff1482 := by
  norm_num [atom1482, coeff1482, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1482_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1482 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1482]
  positivity
theorem weighted1482_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (10007858608690101595569338700200300717464415844897011059199520301769748440615415762350187855137864176534818800948697760636287000006528000 : Int) coeff1482) := by
  rw [CoefficientMerge.eval_scale, ← atom1482_identity]
  exact mul_nonneg (by norm_num) (atom1482_nonneg g t z hg hA hB ht hz hw)

def coeff1483 : CoefficientMerge.Poly :=
  [(2379777, 1)]
noncomputable def atom1483 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1483_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1483 g t z = CoefficientMerge.eval (monomial g t z) coeff1483 := by
  norm_num [atom1483, coeff1483, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1483_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1483 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1483]
  positivity
theorem weighted1483_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (22719841564758937639407857359451635015075599242046257374941954775064777675830270227203069775209693152420234248167066039399086608155608000 : Int) coeff1483) := by
  rw [CoefficientMerge.eval_scale, ← atom1483_identity]
  exact mul_nonneg (by norm_num) (atom1483_nonneg g t z hg hA hB ht hz hw)

def coeff1484 : CoefficientMerge.Poly :=
  [(856065, 1)]
noncomputable def atom1484 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (t) ^ 3)
theorem atom1484_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1484 g t z = CoefficientMerge.eval (monomial g t z) coeff1484 := by
  norm_num [atom1484, coeff1484, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1484_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1484 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1484]
  positivity
theorem weighted1484_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5895689126011050980528898428273519202393207872968633651164094327950928544242627122134238474619906439945591372749417695535589609140761600 : Int) coeff1484) := by
  rw [CoefficientMerge.eval_scale, ← atom1484_identity]
  exact mul_nonneg (by norm_num) (atom1484_nonneg g t z hg hA hB ht hz hw)

def sparseBlock105 : CoefficientMerge.Poly :=
  [(788481, 1960432841868859614221248246055274680217780095018556119340700150965082841938388573707843303556056516682710517068343422274608565932032000), (791553, 8177316336872466750791656798566320654854411494091655809690567156851781995173419047217047370723772280201787305542095665624535866097029120), (794625, 3983599054253139469190740690497205726881513700792726120719250928717015176171407876874917294145031826874274318533623850873605468543206400), (803841, 4734685336434046268803148093537980632370562577546113596869716771635883737288846104317976135452684215124176143738620759817672960381066240), (852993, 3743060543023592489349377836452856727665950059868473618761120899853607868679132206835890368337540695153407588513247846013139419342950400), (856065, 5895689126011050980528898428273519202393207872968633651164094327950928544242627122134238474619906439945591372749417695535589609140761600), (1574913, 3920865683737719228442496492110549360435560190037112238681400301930165683876777147415686607112113033365421034136686844549217131864064000), (1577985, 28049608976688410422633651597494353122502517517959393425496207346856591212044013498193290247661436928793685884214072537830758658599274240), (1581057, 18125581759114388879640873333831476321744421922208793510806515403413623761518598294778700148303842867301751426083430960478306703928499200), (1590273, 9469370672868092537606296187075961264741125155092227193739433543271767474577692208635952270905368430248352287477241519635345920762132480), (1593345, 10007858608690101595569338700200300717464415844897011059199520301769748440615415762350187855137864176534818800948697760636287000006528000), (1638657, 25337375740655281048922654408755089881901096382815161963139891765677010362115528427987919081260492336769847563893983641044764020163397560), (1639425, 6897851240506974228013517703639715952162986698787595558532152201706645009963049671998056787977100917547669527941174620801664797797520640), (2361345, 1960432841868859614221248246055274680217780095018556119340700150965082841938388573707843303556056516682710517068343422274608565932032000), (2364417, 31567268942759420592892332799289744280441800553643819421920713223157836438567769854735438383151557016982009851801858078787909718907461120), (2367489, 24998447062646454283175037494839277418256452889484957170876414302004985979953548028221528906382427050107972381652380101581414065154726400), (2376705, 4734685336434046268803148093537980632370562577546113596869716771635883737288846104317976135452684215124176143738620759817672960381066240), (2379777, 22719841564758937639407857359451635015075599242046257374941954775064777675830270227203069775209693152420234248167066039399086608155608000), (2425089, 30652841990781207642423363263962351326055021732158638326656349824880054305052748470261457775039680072239678856057396496835281829952263920), (2425857, 8275431150403984466828672406478134108736406172144155948831830731676915160365012948295955682822827486084599253882400460948431292476717320)]
theorem sparseBlock105_data : sparseBlock105 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (25337375740655281048922654408755089881901096382815161963139891765677010362115528427987919081260492336769847563893983641044764020163397560 : Int) coeff1465) (CoefficientMerge.scale (30652841990781207642423363263962351326055021732158638326656349824880054305052748470261457775039680072239678856057396496835281829952263920 : Int) coeff1466)) (CoefficientMerge.merge (CoefficientMerge.scale (1960432841868859614221248246055274680217780095018556119340700150965082841938388573707843303556056516682710517068343422274608565932032000 : Int) coeff1467) (CoefficientMerge.merge (CoefficientMerge.scale (3920865683737719228442496492110549360435560190037112238681400301930165683876777147415686607112113033365421034136686844549217131864064000 : Int) coeff1468) (CoefficientMerge.scale (1960432841868859614221248246055274680217780095018556119340700150965082841938388573707843303556056516682710517068343422274608565932032000 : Int) coeff1469)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (8177316336872466750791656798566320654854411494091655809690567156851781995173419047217047370723772280201787305542095665624535866097029120 : Int) coeff1470) (CoefficientMerge.scale (28049608976688410422633651597494353122502517517959393425496207346856591212044013498193290247661436928793685884214072537830758658599274240 : Int) coeff1471)) (CoefficientMerge.merge (CoefficientMerge.scale (31567268942759420592892332799289744280441800553643819421920713223157836438567769854735438383151557016982009851801858078787909718907461120 : Int) coeff1472) (CoefficientMerge.merge (CoefficientMerge.scale (4734685336434046268803148093537980632370562577546113596869716771635883737288846104317976135452684215124176143738620759817672960381066240 : Int) coeff1473) (CoefficientMerge.scale (9469370672868092537606296187075961264741125155092227193739433543271767474577692208635952270905368430248352287477241519635345920762132480 : Int) coeff1474))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (4734685336434046268803148093537980632370562577546113596869716771635883737288846104317976135452684215124176143738620759817672960381066240 : Int) coeff1475) (CoefficientMerge.scale (3743060543023592489349377836452856727665950059868473618761120899853607868679132206835890368337540695153407588513247846013139419342950400 : Int) coeff1476)) (CoefficientMerge.merge (CoefficientMerge.scale (6897851240506974228013517703639715952162986698787595558532152201706645009963049671998056787977100917547669527941174620801664797797520640 : Int) coeff1477) (CoefficientMerge.merge (CoefficientMerge.scale (8275431150403984466828672406478134108736406172144155948831830731676915160365012948295955682822827486084599253882400460948431292476717320 : Int) coeff1478) (CoefficientMerge.scale (3983599054253139469190740690497205726881513700792726120719250928717015176171407876874917294145031826874274318533623850873605468543206400 : Int) coeff1479)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (18125581759114388879640873333831476321744421922208793510806515403413623761518598294778700148303842867301751426083430960478306703928499200 : Int) coeff1480) (CoefficientMerge.scale (24998447062646454283175037494839277418256452889484957170876414302004985979953548028221528906382427050107972381652380101581414065154726400 : Int) coeff1481)) (CoefficientMerge.merge (CoefficientMerge.scale (10007858608690101595569338700200300717464415844897011059199520301769748440615415762350187855137864176534818800948697760636287000006528000 : Int) coeff1482) (CoefficientMerge.merge (CoefficientMerge.scale (22719841564758937639407857359451635015075599242046257374941954775064777675830270227203069775209693152420234248167066039399086608155608000 : Int) coeff1483) (CoefficientMerge.scale (5895689126011050980528898428273519202393207872968633651164094327950928544242627122134238474619906439945591372749417695535589609140761600 : Int) coeff1484)))))) := by decide +kernel
theorem sparseBlock105_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock105 := by
  rw [sparseBlock105_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted1465_nonneg g t z hg hA hB ht hz hw) (weighted1466_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1467_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1468_nonneg g t z hg hA hB ht hz hw) (weighted1469_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1470_nonneg g t z hg hA hB ht hz hw) (weighted1471_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1472_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1473_nonneg g t z hg hA hB ht hz hw) (weighted1474_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted1475_nonneg g t z hg hA hB ht hz hw) (weighted1476_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1477_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1478_nonneg g t z hg hA hB ht hz hw) (weighted1479_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1480_nonneg g t z hg hA hB ht hz hw) (weighted1481_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1482_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1483_nonneg g t z hg hA hB ht hz hw) (weighted1484_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
