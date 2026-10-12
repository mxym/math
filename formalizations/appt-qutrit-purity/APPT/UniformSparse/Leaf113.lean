import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff1625 : CoefficientMerge.Poly :=
  [(3227649, 1)]
noncomputable def atom1625 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (z) ^ 3)
theorem atom1625_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1625 g t z = CoefficientMerge.eval (monomial g t z) coeff1625 := by
  norm_num [atom1625, coeff1625, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1625_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1625 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1625]
  positivity
theorem weighted1625_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (6038518574297713316116735518721737563031604889404589986639203764723726596439119794745369521683982297109520801992499491570660975793258880 : Int) coeff1625) := by
  rw [CoefficientMerge.eval_scale, ← atom1625_identity]
  exact mul_nonneg (by norm_num) (atom1625_nonneg g t z hg hA hB ht hz hw)

def coeff1626 : CoefficientMerge.Poly :=
  [(3178497, 1)]
noncomputable def atom1626 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 7) ^ 2 * (z) ^ 3)
theorem atom1626_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1626 g t z = CoefficientMerge.eval (monomial g t z) coeff1626 := by
  norm_num [atom1626, coeff1626, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1626_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1626 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1626]
  positivity
theorem weighted1626_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3623690254470355554803068830831510040938143864378068253883714235451824160466805922851330516043095703543236913503773442886264886113236960 : Int) coeff1626) := by
  rw [CoefficientMerge.eval_scale, ← atom1626_identity]
  exact mul_nonneg (by norm_num) (atom1626_nonneg g t z hg hA hB ht hz hw)

def coeff1627 : CoefficientMerge.Poly :=
  [(868356, 1)]
noncomputable def atom1627 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (t) ^ 3)
theorem atom1627_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1627 g t z = CoefficientMerge.eval (monomial g t z) coeff1627 := by
  norm_num [atom1627, coeff1627, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1627_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1627 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1627]
  positivity
theorem weighted1627_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4588974952898982320160696566185724377696504332507800564557362412094202330747777984538010773528244925387275375958036508859132524110873600 : Int) coeff1627) := by
  rw [CoefficientMerge.eval_scale, ← atom1627_identity]
  exact mul_nonneg (by norm_num) (atom1627_nonneg g t z hg hA hB ht hz hw)

def coeff1628 : CoefficientMerge.Poly :=
  [(1654788, 1)]
noncomputable def atom1628 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1628_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1628 g t z = CoefficientMerge.eval (monomial g t z) coeff1628 := by
  norm_num [atom1628, coeff1628, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1628_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1628 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1628]
  positivity
theorem weighted1628_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (20788288671733691576853479217026686237831995763326302238995465298380133417919432981066349781546589655581256336676759787168115549347833600 : Int) coeff1628) := by
  rw [CoefficientMerge.eval_scale, ← atom1628_identity]
  exact mul_nonneg (by norm_num) (atom1628_nonneg g t z hg hA hB ht hz hw)

def coeff1629 : CoefficientMerge.Poly :=
  [(2441220, 1)]
noncomputable def atom1629 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1629_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1629 g t z = CoefficientMerge.eval (monomial g t z) coeff1629 := by
  norm_num [atom1629, coeff1629, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1629_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1629 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1629]
  positivity
theorem weighted1629_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (22820583690658072340897781588500053768687467614240051974310170354470000874202883656647576239456980276247086777953210362529715539477708800 : Int) coeff1629) := by
  rw [CoefficientMerge.eval_scale, ← atom1629_identity]
  exact mul_nonneg (by norm_num) (atom1629_nonneg g t z hg hA hB ht hz hw)

def coeff1630 : CoefficientMerge.Poly :=
  [(1605636, 1)]
noncomputable def atom1630 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 7) ^ 2 * (t) ^ 2 * (z) ^ 1)
theorem atom1630_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1630 g t z = CoefficientMerge.eval (monomial g t z) coeff1630 := by
  norm_num [atom1630, coeff1630, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1630_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1630 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1630]
  positivity
theorem weighted1630_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1246014090666969156107091692075731350275132446007466878410020128524303388068592874492239213300935007785474601594889454068777644794540800 : Int) coeff1630) := by
  rw [CoefficientMerge.eval_scale, ← atom1630_identity]
  exact mul_nonneg (by norm_num) (atom1630_nonneg g t z hg hA hB ht hz hw)

def coeff1631 : CoefficientMerge.Poly :=
  [(2392068, 1)]
noncomputable def atom1631 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 7) ^ 2 * (t) ^ 1 * (z) ^ 2)
theorem atom1631_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1631 g t z = CoefficientMerge.eval (monomial g t z) coeff1631 := by
  norm_num [atom1631, coeff1631, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1631_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1631 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1631]
  positivity
theorem weighted1631_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (16182213497632336919632819125903743398795621600051156968773428317547073285571743162956011325009822423202277772160408384351556040799692800 : Int) coeff1631) := by
  rw [CoefficientMerge.eval_scale, ← atom1631_identity]
  exact mul_nonneg (by norm_num) (atom1631_nonneg g t z hg hA hB ht hz hw)

def coeff1632 : CoefficientMerge.Poly :=
  [(3227652, 1)]
noncomputable def atom1632 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (z) ^ 3)
theorem atom1632_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1632 g t z = CoefficientMerge.eval (monomial g t z) coeff1632 := by
  norm_num [atom1632, coeff1632, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1632_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1632 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1632]
  positivity
theorem weighted1632_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (13770650486336180962621185996812967617513807641895445682343591817705825023302081990362452244184388263607920542725424136249820272635778560 : Int) coeff1632) := by
  rw [CoefficientMerge.eval_scale, ← atom1632_identity]
  exact mul_nonneg (by norm_num) (atom1632_nonneg g t z hg hA hB ht hz hw)

def coeff1633 : CoefficientMerge.Poly :=
  [(3178500, 1)]
noncomputable def atom1633 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 7) ^ 2 * (z) ^ 3)
theorem atom1633_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1633 g t z = CoefficientMerge.eval (monomial g t z) coeff1633 := by
  norm_num [atom1633, coeff1633, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1633_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1633 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1633]
  positivity
theorem weighted1633_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (8968297829548436435129381736962275384464463918450035191614317110549128493660035505877768410867199125398374775453168646480984049869577920 : Int) coeff1633) := by
  rw [CoefficientMerge.eval_scale, ← atom1633_identity]
  exact mul_nonneg (by norm_num) (atom1633_nonneg g t z hg hA hB ht hz hw)

def coeff1634 : CoefficientMerge.Poly :=
  [(33792, 1)]
noncomputable def atom1634 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 7) ^ 2)
theorem atom1634_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1634 g t z = CoefficientMerge.eval (monomial g t z) coeff1634 := by
  norm_num [atom1634, coeff1634, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1634_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1634 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1634]
  positivity
theorem weighted1634_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1359673924677795394186087171016044719045318415962495075458816522394627405184340073862128850531457182066958084679155541067106260992186777600 : Int) coeff1634) := by
  rw [CoefficientMerge.eval_scale, ← atom1634_identity]
  exact mul_nonneg (by norm_num) (atom1634_nonneg g t z hg hA hB ht hz hw)

def sparseBlock113 : CoefficientMerge.Poly :=
  [(33792, 1359673924677795394186087171016044719045318415962495075458816522394627405184340073862128850531457182066958084679155541067106260992186777600), (868356, 4588974952898982320160696566185724377696504332507800564557362412094202330747777984538010773528244925387275375958036508859132524110873600), (1605636, 1246014090666969156107091692075731350275132446007466878410020128524303388068592874492239213300935007785474601594889454068777644794540800), (1654788, 20788288671733691576853479217026686237831995763326302238995465298380133417919432981066349781546589655581256336676759787168115549347833600), (2392068, 16182213497632336919632819125903743398795621600051156968773428317547073285571743162956011325009822423202277772160408384351556040799692800), (2441220, 22820583690658072340897781588500053768687467614240051974310170354470000874202883656647576239456980276247086777953210362529715539477708800), (3178497, 3623690254470355554803068830831510040938143864378068253883714235451824160466805922851330516043095703543236913503773442886264886113236960), (3178500, 8968297829548436435129381736962275384464463918450035191614317110549128493660035505877768410867199125398374775453168646480984049869577920), (3227649, 6038518574297713316116735518721737563031604889404589986639203764723726596439119794745369521683982297109520801992499491570660975793258880), (3227652, 13770650486336180962621185996812967617513807641895445682343591817705825023302081990362452244184388263607920542725424136249820272635778560)]
theorem sparseBlock113_data : sparseBlock113 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (6038518574297713316116735518721737563031604889404589986639203764723726596439119794745369521683982297109520801992499491570660975793258880 : Int) coeff1625) (CoefficientMerge.scale (3623690254470355554803068830831510040938143864378068253883714235451824160466805922851330516043095703543236913503773442886264886113236960 : Int) coeff1626)) (CoefficientMerge.merge (CoefficientMerge.scale (4588974952898982320160696566185724377696504332507800564557362412094202330747777984538010773528244925387275375958036508859132524110873600 : Int) coeff1627) (CoefficientMerge.merge (CoefficientMerge.scale (20788288671733691576853479217026686237831995763326302238995465298380133417919432981066349781546589655581256336676759787168115549347833600 : Int) coeff1628) (CoefficientMerge.scale (22820583690658072340897781588500053768687467614240051974310170354470000874202883656647576239456980276247086777953210362529715539477708800 : Int) coeff1629)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1246014090666969156107091692075731350275132446007466878410020128524303388068592874492239213300935007785474601594889454068777644794540800 : Int) coeff1630) (CoefficientMerge.scale (16182213497632336919632819125903743398795621600051156968773428317547073285571743162956011325009822423202277772160408384351556040799692800 : Int) coeff1631)) (CoefficientMerge.merge (CoefficientMerge.scale (13770650486336180962621185996812967617513807641895445682343591817705825023302081990362452244184388263607920542725424136249820272635778560 : Int) coeff1632) (CoefficientMerge.merge (CoefficientMerge.scale (8968297829548436435129381736962275384464463918450035191614317110549128493660035505877768410867199125398374775453168646480984049869577920 : Int) coeff1633) (CoefficientMerge.scale (1359673924677795394186087171016044719045318415962495075458816522394627405184340073862128850531457182066958084679155541067106260992186777600 : Int) coeff1634))))) := by decide +kernel
theorem sparseBlock113_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock113 := by
  rw [sparseBlock113_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (weighted1625_nonneg g t z hg hA hB ht hz hw) (weighted1626_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1627_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1628_nonneg g t z hg hA hB ht hz hw) (weighted1629_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1630_nonneg g t z hg hA hB ht hz hw) (weighted1631_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1632_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1633_nonneg g t z hg hA hB ht hz hw) (weighted1634_nonneg g t z hg hA hB ht hz hw)))))

end APPT.Uniform
