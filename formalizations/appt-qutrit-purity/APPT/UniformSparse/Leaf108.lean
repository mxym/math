import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff1525 : CoefficientMerge.Poly :=
  [(1573380, 1)]
noncomputable def atom1525 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 2 * (t) ^ 2 * (z) ^ 1)
theorem atom1525_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1525 g t z = CoefficientMerge.eval (monomial g t z) coeff1525 := by
  norm_num [atom1525, coeff1525, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1525_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1525 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1525]
  positivity
theorem weighted1525_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (79778728278364010925123166776358622070328601542050222123252590856602837377299081346401866849272763215677995295684403957600610164697955840 : Int) coeff1525) := by
  rw [CoefficientMerge.eval_scale, ← atom1525_identity]
  exact mul_nonneg (by norm_num) (atom1525_nonneg g t z hg hA hB ht hz hw)

def coeff1526 : CoefficientMerge.Poly :=
  [(2359812, 1)]
noncomputable def atom1526 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 2 * (t) ^ 1 * (z) ^ 2)
theorem atom1526_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1526 g t z = CoefficientMerge.eval (monomial g t z) coeff1526 := by
  norm_num [atom1526, coeff1526, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1526_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1526 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1526]
  positivity
theorem weighted1526_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (89897053271902762762932811462129264747229875521454948714809633950788535038191600282302394460482874584642573750454415560061551504918318080 : Int) coeff1526) := by
  rw [CoefficientMerge.eval_scale, ← atom1526_identity]
  exact mul_nonneg (by norm_num) (atom1526_nonneg g t z hg hA hB ht hz hw)

def coeff1527 : CoefficientMerge.Poly :=
  [(787716, 1)]
noncomputable def atom1527 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 5) ^ 1 * (t) ^ 3)
theorem atom1527_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1527 g t z = CoefficientMerge.eval (monomial g t z) coeff1527 := by
  norm_num [atom1527, coeff1527, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1527_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1527 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1527]
  positivity
theorem weighted1527_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (11727025157008906323232637258613212200854282516912922286335013031459035822332838444557197402269432132480491474844626414946081476052275200 : Int) coeff1527) := by
  rw [CoefficientMerge.eval_scale, ← atom1527_identity]
  exact mul_nonneg (by norm_num) (atom1527_nonneg g t z hg hA hB ht hz hw)

def coeff1528 : CoefficientMerge.Poly :=
  [(1574148, 1)]
noncomputable def atom1528 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 5) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1528_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1528 g t z = CoefficientMerge.eval (monomial g t z) coeff1528 := by
  norm_num [atom1528, coeff1528, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1528_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1528 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1528]
  positivity
theorem weighted1528_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (45533488259407220692629978505019677202202836300637776929696640925497598019670619637571320846482747671208214731252229063589519316586893312 : Int) coeff1528) := by
  rw [CoefficientMerge.eval_scale, ← atom1528_identity]
  exact mul_nonneg (by norm_num) (atom1528_nonneg g t z hg hA hB ht hz hw)

def coeff1529 : CoefficientMerge.Poly :=
  [(2360580, 1)]
noncomputable def atom1529 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 5) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1529_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1529 g t z = CoefficientMerge.eval (monomial g t z) coeff1529 := by
  norm_num [atom1529, coeff1529, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1529_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1529 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1529]
  positivity
theorem weighted1529_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (55854117086450862512600787694106841798822819884975698999200788183969464564695243652192138357224226827414537909250539923512783269272039424 : Int) coeff1529) := by
  rw [CoefficientMerge.eval_scale, ← atom1529_identity]
  exact mul_nonneg (by norm_num) (atom1529_nonneg g t z hg hA hB ht hz hw)

def coeff1530 : CoefficientMerge.Poly :=
  [(790788, 1)]
noncomputable def atom1530 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (t) ^ 3)
theorem atom1530_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1530 g t z = CoefficientMerge.eval (monomial g t z) coeff1530 := by
  norm_num [atom1530, coeff1530, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1530_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1530 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1530]
  positivity
theorem weighted1530_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (16239862968605293378091209543263747693513982132325709959331570342163295281848657956854364537529191473174930229854883791164298655795819520 : Int) coeff1530) := by
  rw [CoefficientMerge.eval_scale, ← atom1530_identity]
  exact mul_nonneg (by norm_num) (atom1530_nonneg g t z hg hA hB ht hz hw)

def coeff1531 : CoefficientMerge.Poly :=
  [(1577220, 1)]
noncomputable def atom1531 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1531_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1531 g t z = CoefficientMerge.eval (monomial g t z) coeff1531 := by
  norm_num [atom1531, coeff1531, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1531_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1531 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1531]
  positivity
theorem weighted1531_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (54225070901161451472228202642003928598962380204070949278187268058330937634791060192821588964843608349611567499592075653818269402078100160 : Int) coeff1531) := by
  rw [CoefficientMerge.eval_scale, ← atom1531_identity]
  exact mul_nonneg (by norm_num) (atom1531_nonneg g t z hg hA hB ht hz hw)

def coeff1532 : CoefficientMerge.Poly :=
  [(2363652, 1)]
noncomputable def atom1532 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1532_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1532 g t z = CoefficientMerge.eval (monomial g t z) coeff1532 := by
  norm_num [atom1532, coeff1532, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1532_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1532 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1532]
  positivity
theorem weighted1532_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (58606538770653113678723431803613410901326783275018096662952289134844912173393251612082938608561069567778762925300739263630294294556236160 : Int) coeff1532) := by
  rw [CoefficientMerge.eval_scale, ← atom1532_identity]
  exact mul_nonneg (by norm_num) (atom1532_nonneg g t z hg hA hB ht hz hw)

def coeff1533 : CoefficientMerge.Poly :=
  [(803076, 1)]
noncomputable def atom1533 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (t) ^ 3)
theorem atom1533_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1533 g t z = CoefficientMerge.eval (monomial g t z) coeff1533 := by
  norm_num [atom1533, coeff1533, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1533_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1533 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1533]
  positivity
theorem weighted1533_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4502289348049211004716266254676428404306666698651121421329550348235573084230327488334103858199295591613562383866092791216704910770001920 : Int) coeff1533) := by
  rw [CoefficientMerge.eval_scale, ← atom1533_identity]
  exact mul_nonneg (by norm_num) (atom1533_nonneg g t z hg hA hB ht hz hw)

def coeff1534 : CoefficientMerge.Poly :=
  [(1589508, 1)]
noncomputable def atom1534 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1534_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1534 g t z = CoefficientMerge.eval (monomial g t z) coeff1534 := by
  norm_num [atom1534, coeff1534, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1534_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1534 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1534]
  positivity
theorem weighted1534_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (37548796542861027188146273401805640112224564563825497083906064239310576485081837005821447162667712514424168768134982216593448995345338880 : Int) coeff1534) := by
  rw [CoefficientMerge.eval_scale, ← atom1534_identity]
  exact mul_nonneg (by norm_num) (atom1534_nonneg g t z hg hA hB ht hz hw)

def coeff1535 : CoefficientMerge.Poly :=
  [(2375940, 1)]
noncomputable def atom1535 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1535_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1535 g t z = CoefficientMerge.eval (monomial g t z) coeff1535 := by
  norm_num [atom1535, coeff1535, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1535_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1535 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1535]
  positivity
theorem weighted1535_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (57501735299785381108556045556398255173604938837539545872294533268260823774220251883957760930009258437807812146638267374126901475182173200 : Int) coeff1535) := by
  rw [CoefficientMerge.eval_scale, ← atom1535_identity]
  exact mul_nonneg (by norm_num) (atom1535_nonneg g t z hg hA hB ht hz hw)

def coeff1536 : CoefficientMerge.Poly :=
  [(852228, 1)]
noncomputable def atom1536 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (t) ^ 3)
theorem atom1536_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1536 g t z = CoefficientMerge.eval (monomial g t z) coeff1536 := by
  norm_num [atom1536, coeff1536, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1536_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1536 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1536]
  positivity
theorem weighted1536_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (808027665592865041467446944867971022355039701352535117967428012774579077221495980593855989350734099673527563070118961145687283693004800 : Int) coeff1536) := by
  rw [CoefficientMerge.eval_scale, ← atom1536_identity]
  exact mul_nonneg (by norm_num) (atom1536_nonneg g t z hg hA hB ht hz hw)

def coeff1537 : CoefficientMerge.Poly :=
  [(1638660, 1)]
noncomputable def atom1537 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1537_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1537 g t z = CoefficientMerge.eval (monomial g t z) coeff1537 := by
  norm_num [atom1537, coeff1537, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1537_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1537 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1537]
  positivity
theorem weighted1537_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (13709314899510687716377670602182321517351255973570419788525300415384047194734347683479875840140255096719637799735404838117196321212572160 : Int) coeff1537) := by
  rw [CoefficientMerge.eval_scale, ← atom1537_identity]
  exact mul_nonneg (by norm_num) (atom1537_nonneg g t z hg hA hB ht hz hw)

def coeff1538 : CoefficientMerge.Poly :=
  [(2425092, 1)]
noncomputable def atom1538 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1538_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1538 g t z = CoefficientMerge.eval (monomial g t z) coeff1538 := by
  norm_num [atom1538, coeff1538, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1538_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1538 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1538]
  positivity
theorem weighted1538_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (23870532676388871176893655519157526751581362106936562207720780837117279907161312522181038003689735182499111525941692122283982249133624320 : Int) coeff1538) := by
  rw [CoefficientMerge.eval_scale, ← atom1538_identity]
  exact mul_nonneg (by norm_num) (atom1538_nonneg g t z hg hA hB ht hz hw)

def coeff1539 : CoefficientMerge.Poly :=
  [(788484, 1)]
noncomputable def atom1539 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 2 * (t) ^ 3)
theorem atom1539_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1539 g t z = CoefficientMerge.eval (monomial g t z) coeff1539 := by
  norm_num [atom1539, coeff1539, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1539_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1539 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1539]
  positivity
theorem weighted1539_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3916892688570611740572339299598939860058059544341976238532968480349087682920842111255822715995491518670368893046681974695715764895948800 : Int) coeff1539) := by
  rw [CoefficientMerge.eval_scale, ← atom1539_identity]
  exact mul_nonneg (by norm_num) (atom1539_nonneg g t z hg hA hB ht hz hw)

def coeff1540 : CoefficientMerge.Poly :=
  [(1574916, 1)]
noncomputable def atom1540 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 2 * (t) ^ 2 * (z) ^ 1)
theorem atom1540_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1540 g t z = CoefficientMerge.eval (monomial g t z) coeff1540 := by
  norm_num [atom1540, coeff1540, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1540_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1540 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1540]
  positivity
theorem weighted1540_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (7849677357809653432625307369244317721626121671464496477659664247022487369665424367151100996457469096120946350453383428805436997664358400 : Int) coeff1540) := by
  rw [CoefficientMerge.eval_scale, ← atom1540_identity]
  exact mul_nonneg (by norm_num) (atom1540_nonneg g t z hg hA hB ht hz hw)

def coeff1541 : CoefficientMerge.Poly :=
  [(2361348, 1)]
noncomputable def atom1541 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 2 * (t) ^ 1 * (z) ^ 2)
theorem atom1541_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1541 g t z = CoefficientMerge.eval (monomial g t z) coeff1541 := by
  norm_num [atom1541, coeff1541, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1541_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1541 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1541]
  positivity
theorem weighted1541_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3932784669239041692052968069645377861568062127122520239126695766673399686744582255895278280461977577450577457406701454109721232768409600 : Int) coeff1541) := by
  rw [CoefficientMerge.eval_scale, ← atom1541_identity]
  exact mul_nonneg (by norm_num) (atom1541_nonneg g t z hg hA hB ht hz hw)

def coeff1542 : CoefficientMerge.Poly :=
  [(791556, 1)]
noncomputable def atom1542 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (t) ^ 3)
theorem atom1542_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1542 g t z = CoefficientMerge.eval (monomial g t z) coeff1542 := by
  norm_num [atom1542, coeff1542, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1542_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1542 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1542]
  positivity
theorem weighted1542_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (18527482126476092060896921206478422516406487593893035136020828623693900755332925169085732487782465764582202485655313072446155046041593600 : Int) coeff1542) := by
  rw [CoefficientMerge.eval_scale, ← atom1542_identity]
  exact mul_nonneg (by norm_num) (atom1542_nonneg g t z hg hA hB ht hz hw)

def coeff1543 : CoefficientMerge.Poly :=
  [(1577988, 1)]
noncomputable def atom1543 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1543_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1543 g t z = CoefficientMerge.eval (monomial g t z) coeff1543 := by
  norm_num [atom1543, coeff1543, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1543_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1543 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1543]
  positivity
theorem weighted1543_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (37896056766478596276344798974546615141387053250046591411010430649853993809779951003226602965340468505803506426240319301499809432120353920 : Int) coeff1543) := by
  rw [CoefficientMerge.eval_scale, ← atom1543_identity]
  exact mul_nonneg (by norm_num) (atom1543_nonneg g t z hg hA hB ht hz hw)

def coeff1544 : CoefficientMerge.Poly :=
  [(2364420, 1)]
noncomputable def atom1544 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1544_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1544 g t z = CoefficientMerge.eval (monomial g t z) coeff1544 := by
  norm_num [atom1544, coeff1544, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1544_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1544 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1544]
  positivity
theorem weighted1544_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (19522545093481826929938724403258890402713023210501639004226872026370589400116397441686156590637207243684489713435427399821940226490455040 : Int) coeff1544) := by
  rw [CoefficientMerge.eval_scale, ← atom1544_identity]
  exact mul_nonneg (by norm_num) (atom1544_nonneg g t z hg hA hB ht hz hw)

def sparseBlock108 : CoefficientMerge.Poly :=
  [(787716, 11727025157008906323232637258613212200854282516912922286335013031459035822332838444557197402269432132480491474844626414946081476052275200), (788484, 3916892688570611740572339299598939860058059544341976238532968480349087682920842111255822715995491518670368893046681974695715764895948800), (790788, 16239862968605293378091209543263747693513982132325709959331570342163295281848657956854364537529191473174930229854883791164298655795819520), (791556, 18527482126476092060896921206478422516406487593893035136020828623693900755332925169085732487782465764582202485655313072446155046041593600), (803076, 4502289348049211004716266254676428404306666698651121421329550348235573084230327488334103858199295591613562383866092791216704910770001920), (852228, 808027665592865041467446944867971022355039701352535117967428012774579077221495980593855989350734099673527563070118961145687283693004800), (1573380, 79778728278364010925123166776358622070328601542050222123252590856602837377299081346401866849272763215677995295684403957600610164697955840), (1574148, 45533488259407220692629978505019677202202836300637776929696640925497598019670619637571320846482747671208214731252229063589519316586893312), (1574916, 7849677357809653432625307369244317721626121671464496477659664247022487369665424367151100996457469096120946350453383428805436997664358400), (1577220, 54225070901161451472228202642003928598962380204070949278187268058330937634791060192821588964843608349611567499592075653818269402078100160), (1577988, 37896056766478596276344798974546615141387053250046591411010430649853993809779951003226602965340468505803506426240319301499809432120353920), (1589508, 37548796542861027188146273401805640112224564563825497083906064239310576485081837005821447162667712514424168768134982216593448995345338880), (1638660, 13709314899510687716377670602182321517351255973570419788525300415384047194734347683479875840140255096719637799735404838117196321212572160), (2359812, 89897053271902762762932811462129264747229875521454948714809633950788535038191600282302394460482874584642573750454415560061551504918318080), (2360580, 55854117086450862512600787694106841798822819884975698999200788183969464564695243652192138357224226827414537909250539923512783269272039424), (2361348, 3932784669239041692052968069645377861568062127122520239126695766673399686744582255895278280461977577450577457406701454109721232768409600), (2363652, 58606538770653113678723431803613410901326783275018096662952289134844912173393251612082938608561069567778762925300739263630294294556236160), (2364420, 19522545093481826929938724403258890402713023210501639004226872026370589400116397441686156590637207243684489713435427399821940226490455040), (2375940, 57501735299785381108556045556398255173604938837539545872294533268260823774220251883957760930009258437807812146638267374126901475182173200), (2425092, 23870532676388871176893655519157526751581362106936562207720780837117279907161312522181038003689735182499111525941692122283982249133624320)]
theorem sparseBlock108_data : sparseBlock108 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (79778728278364010925123166776358622070328601542050222123252590856602837377299081346401866849272763215677995295684403957600610164697955840 : Int) coeff1525) (CoefficientMerge.scale (89897053271902762762932811462129264747229875521454948714809633950788535038191600282302394460482874584642573750454415560061551504918318080 : Int) coeff1526)) (CoefficientMerge.merge (CoefficientMerge.scale (11727025157008906323232637258613212200854282516912922286335013031459035822332838444557197402269432132480491474844626414946081476052275200 : Int) coeff1527) (CoefficientMerge.merge (CoefficientMerge.scale (45533488259407220692629978505019677202202836300637776929696640925497598019670619637571320846482747671208214731252229063589519316586893312 : Int) coeff1528) (CoefficientMerge.scale (55854117086450862512600787694106841798822819884975698999200788183969464564695243652192138357224226827414537909250539923512783269272039424 : Int) coeff1529)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (16239862968605293378091209543263747693513982132325709959331570342163295281848657956854364537529191473174930229854883791164298655795819520 : Int) coeff1530) (CoefficientMerge.scale (54225070901161451472228202642003928598962380204070949278187268058330937634791060192821588964843608349611567499592075653818269402078100160 : Int) coeff1531)) (CoefficientMerge.merge (CoefficientMerge.scale (58606538770653113678723431803613410901326783275018096662952289134844912173393251612082938608561069567778762925300739263630294294556236160 : Int) coeff1532) (CoefficientMerge.merge (CoefficientMerge.scale (4502289348049211004716266254676428404306666698651121421329550348235573084230327488334103858199295591613562383866092791216704910770001920 : Int) coeff1533) (CoefficientMerge.scale (37548796542861027188146273401805640112224564563825497083906064239310576485081837005821447162667712514424168768134982216593448995345338880 : Int) coeff1534))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (57501735299785381108556045556398255173604938837539545872294533268260823774220251883957760930009258437807812146638267374126901475182173200 : Int) coeff1535) (CoefficientMerge.scale (808027665592865041467446944867971022355039701352535117967428012774579077221495980593855989350734099673527563070118961145687283693004800 : Int) coeff1536)) (CoefficientMerge.merge (CoefficientMerge.scale (13709314899510687716377670602182321517351255973570419788525300415384047194734347683479875840140255096719637799735404838117196321212572160 : Int) coeff1537) (CoefficientMerge.merge (CoefficientMerge.scale (23870532676388871176893655519157526751581362106936562207720780837117279907161312522181038003689735182499111525941692122283982249133624320 : Int) coeff1538) (CoefficientMerge.scale (3916892688570611740572339299598939860058059544341976238532968480349087682920842111255822715995491518670368893046681974695715764895948800 : Int) coeff1539)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (7849677357809653432625307369244317721626121671464496477659664247022487369665424367151100996457469096120946350453383428805436997664358400 : Int) coeff1540) (CoefficientMerge.scale (3932784669239041692052968069645377861568062127122520239126695766673399686744582255895278280461977577450577457406701454109721232768409600 : Int) coeff1541)) (CoefficientMerge.merge (CoefficientMerge.scale (18527482126476092060896921206478422516406487593893035136020828623693900755332925169085732487782465764582202485655313072446155046041593600 : Int) coeff1542) (CoefficientMerge.merge (CoefficientMerge.scale (37896056766478596276344798974546615141387053250046591411010430649853993809779951003226602965340468505803506426240319301499809432120353920 : Int) coeff1543) (CoefficientMerge.scale (19522545093481826929938724403258890402713023210501639004226872026370589400116397441686156590637207243684489713435427399821940226490455040 : Int) coeff1544)))))) := by decide +kernel
theorem sparseBlock108_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock108 := by
  rw [sparseBlock108_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted1525_nonneg g t z hg hA hB ht hz hw) (weighted1526_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1527_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1528_nonneg g t z hg hA hB ht hz hw) (weighted1529_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1530_nonneg g t z hg hA hB ht hz hw) (weighted1531_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1532_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1533_nonneg g t z hg hA hB ht hz hw) (weighted1534_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted1535_nonneg g t z hg hA hB ht hz hw) (weighted1536_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1537_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1538_nonneg g t z hg hA hB ht hz hw) (weighted1539_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1540_nonneg g t z hg hA hB ht hz hw) (weighted1541_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1542_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1543_nonneg g t z hg hA hB ht hz hw) (weighted1544_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
