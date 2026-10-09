import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff0705 : CoefficientMerge.Poly :=
  [(4164, 1)]
noncomputable def atom0705 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 6) ^ 1)
theorem atom0705_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0705 g t z = CoefficientMerge.eval (monomial g t z) coeff0705 := by
  norm_num [atom0705, coeff0705, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0705_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0705 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0705]
  positivity
theorem weighted0705_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (10188838600404403338547618893562409508269327006008474656475091621246537484998842681562125887258990700334072319063802062778948293458053693440 : Int) coeff0705) := by
  rw [CoefficientMerge.eval_scale, ← atom0705_identity]
  exact mul_nonneg (by norm_num) (atom0705_nonneg g t z hg hA hB ht hz hw)

def coeff0706 : CoefficientMerge.Poly :=
  [(262276, 1)]
noncomputable def atom0706 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 2 * (t) ^ 1)
theorem atom0706_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0706 g t z = CoefficientMerge.eval (monomial g t z) coeff0706 := by
  norm_num [atom0706, coeff0706, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0706_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0706 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0706]
  positivity
theorem weighted0706_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1654320025097901704103413631738417608663771998456044826390077660544150732158365190527070806311826049713257454984942095000017228140319621120 : Int) coeff0706) := by
  rw [CoefficientMerge.eval_scale, ← atom0706_identity]
  exact mul_nonneg (by norm_num) (atom0706_nonneg g t z hg hA hB ht hz hw)

def coeff0707 : CoefficientMerge.Poly :=
  [(262468, 1)]
noncomputable def atom0707 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 4) ^ 1 * (t) ^ 1)
theorem atom0707_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0707 g t z = CoefficientMerge.eval (monomial g t z) coeff0707 := by
  norm_num [atom0707, coeff0707, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0707_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0707 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0707]
  positivity
theorem weighted0707_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (601970136747293110238821990143837749207554057449616402002443718272918723254302203865960307363856180849878706412649407192884093315150883840 : Int) coeff0707) := by
  rw [CoefficientMerge.eval_scale, ← atom0707_identity]
  exact mul_nonneg (by norm_num) (atom0707_nonneg g t z hg hA hB ht hz hw)

def coeff0708 : CoefficientMerge.Poly :=
  [(266308, 1)]
noncomputable def atom0708 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 6) ^ 1 * (t) ^ 1)
theorem atom0708_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0708 g t z = CoefficientMerge.eval (monomial g t z) coeff0708 := by
  norm_num [atom0708, coeff0708, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0708_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0708 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0708]
  positivity
theorem weighted0708_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1761892862356485761914598481898501495011503453822031949142509805661592433180326300924203241058245075661551774118906016540767841368600033280 : Int) coeff0708) := by
  rw [CoefficientMerge.eval_scale, ← atom0708_identity]
  exact mul_nonneg (by norm_num) (atom0708_nonneg g t z hg hA hB ht hz hw)

def coeff0709 : CoefficientMerge.Poly :=
  [(278596, 1)]
noncomputable def atom0709 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 7) ^ 1 * (t) ^ 1)
theorem atom0709_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0709 g t z = CoefficientMerge.eval (monomial g t z) coeff0709 := by
  norm_num [atom0709, coeff0709, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0709_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0709 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0709]
  positivity
theorem weighted0709_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1071148891907523397021277938518519652080158915082093629342348307169847822622726660053966758644738422119595421862259630262800413213496586240 : Int) coeff0709) := by
  rw [CoefficientMerge.eval_scale, ← atom0709_identity]
  exact mul_nonneg (by norm_num) (atom0709_nonneg g t z hg hA hB ht hz hw)

def coeff0710 : CoefficientMerge.Poly :=
  [(327748, 1)]
noncomputable def atom0710 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 8) ^ 1 * (t) ^ 1)
theorem atom0710_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0710 g t z = CoefficientMerge.eval (monomial g t z) coeff0710 := by
  norm_num [atom0710, coeff0710, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0710_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0710 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0710]
  positivity
theorem weighted0710_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (811017691260117797497264866776671691707430238239116888153444882653813509348442368357720328333127304605264268222614965253205931340089139200 : Int) coeff0710) := by
  rw [CoefficientMerge.eval_scale, ← atom0710_identity]
  exact mul_nonneg (by norm_num) (atom0710_nonneg g t z hg hA hB ht hz hw)

def coeff0711 : CoefficientMerge.Poly :=
  [(1048708, 1)]
noncomputable def atom0711 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 2 * (z) ^ 1)
theorem atom0711_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0711 g t z = CoefficientMerge.eval (monomial g t z) coeff0711 := by
  norm_num [atom0711, coeff0711, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0711_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0711 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0711]
  positivity
theorem weighted0711_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5903592309007414896937631652407391430264140653807674972895257465623715554580346621245570386252728464417274955231531231694877884375729122816 : Int) coeff0711) := by
  rw [CoefficientMerge.eval_scale, ← atom0711_identity]
  exact mul_nonneg (by norm_num) (atom0711_nonneg g t z hg hA hB ht hz hw)

def coeff0712 : CoefficientMerge.Poly :=
  [(1048900, 1)]
noncomputable def atom0712 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 4) ^ 1 * (z) ^ 1)
theorem atom0712_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0712 g t z = CoefficientMerge.eval (monomial g t z) coeff0712 := by
  norm_num [atom0712, coeff0712, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0712_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0712 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0712]
  positivity
theorem weighted0712_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (6397639016456406070846866843805313728013016213551488015054258207172052591185625631689568055674634505524496108094632168249327133134973642752 : Int) coeff0712) := by
  rw [CoefficientMerge.eval_scale, ← atom0712_identity]
  exact mul_nonneg (by norm_num) (atom0712_nonneg g t z hg hA hB ht hz hw)

def coeff0713 : CoefficientMerge.Poly :=
  [(1049668, 1)]
noncomputable def atom0713 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 5) ^ 1 * (z) ^ 1)
theorem atom0713_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0713 g t z = CoefficientMerge.eval (monomial g t z) coeff0713 := by
  norm_num [atom0713, coeff0713, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0713_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0713 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0713]
  positivity
theorem weighted0713_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3921769686787353509408796193904451039409606429424733807940885525632357872345028357593226933264896671257111506935353892123885997155395519744 : Int) coeff0713) := by
  rw [CoefficientMerge.eval_scale, ← atom0713_identity]
  exact mul_nonneg (by norm_num) (atom0713_nonneg g t z hg hA hB ht hz hw)

def coeff0714 : CoefficientMerge.Poly :=
  [(1052740, 1)]
noncomputable def atom0714 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 6) ^ 1 * (z) ^ 1)
theorem atom0714_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0714 g t z = CoefficientMerge.eval (monomial g t z) coeff0714 := by
  norm_num [atom0714, coeff0714, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0714_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0714 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0714]
  positivity
theorem weighted0714_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4108016928877134423089309267643260732957668610875862632253539487405506563073467858311656182251407571082359429040754703359056958240219603200 : Int) coeff0714) := by
  rw [CoefficientMerge.eval_scale, ← atom0714_identity]
  exact mul_nonneg (by norm_num) (atom0714_nonneg g t z hg hA hB ht hz hw)

def coeff0715 : CoefficientMerge.Poly :=
  [(1065028, 1)]
noncomputable def atom0715 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 7) ^ 1 * (z) ^ 1)
theorem atom0715_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0715 g t z = CoefficientMerge.eval (monomial g t z) coeff0715 := by
  norm_num [atom0715, coeff0715, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0715_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0715 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0715]
  positivity
theorem weighted0715_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4385132302961496684890779186647004784866394638545868697473903999500154170307414316213505563280472793927176308151402098414453821329901134080 : Int) coeff0715) := by
  rw [CoefficientMerge.eval_scale, ← atom0715_identity]
  exact mul_nonneg (by norm_num) (atom0715_nonneg g t z hg hA hB ht hz hw)

def coeff0716 : CoefficientMerge.Poly :=
  [(1114180, 1)]
noncomputable def atom0716 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 8) ^ 1 * (z) ^ 1)
theorem atom0716_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0716 g t z = CoefficientMerge.eval (monomial g t z) coeff0716 := by
  norm_num [atom0716, coeff0716, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0716_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0716 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0716]
  positivity
theorem weighted0716_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5428980529150641766162015239675200837864815349201960677373285923699127905891003662254702163218081514874673096500612037296700502417689821440 : Int) coeff0716) := by
  rw [CoefficientMerge.eval_scale, ← atom0716_identity]
  exact mul_nonneg (by norm_num) (atom0716_nonneg g t z hg hA hB ht hz hw)

def coeff0717 : CoefficientMerge.Poly :=
  [(4356, 1)]
noncomputable def atom0717 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1)
theorem atom0717_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0717 g t z = CoefficientMerge.eval (monomial g t z) coeff0717 := by
  norm_num [atom0717, coeff0717, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0717_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0717 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0717]
  positivity
theorem weighted0717_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (7428597057964665460679175700061647677665827421856458367081313340644874967980928471565273701405282585820114103028988415400987196478383226880 : Int) coeff0717) := by
  rw [CoefficientMerge.eval_scale, ← atom0717_identity]
  exact mul_nonneg (by norm_num) (atom0717_nonneg g t z hg hA hB ht hz hw)

def coeff0718 : CoefficientMerge.Poly :=
  [(16644, 1)]
noncomputable def atom0718 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1)
theorem atom0718_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0718 g t z = CoefficientMerge.eval (monomial g t z) coeff0718 := by
  norm_num [atom0718, coeff0718, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0718_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0718 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0718]
  positivity
theorem weighted0718_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3980817573820781422158827816986862582293885113788824436089606543770611445660625001785948205495891189406373531831092685027787146550701670400 : Int) coeff0718) := by
  rw [CoefficientMerge.eval_scale, ← atom0718_identity]
  exact mul_nonneg (by norm_num) (atom0718_nonneg g t z hg hA hB ht hz hw)

def coeff0719 : CoefficientMerge.Poly :=
  [(65796, 1)]
noncomputable def atom0719 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1)
theorem atom0719_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0719 g t z = CoefficientMerge.eval (monomial g t z) coeff0719 := by
  norm_num [atom0719, coeff0719, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0719_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0719 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0719]
  positivity
theorem weighted0719_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3624564592464298700269956697356353469448612306189473715241585437402424151442680253278085296855487264307942824575904025450440930059150950400 : Int) coeff0719) := by
  rw [CoefficientMerge.eval_scale, ← atom0719_identity]
  exact mul_nonneg (by norm_num) (atom0719_nonneg g t z hg hA hB ht hz hw)

def coeff0720 : CoefficientMerge.Poly :=
  [(266500, 1)]
noncomputable def atom0720 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (t) ^ 1)
theorem atom0720_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0720 g t z = CoefficientMerge.eval (monomial g t z) coeff0720 := by
  norm_num [atom0720, coeff0720, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0720_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0720 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0720]
  positivity
theorem weighted0720_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4459423947897815536511522314368500742940175391251145475734414838652973016579490686145034316129671847022241032018450023894589603239152168960 : Int) coeff0720) := by
  rw [CoefficientMerge.eval_scale, ← atom0720_identity]
  exact mul_nonneg (by norm_num) (atom0720_nonneg g t z hg hA hB ht hz hw)

def coeff0721 : CoefficientMerge.Poly :=
  [(278788, 1)]
noncomputable def atom0721 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (t) ^ 1)
theorem atom0721_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0721 g t z = CoefficientMerge.eval (monomial g t z) coeff0721 := by
  norm_num [atom0721, coeff0721, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0721_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0721 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0721]
  positivity
theorem weighted0721_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4735866699911100992371215180384890079659985208392525424163245638339764615107335177437610579124532043437955690771463730248234092168538030080 : Int) coeff0721) := by
  rw [CoefficientMerge.eval_scale, ← atom0721_identity]
  exact mul_nonneg (by norm_num) (atom0721_nonneg g t z hg hA hB ht hz hw)

def coeff0722 : CoefficientMerge.Poly :=
  [(327940, 1)]
noncomputable def atom0722 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (t) ^ 1)
theorem atom0722_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0722 g t z = CoefficientMerge.eval (monomial g t z) coeff0722 := by
  norm_num [atom0722, coeff0722, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0722_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0722 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0722]
  positivity
theorem weighted0722_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (10842213093405267718299322343299466677718685015938772880414724018361207002172989207114065458961298563038840713469736217706857971228494643200 : Int) coeff0722) := by
  rw [CoefficientMerge.eval_scale, ← atom0722_identity]
  exact mul_nonneg (by norm_num) (atom0722_nonneg g t z hg hA hB ht hz hw)

def coeff0723 : CoefficientMerge.Poly :=
  [(1049092, 1)]
noncomputable def atom0723 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 2 * (z) ^ 1)
theorem atom0723_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0723 g t z = CoefficientMerge.eval (monomial g t z) coeff0723 := by
  norm_num [atom0723, coeff0723, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0723_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0723 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0723]
  positivity
theorem weighted0723_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4349908915618329958619020234553211733604112687599566766231310825968661379871192101764633095223563009793116638067057102841428491225082741760 : Int) coeff0723) := by
  rw [CoefficientMerge.eval_scale, ← atom0723_identity]
  exact mul_nonneg (by norm_num) (atom0723_nonneg g t z hg hA hB ht hz hw)

def coeff0724 : CoefficientMerge.Poly :=
  [(1049860, 1)]
noncomputable def atom0724 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 5) ^ 1 * (z) ^ 1)
theorem atom0724_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0724 g t z = CoefficientMerge.eval (monomial g t z) coeff0724 := by
  norm_num [atom0724, coeff0724, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0724_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0724 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0724]
  positivity
theorem weighted0724_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (7380910367012106349096448480395578670268608294300719986057927290868304955969018589507065881296884103636660898612096507530352922299631730688 : Int) coeff0724) := by
  rw [CoefficientMerge.eval_scale, ← atom0724_identity]
  exact mul_nonneg (by norm_num) (atom0724_nonneg g t z hg hA hB ht hz hw)

def sparseBlock067 : CoefficientMerge.Poly :=
  [(4164, 10188838600404403338547618893562409508269327006008474656475091621246537484998842681562125887258990700334072319063802062778948293458053693440), (4356, 7428597057964665460679175700061647677665827421856458367081313340644874967980928471565273701405282585820114103028988415400987196478383226880), (16644, 3980817573820781422158827816986862582293885113788824436089606543770611445660625001785948205495891189406373531831092685027787146550701670400), (65796, 3624564592464298700269956697356353469448612306189473715241585437402424151442680253278085296855487264307942824575904025450440930059150950400), (262276, 1654320025097901704103413631738417608663771998456044826390077660544150732158365190527070806311826049713257454984942095000017228140319621120), (262468, 601970136747293110238821990143837749207554057449616402002443718272918723254302203865960307363856180849878706412649407192884093315150883840), (266308, 1761892862356485761914598481898501495011503453822031949142509805661592433180326300924203241058245075661551774118906016540767841368600033280), (266500, 4459423947897815536511522314368500742940175391251145475734414838652973016579490686145034316129671847022241032018450023894589603239152168960), (278596, 1071148891907523397021277938518519652080158915082093629342348307169847822622726660053966758644738422119595421862259630262800413213496586240), (278788, 4735866699911100992371215180384890079659985208392525424163245638339764615107335177437610579124532043437955690771463730248234092168538030080), (327748, 811017691260117797497264866776671691707430238239116888153444882653813509348442368357720328333127304605264268222614965253205931340089139200), (327940, 10842213093405267718299322343299466677718685015938772880414724018361207002172989207114065458961298563038840713469736217706857971228494643200), (1048708, 5903592309007414896937631652407391430264140653807674972895257465623715554580346621245570386252728464417274955231531231694877884375729122816), (1048900, 6397639016456406070846866843805313728013016213551488015054258207172052591185625631689568055674634505524496108094632168249327133134973642752), (1049092, 4349908915618329958619020234553211733604112687599566766231310825968661379871192101764633095223563009793116638067057102841428491225082741760), (1049668, 3921769686787353509408796193904451039409606429424733807940885525632357872345028357593226933264896671257111506935353892123885997155395519744), (1049860, 7380910367012106349096448480395578670268608294300719986057927290868304955969018589507065881296884103636660898612096507530352922299631730688), (1052740, 4108016928877134423089309267643260732957668610875862632253539487405506563073467858311656182251407571082359429040754703359056958240219603200), (1065028, 4385132302961496684890779186647004784866394638545868697473903999500154170307414316213505563280472793927176308151402098414453821329901134080), (1114180, 5428980529150641766162015239675200837864815349201960677373285923699127905891003662254702163218081514874673096500612037296700502417689821440)]
theorem sparseBlock067_data : sparseBlock067 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (10188838600404403338547618893562409508269327006008474656475091621246537484998842681562125887258990700334072319063802062778948293458053693440 : Int) coeff0705) (CoefficientMerge.scale (1654320025097901704103413631738417608663771998456044826390077660544150732158365190527070806311826049713257454984942095000017228140319621120 : Int) coeff0706)) (CoefficientMerge.merge (CoefficientMerge.scale (601970136747293110238821990143837749207554057449616402002443718272918723254302203865960307363856180849878706412649407192884093315150883840 : Int) coeff0707) (CoefficientMerge.merge (CoefficientMerge.scale (1761892862356485761914598481898501495011503453822031949142509805661592433180326300924203241058245075661551774118906016540767841368600033280 : Int) coeff0708) (CoefficientMerge.scale (1071148891907523397021277938518519652080158915082093629342348307169847822622726660053966758644738422119595421862259630262800413213496586240 : Int) coeff0709)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (811017691260117797497264866776671691707430238239116888153444882653813509348442368357720328333127304605264268222614965253205931340089139200 : Int) coeff0710) (CoefficientMerge.scale (5903592309007414896937631652407391430264140653807674972895257465623715554580346621245570386252728464417274955231531231694877884375729122816 : Int) coeff0711)) (CoefficientMerge.merge (CoefficientMerge.scale (6397639016456406070846866843805313728013016213551488015054258207172052591185625631689568055674634505524496108094632168249327133134973642752 : Int) coeff0712) (CoefficientMerge.merge (CoefficientMerge.scale (3921769686787353509408796193904451039409606429424733807940885525632357872345028357593226933264896671257111506935353892123885997155395519744 : Int) coeff0713) (CoefficientMerge.scale (4108016928877134423089309267643260732957668610875862632253539487405506563073467858311656182251407571082359429040754703359056958240219603200 : Int) coeff0714))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (4385132302961496684890779186647004784866394638545868697473903999500154170307414316213505563280472793927176308151402098414453821329901134080 : Int) coeff0715) (CoefficientMerge.scale (5428980529150641766162015239675200837864815349201960677373285923699127905891003662254702163218081514874673096500612037296700502417689821440 : Int) coeff0716)) (CoefficientMerge.merge (CoefficientMerge.scale (7428597057964665460679175700061647677665827421856458367081313340644874967980928471565273701405282585820114103028988415400987196478383226880 : Int) coeff0717) (CoefficientMerge.merge (CoefficientMerge.scale (3980817573820781422158827816986862582293885113788824436089606543770611445660625001785948205495891189406373531831092685027787146550701670400 : Int) coeff0718) (CoefficientMerge.scale (3624564592464298700269956697356353469448612306189473715241585437402424151442680253278085296855487264307942824575904025450440930059150950400 : Int) coeff0719)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (4459423947897815536511522314368500742940175391251145475734414838652973016579490686145034316129671847022241032018450023894589603239152168960 : Int) coeff0720) (CoefficientMerge.scale (4735866699911100992371215180384890079659985208392525424163245638339764615107335177437610579124532043437955690771463730248234092168538030080 : Int) coeff0721)) (CoefficientMerge.merge (CoefficientMerge.scale (10842213093405267718299322343299466677718685015938772880414724018361207002172989207114065458961298563038840713469736217706857971228494643200 : Int) coeff0722) (CoefficientMerge.merge (CoefficientMerge.scale (4349908915618329958619020234553211733604112687599566766231310825968661379871192101764633095223563009793116638067057102841428491225082741760 : Int) coeff0723) (CoefficientMerge.scale (7380910367012106349096448480395578670268608294300719986057927290868304955969018589507065881296884103636660898612096507530352922299631730688 : Int) coeff0724)))))) := by decide +kernel
theorem sparseBlock067_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock067 := by
  rw [sparseBlock067_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted0705_nonneg g t z hg hA hB ht hz hw) (weighted0706_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0707_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0708_nonneg g t z hg hA hB ht hz hw) (weighted0709_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0710_nonneg g t z hg hA hB ht hz hw) (weighted0711_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0712_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0713_nonneg g t z hg hA hB ht hz hw) (weighted0714_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted0715_nonneg g t z hg hA hB ht hz hw) (weighted0716_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0717_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0718_nonneg g t z hg hA hB ht hz hw) (weighted0719_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0720_nonneg g t z hg hA hB ht hz hw) (weighted0721_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0722_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0723_nonneg g t z hg hA hB ht hz hw) (weighted0724_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
