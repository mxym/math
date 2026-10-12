import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff0605 : CoefficientMerge.Poly :=
  [(1118209, 1)]
noncomputable def atom0605 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (z) ^ 1)
theorem atom0605_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0605 g t z = CoefficientMerge.eval (monomial g t z) coeff0605 := by
  norm_num [atom0605, coeff0605, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0605_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0605 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0605]
  positivity
theorem weighted0605_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (8965728727622764811874644957705947140997419369443551523452779589995030229304231476759975305612004640161078179043810806212227838580173721600 : Int) coeff0605) := by
  rw [CoefficientMerge.eval_scale, ← atom0605_identity]
  exact mul_nonneg (by norm_num) (atom0605_nonneg g t z hg hA hB ht hz hw)

def coeff0606 : CoefficientMerge.Poly :=
  [(81921, 1)]
noncomputable def atom0606 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1)
theorem atom0606_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0606 g t z = CoefficientMerge.eval (monomial g t z) coeff0606 := by
  norm_num [atom0606, coeff0606, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0606_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0606 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0606]
  positivity
theorem weighted0606_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5910504400936446134536719550827182708929368644546399041245789200211521514761035608147069714999747822360273539964431725912421416954493030400 : Int) coeff0606) := by
  rw [CoefficientMerge.eval_scale, ← atom0606_identity]
  exact mul_nonneg (by norm_num) (atom0606_nonneg g t z hg hA hB ht hz hw)

def coeff0607 : CoefficientMerge.Poly :=
  [(344065, 1)]
noncomputable def atom0607 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (t) ^ 1)
theorem atom0607_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0607 g t z = CoefficientMerge.eval (monomial g t z) coeff0607 := by
  norm_num [atom0607, coeff0607, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0607_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0607 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0607]
  positivity
theorem weighted0607_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (854727161797261501922389660356921879776234273060150107715719650919598103252828506907903548453647233850222934968269354622434850198931712000 : Int) coeff0607) := by
  rw [CoefficientMerge.eval_scale, ← atom0607_identity]
  exact mul_nonneg (by norm_num) (atom0607_nonneg g t z hg hA hB ht hz hw)

def coeff0608 : CoefficientMerge.Poly :=
  [(1130497, 1)]
noncomputable def atom0608 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (z) ^ 1)
theorem atom0608_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0608 g t z = CoefficientMerge.eval (monomial g t z) coeff0608 := by
  norm_num [atom0608, coeff0608, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0608_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0608 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0608]
  positivity
theorem weighted0608_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1574042737189695639899712010994839737512841997496088799922048598549337078562264976003713020780419572060727838194232707759349304640132096000 : Int) coeff0608) := by
  rw [CoefficientMerge.eval_scale, ← atom0608_identity]
  exact mul_nonneg (by norm_num) (atom0608_nonneg g t z hg hA hB ht hz hw)

def coeff0609 : CoefficientMerge.Poly :=
  [(524321, 1)]
noncomputable def atom0609 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 2 * (t) ^ 2)
theorem atom0609_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0609 g t z = CoefficientMerge.eval (monomial g t z) coeff0609 := by
  norm_num [atom0609, coeff0609, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0609_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0609 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0609]
  positivity
theorem weighted0609_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (595370593046789280371821600390089264553901038466156854476030387573301572991607766937357686032243295512308466447245975792027367449751076864 : Int) coeff0609) := by
  rw [CoefficientMerge.eval_scale, ← atom0609_identity]
  exact mul_nonneg (by norm_num) (atom0609_nonneg g t z hg hA hB ht hz hw)

def coeff0610 : CoefficientMerge.Poly :=
  [(524369, 1)]
noncomputable def atom0610 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 3) ^ 1 * (t) ^ 2)
theorem atom0610_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0610 g t z = CoefficientMerge.eval (monomial g t z) coeff0610 := by
  norm_num [atom0610, coeff0610, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0610_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0610 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0610]
  positivity
theorem weighted0610_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (676650751424047716175752884816122359085958462820989861914596774208330272186138245516016018830462515054630982926000852379349821366865134592 : Int) coeff0610) := by
  rw [CoefficientMerge.eval_scale, ← atom0610_identity]
  exact mul_nonneg (by norm_num) (atom0610_nonneg g t z hg hA hB ht hz hw)

def coeff0611 : CoefficientMerge.Poly :=
  [(524561, 1)]
noncomputable def atom0611 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 4) ^ 1 * (t) ^ 2)
theorem atom0611_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0611 g t z = CoefficientMerge.eval (monomial g t z) coeff0611 := by
  norm_num [atom0611, coeff0611, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0611_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0611 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0611]
  positivity
theorem weighted0611_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (288726086231383315925451628091002287491000160133622939099239653523014573126495212766742725441631805913100328218542451901353784581789429248 : Int) coeff0611) := by
  rw [CoefficientMerge.eval_scale, ← atom0611_identity]
  exact mul_nonneg (by norm_num) (atom0611_nonneg g t z hg hA hB ht hz hw)

def coeff0612 : CoefficientMerge.Poly :=
  [(525329, 1)]
noncomputable def atom0612 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 5) ^ 1 * (t) ^ 2)
theorem atom0612_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0612 g t z = CoefficientMerge.eval (monomial g t z) coeff0612 := by
  norm_num [atom0612, coeff0612, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0612_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0612 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0612]
  positivity
theorem weighted0612_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (59879062542744223102399423488200123272415845573827319107905496396340033631686828998869981078677778812221471090762735412531547460920060928 : Int) coeff0612) := by
  rw [CoefficientMerge.eval_scale, ← atom0612_identity]
  exact mul_nonneg (by norm_num) (atom0612_nonneg g t z hg hA hB ht hz hw)

def coeff0613 : CoefficientMerge.Poly :=
  [(540689, 1)]
noncomputable def atom0613 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 7) ^ 1 * (t) ^ 2)
theorem atom0613_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0613 g t z = CoefficientMerge.eval (monomial g t z) coeff0613 := by
  norm_num [atom0613, coeff0613, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0613_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0613 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0613]
  positivity
theorem weighted0613_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (217769233201698728979747462412541403771848714311322412743826764665785217462161441638423824674896807311489022087434565982600686748871956480 : Int) coeff0613) := by
  rw [CoefficientMerge.eval_scale, ← atom0613_identity]
  exact mul_nonneg (by norm_num) (atom0613_nonneg g t z hg hA hB ht hz hw)

def coeff0614 : CoefficientMerge.Poly :=
  [(589841, 1)]
noncomputable def atom0614 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 8) ^ 1 * (t) ^ 2)
theorem atom0614_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0614 g t z = CoefficientMerge.eval (monomial g t z) coeff0614 := by
  norm_num [atom0614, coeff0614, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0614_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0614 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0614]
  positivity
theorem weighted0614_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1023060657879290219344914697647912841189487032493620607981173795584329253559043773022356264573270941510157277991221268517180415951884492800 : Int) coeff0614) := by
  rw [CoefficientMerge.eval_scale, ← atom0614_identity]
  exact mul_nonneg (by norm_num) (atom0614_nonneg g t z hg hA hB ht hz hw)

def coeff0615 : CoefficientMerge.Poly :=
  [(1310801, 1)]
noncomputable def atom0615 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 3) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0615_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0615 g t z = CoefficientMerge.eval (monomial g t z) coeff0615 := by
  norm_num [atom0615, coeff0615, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0615_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0615 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0615]
  positivity
theorem weighted0615_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (620284821406290680858370757988231347653325785818423223266620287922257369341482255248936374060390229707709812316849805051066719928784888832 : Int) coeff0615) := by
  rw [CoefficientMerge.eval_scale, ← atom0615_identity]
  exact mul_nonneg (by norm_num) (atom0615_nonneg g t z hg hA hB ht hz hw)

def coeff0616 : CoefficientMerge.Poly :=
  [(1310993, 1)]
noncomputable def atom0616 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 4) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0616_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0616 g t z = CoefficientMerge.eval (monomial g t z) coeff0616 := by
  norm_num [atom0616, coeff0616, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0616_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0616 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0616]
  positivity
theorem weighted0616_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (934479514638967847524456009323211697060245376727222604788711461705292673332311539755970527801162805216599715119458899479681845195519928576 : Int) coeff0616) := by
  rw [CoefficientMerge.eval_scale, ← atom0616_identity]
  exact mul_nonneg (by norm_num) (atom0616_nonneg g t z hg hA hB ht hz hw)

def coeff0617 : CoefficientMerge.Poly :=
  [(1311761, 1)]
noncomputable def atom0617 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 5) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0617_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0617 g t z = CoefficientMerge.eval (monomial g t z) coeff0617 := by
  norm_num [atom0617, coeff0617, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0617_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0617 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0617]
  positivity
theorem weighted0617_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (591477396774789844997501415571894412963104875644028538048520187482377340109917465209683629780336526145589890171926568648405881979792565184 : Int) coeff0617) := by
  rw [CoefficientMerge.eval_scale, ← atom0617_identity]
  exact mul_nonneg (by norm_num) (atom0617_nonneg g t z hg hA hB ht hz hw)

def coeff0618 : CoefficientMerge.Poly :=
  [(1314833, 1)]
noncomputable def atom0618 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0618_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0618 g t z = CoefficientMerge.eval (monomial g t z) coeff0618 := by
  norm_num [atom0618, coeff0618, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0618_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0618 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0618]
  positivity
theorem weighted0618_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (41592912368730316639131114823557942784171651020362121289200101354292342122995346522879869048400737216100257978226959444571746580702453760 : Int) coeff0618) := by
  rw [CoefficientMerge.eval_scale, ← atom0618_identity]
  exact mul_nonneg (by norm_num) (atom0618_nonneg g t z hg hA hB ht hz hw)

def coeff0619 : CoefficientMerge.Poly :=
  [(1327121, 1)]
noncomputable def atom0619 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0619_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0619 g t z = CoefficientMerge.eval (monomial g t z) coeff0619 := by
  norm_num [atom0619, coeff0619, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0619_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0619 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0619]
  positivity
theorem weighted0619_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (481378206420276813776473961644896340647820652399017374024423285222082486427501513455925141876004753376152338897910748549511008452952074240 : Int) coeff0619) := by
  rw [CoefficientMerge.eval_scale, ← atom0619_identity]
  exact mul_nonneg (by norm_num) (atom0619_nonneg g t z hg hA hB ht hz hw)

def coeff0620 : CoefficientMerge.Poly :=
  [(1376273, 1)]
noncomputable def atom0620 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0620_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0620 g t z = CoefficientMerge.eval (monomial g t z) coeff0620 := by
  norm_num [atom0620, coeff0620, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0620_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0620 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0620]
  positivity
theorem weighted0620_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1647102936593316097026007456810065315528676033905685491920072982313422180641710907302868717048904227595142637547805644511005875228220364800 : Int) coeff0620) := by
  rw [CoefficientMerge.eval_scale, ← atom0620_identity]
  exact mul_nonneg (by norm_num) (atom0620_nonneg g t z hg hA hB ht hz hw)

def coeff0621 : CoefficientMerge.Poly :=
  [(524417, 1)]
noncomputable def atom0621 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 2 * (t) ^ 2)
theorem atom0621_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0621 g t z = CoefficientMerge.eval (monomial g t z) coeff0621 := by
  norm_num [atom0621, coeff0621, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0621_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0621 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0621]
  positivity
theorem weighted0621_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (872244793002656190723118615839517085629020401893689871730502211920486398259193191472511153421461392303627984322604770654009118398156513280 : Int) coeff0621) := by
  rw [CoefficientMerge.eval_scale, ← atom0621_identity]
  exact mul_nonneg (by norm_num) (atom0621_nonneg g t z hg hA hB ht hz hw)

def coeff0622 : CoefficientMerge.Poly :=
  [(524609, 1)]
noncomputable def atom0622 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 4) ^ 1 * (t) ^ 2)
theorem atom0622_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0622 g t z = CoefficientMerge.eval (monomial g t z) coeff0622 := by
  norm_num [atom0622, coeff0622, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0622_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0622 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0622]
  positivity
theorem weighted0622_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1736847812839650593566261486022424473480600470066852972428446721960161362882977130649679562026726551488121924343852845775108770045922946560 : Int) coeff0622) := by
  rw [CoefficientMerge.eval_scale, ← atom0622_identity]
  exact mul_nonneg (by norm_num) (atom0622_nonneg g t z hg hA hB ht hz hw)

def coeff0623 : CoefficientMerge.Poly :=
  [(525377, 1)]
noncomputable def atom0623 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 5) ^ 1 * (t) ^ 2)
theorem atom0623_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0623 g t z = CoefficientMerge.eval (monomial g t z) coeff0623 := by
  norm_num [atom0623, coeff0623, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0623_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0623 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0623]
  positivity
theorem weighted0623_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2053442182852416314216314923033963355657040450229179406156841748841986559426583277167704942727675985751443642807698864710020351551641815040 : Int) coeff0623) := by
  rw [CoefficientMerge.eval_scale, ← atom0623_identity]
  exact mul_nonneg (by norm_num) (atom0623_nonneg g t z hg hA hB ht hz hw)

def coeff0624 : CoefficientMerge.Poly :=
  [(528449, 1)]
noncomputable def atom0624 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 6) ^ 1 * (t) ^ 2)
theorem atom0624_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0624 g t z = CoefficientMerge.eval (monomial g t z) coeff0624 := by
  norm_num [atom0624, coeff0624, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0624_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0624 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0624]
  positivity
theorem weighted0624_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1782730681566817900316095473600384068080725587024798326284405391683241868243778108683771225312874154220487734695748780954016282391172843520 : Int) coeff0624) := by
  rw [CoefficientMerge.eval_scale, ← atom0624_identity]
  exact mul_nonneg (by norm_num) (atom0624_nonneg g t z hg hA hB ht hz hw)

def sparseBlock062 : CoefficientMerge.Poly :=
  [(81921, 5910504400936446134536719550827182708929368644546399041245789200211521514761035608147069714999747822360273539964431725912421416954493030400), (344065, 854727161797261501922389660356921879776234273060150107715719650919598103252828506907903548453647233850222934968269354622434850198931712000), (524321, 595370593046789280371821600390089264553901038466156854476030387573301572991607766937357686032243295512308466447245975792027367449751076864), (524369, 676650751424047716175752884816122359085958462820989861914596774208330272186138245516016018830462515054630982926000852379349821366865134592), (524417, 872244793002656190723118615839517085629020401893689871730502211920486398259193191472511153421461392303627984322604770654009118398156513280), (524561, 288726086231383315925451628091002287491000160133622939099239653523014573126495212766742725441631805913100328218542451901353784581789429248), (524609, 1736847812839650593566261486022424473480600470066852972428446721960161362882977130649679562026726551488121924343852845775108770045922946560), (525329, 59879062542744223102399423488200123272415845573827319107905496396340033631686828998869981078677778812221471090762735412531547460920060928), (525377, 2053442182852416314216314923033963355657040450229179406156841748841986559426583277167704942727675985751443642807698864710020351551641815040), (528449, 1782730681566817900316095473600384068080725587024798326284405391683241868243778108683771225312874154220487734695748780954016282391172843520), (540689, 217769233201698728979747462412541403771848714311322412743826764665785217462161441638423824674896807311489022087434565982600686748871956480), (589841, 1023060657879290219344914697647912841189487032493620607981173795584329253559043773022356264573270941510157277991221268517180415951884492800), (1118209, 8965728727622764811874644957705947140997419369443551523452779589995030229304231476759975305612004640161078179043810806212227838580173721600), (1130497, 1574042737189695639899712010994839737512841997496088799922048598549337078562264976003713020780419572060727838194232707759349304640132096000), (1310801, 620284821406290680858370757988231347653325785818423223266620287922257369341482255248936374060390229707709812316849805051066719928784888832), (1310993, 934479514638967847524456009323211697060245376727222604788711461705292673332311539755970527801162805216599715119458899479681845195519928576), (1311761, 591477396774789844997501415571894412963104875644028538048520187482377340109917465209683629780336526145589890171926568648405881979792565184), (1314833, 41592912368730316639131114823557942784171651020362121289200101354292342122995346522879869048400737216100257978226959444571746580702453760), (1327121, 481378206420276813776473961644896340647820652399017374024423285222082486427501513455925141876004753376152338897910748549511008452952074240), (1376273, 1647102936593316097026007456810065315528676033905685491920072982313422180641710907302868717048904227595142637547805644511005875228220364800)]
theorem sparseBlock062_data : sparseBlock062 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (8965728727622764811874644957705947140997419369443551523452779589995030229304231476759975305612004640161078179043810806212227838580173721600 : Int) coeff0605) (CoefficientMerge.scale (5910504400936446134536719550827182708929368644546399041245789200211521514761035608147069714999747822360273539964431725912421416954493030400 : Int) coeff0606)) (CoefficientMerge.merge (CoefficientMerge.scale (854727161797261501922389660356921879776234273060150107715719650919598103252828506907903548453647233850222934968269354622434850198931712000 : Int) coeff0607) (CoefficientMerge.merge (CoefficientMerge.scale (1574042737189695639899712010994839737512841997496088799922048598549337078562264976003713020780419572060727838194232707759349304640132096000 : Int) coeff0608) (CoefficientMerge.scale (595370593046789280371821600390089264553901038466156854476030387573301572991607766937357686032243295512308466447245975792027367449751076864 : Int) coeff0609)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (676650751424047716175752884816122359085958462820989861914596774208330272186138245516016018830462515054630982926000852379349821366865134592 : Int) coeff0610) (CoefficientMerge.scale (288726086231383315925451628091002287491000160133622939099239653523014573126495212766742725441631805913100328218542451901353784581789429248 : Int) coeff0611)) (CoefficientMerge.merge (CoefficientMerge.scale (59879062542744223102399423488200123272415845573827319107905496396340033631686828998869981078677778812221471090762735412531547460920060928 : Int) coeff0612) (CoefficientMerge.merge (CoefficientMerge.scale (217769233201698728979747462412541403771848714311322412743826764665785217462161441638423824674896807311489022087434565982600686748871956480 : Int) coeff0613) (CoefficientMerge.scale (1023060657879290219344914697647912841189487032493620607981173795584329253559043773022356264573270941510157277991221268517180415951884492800 : Int) coeff0614))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (620284821406290680858370757988231347653325785818423223266620287922257369341482255248936374060390229707709812316849805051066719928784888832 : Int) coeff0615) (CoefficientMerge.scale (934479514638967847524456009323211697060245376727222604788711461705292673332311539755970527801162805216599715119458899479681845195519928576 : Int) coeff0616)) (CoefficientMerge.merge (CoefficientMerge.scale (591477396774789844997501415571894412963104875644028538048520187482377340109917465209683629780336526145589890171926568648405881979792565184 : Int) coeff0617) (CoefficientMerge.merge (CoefficientMerge.scale (41592912368730316639131114823557942784171651020362121289200101354292342122995346522879869048400737216100257978226959444571746580702453760 : Int) coeff0618) (CoefficientMerge.scale (481378206420276813776473961644896340647820652399017374024423285222082486427501513455925141876004753376152338897910748549511008452952074240 : Int) coeff0619)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1647102936593316097026007456810065315528676033905685491920072982313422180641710907302868717048904227595142637547805644511005875228220364800 : Int) coeff0620) (CoefficientMerge.scale (872244793002656190723118615839517085629020401893689871730502211920486398259193191472511153421461392303627984322604770654009118398156513280 : Int) coeff0621)) (CoefficientMerge.merge (CoefficientMerge.scale (1736847812839650593566261486022424473480600470066852972428446721960161362882977130649679562026726551488121924343852845775108770045922946560 : Int) coeff0622) (CoefficientMerge.merge (CoefficientMerge.scale (2053442182852416314216314923033963355657040450229179406156841748841986559426583277167704942727675985751443642807698864710020351551641815040 : Int) coeff0623) (CoefficientMerge.scale (1782730681566817900316095473600384068080725587024798326284405391683241868243778108683771225312874154220487734695748780954016282391172843520 : Int) coeff0624)))))) := by decide +kernel
theorem sparseBlock062_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock062 := by
  rw [sparseBlock062_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted0605_nonneg g t z hg hA hB ht hz hw) (weighted0606_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0607_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0608_nonneg g t z hg hA hB ht hz hw) (weighted0609_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0610_nonneg g t z hg hA hB ht hz hw) (weighted0611_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0612_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0613_nonneg g t z hg hA hB ht hz hw) (weighted0614_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted0615_nonneg g t z hg hA hB ht hz hw) (weighted0616_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0617_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0618_nonneg g t z hg hA hB ht hz hw) (weighted0619_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0620_nonneg g t z hg hA hB ht hz hw) (weighted0621_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0622_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0623_nonneg g t z hg hA hB ht hz hw) (weighted0624_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
