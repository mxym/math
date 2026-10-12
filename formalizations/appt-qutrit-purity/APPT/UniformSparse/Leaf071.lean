import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff0785 : CoefficientMerge.Poly :=
  [(1376516, 1)]
noncomputable def atom0785 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0785_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0785 g t z = CoefficientMerge.eval (monomial g t z) coeff0785 := by
  norm_num [atom0785, coeff0785, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0785_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0785 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0785]
  positivity
theorem weighted0785_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1992887904883259568723761790254750250191912570810791833574275277752172150495203664495181115073920888177107753549059276434490684013585740800 : Int) coeff0785) := by
  rw [CoefficientMerge.eval_scale, ← atom0785_identity]
  exact mul_nonneg (by norm_num) (atom0785_nonneg g t z hg hA hB ht hz hw)

def coeff0786 : CoefficientMerge.Poly :=
  [(526340, 1)]
noncomputable def atom0786 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 2 * (t) ^ 2)
theorem atom0786_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0786 g t z = CoefficientMerge.eval (monomial g t z) coeff0786 := by
  norm_num [atom0786, coeff0786, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0786_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0786 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0786]
  positivity
theorem weighted0786_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1842748444850467948862547707102209651311792914114207598598345824898067879337667701360496383237196953133739901902303349005873954517824716800 : Int) coeff0786) := by
  rw [CoefficientMerge.eval_scale, ← atom0786_identity]
  exact mul_nonneg (by norm_num) (atom0786_nonneg g t z hg hA hB ht hz hw)

def coeff0787 : CoefficientMerge.Poly :=
  [(529412, 1)]
noncomputable def atom0787 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (t) ^ 2)
theorem atom0787_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0787 g t z = CoefficientMerge.eval (monomial g t z) coeff0787 := by
  norm_num [atom0787, coeff0787, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0787_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0787 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0787]
  positivity
theorem weighted0787_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2403392112976628415354072539564132099221894685500678587597787409063193013578888126214031887089098449952179409545776762221242418898552345600 : Int) coeff0787) := by
  rw [CoefficientMerge.eval_scale, ← atom0787_identity]
  exact mul_nonneg (by norm_num) (atom0787_nonneg g t z hg hA hB ht hz hw)

def coeff0788 : CoefficientMerge.Poly :=
  [(541700, 1)]
noncomputable def atom0788 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (t) ^ 2)
theorem atom0788_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0788 g t z = CoefficientMerge.eval (monomial g t z) coeff0788 := by
  norm_num [atom0788, coeff0788, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0788_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0788 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0788]
  positivity
theorem weighted0788_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2010749954280139307528202654957447768400638880204357313325770986176779253842691024216775012202362567426175446994527636717659681899881420800 : Int) coeff0788) := by
  rw [CoefficientMerge.eval_scale, ← atom0788_identity]
  exact mul_nonneg (by norm_num) (atom0788_nonneg g t z hg hA hB ht hz hw)

def coeff0789 : CoefficientMerge.Poly :=
  [(590852, 1)]
noncomputable def atom0789 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (t) ^ 2)
theorem atom0789_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0789 g t z = CoefficientMerge.eval (monomial g t z) coeff0789 := by
  norm_num [atom0789, coeff0789, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0789_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0789 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0789]
  positivity
theorem weighted0789_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1882870106496697009582519601646580881449769231147369547431702913542555080370211197963178538737490365674966516182217656406369286259049830400 : Int) coeff0789) := by
  rw [CoefficientMerge.eval_scale, ← atom0789_identity]
  exact mul_nonneg (by norm_num) (atom0789_nonneg g t z hg hA hB ht hz hw)

def coeff0790 : CoefficientMerge.Poly :=
  [(1312772, 1)]
noncomputable def atom0790 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 2 * (t) ^ 1 * (z) ^ 1)
theorem atom0790_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0790 g t z = CoefficientMerge.eval (monomial g t z) coeff0790 := by
  norm_num [atom0790, coeff0790, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0790_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0790 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0790]
  positivity
theorem weighted0790_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3683602935158488969840493007204004350538756060676008062684000902535599598465138868275052639327062886442158647769681324366462851226216857600 : Int) coeff0790) := by
  rw [CoefficientMerge.eval_scale, ← atom0790_identity]
  exact mul_nonneg (by norm_num) (atom0790_nonneg g t z hg hA hB ht hz hw)

def coeff0791 : CoefficientMerge.Poly :=
  [(1315844, 1)]
noncomputable def atom0791 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0791_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0791 g t z = CoefficientMerge.eval (monomial g t z) coeff0791 := by
  norm_num [atom0791, coeff0791, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0791_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0791 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0791]
  positivity
theorem weighted0791_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5212755731019817450642520602761922725050616756075479804012966950770387750769676304626243292941393290896112737761314796530982404486778042880 : Int) coeff0791) := by
  rw [CoefficientMerge.eval_scale, ← atom0791_identity]
  exact mul_nonneg (by norm_num) (atom0791_nonneg g t z hg hA hB ht hz hw)

def coeff0792 : CoefficientMerge.Poly :=
  [(1328132, 1)]
noncomputable def atom0792 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0792_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0792 g t z = CoefficientMerge.eval (monomial g t z) coeff0792 := by
  norm_num [atom0792, coeff0792, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0792_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0792 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0792]
  positivity
theorem weighted0792_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4072828866468742578028487760310608899808215922211527213692587969238538473010593111175485468130285818827299346164049876464656439625467648000 : Int) coeff0792) := by
  rw [CoefficientMerge.eval_scale, ← atom0792_identity]
  exact mul_nonneg (by norm_num) (atom0792_nonneg g t z hg hA hB ht hz hw)

def coeff0793 : CoefficientMerge.Poly :=
  [(1377284, 1)]
noncomputable def atom0793 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0793_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0793 g t z = CoefficientMerge.eval (monomial g t z) coeff0793 := by
  norm_num [atom0793, coeff0793, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0793_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0793 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0793]
  positivity
theorem weighted0793_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3942145137399080880622514921827032758671281445453906891198576785746918955193923377002155018770075554158248830901698415799074876522074210560 : Int) coeff0793) := by
  rw [CoefficientMerge.eval_scale, ← atom0793_identity]
  exact mul_nonneg (by norm_num) (atom0793_nonneg g t z hg hA hB ht hz hw)

def coeff0794 : CoefficientMerge.Poly :=
  [(532484, 1)]
noncomputable def atom0794 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 6) ^ 2 * (t) ^ 2)
theorem atom0794_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0794 g t z = CoefficientMerge.eval (monomial g t z) coeff0794 := by
  norm_num [atom0794, coeff0794, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0794_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0794 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0794]
  positivity
theorem weighted0794_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (567441965115353133013669502717203140732273422279989264392975984845355863006954104208431679387030265449594790512112575284769550769568486400 : Int) coeff0794) := by
  rw [CoefficientMerge.eval_scale, ← atom0794_identity]
  exact mul_nonneg (by norm_num) (atom0794_nonneg g t z hg hA hB ht hz hw)

def coeff0795 : CoefficientMerge.Poly :=
  [(544772, 1)]
noncomputable def atom0795 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (t) ^ 2)
theorem atom0795_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0795 g t z = CoefficientMerge.eval (monomial g t z) coeff0795 := by
  norm_num [atom0795, coeff0795, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0795_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0795 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0795]
  positivity
theorem weighted0795_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1152077407463965258073294752573671377117589504420134478509533695525988808176711006839388299054859426508435738535277205271335663488100736000 : Int) coeff0795) := by
  rw [CoefficientMerge.eval_scale, ← atom0795_identity]
  exact mul_nonneg (by norm_num) (atom0795_nonneg g t z hg hA hB ht hz hw)

def coeff0796 : CoefficientMerge.Poly :=
  [(593924, 1)]
noncomputable def atom0796 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (t) ^ 2)
theorem atom0796_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0796 g t z = CoefficientMerge.eval (monomial g t z) coeff0796 := by
  norm_num [atom0796, coeff0796, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0796_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0796 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0796]
  positivity
theorem weighted0796_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (526431998159194281866163826459723818272863479697930174803620454211541120704771382487611754414051827786348668327011910007906015048371123200 : Int) coeff0796) := by
  rw [CoefficientMerge.eval_scale, ← atom0796_identity]
  exact mul_nonneg (by norm_num) (atom0796_nonneg g t z hg hA hB ht hz hw)

def coeff0797 : CoefficientMerge.Poly :=
  [(1318916, 1)]
noncomputable def atom0797 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 6) ^ 2 * (t) ^ 1 * (z) ^ 1)
theorem atom0797_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0797 g t z = CoefficientMerge.eval (monomial g t z) coeff0797 := by
  norm_num [atom0797, coeff0797, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0797_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0797 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0797]
  positivity
theorem weighted0797_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1602652081129926504142852504522705404207134337718098564928908839967961209517229840993320383517071529266273937488524772653744219920664217600 : Int) coeff0797) := by
  rw [CoefficientMerge.eval_scale, ← atom0797_identity]
  exact mul_nonneg (by norm_num) (atom0797_nonneg g t z hg hA hB ht hz hw)

def coeff0798 : CoefficientMerge.Poly :=
  [(1331204, 1)]
noncomputable def atom0798 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0798_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0798 g t z = CoefficientMerge.eval (monomial g t z) coeff0798 := by
  norm_num [atom0798, coeff0798, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0798_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0798 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0798]
  positivity
theorem weighted0798_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2358497570625382883162280609956689226042489881168144807847000798172876480394947926538259728906170814795641405418692155823275203707121792000 : Int) coeff0798) := by
  rw [CoefficientMerge.eval_scale, ← atom0798_identity]
  exact mul_nonneg (by norm_num) (atom0798_nonneg g t z hg hA hB ht hz hw)

def coeff0799 : CoefficientMerge.Poly :=
  [(1380356, 1)]
noncomputable def atom0799 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0799_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0799 g t z = CoefficientMerge.eval (monomial g t z) coeff0799 := by
  norm_num [atom0799, coeff0799, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0799_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0799 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0799]
  positivity
theorem weighted0799_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1599666156023235732050778379817574671899637403680895039719997841521983773870473077586653136574049558948379467931758122382909879871303843840 : Int) coeff0799) := by
  rw [CoefficientMerge.eval_scale, ← atom0799_identity]
  exact mul_nonneg (by norm_num) (atom0799_nonneg g t z hg hA hB ht hz hw)

def coeff0800 : CoefficientMerge.Poly :=
  [(294916, 1)]
noncomputable def atom0800 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 7) ^ 2 * (t) ^ 1)
theorem atom0800_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0800 g t z = CoefficientMerge.eval (monomial g t z) coeff0800 := by
  norm_num [atom0800, coeff0800, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0800_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0800 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0800]
  positivity
theorem weighted0800_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1574204395298749144416074786893712609760570593556842667606791326883482354984608641604022878920386528567328054225923156317998474149497907200 : Int) coeff0800) := by
  rw [CoefficientMerge.eval_scale, ← atom0800_identity]
  exact mul_nonneg (by norm_num) (atom0800_nonneg g t z hg hA hB ht hz hw)

def coeff0801 : CoefficientMerge.Poly :=
  [(557060, 1)]
noncomputable def atom0801 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 7) ^ 2 * (t) ^ 2)
theorem atom0801_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0801 g t z = CoefficientMerge.eval (monomial g t z) coeff0801 := by
  norm_num [atom0801, coeff0801, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0801_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0801 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0801]
  positivity
theorem weighted0801_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (102139865512022074591704753671069704414091625179273877623349039219521904456011710972390539647045035430353974318940669023295155698485401600 : Int) coeff0801) := by
  rw [CoefficientMerge.eval_scale, ← atom0801_identity]
  exact mul_nonneg (by norm_num) (atom0801_nonneg g t z hg hA hB ht hz hw)

def coeff0802 : CoefficientMerge.Poly :=
  [(1343492, 1)]
noncomputable def atom0802 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 7) ^ 2 * (t) ^ 1 * (z) ^ 1)
theorem atom0802_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0802 g t z = CoefficientMerge.eval (monomial g t z) coeff0802 := by
  norm_num [atom0802, coeff0802, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0802_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0802 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0802]
  positivity
theorem weighted0802_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (45707018720266100531699603144239341136595137889268655739094456508624342967776006176015705706751066407322338286590261054161675821854080000 : Int) coeff0802) := by
  rw [CoefficientMerge.eval_scale, ← atom0802_identity]
  exact mul_nonneg (by norm_num) (atom0802_nonneg g t z hg hA hB ht hz hw)

def coeff0803 : CoefficientMerge.Poly :=
  [(1392644, 1)]
noncomputable def atom0803 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0803_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0803 g t z = CoefficientMerge.eval (monomial g t z) coeff0803 := by
  norm_num [atom0803, coeff0803, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0803_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0803 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0803]
  positivity
theorem weighted0803_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (428492626690090674885959614033641299069126979835473913921980819665762000876888579049321017223062471836062556241576562377791365741629721600 : Int) coeff0803) := by
  rw [CoefficientMerge.eval_scale, ← atom0803_identity]
  exact mul_nonneg (by norm_num) (atom0803_nonneg g t z hg hA hB ht hz hw)

def coeff0804 : CoefficientMerge.Poly :=
  [(2097284, 1)]
noncomputable def atom0804 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 2 * (z) ^ 2)
theorem atom0804_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0804 g t z = CoefficientMerge.eval (monomial g t z) coeff0804 := by
  norm_num [atom0804, coeff0804, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0804_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0804 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0804]
  positivity
theorem weighted0804_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (593184256132800155151487924671457244911581827263304850399064006685439866743394733785743434476464565466432310901162425291680790202230043136 : Int) coeff0804) := by
  rw [CoefficientMerge.eval_scale, ← atom0804_identity]
  exact mul_nonneg (by norm_num) (atom0804_nonneg g t z hg hA hB ht hz hw)

def sparseBlock071 : CoefficientMerge.Poly :=
  [(294916, 1574204395298749144416074786893712609760570593556842667606791326883482354984608641604022878920386528567328054225923156317998474149497907200), (526340, 1842748444850467948862547707102209651311792914114207598598345824898067879337667701360496383237196953133739901902303349005873954517824716800), (529412, 2403392112976628415354072539564132099221894685500678587597787409063193013578888126214031887089098449952179409545776762221242418898552345600), (532484, 567441965115353133013669502717203140732273422279989264392975984845355863006954104208431679387030265449594790512112575284769550769568486400), (541700, 2010749954280139307528202654957447768400638880204357313325770986176779253842691024216775012202362567426175446994527636717659681899881420800), (544772, 1152077407463965258073294752573671377117589504420134478509533695525988808176711006839388299054859426508435738535277205271335663488100736000), (557060, 102139865512022074591704753671069704414091625179273877623349039219521904456011710972390539647045035430353974318940669023295155698485401600), (590852, 1882870106496697009582519601646580881449769231147369547431702913542555080370211197963178538737490365674966516182217656406369286259049830400), (593924, 526431998159194281866163826459723818272863479697930174803620454211541120704771382487611754414051827786348668327011910007906015048371123200), (1312772, 3683602935158488969840493007204004350538756060676008062684000902535599598465138868275052639327062886442158647769681324366462851226216857600), (1315844, 5212755731019817450642520602761922725050616756075479804012966950770387750769676304626243292941393290896112737761314796530982404486778042880), (1318916, 1602652081129926504142852504522705404207134337718098564928908839967961209517229840993320383517071529266273937488524772653744219920664217600), (1328132, 4072828866468742578028487760310608899808215922211527213692587969238538473010593111175485468130285818827299346164049876464656439625467648000), (1331204, 2358497570625382883162280609956689226042489881168144807847000798172876480394947926538259728906170814795641405418692155823275203707121792000), (1343492, 45707018720266100531699603144239341136595137889268655739094456508624342967776006176015705706751066407322338286590261054161675821854080000), (1376516, 1992887904883259568723761790254750250191912570810791833574275277752172150495203664495181115073920888177107753549059276434490684013585740800), (1377284, 3942145137399080880622514921827032758671281445453906891198576785746918955193923377002155018770075554158248830901698415799074876522074210560), (1380356, 1599666156023235732050778379817574671899637403680895039719997841521983773870473077586653136574049558948379467931758122382909879871303843840), (1392644, 428492626690090674885959614033641299069126979835473913921980819665762000876888579049321017223062471836062556241576562377791365741629721600), (2097284, 593184256132800155151487924671457244911581827263304850399064006685439866743394733785743434476464565466432310901162425291680790202230043136)]
theorem sparseBlock071_data : sparseBlock071 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1992887904883259568723761790254750250191912570810791833574275277752172150495203664495181115073920888177107753549059276434490684013585740800 : Int) coeff0785) (CoefficientMerge.scale (1842748444850467948862547707102209651311792914114207598598345824898067879337667701360496383237196953133739901902303349005873954517824716800 : Int) coeff0786)) (CoefficientMerge.merge (CoefficientMerge.scale (2403392112976628415354072539564132099221894685500678587597787409063193013578888126214031887089098449952179409545776762221242418898552345600 : Int) coeff0787) (CoefficientMerge.merge (CoefficientMerge.scale (2010749954280139307528202654957447768400638880204357313325770986176779253842691024216775012202362567426175446994527636717659681899881420800 : Int) coeff0788) (CoefficientMerge.scale (1882870106496697009582519601646580881449769231147369547431702913542555080370211197963178538737490365674966516182217656406369286259049830400 : Int) coeff0789)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (3683602935158488969840493007204004350538756060676008062684000902535599598465138868275052639327062886442158647769681324366462851226216857600 : Int) coeff0790) (CoefficientMerge.scale (5212755731019817450642520602761922725050616756075479804012966950770387750769676304626243292941393290896112737761314796530982404486778042880 : Int) coeff0791)) (CoefficientMerge.merge (CoefficientMerge.scale (4072828866468742578028487760310608899808215922211527213692587969238538473010593111175485468130285818827299346164049876464656439625467648000 : Int) coeff0792) (CoefficientMerge.merge (CoefficientMerge.scale (3942145137399080880622514921827032758671281445453906891198576785746918955193923377002155018770075554158248830901698415799074876522074210560 : Int) coeff0793) (CoefficientMerge.scale (567441965115353133013669502717203140732273422279989264392975984845355863006954104208431679387030265449594790512112575284769550769568486400 : Int) coeff0794))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1152077407463965258073294752573671377117589504420134478509533695525988808176711006839388299054859426508435738535277205271335663488100736000 : Int) coeff0795) (CoefficientMerge.scale (526431998159194281866163826459723818272863479697930174803620454211541120704771382487611754414051827786348668327011910007906015048371123200 : Int) coeff0796)) (CoefficientMerge.merge (CoefficientMerge.scale (1602652081129926504142852504522705404207134337718098564928908839967961209517229840993320383517071529266273937488524772653744219920664217600 : Int) coeff0797) (CoefficientMerge.merge (CoefficientMerge.scale (2358497570625382883162280609956689226042489881168144807847000798172876480394947926538259728906170814795641405418692155823275203707121792000 : Int) coeff0798) (CoefficientMerge.scale (1599666156023235732050778379817574671899637403680895039719997841521983773870473077586653136574049558948379467931758122382909879871303843840 : Int) coeff0799)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1574204395298749144416074786893712609760570593556842667606791326883482354984608641604022878920386528567328054225923156317998474149497907200 : Int) coeff0800) (CoefficientMerge.scale (102139865512022074591704753671069704414091625179273877623349039219521904456011710972390539647045035430353974318940669023295155698485401600 : Int) coeff0801)) (CoefficientMerge.merge (CoefficientMerge.scale (45707018720266100531699603144239341136595137889268655739094456508624342967776006176015705706751066407322338286590261054161675821854080000 : Int) coeff0802) (CoefficientMerge.merge (CoefficientMerge.scale (428492626690090674885959614033641299069126979835473913921980819665762000876888579049321017223062471836062556241576562377791365741629721600 : Int) coeff0803) (CoefficientMerge.scale (593184256132800155151487924671457244911581827263304850399064006685439866743394733785743434476464565466432310901162425291680790202230043136 : Int) coeff0804)))))) := by decide +kernel
theorem sparseBlock071_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock071 := by
  rw [sparseBlock071_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted0785_nonneg g t z hg hA hB ht hz hw) (weighted0786_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0787_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0788_nonneg g t z hg hA hB ht hz hw) (weighted0789_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0790_nonneg g t z hg hA hB ht hz hw) (weighted0791_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0792_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0793_nonneg g t z hg hA hB ht hz hw) (weighted0794_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted0795_nonneg g t z hg hA hB ht hz hw) (weighted0796_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0797_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0798_nonneg g t z hg hA hB ht hz hw) (weighted0799_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0800_nonneg g t z hg hA hB ht hz hw) (weighted0801_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0802_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0803_nonneg g t z hg hA hB ht hz hw) (weighted0804_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
