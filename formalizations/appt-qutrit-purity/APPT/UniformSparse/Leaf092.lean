import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff1205 : CoefficientMerge.Poly :=
  [(794880, 1)]
noncomputable def atom1205 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 6) ^ 2 * (t) ^ 3)
theorem atom1205_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1205 g t z = CoefficientMerge.eval (monomial g t z) coeff1205 := by
  norm_num [atom1205, coeff1205, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1205_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1205 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1205]
  positivity
theorem weighted1205_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (112141257774353585564525867421429197482617255675320673659480521699593221909575705088425031796291614176290696201638600555284844602818355200 : Int) coeff1205) := by
  rw [CoefficientMerge.eval_scale, ← atom1205_identity]
  exact mul_nonneg (by norm_num) (atom1205_nonneg g t z hg hA hB ht hz hw)

def coeff1206 : CoefficientMerge.Poly :=
  [(807168, 1)]
noncomputable def atom1206 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (t) ^ 3)
theorem atom1206_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1206 g t z = CoefficientMerge.eval (monomial g t z) coeff1206 := by
  norm_num [atom1206, coeff1206, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1206_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1206 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1206]
  positivity
theorem weighted1206_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (181187142055655414233547001198817158772654233628419237520493601355480736809538214223724576267165201078392552407010692470564729343698380800 : Int) coeff1206) := by
  rw [CoefficientMerge.eval_scale, ← atom1206_identity]
  exact mul_nonneg (by norm_num) (atom1206_nonneg g t z hg hA hB ht hz hw)

def coeff1207 : CoefficientMerge.Poly :=
  [(856320, 1)]
noncomputable def atom1207 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (t) ^ 3)
theorem atom1207_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1207 g t z = CoefficientMerge.eval (monomial g t z) coeff1207 := by
  norm_num [atom1207, coeff1207, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1207_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1207 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1207]
  positivity
theorem weighted1207_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (147369951337552415864798707075296975381569124160644355516371811724253850103819681904544729981397610727277219074463106176752405571814451200 : Int) coeff1207) := by
  rw [CoefficientMerge.eval_scale, ← atom1207_identity]
  exact mul_nonneg (by norm_num) (atom1207_nonneg g t z hg hA hB ht hz hw)

def coeff1208 : CoefficientMerge.Poly :=
  [(1581312, 1)]
noncomputable def atom1208 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 6) ^ 2 * (t) ^ 2 * (z) ^ 1)
theorem atom1208_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1208 g t z = CoefficientMerge.eval (monomial g t z) coeff1208 := by
  norm_num [atom1208, coeff1208, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1208_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1208 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1208]
  positivity
theorem weighted1208_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (332279313232073641692695485056441017343365574526996908411949009161445499106336948638186545293752047513321746665314742486909527771806557760 : Int) coeff1208) := by
  rw [CoefficientMerge.eval_scale, ← atom1208_identity]
  exact mul_nonneg (by norm_num) (atom1208_nonneg g t z hg hA hB ht hz hw)

def coeff1209 : CoefficientMerge.Poly :=
  [(1593600, 1)]
noncomputable def atom1209 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1209_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1209 g t z = CoefficientMerge.eval (monomial g t z) coeff1209 := by
  norm_num [atom1209, coeff1209, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1209_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1209 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1209]
  positivity
theorem weighted1209_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (566073977457969215995683932198772559491369387358450143311800964480209541056910889177510775164792139401819498255536081361243445798733867520 : Int) coeff1209) := by
  rw [CoefficientMerge.eval_scale, ← atom1209_identity]
  exact mul_nonneg (by norm_num) (atom1209_nonneg g t z hg hA hB ht hz hw)

def coeff1210 : CoefficientMerge.Poly :=
  [(1642752, 1)]
noncomputable def atom1210 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1210_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1210 g t z = CoefficientMerge.eval (monomial g t z) coeff1210 := by
  norm_num [atom1210, coeff1210, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1210_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1210 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1210]
  positivity
theorem weighted1210_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (454421308776920193961696798511936772405589096856192828271123782570696362044958403685601312650752309125206142915955701782410269888655087520 : Int) coeff1210) := by
  rw [CoefficientMerge.eval_scale, ← atom1210_identity]
  exact mul_nonneg (by norm_num) (atom1210_nonneg g t z hg hA hB ht hz hw)

def coeff1211 : CoefficientMerge.Poly :=
  [(819456, 1)]
noncomputable def atom1211 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 7) ^ 2 * (t) ^ 3)
theorem atom1211_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1211 g t z = CoefficientMerge.eval (monomial g t z) coeff1211 := by
  norm_num [atom1211, coeff1211, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1211_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1211 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1211]
  positivity
theorem weighted1211_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (75603465258961361189767988125297227629467566141107555351405519052639339379402456036676259057496846098082038259924384269233828503427308800 : Int) coeff1211) := by
  rw [CoefficientMerge.eval_scale, ← atom1211_identity]
  exact mul_nonneg (by norm_num) (atom1211_nonneg g t z hg hA hB ht hz hw)

def coeff1212 : CoefficientMerge.Poly :=
  [(868608, 1)]
noncomputable def atom1212 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (t) ^ 3)
theorem atom1212_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1212 g t z = CoefficientMerge.eval (monomial g t z) coeff1212 := by
  norm_num [atom1212, coeff1212, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1212_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1212 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1212]
  positivity
theorem weighted1212_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (91601351476841048822422528252063034389204358818344373046951180371106679941322945316008590235374572924270386204494183606908261590247737600 : Int) coeff1212) := by
  rw [CoefficientMerge.eval_scale, ← atom1212_identity]
  exact mul_nonneg (by norm_num) (atom1212_nonneg g t z hg hA hB ht hz hw)

def coeff1213 : CoefficientMerge.Poly :=
  [(1605888, 1)]
noncomputable def atom1213 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 7) ^ 2 * (t) ^ 2 * (z) ^ 1)
theorem atom1213_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1213 g t z = CoefficientMerge.eval (monomial g t z) coeff1213 := by
  norm_num [atom1213, coeff1213, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1213_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1213 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1213]
  positivity
theorem weighted1213_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (247029816880230692591431901966053963401572437266048754524775623968915015983665171060907980200159209331837012108091369018401328213950972160 : Int) coeff1213) := by
  rw [CoefficientMerge.eval_scale, ← atom1213_identity]
  exact mul_nonneg (by norm_num) (atom1213_nonneg g t z hg hA hB ht hz hw)

def coeff1214 : CoefficientMerge.Poly :=
  [(1655040, 1)]
noncomputable def atom1214 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1214_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1214 g t z = CoefficientMerge.eval (monomial g t z) coeff1214 := by
  norm_num [atom1214, coeff1214, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1214_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1214 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1214]
  positivity
theorem weighted1214_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (317528428193263442675692153342453089629075157744615359950525029798298437933276023318044106022294076254471380263899602211732973192557304320 : Int) coeff1214) := by
  rw [CoefficientMerge.eval_scale, ← atom1214_identity]
  exact mul_nonneg (by norm_num) (atom1214_nonneg g t z hg hA hB ht hz hw)

def coeff1215 : CoefficientMerge.Poly :=
  [(917760, 1)]
noncomputable def atom1215 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 8) ^ 2 * (t) ^ 3)
theorem atom1215_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1215 g t z = CoefficientMerge.eval (monomial g t z) coeff1215 := by
  norm_num [atom1215, coeff1215, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1215_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1215 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1215]
  positivity
theorem weighted1215_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (30422592892323330758818928374828643297687777500120674776953071153660974040681271901798760031456597780531493813977415739459353352899788800 : Int) coeff1215) := by
  rw [CoefficientMerge.eval_scale, ← atom1215_identity]
  exact mul_nonneg (by norm_num) (atom1215_nonneg g t z hg hA hB ht hz hw)

def coeff1216 : CoefficientMerge.Poly :=
  [(1704192, 1)]
noncomputable def atom1216 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 8) ^ 2 * (t) ^ 2 * (z) ^ 1)
theorem atom1216_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1216 g t z = CoefficientMerge.eval (monomial g t z) coeff1216 := by
  norm_num [atom1216, coeff1216, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1216_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1216 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1216]
  positivity
theorem weighted1216_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (114285938914696753075408224334224464617669371600983199025591108052053536421796635692183018557535383096223564925919276907603150499059912960 : Int) coeff1216) := by
  rw [CoefficientMerge.eval_scale, ← atom1216_identity]
  exact mul_nonneg (by norm_num) (atom1216_nonneg g t z hg hA hB ht hz hw)

def coeff1217 : CoefficientMerge.Poly :=
  [(2360064, 1)]
noncomputable def atom1217 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 3 * (t) ^ 1 * (z) ^ 2)
theorem atom1217_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1217 g t z = CoefficientMerge.eval (monomial g t z) coeff1217 := by
  norm_num [atom1217, coeff1217, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1217_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1217 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1217]
  positivity
theorem weighted1217_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2589181788888482302269709064577461955234099020565530550946570683511240906625103482226506199930417739724018132286377244152597553778176000 : Int) coeff1217) := by
  rw [CoefficientMerge.eval_scale, ← atom1217_identity]
  exact mul_nonneg (by norm_num) (atom1217_nonneg g t z hg hA hB ht hz hw)

def coeff1218 : CoefficientMerge.Poly :=
  [(2360832, 1)]
noncomputable def atom1218 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 2 * (g 5) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1218_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1218 g t z = CoefficientMerge.eval (monomial g t z) coeff1218 := by
  norm_num [atom1218, coeff1218, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1218_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1218 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1218]
  positivity
theorem weighted1218_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (238423051185308067452809008387275226128307554647102090312010316170034526216096204853049302531608314206427653137093260011063009701785600000 : Int) coeff1218) := by
  rw [CoefficientMerge.eval_scale, ← atom1218_identity]
  exact mul_nonneg (by norm_num) (atom1218_nonneg g t z hg hA hB ht hz hw)

def coeff1219 : CoefficientMerge.Poly :=
  [(2363904, 1)]
noncomputable def atom1219 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 2 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1219_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1219 g t z = CoefficientMerge.eval (monomial g t z) coeff1219 := by
  norm_num [atom1219, coeff1219, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1219_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1219 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1219]
  positivity
theorem weighted1219_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (176456270129894175662480157960402472687495194135652379815028414653889267352195357193144925418283864464218528550796621188741236678332606080 : Int) coeff1219) := by
  rw [CoefficientMerge.eval_scale, ← atom1219_identity]
  exact mul_nonneg (by norm_num) (atom1219_nonneg g t z hg hA hB ht hz hw)

def coeff1220 : CoefficientMerge.Poly :=
  [(2376192, 1)]
noncomputable def atom1220 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 2 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1220_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1220 g t z = CoefficientMerge.eval (monomial g t z) coeff1220 := by
  norm_num [atom1220, coeff1220, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1220_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1220 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1220]
  positivity
theorem weighted1220_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (143602545534220632470605845747992781887815361462943777635845651033584839356549234431688321593826838932377458177589024092165559432515502720 : Int) coeff1220) := by
  rw [CoefficientMerge.eval_scale, ← atom1220_identity]
  exact mul_nonneg (by norm_num) (atom1220_nonneg g t z hg hA hB ht hz hw)

def coeff1221 : CoefficientMerge.Poly :=
  [(2425344, 1)]
noncomputable def atom1221 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 2 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1221_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1221 g t z = CoefficientMerge.eval (monomial g t z) coeff1221 := by
  norm_num [atom1221, coeff1221, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1221_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1221 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1221]
  positivity
theorem weighted1221_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (71918502810099610380429941242386162008361831063654378310750397441724210844014258804818661915481854365037331257045945181272064497126583680 : Int) coeff1221) := by
  rw [CoefficientMerge.eval_scale, ← atom1221_identity]
  exact mul_nonneg (by norm_num) (atom1221_nonneg g t z hg hA hB ht hz hw)

def coeff1222 : CoefficientMerge.Poly :=
  [(2361600, 1)]
noncomputable def atom1222 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 5) ^ 2 * (t) ^ 1 * (z) ^ 2)
theorem atom1222_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1222 g t z = CoefficientMerge.eval (monomial g t z) coeff1222 := by
  norm_num [atom1222, coeff1222, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1222_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1222 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1222]
  positivity
theorem weighted1222_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (390162135790645233127191958511147519790486969678230166474644474937509507497387989447398044381443028488879092787138383089777225430998260480 : Int) coeff1222) := by
  rw [CoefficientMerge.eval_scale, ← atom1222_identity]
  exact mul_nonneg (by norm_num) (atom1222_nonneg g t z hg hA hB ht hz hw)

def coeff1223 : CoefficientMerge.Poly :=
  [(2364672, 1)]
noncomputable def atom1223 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1223_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1223 g t z = CoefficientMerge.eval (monomial g t z) coeff1223 := by
  norm_num [atom1223, coeff1223, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1223_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1223 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1223]
  positivity
theorem weighted1223_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (701526015731183271861671450004887239516544900453055484106383655341691823551509291410564777027144688427269958184576105514250508712710432000 : Int) coeff1223) := by
  rw [CoefficientMerge.eval_scale, ← atom1223_identity]
  exact mul_nonneg (by norm_num) (atom1223_nonneg g t z hg hA hB ht hz hw)

def coeff1224 : CoefficientMerge.Poly :=
  [(2376960, 1)]
noncomputable def atom1224 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1224_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1224 g t z = CoefficientMerge.eval (monomial g t z) coeff1224 := by
  norm_num [atom1224, coeff1224, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1224_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1224 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1224]
  positivity
theorem weighted1224_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (618230924750898175897007936201699352939267449668507402404527865825502474724750724414177194367402815339175192401235980010391335319094611200 : Int) coeff1224) := by
  rw [CoefficientMerge.eval_scale, ← atom1224_identity]
  exact mul_nonneg (by norm_num) (atom1224_nonneg g t z hg hA hB ht hz hw)

def sparseBlock092 : CoefficientMerge.Poly :=
  [(794880, 112141257774353585564525867421429197482617255675320673659480521699593221909575705088425031796291614176290696201638600555284844602818355200), (807168, 181187142055655414233547001198817158772654233628419237520493601355480736809538214223724576267165201078392552407010692470564729343698380800), (819456, 75603465258961361189767988125297227629467566141107555351405519052639339379402456036676259057496846098082038259924384269233828503427308800), (856320, 147369951337552415864798707075296975381569124160644355516371811724253850103819681904544729981397610727277219074463106176752405571814451200), (868608, 91601351476841048822422528252063034389204358818344373046951180371106679941322945316008590235374572924270386204494183606908261590247737600), (917760, 30422592892323330758818928374828643297687777500120674776953071153660974040681271901798760031456597780531493813977415739459353352899788800), (1581312, 332279313232073641692695485056441017343365574526996908411949009161445499106336948638186545293752047513321746665314742486909527771806557760), (1593600, 566073977457969215995683932198772559491369387358450143311800964480209541056910889177510775164792139401819498255536081361243445798733867520), (1605888, 247029816880230692591431901966053963401572437266048754524775623968915015983665171060907980200159209331837012108091369018401328213950972160), (1642752, 454421308776920193961696798511936772405589096856192828271123782570696362044958403685601312650752309125206142915955701782410269888655087520), (1655040, 317528428193263442675692153342453089629075157744615359950525029798298437933276023318044106022294076254471380263899602211732973192557304320), (1704192, 114285938914696753075408224334224464617669371600983199025591108052053536421796635692183018557535383096223564925919276907603150499059912960), (2360064, 2589181788888482302269709064577461955234099020565530550946570683511240906625103482226506199930417739724018132286377244152597553778176000), (2360832, 238423051185308067452809008387275226128307554647102090312010316170034526216096204853049302531608314206427653137093260011063009701785600000), (2361600, 390162135790645233127191958511147519790486969678230166474644474937509507497387989447398044381443028488879092787138383089777225430998260480), (2363904, 176456270129894175662480157960402472687495194135652379815028414653889267352195357193144925418283864464218528550796621188741236678332606080), (2364672, 701526015731183271861671450004887239516544900453055484106383655341691823551509291410564777027144688427269958184576105514250508712710432000), (2376192, 143602545534220632470605845747992781887815361462943777635845651033584839356549234431688321593826838932377458177589024092165559432515502720), (2376960, 618230924750898175897007936201699352939267449668507402404527865825502474724750724414177194367402815339175192401235980010391335319094611200), (2425344, 71918502810099610380429941242386162008361831063654378310750397441724210844014258804818661915481854365037331257045945181272064497126583680)]
theorem sparseBlock092_data : sparseBlock092 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (112141257774353585564525867421429197482617255675320673659480521699593221909575705088425031796291614176290696201638600555284844602818355200 : Int) coeff1205) (CoefficientMerge.scale (181187142055655414233547001198817158772654233628419237520493601355480736809538214223724576267165201078392552407010692470564729343698380800 : Int) coeff1206)) (CoefficientMerge.merge (CoefficientMerge.scale (147369951337552415864798707075296975381569124160644355516371811724253850103819681904544729981397610727277219074463106176752405571814451200 : Int) coeff1207) (CoefficientMerge.merge (CoefficientMerge.scale (332279313232073641692695485056441017343365574526996908411949009161445499106336948638186545293752047513321746665314742486909527771806557760 : Int) coeff1208) (CoefficientMerge.scale (566073977457969215995683932198772559491369387358450143311800964480209541056910889177510775164792139401819498255536081361243445798733867520 : Int) coeff1209)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (454421308776920193961696798511936772405589096856192828271123782570696362044958403685601312650752309125206142915955701782410269888655087520 : Int) coeff1210) (CoefficientMerge.scale (75603465258961361189767988125297227629467566141107555351405519052639339379402456036676259057496846098082038259924384269233828503427308800 : Int) coeff1211)) (CoefficientMerge.merge (CoefficientMerge.scale (91601351476841048822422528252063034389204358818344373046951180371106679941322945316008590235374572924270386204494183606908261590247737600 : Int) coeff1212) (CoefficientMerge.merge (CoefficientMerge.scale (247029816880230692591431901966053963401572437266048754524775623968915015983665171060907980200159209331837012108091369018401328213950972160 : Int) coeff1213) (CoefficientMerge.scale (317528428193263442675692153342453089629075157744615359950525029798298437933276023318044106022294076254471380263899602211732973192557304320 : Int) coeff1214))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (30422592892323330758818928374828643297687777500120674776953071153660974040681271901798760031456597780531493813977415739459353352899788800 : Int) coeff1215) (CoefficientMerge.scale (114285938914696753075408224334224464617669371600983199025591108052053536421796635692183018557535383096223564925919276907603150499059912960 : Int) coeff1216)) (CoefficientMerge.merge (CoefficientMerge.scale (2589181788888482302269709064577461955234099020565530550946570683511240906625103482226506199930417739724018132286377244152597553778176000 : Int) coeff1217) (CoefficientMerge.merge (CoefficientMerge.scale (238423051185308067452809008387275226128307554647102090312010316170034526216096204853049302531608314206427653137093260011063009701785600000 : Int) coeff1218) (CoefficientMerge.scale (176456270129894175662480157960402472687495194135652379815028414653889267352195357193144925418283864464218528550796621188741236678332606080 : Int) coeff1219)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (143602545534220632470605845747992781887815361462943777635845651033584839356549234431688321593826838932377458177589024092165559432515502720 : Int) coeff1220) (CoefficientMerge.scale (71918502810099610380429941242386162008361831063654378310750397441724210844014258804818661915481854365037331257045945181272064497126583680 : Int) coeff1221)) (CoefficientMerge.merge (CoefficientMerge.scale (390162135790645233127191958511147519790486969678230166474644474937509507497387989447398044381443028488879092787138383089777225430998260480 : Int) coeff1222) (CoefficientMerge.merge (CoefficientMerge.scale (701526015731183271861671450004887239516544900453055484106383655341691823551509291410564777027144688427269958184576105514250508712710432000 : Int) coeff1223) (CoefficientMerge.scale (618230924750898175897007936201699352939267449668507402404527865825502474724750724414177194367402815339175192401235980010391335319094611200 : Int) coeff1224)))))) := by decide +kernel
theorem sparseBlock092_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock092 := by
  rw [sparseBlock092_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted1205_nonneg g t z hg hA hB ht hz hw) (weighted1206_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1207_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1208_nonneg g t z hg hA hB ht hz hw) (weighted1209_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1210_nonneg g t z hg hA hB ht hz hw) (weighted1211_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1212_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1213_nonneg g t z hg hA hB ht hz hw) (weighted1214_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted1215_nonneg g t z hg hA hB ht hz hw) (weighted1216_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1217_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1218_nonneg g t z hg hA hB ht hz hw) (weighted1219_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1220_nonneg g t z hg hA hB ht hz hw) (weighted1221_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1222_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1223_nonneg g t z hg hA hB ht hz hw) (weighted1224_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
