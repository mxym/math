import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff0865 : CoefficientMerge.Poly :=
  [(1312784, 1)]
noncomputable def atom0865 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 5) ^ 2 * (t) ^ 1 * (z) ^ 1)
theorem atom0865_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0865 g t z = CoefficientMerge.eval (monomial g t z) coeff0865 := by
  norm_num [atom0865, coeff0865, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0865_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0865 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0865]
  positivity
theorem weighted0865_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (988857147700983487105220693940214568756800822728915609102877867182547932299513524981180492879640702687238901959265182577665758622888731520 : Int) coeff0865) := by
  rw [CoefficientMerge.eval_scale, ← atom0865_identity]
  exact mul_nonneg (by norm_num) (atom0865_nonneg g t z hg hA hB ht hz hw)

def coeff0866 : CoefficientMerge.Poly :=
  [(1315856, 1)]
noncomputable def atom0866 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0866_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0866 g t z = CoefficientMerge.eval (monomial g t z) coeff0866 := by
  norm_num [atom0866, coeff0866, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0866_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0866 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0866]
  positivity
theorem weighted0866_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1447082629408514553673505486040627858211970404419308030165934244230056802608150724500571718105675250261634419018333217505457499799254223680 : Int) coeff0866) := by
  rw [CoefficientMerge.eval_scale, ← atom0866_identity]
  exact mul_nonneg (by norm_num) (atom0866_nonneg g t z hg hA hB ht hz hw)

def coeff0867 : CoefficientMerge.Poly :=
  [(1328144, 1)]
noncomputable def atom0867 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0867_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0867 g t z = CoefficientMerge.eval (monomial g t z) coeff0867 := by
  norm_num [atom0867, coeff0867, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0867_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0867 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0867]
  positivity
theorem weighted0867_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (666204437948161978944190272751968632054158484551062249610921179450962951723884485671207574536159082832591564591879118487424131265427738880 : Int) coeff0867) := by
  rw [CoefficientMerge.eval_scale, ← atom0867_identity]
  exact mul_nonneg (by norm_num) (atom0867_nonneg g t z hg hA hB ht hz hw)

def coeff0868 : CoefficientMerge.Poly :=
  [(1377296, 1)]
noncomputable def atom0868 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0868_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0868 g t z = CoefficientMerge.eval (monomial g t z) coeff0868 := by
  norm_num [atom0868, coeff0868, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0868_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0868 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0868]
  positivity
theorem weighted0868_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4235567867739444496769220449133934405533388195640933426703450823754397516996700438627559762914313901255753379640257780348711714849211085600 : Int) coeff0868) := by
  rw [CoefficientMerge.eval_scale, ← atom0868_identity]
  exact mul_nonneg (by norm_num) (atom0868_nonneg g t z hg hA hB ht hz hw)

def coeff0869 : CoefficientMerge.Poly :=
  [(544784, 1)]
noncomputable def atom0869 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (t) ^ 2)
theorem atom0869_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0869 g t z = CoefficientMerge.eval (monomial g t z) coeff0869 := by
  norm_num [atom0869, coeff0869, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0869_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0869 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0869]
  positivity
theorem weighted0869_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (790506277916688886026127966248705178244541385821390650290469624301708622680641610877602138410311229041673663630037389537110632216207052800 : Int) coeff0869) := by
  rw [CoefficientMerge.eval_scale, ← atom0869_identity]
  exact mul_nonneg (by norm_num) (atom0869_nonneg g t z hg hA hB ht hz hw)

def coeff0870 : CoefficientMerge.Poly :=
  [(593936, 1)]
noncomputable def atom0870 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (t) ^ 2)
theorem atom0870_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0870 g t z = CoefficientMerge.eval (monomial g t z) coeff0870 := by
  norm_num [atom0870, coeff0870, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0870_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0870 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0870]
  positivity
theorem weighted0870_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2486089941123133472578007031986733520507907830622329052586733133424359636977047672068752900882455778129474971733131534529690625045421527040 : Int) coeff0870) := by
  rw [CoefficientMerge.eval_scale, ← atom0870_identity]
  exact mul_nonneg (by norm_num) (atom0870_nonneg g t z hg hA hB ht hz hw)

def coeff0871 : CoefficientMerge.Poly :=
  [(1331216, 1)]
noncomputable def atom0871 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0871_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0871 g t z = CoefficientMerge.eval (monomial g t z) coeff0871 := by
  norm_num [atom0871, coeff0871, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0871_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0871 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0871]
  positivity
theorem weighted0871_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (194492199217532417591898384094280373223212771887240950775074021601629911499436971297924622585547012028691186535779729971989454361624033280 : Int) coeff0871) := by
  rw [CoefficientMerge.eval_scale, ← atom0871_identity]
  exact mul_nonneg (by norm_num) (atom0871_nonneg g t z hg hA hB ht hz hw)

def coeff0872 : CoefficientMerge.Poly :=
  [(1380368, 1)]
noncomputable def atom0872 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0872_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0872 g t z = CoefficientMerge.eval (monomial g t z) coeff0872 := by
  norm_num [atom0872, coeff0872, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0872_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0872 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0872]
  positivity
theorem weighted0872_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2239149826445933288124763433298212356847093005996577226938321372384251448141569652759989617977754271159255409859749309112666921728294415360 : Int) coeff0872) := by
  rw [CoefficientMerge.eval_scale, ← atom0872_identity]
  exact mul_nonneg (by norm_num) (atom0872_nonneg g t z hg hA hB ht hz hw)

def coeff0873 : CoefficientMerge.Poly :=
  [(606224, 1)]
noncomputable def atom0873 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (t) ^ 2)
theorem atom0873_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0873 g t z = CoefficientMerge.eval (monomial g t z) coeff0873 := by
  norm_num [atom0873, coeff0873, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0873_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0873 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0873]
  positivity
theorem weighted0873_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (315696406140841305946601143409699020819587308192997183639553503577166831043686398367002533492545373480714302481812575747609697852181196800 : Int) coeff0873) := by
  rw [CoefficientMerge.eval_scale, ← atom0873_identity]
  exact mul_nonneg (by norm_num) (atom0873_nonneg g t z hg hA hB ht hz hw)

def coeff0874 : CoefficientMerge.Poly :=
  [(2097488, 1)]
noncomputable def atom0874 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 4) ^ 1 * (z) ^ 2)
theorem atom0874_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0874 g t z = CoefficientMerge.eval (monomial g t z) coeff0874 := by
  norm_num [atom0874, coeff0874, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0874_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0874 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0874]
  positivity
theorem weighted0874_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (524909097034021450560932642191123302406484912802815361302138275533905430556626720496427298622569576745704028762191335847236387566853416896 : Int) coeff0874) := by
  rw [CoefficientMerge.eval_scale, ← atom0874_identity]
  exact mul_nonneg (by norm_num) (atom0874_nonneg g t z hg hA hB ht hz hw)

def coeff0875 : CoefficientMerge.Poly :=
  [(2098256, 1)]
noncomputable def atom0875 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 5) ^ 1 * (z) ^ 2)
theorem atom0875_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0875 g t z = CoefficientMerge.eval (monomial g t z) coeff0875 := by
  norm_num [atom0875, coeff0875, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0875_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0875 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0875]
  positivity
theorem weighted0875_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2728583320544126415056998455266340882510251045481805403289042334190602705818712369026630229008912958235550272261017174488665043426464939520 : Int) coeff0875) := by
  rw [CoefficientMerge.eval_scale, ← atom0875_identity]
  exact mul_nonneg (by norm_num) (atom0875_nonneg g t z hg hA hB ht hz hw)

def coeff0876 : CoefficientMerge.Poly :=
  [(2101328, 1)]
noncomputable def atom0876 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 6) ^ 1 * (z) ^ 2)
theorem atom0876_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0876 g t z = CoefficientMerge.eval (monomial g t z) coeff0876 := by
  norm_num [atom0876, coeff0876, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0876_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0876 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0876]
  positivity
theorem weighted0876_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2717274417681958973279536282536463574387995762151463157790293589290335009233977471819518377149178503462422032814575932757193678799629392640 : Int) coeff0876) := by
  rw [CoefficientMerge.eval_scale, ← atom0876_identity]
  exact mul_nonneg (by norm_num) (atom0876_nonneg g t z hg hA hB ht hz hw)

def coeff0877 : CoefficientMerge.Poly :=
  [(2113616, 1)]
noncomputable def atom0877 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 7) ^ 1 * (z) ^ 2)
theorem atom0877_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0877 g t z = CoefficientMerge.eval (monomial g t z) coeff0877 := by
  norm_num [atom0877, coeff0877, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0877_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0877 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0877]
  positivity
theorem weighted0877_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (473614590498962619167756326678281705939214282134640233366081370899239533774879697562902602066349225186202330132634278693757510907446844160 : Int) coeff0877) := by
  rw [CoefficientMerge.eval_scale, ← atom0877_identity]
  exact mul_nonneg (by norm_num) (atom0877_nonneg g t z hg hA hB ht hz hw)

def coeff0878 : CoefficientMerge.Poly :=
  [(2162768, 1)]
noncomputable def atom0878 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 8) ^ 1 * (z) ^ 2)
theorem atom0878_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0878 g t z = CoefficientMerge.eval (monomial g t z) coeff0878 := by
  norm_num [atom0878, coeff0878, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0878_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0878 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0878]
  positivity
theorem weighted0878_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (700512841610557960530083931412077937450040079157104502492678529506092031827911411461280557075910829384582044589913978418750622131484629760 : Int) coeff0878) := by
  rw [CoefficientMerge.eval_scale, ← atom0878_identity]
  exact mul_nonneg (by norm_num) (atom0878_nonneg g t z hg hA hB ht hz hw)

def coeff0879 : CoefficientMerge.Poly :=
  [(2097680, 1)]
noncomputable def atom0879 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 2 * (z) ^ 2)
theorem atom0879_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0879 g t z = CoefficientMerge.eval (monomial g t z) coeff0879 := by
  norm_num [atom0879, coeff0879, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0879_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0879 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0879]
  positivity
theorem weighted0879_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (392204173834411263413895319893032618173525757370370707805853661928851473245328207769570992622830617120438360889405137970966314262409733440 : Int) coeff0879) := by
  rw [CoefficientMerge.eval_scale, ← atom0879_identity]
  exact mul_nonneg (by norm_num) (atom0879_nonneg g t z hg hA hB ht hz hw)

def coeff0880 : CoefficientMerge.Poly :=
  [(2098448, 1)]
noncomputable def atom0880 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 5) ^ 1 * (z) ^ 2)
theorem atom0880_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0880 g t z = CoefficientMerge.eval (monomial g t z) coeff0880 := by
  norm_num [atom0880, coeff0880, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0880_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0880 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0880]
  positivity
theorem weighted0880_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3056627705186770510674623569472485997752108545117159481172488365066602986848221142358659355752880645140273967607573458304134385616586974528 : Int) coeff0880) := by
  rw [CoefficientMerge.eval_scale, ← atom0880_identity]
  exact mul_nonneg (by norm_num) (atom0880_nonneg g t z hg hA hB ht hz hw)

def coeff0881 : CoefficientMerge.Poly :=
  [(2101520, 1)]
noncomputable def atom0881 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (z) ^ 2)
theorem atom0881_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0881 g t z = CoefficientMerge.eval (monomial g t z) coeff0881 := by
  norm_num [atom0881, coeff0881, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0881_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0881 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0881]
  positivity
theorem weighted0881_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3129046378118332775440582110735292447552147503474134386051467504656601362855796088216798300008471857638138385270015965154091961003760731392 : Int) coeff0881) := by
  rw [CoefficientMerge.eval_scale, ← atom0881_identity]
  exact mul_nonneg (by norm_num) (atom0881_nonneg g t z hg hA hB ht hz hw)

def coeff0882 : CoefficientMerge.Poly :=
  [(2113808, 1)]
noncomputable def atom0882 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (z) ^ 2)
theorem atom0882_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0882 g t z = CoefficientMerge.eval (monomial g t z) coeff0882 := by
  norm_num [atom0882, coeff0882, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0882_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0882 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0882]
  positivity
theorem weighted0882_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1196984408090472379038630528870255979426780243050829496496529734594329540797187022230070331287762859828954862285550060955047237348528189120 : Int) coeff0882) := by
  rw [CoefficientMerge.eval_scale, ← atom0882_identity]
  exact mul_nonneg (by norm_num) (atom0882_nonneg g t z hg hA hB ht hz hw)

def coeff0883 : CoefficientMerge.Poly :=
  [(2162960, 1)]
noncomputable def atom0883 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (z) ^ 2)
theorem atom0883_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0883 g t z = CoefficientMerge.eval (monomial g t z) coeff0883 := by
  norm_num [atom0883, coeff0883, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0883_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0883 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0883]
  positivity
theorem weighted0883_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1041383151003266235010437813357331764518753619686283460551774087111190960355916604350734512578816192579825494814679010475458810692562018208 : Int) coeff0883) := by
  rw [CoefficientMerge.eval_scale, ← atom0883_identity]
  exact mul_nonneg (by norm_num) (atom0883_nonneg g t z hg hA hB ht hz hw)

def coeff0884 : CoefficientMerge.Poly :=
  [(2099216, 1)]
noncomputable def atom0884 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 5) ^ 2 * (z) ^ 2)
theorem atom0884_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0884 g t z = CoefficientMerge.eval (monomial g t z) coeff0884 := by
  norm_num [atom0884, coeff0884, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0884_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0884 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0884]
  positivity
theorem weighted0884_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2089903444492675844187160648271914442901639751670400492000077825604062276511406472931257862116433975886748264051056353268509614245853875200 : Int) coeff0884) := by
  rw [CoefficientMerge.eval_scale, ← atom0884_identity]
  exact mul_nonneg (by norm_num) (atom0884_nonneg g t z hg hA hB ht hz hw)

def sparseBlock075 : CoefficientMerge.Poly :=
  [(544784, 790506277916688886026127966248705178244541385821390650290469624301708622680641610877602138410311229041673663630037389537110632216207052800), (593936, 2486089941123133472578007031986733520507907830622329052586733133424359636977047672068752900882455778129474971733131534529690625045421527040), (606224, 315696406140841305946601143409699020819587308192997183639553503577166831043686398367002533492545373480714302481812575747609697852181196800), (1312784, 988857147700983487105220693940214568756800822728915609102877867182547932299513524981180492879640702687238901959265182577665758622888731520), (1315856, 1447082629408514553673505486040627858211970404419308030165934244230056802608150724500571718105675250261634419018333217505457499799254223680), (1328144, 666204437948161978944190272751968632054158484551062249610921179450962951723884485671207574536159082832591564591879118487424131265427738880), (1331216, 194492199217532417591898384094280373223212771887240950775074021601629911499436971297924622585547012028691186535779729971989454361624033280), (1377296, 4235567867739444496769220449133934405533388195640933426703450823754397516996700438627559762914313901255753379640257780348711714849211085600), (1380368, 2239149826445933288124763433298212356847093005996577226938321372384251448141569652759989617977754271159255409859749309112666921728294415360), (2097488, 524909097034021450560932642191123302406484912802815361302138275533905430556626720496427298622569576745704028762191335847236387566853416896), (2097680, 392204173834411263413895319893032618173525757370370707805853661928851473245328207769570992622830617120438360889405137970966314262409733440), (2098256, 2728583320544126415056998455266340882510251045481805403289042334190602705818712369026630229008912958235550272261017174488665043426464939520), (2098448, 3056627705186770510674623569472485997752108545117159481172488365066602986848221142358659355752880645140273967607573458304134385616586974528), (2099216, 2089903444492675844187160648271914442901639751670400492000077825604062276511406472931257862116433975886748264051056353268509614245853875200), (2101328, 2717274417681958973279536282536463574387995762151463157790293589290335009233977471819518377149178503462422032814575932757193678799629392640), (2101520, 3129046378118332775440582110735292447552147503474134386051467504656601362855796088216798300008471857638138385270015965154091961003760731392), (2113616, 473614590498962619167756326678281705939214282134640233366081370899239533774879697562902602066349225186202330132634278693757510907446844160), (2113808, 1196984408090472379038630528870255979426780243050829496496529734594329540797187022230070331287762859828954862285550060955047237348528189120), (2162768, 700512841610557960530083931412077937450040079157104502492678529506092031827911411461280557075910829384582044589913978418750622131484629760), (2162960, 1041383151003266235010437813357331764518753619686283460551774087111190960355916604350734512578816192579825494814679010475458810692562018208)]
theorem sparseBlock075_data : sparseBlock075 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (988857147700983487105220693940214568756800822728915609102877867182547932299513524981180492879640702687238901959265182577665758622888731520 : Int) coeff0865) (CoefficientMerge.scale (1447082629408514553673505486040627858211970404419308030165934244230056802608150724500571718105675250261634419018333217505457499799254223680 : Int) coeff0866)) (CoefficientMerge.merge (CoefficientMerge.scale (666204437948161978944190272751968632054158484551062249610921179450962951723884485671207574536159082832591564591879118487424131265427738880 : Int) coeff0867) (CoefficientMerge.merge (CoefficientMerge.scale (4235567867739444496769220449133934405533388195640933426703450823754397516996700438627559762914313901255753379640257780348711714849211085600 : Int) coeff0868) (CoefficientMerge.scale (790506277916688886026127966248705178244541385821390650290469624301708622680641610877602138410311229041673663630037389537110632216207052800 : Int) coeff0869)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (2486089941123133472578007031986733520507907830622329052586733133424359636977047672068752900882455778129474971733131534529690625045421527040 : Int) coeff0870) (CoefficientMerge.scale (194492199217532417591898384094280373223212771887240950775074021601629911499436971297924622585547012028691186535779729971989454361624033280 : Int) coeff0871)) (CoefficientMerge.merge (CoefficientMerge.scale (2239149826445933288124763433298212356847093005996577226938321372384251448141569652759989617977754271159255409859749309112666921728294415360 : Int) coeff0872) (CoefficientMerge.merge (CoefficientMerge.scale (315696406140841305946601143409699020819587308192997183639553503577166831043686398367002533492545373480714302481812575747609697852181196800 : Int) coeff0873) (CoefficientMerge.scale (524909097034021450560932642191123302406484912802815361302138275533905430556626720496427298622569576745704028762191335847236387566853416896 : Int) coeff0874))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (2728583320544126415056998455266340882510251045481805403289042334190602705818712369026630229008912958235550272261017174488665043426464939520 : Int) coeff0875) (CoefficientMerge.scale (2717274417681958973279536282536463574387995762151463157790293589290335009233977471819518377149178503462422032814575932757193678799629392640 : Int) coeff0876)) (CoefficientMerge.merge (CoefficientMerge.scale (473614590498962619167756326678281705939214282134640233366081370899239533774879697562902602066349225186202330132634278693757510907446844160 : Int) coeff0877) (CoefficientMerge.merge (CoefficientMerge.scale (700512841610557960530083931412077937450040079157104502492678529506092031827911411461280557075910829384582044589913978418750622131484629760 : Int) coeff0878) (CoefficientMerge.scale (392204173834411263413895319893032618173525757370370707805853661928851473245328207769570992622830617120438360889405137970966314262409733440 : Int) coeff0879)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (3056627705186770510674623569472485997752108545117159481172488365066602986848221142358659355752880645140273967607573458304134385616586974528 : Int) coeff0880) (CoefficientMerge.scale (3129046378118332775440582110735292447552147503474134386051467504656601362855796088216798300008471857638138385270015965154091961003760731392 : Int) coeff0881)) (CoefficientMerge.merge (CoefficientMerge.scale (1196984408090472379038630528870255979426780243050829496496529734594329540797187022230070331287762859828954862285550060955047237348528189120 : Int) coeff0882) (CoefficientMerge.merge (CoefficientMerge.scale (1041383151003266235010437813357331764518753619686283460551774087111190960355916604350734512578816192579825494814679010475458810692562018208 : Int) coeff0883) (CoefficientMerge.scale (2089903444492675844187160648271914442901639751670400492000077825604062276511406472931257862116433975886748264051056353268509614245853875200 : Int) coeff0884)))))) := by decide +kernel
theorem sparseBlock075_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock075 := by
  rw [sparseBlock075_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted0865_nonneg g t z hg hA hB ht hz hw) (weighted0866_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0867_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0868_nonneg g t z hg hA hB ht hz hw) (weighted0869_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0870_nonneg g t z hg hA hB ht hz hw) (weighted0871_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0872_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0873_nonneg g t z hg hA hB ht hz hw) (weighted0874_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted0875_nonneg g t z hg hA hB ht hz hw) (weighted0876_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0877_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0878_nonneg g t z hg hA hB ht hz hw) (weighted0879_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0880_nonneg g t z hg hA hB ht hz hw) (weighted0881_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0882_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0883_nonneg g t z hg hA hB ht hz hw) (weighted0884_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
