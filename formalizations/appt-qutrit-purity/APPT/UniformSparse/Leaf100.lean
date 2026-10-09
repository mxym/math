import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff1365 : CoefficientMerge.Poly :=
  [(2359554, 1)]
noncomputable def atom1365 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 2 * (g 4) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1365_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1365 g t z = CoefficientMerge.eval (monomial g t z) coeff1365 := by
  norm_num [atom1365, coeff1365, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1365_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1365 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1365]
  positivity
theorem weighted1365_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5937305907091322089454380423371098604447979016756580497562919607083374075165571942764462092955612146678144252938888496403763998082437120 : Int) coeff1365) := by
  rw [CoefficientMerge.eval_scale, ← atom1365_identity]
  exact mul_nonneg (by norm_num) (atom1365_nonneg g t z hg hA hB ht hz hw)

def coeff1366 : CoefficientMerge.Poly :=
  [(3145986, 1)]
noncomputable def atom1366 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 2 * (g 4) ^ 1 * (z) ^ 3)
theorem atom1366_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1366 g t z = CoefficientMerge.eval (monomial g t z) coeff1366 := by
  norm_num [atom1366, coeff1366, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1366_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1366 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1366]
  positivity
theorem weighted1366_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2204332680041491298621815912465543043900356898064019495580792536991029635120222154527723042223316641454907736274996672739581119555891200 : Int) coeff1366) := by
  rw [CoefficientMerge.eval_scale, ← atom1366_identity]
  exact mul_nonneg (by norm_num) (atom1366_nonneg g t z hg hA hB ht hz hw)

def coeff1367 : CoefficientMerge.Poly :=
  [(787458, 1)]
noncomputable def atom1367 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 2 * (g 5) ^ 1 * (t) ^ 3)
theorem atom1367_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1367 g t z = CoefficientMerge.eval (monomial g t z) coeff1367 := by
  norm_num [atom1367, coeff1367, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1367_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1367 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1367]
  positivity
theorem weighted1367_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1810677902051995204175440196402799628420115920785631293461953130752388914189095097633399588347380544488961584387423468872103247012526080 : Int) coeff1367) := by
  rw [CoefficientMerge.eval_scale, ← atom1367_identity]
  exact mul_nonneg (by norm_num) (atom1367_nonneg g t z hg hA hB ht hz hw)

def coeff1368 : CoefficientMerge.Poly :=
  [(1573890, 1)]
noncomputable def atom1368 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 2 * (g 5) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1368_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1368 g t z = CoefficientMerge.eval (monomial g t z) coeff1368 := by
  norm_num [atom1368, coeff1368, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1368_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1368 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1368]
  positivity
theorem weighted1368_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5317889748203735248686814454146157896471569680752679219662952647690079559902401416359644123183688981729783561501545740032967181489612800 : Int) coeff1368) := by
  rw [CoefficientMerge.eval_scale, ← atom1368_identity]
  exact mul_nonneg (by norm_num) (atom1368_nonneg g t z hg hA hB ht hz hw)

def coeff1369 : CoefficientMerge.Poly :=
  [(2360322, 1)]
noncomputable def atom1369 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 2 * (g 5) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1369_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1369 g t z = CoefficientMerge.eval (monomial g t z) coeff1369 := by
  norm_num [atom1369, coeff1369, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1369_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1369 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1369]
  positivity
theorem weighted1369_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5320826235625595230486508925605346703300398534022719439965960998163918527781469714497587823353120930540327343146213749031566794381158400 : Int) coeff1369) := by
  rw [CoefficientMerge.eval_scale, ← atom1369_identity]
  exact mul_nonneg (by norm_num) (atom1369_nonneg g t z hg hA hB ht hz hw)

def coeff1370 : CoefficientMerge.Poly :=
  [(3146754, 1)]
noncomputable def atom1370 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 2 * (g 5) ^ 1 * (z) ^ 3)
theorem atom1370_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1370 g t z = CoefficientMerge.eval (monomial g t z) coeff1370 := by
  norm_num [atom1370, coeff1370, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1370_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1370 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1370]
  positivity
theorem weighted1370_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1813614389473855185975134667861988435248944774055671513764961481226227882068163395771343288516812493299505366032091477870702859904071680 : Int) coeff1370) := by
  rw [CoefficientMerge.eval_scale, ← atom1370_identity]
  exact mul_nonneg (by norm_num) (atom1370_nonneg g t z hg hA hB ht hz hw)

def coeff1371 : CoefficientMerge.Poly :=
  [(790530, 1)]
noncomputable def atom1371 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 2 * (g 6) ^ 1 * (t) ^ 3)
theorem atom1371_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1371 g t z = CoefficientMerge.eval (monomial g t z) coeff1371 := by
  norm_num [atom1371, coeff1371, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1371_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1371 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1371]
  positivity
theorem weighted1371_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (595064021255885382423952417337691562465322810223859260214164031929349463653576245730242579646578475983769486984069456565081605786521600 : Int) coeff1371) := by
  rw [CoefficientMerge.eval_scale, ← atom1371_identity]
  exact mul_nonneg (by norm_num) (atom1371_nonneg g t z hg hA hB ht hz hw)

def coeff1372 : CoefficientMerge.Poly :=
  [(1576962, 1)]
noncomputable def atom1372 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 2 * (g 6) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1372_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1372 g t z = CoefficientMerge.eval (monomial g t z) coeff1372 := by
  norm_num [atom1372, coeff1372, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1372_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1372 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1372]
  positivity
theorem weighted1372_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1308256138681044783304961001492662276247259291456896974778705486046697101784553960270356445544827381038209063262801455566347906665574400 : Int) coeff1372) := by
  rw [CoefficientMerge.eval_scale, ← atom1372_identity]
  exact mul_nonneg (by norm_num) (atom1372_nonneg g t z hg hA hB ht hz hw)

def coeff1373 : CoefficientMerge.Poly :=
  [(2363394, 1)]
noncomputable def atom1373 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 2 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1373_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1373 g t z = CoefficientMerge.eval (monomial g t z) coeff1373 := by
  norm_num [atom1373, coeff1373, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1373_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1373 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1373]
  positivity
theorem weighted1373_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1308256138681044783304961001492662276247259291456896974778705486046697101784553960270356445544827381038209063262801455566347906665574400 : Int) coeff1373) := by
  rw [CoefficientMerge.eval_scale, ← atom1373_identity]
  exact mul_nonneg (by norm_num) (atom1373_nonneg g t z hg hA hB ht hz hw)

def coeff1374 : CoefficientMerge.Poly :=
  [(3149826, 1)]
noncomputable def atom1374 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 2 * (g 6) ^ 1 * (z) ^ 3)
theorem atom1374_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1374 g t z = CoefficientMerge.eval (monomial g t z) coeff1374 := by
  norm_num [atom1374, coeff1374, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1374_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1374 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1374]
  positivity
theorem weighted1374_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (595064021255885382423952417337691562465322810223859260214164031929349463653576245730242579646578475983769486984069456565081605786521600 : Int) coeff1374) := by
  rw [CoefficientMerge.eval_scale, ← atom1374_identity]
  exact mul_nonneg (by norm_num) (atom1374_nonneg g t z hg hA hB ht hz hw)

def coeff1375 : CoefficientMerge.Poly :=
  [(786441, 1)]
noncomputable def atom1375 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 1) ^ 2 * (t) ^ 3)
theorem atom1375_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1375 g t z = CoefficientMerge.eval (monomial g t z) coeff1375 := by
  norm_num [atom1375, coeff1375, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1375_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1375 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1375]
  positivity
theorem weighted1375_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2795830100677703894469638896022611500957008332066065853134794634777396284149172774235194488187775024115136950356182000728156982952960000 : Int) coeff1375) := by
  rw [CoefficientMerge.eval_scale, ← atom1375_identity]
  exact mul_nonneg (by norm_num) (atom1375_nonneg g t z hg hA hB ht hz hw)

def coeff1376 : CoefficientMerge.Poly :=
  [(1572873, 1)]
noncomputable def atom1376 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 1) ^ 2 * (t) ^ 2 * (z) ^ 1)
theorem atom1376_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1376 g t z = CoefficientMerge.eval (monomial g t z) coeff1376 := by
  norm_num [atom1376, coeff1376, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1376_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1376 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1376]
  positivity
theorem weighted1376_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (8308885390771688584726528728824809848613576690855753159983412082558674892600027882105151228838716152921856366796653397794699036695992320 : Int) coeff1376) := by
  rw [CoefficientMerge.eval_scale, ← atom1376_identity]
  exact mul_nonneg (by norm_num) (atom1376_nonneg g t z hg hA hB ht hz hw)

def coeff1377 : CoefficientMerge.Poly :=
  [(2359305, 1)]
noncomputable def atom1377 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 1) ^ 2 * (t) ^ 1 * (z) ^ 2)
theorem atom1377_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1377 g t z = CoefficientMerge.eval (monomial g t z) coeff1377 := by
  norm_num [atom1377, coeff1377, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1377_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1377 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1377]
  positivity
theorem weighted1377_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (8255299640780632023358731147149752391930785834816500961660018417424783600671610961832637851686760498345805750820803002885852709380085760 : Int) coeff1377) := by
  rw [CoefficientMerge.eval_scale, ← atom1377_identity]
  exact mul_nonneg (by norm_num) (atom1377_nonneg g t z hg hA hB ht hz hw)

def coeff1378 : CoefficientMerge.Poly :=
  [(3145737, 1)]
noncomputable def atom1378 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 1) ^ 2 * (z) ^ 3)
theorem atom1378_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1378 g t z = CoefficientMerge.eval (monomial g t z) coeff1378 := by
  norm_num [atom1378, coeff1378, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1378_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1378 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1378]
  positivity
theorem weighted1378_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2742244350686647333101841314347554044274217476026813654811400969643504992220755853962681111035819369539086334380331605819310655637053440 : Int) coeff1378) := by
  rw [CoefficientMerge.eval_scale, ← atom1378_identity]
  exact mul_nonneg (by norm_num) (atom1378_nonneg g t z hg hA hB ht hz hw)

def coeff1379 : CoefficientMerge.Poly :=
  [(786453, 1)]
noncomputable def atom1379 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 1) ^ 1 * (g 2) ^ 1 * (t) ^ 3)
theorem atom1379_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1379 g t z = CoefficientMerge.eval (monomial g t z) coeff1379 := by
  norm_num [atom1379, coeff1379, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1379_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1379 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1379]
  positivity
theorem weighted1379_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (37114476220426921461913870660144911612759492464928243829327248414850438104738812463535830844503766283058701877289522527183251451402362880 : Int) coeff1379) := by
  rw [CoefficientMerge.eval_scale, ← atom1379_identity]
  exact mul_nonneg (by norm_num) (atom1379_nonneg g t z hg hA hB ht hz hw)

def coeff1380 : CoefficientMerge.Poly :=
  [(1572885, 1)]
noncomputable def atom1380 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 1) ^ 1 * (g 2) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1380_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1380 g t z = CoefficientMerge.eval (monomial g t z) coeff1380 := by
  norm_num [atom1380, coeff1380, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1380_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1380 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1380]
  positivity
theorem weighted1380_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (111423655925537104465356661378521191639594019439800201388157896803093055374603284928491202602462889445092143646206130583668012958466672640 : Int) coeff1380) := by
  rw [CoefficientMerge.eval_scale, ← atom1380_identity]
  exact mul_nonneg (by norm_num) (atom1380_nonneg g t z hg hA hB ht hz hw)

def coeff1381 : CoefficientMerge.Poly :=
  [(2359317, 1)]
noncomputable def atom1381 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 1) ^ 1 * (g 2) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1381_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1381 g t z = CoefficientMerge.eval (monomial g t z) coeff1381 := by
  norm_num [atom1381, coeff1381, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1381_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1381 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1381]
  positivity
theorem weighted1381_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (99282544701111154090730559334460188036975113255578130018674950178841513962386726235789527355618531050030926135710756600970478766088437760 : Int) coeff1381) := by
  rw [CoefficientMerge.eval_scale, ← atom1381_identity]
  exact mul_nonneg (by norm_num) (atom1381_nonneg g t z hg hA hB ht hz hw)

def coeff1382 : CoefficientMerge.Poly :=
  [(3145749, 1)]
noncomputable def atom1382 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 1) ^ 1 * (g 2) ^ 1 * (z) ^ 3)
theorem atom1382_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1382 g t z = CoefficientMerge.eval (monomial g t z) coeff1382 := by
  norm_num [atom1382, coeff1382, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1382_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1382 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1382]
  positivity
theorem weighted1382_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (24702878219455213880962736550352244718230502648152202287943768091917124904037962992521026153990206231759756206158016602851912586517073920 : Int) coeff1382) := by
  rw [CoefficientMerge.eval_scale, ← atom1382_identity]
  exact mul_nonneg (by norm_num) (atom1382_nonneg g t z hg hA hB ht hz hw)

def coeff1383 : CoefficientMerge.Poly :=
  [(802821, 1)]
noncomputable def atom1383 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 1) ^ 1 * (g 7) ^ 1 * (t) ^ 3)
theorem atom1383_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1383 g t z = CoefficientMerge.eval (monomial g t z) coeff1383 := by
  norm_num [atom1383, coeff1383, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1383_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1383 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1383]
  positivity
theorem weighted1383_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2054005297371007980551760680156893837306290112286590458596816752298090725183289895224369854883738268038680934086854793787936661715046400 : Int) coeff1383) := by
  rw [CoefficientMerge.eval_scale, ← atom1383_identity]
  exact mul_nonneg (by norm_num) (atom1383_nonneg g t z hg hA hB ht hz hw)

def coeff1384 : CoefficientMerge.Poly :=
  [(1589253, 1)]
noncomputable def atom1384 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 1) ^ 1 * (g 7) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1384_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1384 g t z = CoefficientMerge.eval (monomial g t z) coeff1384 := by
  norm_num [atom1384, coeff1384, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1384_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1384 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1384]
  positivity
theorem weighted1384_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (6905085315511762603367968537211444731415638568988359937387944802212437117794231787125738136267743357625313744141469902205810204483456000 : Int) coeff1384) := by
  rw [CoefficientMerge.eval_scale, ← atom1384_identity]
  exact mul_nonneg (by norm_num) (atom1384_nonneg g t z hg hA hB ht hz hw)

def sparseBlock100 : CoefficientMerge.Poly :=
  [(786441, 2795830100677703894469638896022611500957008332066065853134794634777396284149172774235194488187775024115136950356182000728156982952960000), (786453, 37114476220426921461913870660144911612759492464928243829327248414850438104738812463535830844503766283058701877289522527183251451402362880), (787458, 1810677902051995204175440196402799628420115920785631293461953130752388914189095097633399588347380544488961584387423468872103247012526080), (790530, 595064021255885382423952417337691562465322810223859260214164031929349463653576245730242579646578475983769486984069456565081605786521600), (802821, 2054005297371007980551760680156893837306290112286590458596816752298090725183289895224369854883738268038680934086854793787936661715046400), (1572873, 8308885390771688584726528728824809848613576690855753159983412082558674892600027882105151228838716152921856366796653397794699036695992320), (1572885, 111423655925537104465356661378521191639594019439800201388157896803093055374603284928491202602462889445092143646206130583668012958466672640), (1573890, 5317889748203735248686814454146157896471569680752679219662952647690079559902401416359644123183688981729783561501545740032967181489612800), (1576962, 1308256138681044783304961001492662276247259291456896974778705486046697101784553960270356445544827381038209063262801455566347906665574400), (1589253, 6905085315511762603367968537211444731415638568988359937387944802212437117794231787125738136267743357625313744141469902205810204483456000), (2359305, 8255299640780632023358731147149752391930785834816500961660018417424783600671610961832637851686760498345805750820803002885852709380085760), (2359317, 99282544701111154090730559334460188036975113255578130018674950178841513962386726235789527355618531050030926135710756600970478766088437760), (2359554, 5937305907091322089454380423371098604447979016756580497562919607083374075165571942764462092955612146678144252938888496403763998082437120), (2360322, 5320826235625595230486508925605346703300398534022719439965960998163918527781469714497587823353120930540327343146213749031566794381158400), (2363394, 1308256138681044783304961001492662276247259291456896974778705486046697101784553960270356445544827381038209063262801455566347906665574400), (3145737, 2742244350686647333101841314347554044274217476026813654811400969643504992220755853962681111035819369539086334380331605819310655637053440), (3145749, 24702878219455213880962736550352244718230502648152202287943768091917124904037962992521026153990206231759756206158016602851912586517073920), (3145986, 2204332680041491298621815912465543043900356898064019495580792536991029635120222154527723042223316641454907736274996672739581119555891200), (3146754, 1813614389473855185975134667861988435248944774055671513764961481226227882068163395771343288516812493299505366032091477870702859904071680), (3149826, 595064021255885382423952417337691562465322810223859260214164031929349463653576245730242579646578475983769486984069456565081605786521600)]
theorem sparseBlock100_data : sparseBlock100 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (5937305907091322089454380423371098604447979016756580497562919607083374075165571942764462092955612146678144252938888496403763998082437120 : Int) coeff1365) (CoefficientMerge.scale (2204332680041491298621815912465543043900356898064019495580792536991029635120222154527723042223316641454907736274996672739581119555891200 : Int) coeff1366)) (CoefficientMerge.merge (CoefficientMerge.scale (1810677902051995204175440196402799628420115920785631293461953130752388914189095097633399588347380544488961584387423468872103247012526080 : Int) coeff1367) (CoefficientMerge.merge (CoefficientMerge.scale (5317889748203735248686814454146157896471569680752679219662952647690079559902401416359644123183688981729783561501545740032967181489612800 : Int) coeff1368) (CoefficientMerge.scale (5320826235625595230486508925605346703300398534022719439965960998163918527781469714497587823353120930540327343146213749031566794381158400 : Int) coeff1369)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1813614389473855185975134667861988435248944774055671513764961481226227882068163395771343288516812493299505366032091477870702859904071680 : Int) coeff1370) (CoefficientMerge.scale (595064021255885382423952417337691562465322810223859260214164031929349463653576245730242579646578475983769486984069456565081605786521600 : Int) coeff1371)) (CoefficientMerge.merge (CoefficientMerge.scale (1308256138681044783304961001492662276247259291456896974778705486046697101784553960270356445544827381038209063262801455566347906665574400 : Int) coeff1372) (CoefficientMerge.merge (CoefficientMerge.scale (1308256138681044783304961001492662276247259291456896974778705486046697101784553960270356445544827381038209063262801455566347906665574400 : Int) coeff1373) (CoefficientMerge.scale (595064021255885382423952417337691562465322810223859260214164031929349463653576245730242579646578475983769486984069456565081605786521600 : Int) coeff1374))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (2795830100677703894469638896022611500957008332066065853134794634777396284149172774235194488187775024115136950356182000728156982952960000 : Int) coeff1375) (CoefficientMerge.scale (8308885390771688584726528728824809848613576690855753159983412082558674892600027882105151228838716152921856366796653397794699036695992320 : Int) coeff1376)) (CoefficientMerge.merge (CoefficientMerge.scale (8255299640780632023358731147149752391930785834816500961660018417424783600671610961832637851686760498345805750820803002885852709380085760 : Int) coeff1377) (CoefficientMerge.merge (CoefficientMerge.scale (2742244350686647333101841314347554044274217476026813654811400969643504992220755853962681111035819369539086334380331605819310655637053440 : Int) coeff1378) (CoefficientMerge.scale (37114476220426921461913870660144911612759492464928243829327248414850438104738812463535830844503766283058701877289522527183251451402362880 : Int) coeff1379)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (111423655925537104465356661378521191639594019439800201388157896803093055374603284928491202602462889445092143646206130583668012958466672640 : Int) coeff1380) (CoefficientMerge.scale (99282544701111154090730559334460188036975113255578130018674950178841513962386726235789527355618531050030926135710756600970478766088437760 : Int) coeff1381)) (CoefficientMerge.merge (CoefficientMerge.scale (24702878219455213880962736550352244718230502648152202287943768091917124904037962992521026153990206231759756206158016602851912586517073920 : Int) coeff1382) (CoefficientMerge.merge (CoefficientMerge.scale (2054005297371007980551760680156893837306290112286590458596816752298090725183289895224369854883738268038680934086854793787936661715046400 : Int) coeff1383) (CoefficientMerge.scale (6905085315511762603367968537211444731415638568988359937387944802212437117794231787125738136267743357625313744141469902205810204483456000 : Int) coeff1384)))))) := by decide +kernel
theorem sparseBlock100_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock100 := by
  rw [sparseBlock100_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted1365_nonneg g t z hg hA hB ht hz hw) (weighted1366_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1367_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1368_nonneg g t z hg hA hB ht hz hw) (weighted1369_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1370_nonneg g t z hg hA hB ht hz hw) (weighted1371_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1372_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1373_nonneg g t z hg hA hB ht hz hw) (weighted1374_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted1375_nonneg g t z hg hA hB ht hz hw) (weighted1376_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1377_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1378_nonneg g t z hg hA hB ht hz hw) (weighted1379_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1380_nonneg g t z hg hA hB ht hz hw) (weighted1381_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1382_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1383_nonneg g t z hg hA hB ht hz hw) (weighted1384_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
