import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff1285 : CoefficientMerge.Poly :=
  [(2457600, 1)]
noncomputable def atom1285 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 7) ^ 2 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1285_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1285 g t z = CoefficientMerge.eval (monomial g t z) coeff1285 := by
  norm_num [atom1285, coeff1285, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1285_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1285 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1285]
  positivity
theorem weighted1285_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (37053222767512392561234798824298611191799112929663220096284534900030066499990081749989746696118549734496142102823934354789610753583129600 : Int) coeff1285) := by
  rw [CoefficientMerge.eval_scale, ← atom1285_identity]
  exact mul_nonneg (by norm_num) (atom1285_nonneg g t z hg hA hB ht hz hw)

def coeff1286 : CoefficientMerge.Poly :=
  [(3145920, 1)]
noncomputable def atom1286 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 3 * (z) ^ 3)
theorem atom1286_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1286 g t z = CoefficientMerge.eval (monomial g t z) coeff1286 := by
  norm_num [atom1286, coeff1286, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1286_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1286 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1286]
  positivity
theorem weighted1286_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1049090554611041602065266742458889891990617136116586116761428617934508597595562488037813258407630702350176685051779816414339159541555200 : Int) coeff1286) := by
  rw [CoefficientMerge.eval_scale, ← atom1286_identity]
  exact mul_nonneg (by norm_num) (atom1286_nonneg g t z hg hA hB ht hz hw)

def coeff1287 : CoefficientMerge.Poly :=
  [(3146112, 1)]
noncomputable def atom1287 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 2 * (g 4) ^ 1 * (z) ^ 3)
theorem atom1287_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1287 g t z = CoefficientMerge.eval (monomial g t z) coeff1287 := by
  norm_num [atom1287, coeff1287, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1287_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1287 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1287]
  positivity
theorem weighted1287_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (23318267650387001711835279283886963950645401390179407204769093981411000295592690167028834571853568722724078421475330696914316584209962240 : Int) coeff1287) := by
  rw [CoefficientMerge.eval_scale, ← atom1287_identity]
  exact mul_nonneg (by norm_num) (atom1287_nonneg g t z hg hA hB ht hz hw)

def coeff1288 : CoefficientMerge.Poly :=
  [(3146880, 1)]
noncomputable def atom1288 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 2 * (g 5) ^ 1 * (z) ^ 3)
theorem atom1288_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1288 g t z = CoefficientMerge.eval (monomial g t z) coeff1288 := by
  norm_num [atom1288, coeff1288, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1288_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1288 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1288]
  positivity
theorem weighted1288_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (49167534982039177247067377919630094382136289171570081845482121526905119202892116822350613981929453141554958178853173042100374489423277440 : Int) coeff1288) := by
  rw [CoefficientMerge.eval_scale, ← atom1288_identity]
  exact mul_nonneg (by norm_num) (atom1288_nonneg g t z hg hA hB ht hz hw)

def coeff1289 : CoefficientMerge.Poly :=
  [(3146304, 1)]
noncomputable def atom1289 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 2 * (z) ^ 3)
theorem atom1289_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1289 g t z = CoefficientMerge.eval (monomial g t z) coeff1289 := by
  norm_num [atom1289, coeff1289, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1289_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1289 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1289]
  positivity
theorem weighted1289_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (29019769505361785955786044482039751702672699111492483543735521476157288586944091107281090775742124964858016963960241432052151103992832000 : Int) coeff1289) := by
  rw [CoefficientMerge.eval_scale, ← atom1289_identity]
  exact mul_nonneg (by norm_num) (atom1289_nonneg g t z hg hA hB ht hz hw)

def coeff1290 : CoefficientMerge.Poly :=
  [(3147072, 1)]
noncomputable def atom1290 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 1 * (g 5) ^ 1 * (z) ^ 3)
theorem atom1290_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1290 g t z = CoefficientMerge.eval (monomial g t z) coeff1290 := by
  norm_num [atom1290, coeff1290, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1290_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1290 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1290]
  positivity
theorem weighted1290_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (167871932342906943587076874327059013069623405246190250591032496638881654175466199056770656701552927160123874229720302928205927619193911680 : Int) coeff1290) := by
  rw [CoefficientMerge.eval_scale, ← atom1290_identity]
  exact mul_nonneg (by norm_num) (atom1290_nonneg g t z hg hA hB ht hz hw)

def coeff1291 : CoefficientMerge.Poly :=
  [(3150144, 1)]
noncomputable def atom1291 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (z) ^ 3)
theorem atom1291_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1291 g t z = CoefficientMerge.eval (monomial g t z) coeff1291 := by
  norm_num [atom1291, coeff1291, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1291_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1291 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1291]
  positivity
theorem weighted1291_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (114154543322979754029667877689832938883108738782933839751815336415426851675804310616786174912675969021639865490511727772795419514003280160 : Int) coeff1291) := by
  rw [CoefficientMerge.eval_scale, ← atom1291_identity]
  exact mul_nonneg (by norm_num) (atom1291_nonneg g t z hg hA hB ht hz hw)

def coeff1292 : CoefficientMerge.Poly :=
  [(3162432, 1)]
noncomputable def atom1292 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (z) ^ 3)
theorem atom1292_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1292 g t z = CoefficientMerge.eval (monomial g t z) coeff1292 := by
  norm_num [atom1292, coeff1292, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1292_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1292 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1292]
  positivity
theorem weighted1292_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (103854310925184611256978676012204827529215493777329426801052148342894011014953258227647074282819589990824886105795664204076667718042956960 : Int) coeff1292) := by
  rw [CoefficientMerge.eval_scale, ← atom1292_identity]
  exact mul_nonneg (by norm_num) (atom1292_nonneg g t z hg hA hB ht hz hw)

def coeff1293 : CoefficientMerge.Poly :=
  [(3211584, 1)]
noncomputable def atom1293 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (z) ^ 3)
theorem atom1293_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1293 g t z = CoefficientMerge.eval (monomial g t z) coeff1293 := by
  norm_num [atom1293, coeff1293, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1293_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1293 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1293]
  positivity
theorem weighted1293_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (90349065165222221032961991255870001383360596890545882456984720446854938605937846232954893286251124715746942244259640013689595828044797600 : Int) coeff1293) := by
  rw [CoefficientMerge.eval_scale, ← atom1293_identity]
  exact mul_nonneg (by norm_num) (atom1293_nonneg g t z hg hA hB ht hz hw)

def coeff1294 : CoefficientMerge.Poly :=
  [(3147840, 1)]
noncomputable def atom1294 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 5) ^ 2 * (z) ^ 3)
theorem atom1294_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1294 g t z = CoefficientMerge.eval (monomial g t z) coeff1294 := by
  norm_num [atom1294, coeff1294, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1294_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1294 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1294]
  positivity
theorem weighted1294_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (120730559311251303019862663443541863241678869290895052861192928615738257605622379667274530831744521228220854587623621992804470237367121920 : Int) coeff1294) := by
  rw [CoefficientMerge.eval_scale, ← atom1294_identity]
  exact mul_nonneg (by norm_num) (atom1294_nonneg g t z hg hA hB ht hz hw)

def coeff1295 : CoefficientMerge.Poly :=
  [(3150912, 1)]
noncomputable def atom1295 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (z) ^ 3)
theorem atom1295_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1295 g t z = CoefficientMerge.eval (monomial g t z) coeff1295 := by
  norm_num [atom1295, coeff1295, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1295_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1295 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1295]
  positivity
theorem weighted1295_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (221532542745132621822834609443635635755088672140104100786050930551771958988020199985668294890522039588095273367988649871714355899980971520 : Int) coeff1295) := by
  rw [CoefficientMerge.eval_scale, ← atom1295_identity]
  exact mul_nonneg (by norm_num) (atom1295_nonneg g t z hg hA hB ht hz hw)

def coeff1296 : CoefficientMerge.Poly :=
  [(3163200, 1)]
noncomputable def atom1296 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (z) ^ 3)
theorem atom1296_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1296 g t z = CoefficientMerge.eval (monomial g t z) coeff1296 := by
  norm_num [atom1296, coeff1296, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1296_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1296 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1296]
  positivity
theorem weighted1296_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (203781864382833410837933773912198282403163458570173550765756544768670112658894755540066115200465799990840336092043461318980025106387169920 : Int) coeff1296) := by
  rw [CoefficientMerge.eval_scale, ← atom1296_identity]
  exact mul_nonneg (by norm_num) (atom1296_nonneg g t z hg hA hB ht hz hw)

def coeff1297 : CoefficientMerge.Poly :=
  [(3212352, 1)]
noncomputable def atom1297 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (z) ^ 3)
theorem atom1297_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1297 g t z = CoefficientMerge.eval (monomial g t z) coeff1297 := by
  norm_num [atom1297, coeff1297, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1297_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1297 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1297]
  positivity
theorem weighted1297_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (203723254306183755478373077470051757540899881191897772536145115071903848039391232658468132022824261283568467738191490664857140308394764750 : Int) coeff1297) := by
  rw [CoefficientMerge.eval_scale, ← atom1297_identity]
  exact mul_nonneg (by norm_num) (atom1297_nonneg g t z hg hA hB ht hz hw)

def coeff1298 : CoefficientMerge.Poly :=
  [(3153984, 1)]
noncomputable def atom1298 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 6) ^ 2 * (z) ^ 3)
theorem atom1298_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1298 g t z = CoefficientMerge.eval (monomial g t z) coeff1298 := by
  norm_num [atom1298, coeff1298, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1298_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1298 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1298]
  positivity
theorem weighted1298_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (107759043949097628520098658469017749058382287921685257273913138436616363778155971023648828890101605906749979993631291238453176569168592000 : Int) coeff1298) := by
  rw [CoefficientMerge.eval_scale, ← atom1298_identity]
  exact mul_nonneg (by norm_num) (atom1298_nonneg g t z hg hA hB ht hz hw)

def coeff1299 : CoefficientMerge.Poly :=
  [(3166272, 1)]
noncomputable def atom1299 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (z) ^ 3)
theorem atom1299_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1299 g t z = CoefficientMerge.eval (monomial g t z) coeff1299 := by
  norm_num [atom1299, coeff1299, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1299_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1299 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1299]
  positivity
theorem weighted1299_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (191213769702062511385393028081518253380612387323415775148002023166130476247103219853974786920955953516580966511718462713658260895848995600 : Int) coeff1299) := by
  rw [CoefficientMerge.eval_scale, ← atom1299_identity]
  exact mul_nonneg (by norm_num) (atom1299_nonneg g t z hg hA hB ht hz hw)

def coeff1300 : CoefficientMerge.Poly :=
  [(3215424, 1)]
noncomputable def atom1300 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (z) ^ 3)
theorem atom1300_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1300 g t z = CoefficientMerge.eval (monomial g t z) coeff1300 := by
  norm_num [atom1300, coeff1300, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1300_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1300 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1300]
  positivity
theorem weighted1300_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (167410874888682128069549609510350294233702797718301147295202231173770241193020919621125219742702952811092074494183525867360711437691686080 : Int) coeff1300) := by
  rw [CoefficientMerge.eval_scale, ← atom1300_identity]
  exact mul_nonneg (by norm_num) (atom1300_nonneg g t z hg hA hB ht hz hw)

def coeff1301 : CoefficientMerge.Poly :=
  [(3178560, 1)]
noncomputable def atom1301 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 7) ^ 2 * (z) ^ 3)
theorem atom1301_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1301 g t z = CoefficientMerge.eval (monomial g t z) coeff1301 := by
  norm_num [atom1301, coeff1301, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1301_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1301 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1301]
  positivity
theorem weighted1301_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (82356848002141946166534410439243438857995296067494055436452362816986565861952581319692213075504554162916412547389939780260578695117920320 : Int) coeff1301) := by
  rw [CoefficientMerge.eval_scale, ← atom1301_identity]
  exact mul_nonneg (by norm_num) (atom1301_nonneg g t z hg hA hB ht hz hw)

def coeff1302 : CoefficientMerge.Poly :=
  [(3227712, 1)]
noncomputable def atom1302 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (z) ^ 3)
theorem atom1302_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1302 g t z = CoefficientMerge.eval (monomial g t z) coeff1302 := by
  norm_num [atom1302, coeff1302, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1302_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1302 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1302]
  positivity
theorem weighted1302_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (117579997458085117332390942859767280741108886300264541120625425256800174706115574829576978376968191439795794458579189109269275080580335360 : Int) coeff1302) := by
  rw [CoefficientMerge.eval_scale, ← atom1302_identity]
  exact mul_nonneg (by norm_num) (atom1302_nonneg g t z hg hA hB ht hz hw)

def coeff1303 : CoefficientMerge.Poly :=
  [(3276864, 1)]
noncomputable def atom1303 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 8) ^ 2 * (z) ^ 3)
theorem atom1303_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1303 g t z = CoefficientMerge.eval (monomial g t z) coeff1303 := by
  norm_num [atom1303, coeff1303, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1303_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1303 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1303]
  positivity
theorem weighted1303_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (21336557143478526438058003763130204206892013279940941550299769739106253730077133368835396157911618522083558809326491681756362505899701120 : Int) coeff1303) := by
  rw [CoefficientMerge.eval_scale, ← atom1303_identity]
  exact mul_nonneg (by norm_num) (atom1303_nonneg g t z hg hA hB ht hz hw)

def coeff1304 : CoefficientMerge.Poly :=
  [(3146496, 1)]
noncomputable def atom1304 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 3 * (z) ^ 3)
theorem atom1304_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1304 g t z = CoefficientMerge.eval (monomial g t z) coeff1304 := by
  norm_num [atom1304, coeff1304, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1304_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1304 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1304]
  positivity
theorem weighted1304_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (863060596296160767423236354859153985078033006855176850315523561170413635541701160742168733310139246574672710762125748050865851259392000 : Int) coeff1304) := by
  rw [CoefficientMerge.eval_scale, ← atom1304_identity]
  exact mul_nonneg (by norm_num) (atom1304_nonneg g t z hg hA hB ht hz hw)

def sparseBlock096 : CoefficientMerge.Poly :=
  [(2457600, 37053222767512392561234798824298611191799112929663220096284534900030066499990081749989746696118549734496142102823934354789610753583129600), (3145920, 1049090554611041602065266742458889891990617136116586116761428617934508597595562488037813258407630702350176685051779816414339159541555200), (3146112, 23318267650387001711835279283886963950645401390179407204769093981411000295592690167028834571853568722724078421475330696914316584209962240), (3146304, 29019769505361785955786044482039751702672699111492483543735521476157288586944091107281090775742124964858016963960241432052151103992832000), (3146496, 863060596296160767423236354859153985078033006855176850315523561170413635541701160742168733310139246574672710762125748050865851259392000), (3146880, 49167534982039177247067377919630094382136289171570081845482121526905119202892116822350613981929453141554958178853173042100374489423277440), (3147072, 167871932342906943587076874327059013069623405246190250591032496638881654175466199056770656701552927160123874229720302928205927619193911680), (3147840, 120730559311251303019862663443541863241678869290895052861192928615738257605622379667274530831744521228220854587623621992804470237367121920), (3150144, 114154543322979754029667877689832938883108738782933839751815336415426851675804310616786174912675969021639865490511727772795419514003280160), (3150912, 221532542745132621822834609443635635755088672140104100786050930551771958988020199985668294890522039588095273367988649871714355899980971520), (3153984, 107759043949097628520098658469017749058382287921685257273913138436616363778155971023648828890101605906749979993631291238453176569168592000), (3162432, 103854310925184611256978676012204827529215493777329426801052148342894011014953258227647074282819589990824886105795664204076667718042956960), (3163200, 203781864382833410837933773912198282403163458570173550765756544768670112658894755540066115200465799990840336092043461318980025106387169920), (3166272, 191213769702062511385393028081518253380612387323415775148002023166130476247103219853974786920955953516580966511718462713658260895848995600), (3178560, 82356848002141946166534410439243438857995296067494055436452362816986565861952581319692213075504554162916412547389939780260578695117920320), (3211584, 90349065165222221032961991255870001383360596890545882456984720446854938605937846232954893286251124715746942244259640013689595828044797600), (3212352, 203723254306183755478373077470051757540899881191897772536145115071903848039391232658468132022824261283568467738191490664857140308394764750), (3215424, 167410874888682128069549609510350294233702797718301147295202231173770241193020919621125219742702952811092074494183525867360711437691686080), (3227712, 117579997458085117332390942859767280741108886300264541120625425256800174706115574829576978376968191439795794458579189109269275080580335360), (3276864, 21336557143478526438058003763130204206892013279940941550299769739106253730077133368835396157911618522083558809326491681756362505899701120)]
theorem sparseBlock096_data : sparseBlock096 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (37053222767512392561234798824298611191799112929663220096284534900030066499990081749989746696118549734496142102823934354789610753583129600 : Int) coeff1285) (CoefficientMerge.scale (1049090554611041602065266742458889891990617136116586116761428617934508597595562488037813258407630702350176685051779816414339159541555200 : Int) coeff1286)) (CoefficientMerge.merge (CoefficientMerge.scale (23318267650387001711835279283886963950645401390179407204769093981411000295592690167028834571853568722724078421475330696914316584209962240 : Int) coeff1287) (CoefficientMerge.merge (CoefficientMerge.scale (49167534982039177247067377919630094382136289171570081845482121526905119202892116822350613981929453141554958178853173042100374489423277440 : Int) coeff1288) (CoefficientMerge.scale (29019769505361785955786044482039751702672699111492483543735521476157288586944091107281090775742124964858016963960241432052151103992832000 : Int) coeff1289)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (167871932342906943587076874327059013069623405246190250591032496638881654175466199056770656701552927160123874229720302928205927619193911680 : Int) coeff1290) (CoefficientMerge.scale (114154543322979754029667877689832938883108738782933839751815336415426851675804310616786174912675969021639865490511727772795419514003280160 : Int) coeff1291)) (CoefficientMerge.merge (CoefficientMerge.scale (103854310925184611256978676012204827529215493777329426801052148342894011014953258227647074282819589990824886105795664204076667718042956960 : Int) coeff1292) (CoefficientMerge.merge (CoefficientMerge.scale (90349065165222221032961991255870001383360596890545882456984720446854938605937846232954893286251124715746942244259640013689595828044797600 : Int) coeff1293) (CoefficientMerge.scale (120730559311251303019862663443541863241678869290895052861192928615738257605622379667274530831744521228220854587623621992804470237367121920 : Int) coeff1294))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (221532542745132621822834609443635635755088672140104100786050930551771958988020199985668294890522039588095273367988649871714355899980971520 : Int) coeff1295) (CoefficientMerge.scale (203781864382833410837933773912198282403163458570173550765756544768670112658894755540066115200465799990840336092043461318980025106387169920 : Int) coeff1296)) (CoefficientMerge.merge (CoefficientMerge.scale (203723254306183755478373077470051757540899881191897772536145115071903848039391232658468132022824261283568467738191490664857140308394764750 : Int) coeff1297) (CoefficientMerge.merge (CoefficientMerge.scale (107759043949097628520098658469017749058382287921685257273913138436616363778155971023648828890101605906749979993631291238453176569168592000 : Int) coeff1298) (CoefficientMerge.scale (191213769702062511385393028081518253380612387323415775148002023166130476247103219853974786920955953516580966511718462713658260895848995600 : Int) coeff1299)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (167410874888682128069549609510350294233702797718301147295202231173770241193020919621125219742702952811092074494183525867360711437691686080 : Int) coeff1300) (CoefficientMerge.scale (82356848002141946166534410439243438857995296067494055436452362816986565861952581319692213075504554162916412547389939780260578695117920320 : Int) coeff1301)) (CoefficientMerge.merge (CoefficientMerge.scale (117579997458085117332390942859767280741108886300264541120625425256800174706115574829576978376968191439795794458579189109269275080580335360 : Int) coeff1302) (CoefficientMerge.merge (CoefficientMerge.scale (21336557143478526438058003763130204206892013279940941550299769739106253730077133368835396157911618522083558809326491681756362505899701120 : Int) coeff1303) (CoefficientMerge.scale (863060596296160767423236354859153985078033006855176850315523561170413635541701160742168733310139246574672710762125748050865851259392000 : Int) coeff1304)))))) := by decide +kernel
theorem sparseBlock096_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock096 := by
  rw [sparseBlock096_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted1285_nonneg g t z hg hA hB ht hz hw) (weighted1286_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1287_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1288_nonneg g t z hg hA hB ht hz hw) (weighted1289_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1290_nonneg g t z hg hA hB ht hz hw) (weighted1291_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1292_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1293_nonneg g t z hg hA hB ht hz hw) (weighted1294_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted1295_nonneg g t z hg hA hB ht hz hw) (weighted1296_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1297_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1298_nonneg g t z hg hA hB ht hz hw) (weighted1299_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1300_nonneg g t z hg hA hB ht hz hw) (weighted1301_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1302_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1303_nonneg g t z hg hA hB ht hz hw) (weighted1304_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
