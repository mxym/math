import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff1385 : CoefficientMerge.Poly :=
  [(2375685, 1)]
noncomputable def atom1385 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 1) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1385_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1385 g t z = CoefficientMerge.eval (monomial g t z) coeff1385 := by
  norm_num [atom1385, coeff1385, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1385_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1385 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1385]
  positivity
theorem weighted1385_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (6381950895526788733330564443418934156587818912959245530059259277716233645954338425201329422172770916724684554193364755823367776372072800 : Int) coeff1385) := by
  rw [CoefficientMerge.eval_scale, ← atom1385_identity]
  exact mul_nonneg (by norm_num) (atom1385_nonneg g t z hg hA hB ht hz hw)

def coeff1386 : CoefficientMerge.Poly :=
  [(3162117, 1)]
noncomputable def atom1386 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 1) ^ 1 * (g 7) ^ 1 * (z) ^ 3)
theorem atom1386_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1386 g t z = CoefficientMerge.eval (monomial g t z) coeff1386 := by
  norm_num [atom1386, coeff1386, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1386_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1386 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1386]
  positivity
theorem weighted1386_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2510118823733982405475584814910071418737536987752337285214097492627844323793325132804314371916442234831842952482868009550377080349593600 : Int) coeff1386) := by
  rw [CoefficientMerge.eval_scale, ← atom1386_identity]
  exact mul_nonneg (by norm_num) (atom1386_nonneg g t z hg hA hB ht hz hw)

def coeff1387 : CoefficientMerge.Poly :=
  [(786456, 1)]
noncomputable def atom1387 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 2 * (g 2) ^ 1 * (t) ^ 3)
theorem atom1387_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1387 g t z = CoefficientMerge.eval (monomial g t z) coeff1387 := by
  norm_num [atom1387, coeff1387, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1387_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1387 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1387]
  positivity
theorem weighted1387_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (7979941368075209579712464719013144676354470592425629402713412462837467397856120290514866327357526917886079217614031621549835982744729600 : Int) coeff1387) := by
  rw [CoefficientMerge.eval_scale, ← atom1387_identity]
  exact mul_nonneg (by norm_num) (atom1387_nonneg g t z hg hA hB ht hz hw)

def coeff1388 : CoefficientMerge.Poly :=
  [(1572888, 1)]
noncomputable def atom1388 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 2 * (g 2) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1388_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1388 g t z = CoefficientMerge.eval (monomial g t z) coeff1388 := by
  norm_num [atom1388, coeff1388, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1388_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1388 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1388]
  positivity
theorem weighted1388_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (51355147579664537517635120369063110476097604824525261069275270088581837769429141492957836830249172807172700331838922467801026423041694720 : Int) coeff1388) := by
  rw [CoefficientMerge.eval_scale, ← atom1388_identity]
  exact mul_nonneg (by norm_num) (atom1388_nonneg g t z hg hA hB ht hz hw)

def coeff1389 : CoefficientMerge.Poly :=
  [(2359320, 1)]
noncomputable def atom1389 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 2 * (g 2) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1389_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1389 g t z = CoefficientMerge.eval (monomial g t z) coeff1389 := by
  norm_num [atom1389, coeff1389, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1389_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1389 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1389]
  positivity
theorem weighted1389_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (59171234505083370111679294366937177108485434282818071850174097557114131252367357225428076491075127391456495264131666437414883506916766720 : Int) coeff1389) := by
  rw [CoefficientMerge.eval_scale, ← atom1389_identity]
  exact mul_nonneg (by norm_num) (atom1389_nonneg g t z hg hA hB ht hz hw)

def coeff1390 : CoefficientMerge.Poly :=
  [(3145752, 1)]
noncomputable def atom1390 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 2 * (g 2) ^ 1 * (z) ^ 3)
theorem atom1390_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1390 g t z = CoefficientMerge.eval (monomial g t z) coeff1390 := by
  norm_num [atom1390, coeff1390, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1390_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1390 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1390]
  positivity
theorem weighted1390_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (15796028293494042173756638716887211308742300050718440183612239931369760880794336022985105988183481502169874149906775591163693066619801600 : Int) coeff1390) := by
  rw [CoefficientMerge.eval_scale, ← atom1390_identity]
  exact mul_nonneg (by norm_num) (atom1390_nonneg g t z hg hA hB ht hz hw)

def coeff1391 : CoefficientMerge.Poly :=
  [(786504, 1)]
noncomputable def atom1391 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 2 * (g 3) ^ 1 * (t) ^ 3)
theorem atom1391_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1391 g t z = CoefficientMerge.eval (monomial g t z) coeff1391 := by
  norm_num [atom1391, coeff1391, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1391_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1391 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1391]
  positivity
theorem weighted1391_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (8456663051959175828149739977165917747914060314528341800188886246737840809550978730792719113781851599472537445440985815124623251314483200 : Int) coeff1391) := by
  rw [CoefficientMerge.eval_scale, ← atom1391_identity]
  exact mul_nonneg (by norm_num) (atom1391_nonneg g t z hg hA hB ht hz hw)

def coeff1392 : CoefficientMerge.Poly :=
  [(1572936, 1)]
noncomputable def atom1392 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 2 * (g 3) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1392_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1392 g t z = CoefficientMerge.eval (monomial g t z) coeff1392 := by
  norm_num [atom1392, coeff1392, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1392_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1392 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1392]
  positivity
theorem weighted1392_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (23187572082222731913022821515521956674490497958651152657493949506594842389427896534931008015382292927614441720031491547749088378164736000 : Int) coeff1392) := by
  rw [CoefficientMerge.eval_scale, ← atom1392_identity]
  exact mul_nonneg (by norm_num) (atom1392_nonneg g t z hg hA hB ht hz hw)

def coeff1393 : CoefficientMerge.Poly :=
  [(2359368, 1)]
noncomputable def atom1393 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 2 * (g 3) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1393_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1393 g t z = CoefficientMerge.eval (monomial g t z) coeff1393 := by
  norm_num [atom1393, coeff1393, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1393_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1393 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1393]
  positivity
theorem weighted1393_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (22315831205988395415794127872158552760882045658419980731509337932190306241797354413945740184945751770042268210458491704146712130147123200 : Int) coeff1393) := by
  rw [CoefficientMerge.eval_scale, ← atom1393_identity]
  exact mul_nonneg (by norm_num) (atom1393_nonneg g t z hg hA hB ht hz hw)

def coeff1394 : CoefficientMerge.Poly :=
  [(3145800, 1)]
noncomputable def atom1394 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 2 * (g 3) ^ 1 * (z) ^ 3)
theorem atom1394_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1394 g t z = CoefficientMerge.eval (monomial g t z) coeff1394 := by
  norm_num [atom1394, coeff1394, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1394_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1394 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1394]
  positivity
theorem weighted1394_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (7584922175724839330921046333802513834305608014297169874204274672333304661920436609807451283345310441900363935867985971522247003296870400 : Int) coeff1394) := by
  rw [CoefficientMerge.eval_scale, ← atom1394_identity]
  exact mul_nonneg (by norm_num) (atom1394_nonneg g t z hg hA hB ht hz hw)

def coeff1395 : CoefficientMerge.Poly :=
  [(3145824, 1)]
noncomputable def atom1395 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 2 * (g 3) ^ 1 * (z) ^ 3)
theorem atom1395_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1395 g t z = CoefficientMerge.eval (monomial g t z) coeff1395 := by
  norm_num [atom1395, coeff1395, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1395_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1395 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1395]
  positivity
theorem weighted1395_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (14868573083554949387627262977532756250143952404000902531580606273282353922918343126254276465346629802892133101149397864018364971452631040 : Int) coeff1395) := by
  rw [CoefficientMerge.eval_scale, ← atom1395_identity]
  exact mul_nonneg (by norm_num) (atom1395_nonneg g t z hg hA hB ht hz hw)

def coeff1396 : CoefficientMerge.Poly :=
  [(3146016, 1)]
noncomputable def atom1396 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 2 * (g 4) ^ 1 * (z) ^ 3)
theorem atom1396_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1396 g t z = CoefficientMerge.eval (monomial g t z) coeff1396 := by
  norm_num [atom1396, coeff1396, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1396_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1396 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1396]
  positivity
theorem weighted1396_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3669332003672454527063161546995973860118976087041864703558842554685723680750533125148351990712645995456425939928120286389672092744051968 : Int) coeff1396) := by
  rw [CoefficientMerge.eval_scale, ← atom1396_identity]
  exact mul_nonneg (by norm_num) (atom1396_nonneg g t z hg hA hB ht hz hw)

def coeff1397 : CoefficientMerge.Poly :=
  [(3149856, 1)]
noncomputable def atom1397 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 2 * (g 6) ^ 1 * (z) ^ 3)
theorem atom1397_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1397 g t z = CoefficientMerge.eval (monomial g t z) coeff1397 := by
  norm_num [atom1397, coeff1397, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1397_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1397 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1397]
  positivity
theorem weighted1397_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (17928567633676122538902652313719632319489183862270500125732915973466283702811217105402635887314491613874603755990471845951300979677962240 : Int) coeff1397) := by
  rw [CoefficientMerge.eval_scale, ← atom1397_identity]
  exact mul_nonneg (by norm_num) (atom1397_nonneg g t z hg hA hB ht hz hw)

def coeff1398 : CoefficientMerge.Poly :=
  [(3145872, 1)]
noncomputable def atom1398 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 2 * (z) ^ 3)
theorem atom1398_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1398 g t z = CoefficientMerge.eval (monomial g t z) coeff1398 := by
  norm_num [atom1398, coeff1398, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1398_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1398 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1398]
  positivity
theorem weighted1398_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (99588746235299818798889528551787549650242476182182729938947696851775786316267052682171485207873259237042735906711139507473678176254856960 : Int) coeff1398) := by
  rw [CoefficientMerge.eval_scale, ← atom1398_identity]
  exact mul_nonneg (by norm_num) (atom1398_nonneg g t z hg hA hB ht hz hw)

def coeff1399 : CoefficientMerge.Poly :=
  [(3146256, 1)]
noncomputable def atom1399 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 2 * (z) ^ 3)
theorem atom1399_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1399 g t z = CoefficientMerge.eval (monomial g t z) coeff1399 := by
  norm_num [atom1399, coeff1399, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1399_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1399 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1399]
  positivity
theorem weighted1399_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (50563115937394209232669027536968218085447580574088969305386184566797060864354893726138561293848384451770727752360954605049961182635382400 : Int) coeff1399) := by
  rw [CoefficientMerge.eval_scale, ← atom1399_identity]
  exact mul_nonneg (by norm_num) (atom1399_nonneg g t z hg hA hB ht hz hw)

def coeff1400 : CoefficientMerge.Poly :=
  [(540944, 1)]
noncomputable def atom1400 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (t) ^ 2)
theorem atom1400_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1400 g t z = CoefficientMerge.eval (monomial g t z) coeff1400 := by
  norm_num [atom1400, coeff1400, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1400_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1400 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1400]
  positivity
theorem weighted1400_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2420694799674856529619260083504052915610016441331666492635690608332523938026674975558135296433281027317281168630588441483228411237074611200 : Int) coeff1400) := by
  rw [CoefficientMerge.eval_scale, ← atom1400_identity]
  exact mul_nonneg (by norm_num) (atom1400_nonneg g t z hg hA hB ht hz hw)

def coeff1401 : CoefficientMerge.Poly :=
  [(2097185, 1)]
noncomputable def atom1401 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 2 * (z) ^ 2)
theorem atom1401_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1401 g t z = CoefficientMerge.eval (monomial g t z) coeff1401 := by
  norm_num [atom1401, coeff1401, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1401_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1401 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1401]
  positivity
theorem weighted1401_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (346218907044508254199882476700835727461293313521277905198335628223190951464956636482773989978140396910066573472380391341664429842449776640 : Int) coeff1401) := by
  rw [CoefficientMerge.eval_scale, ← atom1401_identity]
  exact mul_nonneg (by norm_num) (atom1401_nonneg g t z hg hA hB ht hz hw)

def coeff1402 : CoefficientMerge.Poly :=
  [(2097188, 1)]
noncomputable def atom1402 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 2 * (z) ^ 2)
theorem atom1402_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1402 g t z = CoefficientMerge.eval (monomial g t z) coeff1402 := by
  norm_num [atom1402, coeff1402, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1402_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1402 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1402]
  positivity
theorem weighted1402_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (326628682864775085721203789406401932051538749222847617164179857264628789957068852688038295410936642898920134319495370811381001150711353344 : Int) coeff1402) := by
  rw [CoefficientMerge.eval_scale, ← atom1402_identity]
  exact mul_nonneg (by norm_num) (atom1402_nonneg g t z hg hA hB ht hz hw)

def coeff1403 : CoefficientMerge.Poly :=
  [(802818, 1)]
noncomputable def atom1403 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 2 * (g 7) ^ 1 * (t) ^ 3)
theorem atom1403_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1403 g t z = CoefficientMerge.eval (monomial g t z) coeff1403 := by
  norm_num [atom1403, coeff1403, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1403_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1403 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1403]
  positivity
theorem weighted1403_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1100513854239502006061549598295190938117831329136009159804769535886059866574280679833345037478561927289656450533893653897314642994278400 : Int) coeff1403) := by
  rw [CoefficientMerge.eval_scale, ← atom1403_identity]
  exact mul_nonneg (by norm_num) (atom1403_nonneg g t z hg hA hB ht hz hw)

def coeff1404 : CoefficientMerge.Poly :=
  [(1589250, 1)]
noncomputable def atom1404 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 2 * (g 7) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1404_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1404 g t z = CoefficientMerge.eval (monomial g t z) coeff1404 := by
  norm_num [atom1404, coeff1404, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1404_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1404 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1404]
  positivity
theorem weighted1404_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2760606020014660661465050745059749478452223719260279036887301836959053270224140133503277173642694012757008234858246400326642301865062400 : Int) coeff1404) := by
  rw [CoefficientMerge.eval_scale, ← atom1404_identity]
  exact mul_nonneg (by norm_num) (atom1404_nonneg g t z hg hA hB ht hz hw)

def sparseBlock101 : CoefficientMerge.Poly :=
  [(540944, 2420694799674856529619260083504052915610016441331666492635690608332523938026674975558135296433281027317281168630588441483228411237074611200), (786456, 7979941368075209579712464719013144676354470592425629402713412462837467397856120290514866327357526917886079217614031621549835982744729600), (786504, 8456663051959175828149739977165917747914060314528341800188886246737840809550978730792719113781851599472537445440985815124623251314483200), (802818, 1100513854239502006061549598295190938117831329136009159804769535886059866574280679833345037478561927289656450533893653897314642994278400), (1572888, 51355147579664537517635120369063110476097604824525261069275270088581837769429141492957836830249172807172700331838922467801026423041694720), (1572936, 23187572082222731913022821515521956674490497958651152657493949506594842389427896534931008015382292927614441720031491547749088378164736000), (1589250, 2760606020014660661465050745059749478452223719260279036887301836959053270224140133503277173642694012757008234858246400326642301865062400), (2097185, 346218907044508254199882476700835727461293313521277905198335628223190951464956636482773989978140396910066573472380391341664429842449776640), (2097188, 326628682864775085721203789406401932051538749222847617164179857264628789957068852688038295410936642898920134319495370811381001150711353344), (2359320, 59171234505083370111679294366937177108485434282818071850174097557114131252367357225428076491075127391456495264131666437414883506916766720), (2359368, 22315831205988395415794127872158552760882045658419980731509337932190306241797354413945740184945751770042268210458491704146712130147123200), (2375685, 6381950895526788733330564443418934156587818912959245530059259277716233645954338425201329422172770916724684554193364755823367776372072800), (3145752, 15796028293494042173756638716887211308742300050718440183612239931369760880794336022985105988183481502169874149906775591163693066619801600), (3145800, 7584922175724839330921046333802513834305608014297169874204274672333304661920436609807451283345310441900363935867985971522247003296870400), (3145824, 14868573083554949387627262977532756250143952404000902531580606273282353922918343126254276465346629802892133101149397864018364971452631040), (3145872, 99588746235299818798889528551787549650242476182182729938947696851775786316267052682171485207873259237042735906711139507473678176254856960), (3146016, 3669332003672454527063161546995973860118976087041864703558842554685723680750533125148351990712645995456425939928120286389672092744051968), (3146256, 50563115937394209232669027536968218085447580574088969305386184566797060864354893726138561293848384451770727752360954605049961182635382400), (3149856, 17928567633676122538902652313719632319489183862270500125732915973466283702811217105402635887314491613874603755990471845951300979677962240), (3162117, 2510118823733982405475584814910071418737536987752337285214097492627844323793325132804314371916442234831842952482868009550377080349593600)]
theorem sparseBlock101_data : sparseBlock101 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (6381950895526788733330564443418934156587818912959245530059259277716233645954338425201329422172770916724684554193364755823367776372072800 : Int) coeff1385) (CoefficientMerge.scale (2510118823733982405475584814910071418737536987752337285214097492627844323793325132804314371916442234831842952482868009550377080349593600 : Int) coeff1386)) (CoefficientMerge.merge (CoefficientMerge.scale (7979941368075209579712464719013144676354470592425629402713412462837467397856120290514866327357526917886079217614031621549835982744729600 : Int) coeff1387) (CoefficientMerge.merge (CoefficientMerge.scale (51355147579664537517635120369063110476097604824525261069275270088581837769429141492957836830249172807172700331838922467801026423041694720 : Int) coeff1388) (CoefficientMerge.scale (59171234505083370111679294366937177108485434282818071850174097557114131252367357225428076491075127391456495264131666437414883506916766720 : Int) coeff1389)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (15796028293494042173756638716887211308742300050718440183612239931369760880794336022985105988183481502169874149906775591163693066619801600 : Int) coeff1390) (CoefficientMerge.scale (8456663051959175828149739977165917747914060314528341800188886246737840809550978730792719113781851599472537445440985815124623251314483200 : Int) coeff1391)) (CoefficientMerge.merge (CoefficientMerge.scale (23187572082222731913022821515521956674490497958651152657493949506594842389427896534931008015382292927614441720031491547749088378164736000 : Int) coeff1392) (CoefficientMerge.merge (CoefficientMerge.scale (22315831205988395415794127872158552760882045658419980731509337932190306241797354413945740184945751770042268210458491704146712130147123200 : Int) coeff1393) (CoefficientMerge.scale (7584922175724839330921046333802513834305608014297169874204274672333304661920436609807451283345310441900363935867985971522247003296870400 : Int) coeff1394))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (14868573083554949387627262977532756250143952404000902531580606273282353922918343126254276465346629802892133101149397864018364971452631040 : Int) coeff1395) (CoefficientMerge.scale (3669332003672454527063161546995973860118976087041864703558842554685723680750533125148351990712645995456425939928120286389672092744051968 : Int) coeff1396)) (CoefficientMerge.merge (CoefficientMerge.scale (17928567633676122538902652313719632319489183862270500125732915973466283702811217105402635887314491613874603755990471845951300979677962240 : Int) coeff1397) (CoefficientMerge.merge (CoefficientMerge.scale (99588746235299818798889528551787549650242476182182729938947696851775786316267052682171485207873259237042735906711139507473678176254856960 : Int) coeff1398) (CoefficientMerge.scale (50563115937394209232669027536968218085447580574088969305386184566797060864354893726138561293848384451770727752360954605049961182635382400 : Int) coeff1399)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (2420694799674856529619260083504052915610016441331666492635690608332523938026674975558135296433281027317281168630588441483228411237074611200 : Int) coeff1400) (CoefficientMerge.scale (346218907044508254199882476700835727461293313521277905198335628223190951464956636482773989978140396910066573472380391341664429842449776640 : Int) coeff1401)) (CoefficientMerge.merge (CoefficientMerge.scale (326628682864775085721203789406401932051538749222847617164179857264628789957068852688038295410936642898920134319495370811381001150711353344 : Int) coeff1402) (CoefficientMerge.merge (CoefficientMerge.scale (1100513854239502006061549598295190938117831329136009159804769535886059866574280679833345037478561927289656450533893653897314642994278400 : Int) coeff1403) (CoefficientMerge.scale (2760606020014660661465050745059749478452223719260279036887301836959053270224140133503277173642694012757008234858246400326642301865062400 : Int) coeff1404)))))) := by decide +kernel
theorem sparseBlock101_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock101 := by
  rw [sparseBlock101_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted1385_nonneg g t z hg hA hB ht hz hw) (weighted1386_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1387_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1388_nonneg g t z hg hA hB ht hz hw) (weighted1389_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1390_nonneg g t z hg hA hB ht hz hw) (weighted1391_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1392_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1393_nonneg g t z hg hA hB ht hz hw) (weighted1394_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted1395_nonneg g t z hg hA hB ht hz hw) (weighted1396_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1397_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1398_nonneg g t z hg hA hB ht hz hw) (weighted1399_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1400_nonneg g t z hg hA hB ht hz hw) (weighted1401_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1402_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1403_nonneg g t z hg hA hB ht hz hw) (weighted1404_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
