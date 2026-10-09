import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff0625 : CoefficientMerge.Poly :=
  [(540737, 1)]
noncomputable def atom0625 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 7) ^ 1 * (t) ^ 2)
theorem atom0625_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0625 g t z = CoefficientMerge.eval (monomial g t z) coeff0625 := by
  norm_num [atom0625, coeff0625, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0625_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0625 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0625]
  positivity
theorem weighted0625_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (918756139293164734280282216265075858518598915531304859587877553649275360460071761189146849150374900998621777740810549648265256973638819840 : Int) coeff0625) := by
  rw [CoefficientMerge.eval_scale, ← atom0625_identity]
  exact mul_nonneg (by norm_num) (atom0625_nonneg g t z hg hA hB ht hz hw)

def coeff0626 : CoefficientMerge.Poly :=
  [(589889, 1)]
noncomputable def atom0626 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 8) ^ 1 * (t) ^ 2)
theorem atom0626_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0626 g t z = CoefficientMerge.eval (monomial g t z) coeff0626 := by
  norm_num [atom0626, coeff0626, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0626_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0626 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0626]
  positivity
theorem weighted0626_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1068407912732578685694524745732988140955221176817224878626688568050500435623790004952197533504613308276127230925391673434745396861709670400 : Int) coeff0626) := by
  rw [CoefficientMerge.eval_scale, ← atom0626_identity]
  exact mul_nonneg (by norm_num) (atom0626_nonneg g t z hg hA hB ht hz hw)

def coeff0627 : CoefficientMerge.Poly :=
  [(1310849, 1)]
noncomputable def atom0627 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 2 * (t) ^ 1 * (z) ^ 1)
theorem atom0627_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0627 g t z = CoefficientMerge.eval (monomial g t z) coeff0627 := by
  norm_num [atom0627, coeff0627, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0627_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0627 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0627]
  positivity
theorem weighted0627_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1693526018371232855907356030632397731134101567894048320257561978259526244539389387216432363455413845420411844830415124174894952975877813760 : Int) coeff0627) := by
  rw [CoefficientMerge.eval_scale, ← atom0627_identity]
  exact mul_nonneg (by norm_num) (atom0627_nonneg g t z hg hA hB ht hz hw)

def coeff0628 : CoefficientMerge.Poly :=
  [(1311041, 1)]
noncomputable def atom0628 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 4) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0628_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0628 g t z = CoefficientMerge.eval (monomial g t z) coeff0628 := by
  norm_num [atom0628, coeff0628, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0628_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0628 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0628]
  positivity
theorem weighted0628_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3275096176577753988742393354519517028765751240097682559226436197650434474577482434986655834010491185034070323959233184116239804669293492032 : Int) coeff0628) := by
  rw [CoefficientMerge.eval_scale, ← atom0628_identity]
  exact mul_nonneg (by norm_num) (atom0628_nonneg g t z hg hA hB ht hz hw)

def coeff0629 : CoefficientMerge.Poly :=
  [(1311809, 1)]
noncomputable def atom0629 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 5) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0629_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0629 g t z = CoefficientMerge.eval (monomial g t z) coeff0629 := by
  norm_num [atom0629, coeff0629, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0629_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0629 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0629]
  positivity
theorem weighted0629_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4294613170927161574875928438000479404026524015543071279898121905979115501581067491871023183032203621947024469188189370340356514667057741824 : Int) coeff0629) := by
  rw [CoefficientMerge.eval_scale, ← atom0629_identity]
  exact mul_nonneg (by norm_num) (atom0629_nonneg g t z hg hA hB ht hz hw)

def coeff0630 : CoefficientMerge.Poly :=
  [(1314881, 1)]
noncomputable def atom0630 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0630_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0630 g t z = CoefficientMerge.eval (monomial g t z) coeff0630 := by
  norm_num [atom0630, coeff0630, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0630_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0630 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0630]
  positivity
theorem weighted0630_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3637090358713287957171882403699291734379069303644562391741102786428143713532600063583600099523131211355917518110786921456133426870927902720 : Int) coeff0630) := by
  rw [CoefficientMerge.eval_scale, ← atom0630_identity]
  exact mul_nonneg (by norm_num) (atom0630_nonneg g t z hg hA hB ht hz hw)

def coeff0631 : CoefficientMerge.Poly :=
  [(1327169, 1)]
noncomputable def atom0631 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0631_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0631 g t z = CoefficientMerge.eval (monomial g t z) coeff0631 := by
  norm_num [atom0631, coeff0631, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0631_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0631 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0631]
  positivity
theorem weighted0631_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1990219590721671778366516743812607712307933781291377869508742050521025480045412395629381874116616577426870078463683809010402942592136017920 : Int) coeff0631) := by
  rw [CoefficientMerge.eval_scale, ← atom0631_identity]
  exact mul_nonneg (by norm_num) (atom0631_nonneg g t z hg hA hB ht hz hw)

def coeff0632 : CoefficientMerge.Poly :=
  [(1376321, 1)]
noncomputable def atom0632 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0632_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0632 g t z = CoefficientMerge.eval (monomial g t z) coeff0632 := by
  norm_num [atom0632, coeff0632, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0632_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0632 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0632]
  positivity
theorem weighted0632_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2322090918283244499599908635959073660325723224554788317614653581762409078586045575836726984170930426165776553454280415662989827235600230400 : Int) coeff0632) := by
  rw [CoefficientMerge.eval_scale, ← atom0632_identity]
  exact mul_nonneg (by norm_num) (atom0632_nonneg g t z hg hA hB ht hz hw)

def coeff0633 : CoefficientMerge.Poly :=
  [(524801, 1)]
noncomputable def atom0633 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 2 * (t) ^ 2)
theorem atom0633_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0633 g t z = CoefficientMerge.eval (monomial g t z) coeff0633 := by
  norm_num [atom0633, coeff0633, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0633_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0633 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0633]
  positivity
theorem weighted0633_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (809605275778024889315840312546679245098097549523529121838878193388677502401913780946114644302120399630344223399041648801173537056990412800 : Int) coeff0633) := by
  rw [CoefficientMerge.eval_scale, ← atom0633_identity]
  exact mul_nonneg (by norm_num) (atom0633_nonneg g t z hg hA hB ht hz hw)

def coeff0634 : CoefficientMerge.Poly :=
  [(525569, 1)]
noncomputable def atom0634 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 5) ^ 1 * (t) ^ 2)
theorem atom0634_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0634 g t z = CoefficientMerge.eval (monomial g t z) coeff0634 := by
  norm_num [atom0634, coeff0634, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0634_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0634 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0634]
  positivity
theorem weighted0634_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1691047609437623316866553380555175024871069069895514027296753509737327635280562266656127684015257543928739001962100690917958424248776047360 : Int) coeff0634) := by
  rw [CoefficientMerge.eval_scale, ← atom0634_identity]
  exact mul_nonneg (by norm_num) (atom0634_nonneg g t z hg hA hB ht hz hw)

def coeff0635 : CoefficientMerge.Poly :=
  [(528641, 1)]
noncomputable def atom0635 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (t) ^ 2)
theorem atom0635_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0635 g t z = CoefficientMerge.eval (monomial g t z) coeff0635 := by
  norm_num [atom0635, coeff0635, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0635_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0635 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0635]
  positivity
theorem weighted0635_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1898109656227188387093946831798689873922763463586431776297581995203899133246753426029564413470855408168076658974636193386638303037232899840 : Int) coeff0635) := by
  rw [CoefficientMerge.eval_scale, ← atom0635_identity]
  exact mul_nonneg (by norm_num) (atom0635_nonneg g t z hg hA hB ht hz hw)

def coeff0636 : CoefficientMerge.Poly :=
  [(540929, 1)]
noncomputable def atom0636 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (t) ^ 2)
theorem atom0636_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0636 g t z = CoefficientMerge.eval (monomial g t z) coeff0636 := by
  norm_num [atom0636, coeff0636, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0636_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0636 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0636]
  positivity
theorem weighted0636_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (946911372411665385053245778382179978854247802933885714412972873508789408499291151214563838457467182000909284950719107900223023093421735680 : Int) coeff0636) := by
  rw [CoefficientMerge.eval_scale, ← atom0636_identity]
  exact mul_nonneg (by norm_num) (atom0636_nonneg g t z hg hA hB ht hz hw)

def coeff0637 : CoefficientMerge.Poly :=
  [(590081, 1)]
noncomputable def atom0637 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (t) ^ 2)
theorem atom0637_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0637 g t z = CoefficientMerge.eval (monomial g t z) coeff0637 := by
  norm_num [atom0637, coeff0637, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0637_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0637 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0637]
  positivity
theorem weighted0637_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (945338709508902003042672697330500133434584345248236311837193465277969978625419518802307205178821856324507865843641572030880806946836268800 : Int) coeff0637) := by
  rw [CoefficientMerge.eval_scale, ← atom0637_identity]
  exact mul_nonneg (by norm_num) (atom0637_nonneg g t z hg hA hB ht hz hw)

def coeff0638 : CoefficientMerge.Poly :=
  [(1311233, 1)]
noncomputable def atom0638 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 2 * (t) ^ 1 * (z) ^ 1)
theorem atom0638_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0638 g t z = CoefficientMerge.eval (monomial g t z) coeff0638 := by
  norm_num [atom0638, coeff0638, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0638_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0638 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0638]
  positivity
theorem weighted0638_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1218398444943492630533523023811946295733541536679728198578440521970571713646797781947915608799448254225971288713946910853129283589763647104 : Int) coeff0638) := by
  rw [CoefficientMerge.eval_scale, ← atom0638_identity]
  exact mul_nonneg (by norm_num) (atom0638_nonneg g t z hg hA hB ht hz hw)

def coeff0639 : CoefficientMerge.Poly :=
  [(1312001, 1)]
noncomputable def atom0639 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 5) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0639_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0639 g t z = CoefficientMerge.eval (monomial g t z) coeff0639 := by
  norm_num [atom0639, coeff0639, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0639_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0639 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0639]
  positivity
theorem weighted0639_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3069114974190551756039296783160601929007798573259349491333779356524556526035023370473008877184118569650878764109587363851797997876904782368 : Int) coeff0639) := by
  rw [CoefficientMerge.eval_scale, ← atom0639_identity]
  exact mul_nonneg (by norm_num) (atom0639_nonneg g t z hg hA hB ht hz hw)

def coeff0640 : CoefficientMerge.Poly :=
  [(1315073, 1)]
noncomputable def atom0640 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0640_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0640 g t z = CoefficientMerge.eval (monomial g t z) coeff0640 := by
  norm_num [atom0640, coeff0640, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0640_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0640 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0640]
  positivity
theorem weighted0640_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3130717610723582498207964919069551341914136483015835123095985830597700819553259123087339264848716738742011825871979707991355667823945797920 : Int) coeff0640) := by
  rw [CoefficientMerge.eval_scale, ← atom0640_identity]
  exact mul_nonneg (by norm_num) (atom0640_nonneg g t z hg hA hB ht hz hw)

def coeff0641 : CoefficientMerge.Poly :=
  [(1327361, 1)]
noncomputable def atom0641 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0641_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0641 g t z = CoefficientMerge.eval (monomial g t z) coeff0641 := by
  norm_num [atom0641, coeff0641, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0641_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0641 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0641]
  positivity
theorem weighted0641_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1431594606526286288011399049569352884684394894938564940433074892694381165666223332901378504042054258976157588320273215592098225184437421600 : Int) coeff0641) := by
  rw [CoefficientMerge.eval_scale, ← atom0641_identity]
  exact mul_nonneg (by norm_num) (atom0641_nonneg g t z hg hA hB ht hz hw)

def coeff0642 : CoefficientMerge.Poly :=
  [(1376513, 1)]
noncomputable def atom0642 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0642_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0642 g t z = CoefficientMerge.eval (monomial g t z) coeff0642 := by
  norm_num [atom0642, coeff0642, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0642_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0642 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0642]
  positivity
theorem weighted0642_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1584833233051683553357332031488333853396763970569203429907906871277291544943865382031338949776517251525828691678735527833499103220027959840 : Int) coeff0642) := by
  rw [CoefficientMerge.eval_scale, ← atom0642_identity]
  exact mul_nonneg (by norm_num) (atom0642_nonneg g t z hg hA hB ht hz hw)

def coeff0643 : CoefficientMerge.Poly :=
  [(526337, 1)]
noncomputable def atom0643 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 2 * (t) ^ 2)
theorem atom0643_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0643 g t z = CoefficientMerge.eval (monomial g t z) coeff0643 := by
  norm_num [atom0643, coeff0643, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0643_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0643 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0643]
  positivity
theorem weighted0643_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (941468442193609475080623838869863142959389411236723249440407547425201490906104479329302816913500863108243467723906141079498195233460633600 : Int) coeff0643) := by
  rw [CoefficientMerge.eval_scale, ← atom0643_identity]
  exact mul_nonneg (by norm_num) (atom0643_nonneg g t z hg hA hB ht hz hw)

def coeff0644 : CoefficientMerge.Poly :=
  [(529409, 1)]
noncomputable def atom0644 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (t) ^ 2)
theorem atom0644_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0644 g t z = CoefficientMerge.eval (monomial g t z) coeff0644 := by
  norm_num [atom0644, coeff0644, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0644_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0644 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0644]
  positivity
theorem weighted0644_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1730954927128511165156943401740634277720588309729993088823446226501956317569150305861856774003819691024945437408827382299717115641622661120 : Int) coeff0644) := by
  rw [CoefficientMerge.eval_scale, ← atom0644_identity]
  exact mul_nonneg (by norm_num) (atom0644_nonneg g t z hg hA hB ht hz hw)

def sparseBlock063 : CoefficientMerge.Poly :=
  [(524801, 809605275778024889315840312546679245098097549523529121838878193388677502401913780946114644302120399630344223399041648801173537056990412800), (525569, 1691047609437623316866553380555175024871069069895514027296753509737327635280562266656127684015257543928739001962100690917958424248776047360), (526337, 941468442193609475080623838869863142959389411236723249440407547425201490906104479329302816913500863108243467723906141079498195233460633600), (528641, 1898109656227188387093946831798689873922763463586431776297581995203899133246753426029564413470855408168076658974636193386638303037232899840), (529409, 1730954927128511165156943401740634277720588309729993088823446226501956317569150305861856774003819691024945437408827382299717115641622661120), (540737, 918756139293164734280282216265075858518598915531304859587877553649275360460071761189146849150374900998621777740810549648265256973638819840), (540929, 946911372411665385053245778382179978854247802933885714412972873508789408499291151214563838457467182000909284950719107900223023093421735680), (589889, 1068407912732578685694524745732988140955221176817224878626688568050500435623790004952197533504613308276127230925391673434745396861709670400), (590081, 945338709508902003042672697330500133434584345248236311837193465277969978625419518802307205178821856324507865843641572030880806946836268800), (1310849, 1693526018371232855907356030632397731134101567894048320257561978259526244539389387216432363455413845420411844830415124174894952975877813760), (1311041, 3275096176577753988742393354519517028765751240097682559226436197650434474577482434986655834010491185034070323959233184116239804669293492032), (1311233, 1218398444943492630533523023811946295733541536679728198578440521970571713646797781947915608799448254225971288713946910853129283589763647104), (1311809, 4294613170927161574875928438000479404026524015543071279898121905979115501581067491871023183032203621947024469188189370340356514667057741824), (1312001, 3069114974190551756039296783160601929007798573259349491333779356524556526035023370473008877184118569650878764109587363851797997876904782368), (1314881, 3637090358713287957171882403699291734379069303644562391741102786428143713532600063583600099523131211355917518110786921456133426870927902720), (1315073, 3130717610723582498207964919069551341914136483015835123095985830597700819553259123087339264848716738742011825871979707991355667823945797920), (1327169, 1990219590721671778366516743812607712307933781291377869508742050521025480045412395629381874116616577426870078463683809010402942592136017920), (1327361, 1431594606526286288011399049569352884684394894938564940433074892694381165666223332901378504042054258976157588320273215592098225184437421600), (1376321, 2322090918283244499599908635959073660325723224554788317614653581762409078586045575836726984170930426165776553454280415662989827235600230400), (1376513, 1584833233051683553357332031488333853396763970569203429907906871277291544943865382031338949776517251525828691678735527833499103220027959840)]
theorem sparseBlock063_data : sparseBlock063 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (918756139293164734280282216265075858518598915531304859587877553649275360460071761189146849150374900998621777740810549648265256973638819840 : Int) coeff0625) (CoefficientMerge.scale (1068407912732578685694524745732988140955221176817224878626688568050500435623790004952197533504613308276127230925391673434745396861709670400 : Int) coeff0626)) (CoefficientMerge.merge (CoefficientMerge.scale (1693526018371232855907356030632397731134101567894048320257561978259526244539389387216432363455413845420411844830415124174894952975877813760 : Int) coeff0627) (CoefficientMerge.merge (CoefficientMerge.scale (3275096176577753988742393354519517028765751240097682559226436197650434474577482434986655834010491185034070323959233184116239804669293492032 : Int) coeff0628) (CoefficientMerge.scale (4294613170927161574875928438000479404026524015543071279898121905979115501581067491871023183032203621947024469188189370340356514667057741824 : Int) coeff0629)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (3637090358713287957171882403699291734379069303644562391741102786428143713532600063583600099523131211355917518110786921456133426870927902720 : Int) coeff0630) (CoefficientMerge.scale (1990219590721671778366516743812607712307933781291377869508742050521025480045412395629381874116616577426870078463683809010402942592136017920 : Int) coeff0631)) (CoefficientMerge.merge (CoefficientMerge.scale (2322090918283244499599908635959073660325723224554788317614653581762409078586045575836726984170930426165776553454280415662989827235600230400 : Int) coeff0632) (CoefficientMerge.merge (CoefficientMerge.scale (809605275778024889315840312546679245098097549523529121838878193388677502401913780946114644302120399630344223399041648801173537056990412800 : Int) coeff0633) (CoefficientMerge.scale (1691047609437623316866553380555175024871069069895514027296753509737327635280562266656127684015257543928739001962100690917958424248776047360 : Int) coeff0634))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1898109656227188387093946831798689873922763463586431776297581995203899133246753426029564413470855408168076658974636193386638303037232899840 : Int) coeff0635) (CoefficientMerge.scale (946911372411665385053245778382179978854247802933885714412972873508789408499291151214563838457467182000909284950719107900223023093421735680 : Int) coeff0636)) (CoefficientMerge.merge (CoefficientMerge.scale (945338709508902003042672697330500133434584345248236311837193465277969978625419518802307205178821856324507865843641572030880806946836268800 : Int) coeff0637) (CoefficientMerge.merge (CoefficientMerge.scale (1218398444943492630533523023811946295733541536679728198578440521970571713646797781947915608799448254225971288713946910853129283589763647104 : Int) coeff0638) (CoefficientMerge.scale (3069114974190551756039296783160601929007798573259349491333779356524556526035023370473008877184118569650878764109587363851797997876904782368 : Int) coeff0639)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (3130717610723582498207964919069551341914136483015835123095985830597700819553259123087339264848716738742011825871979707991355667823945797920 : Int) coeff0640) (CoefficientMerge.scale (1431594606526286288011399049569352884684394894938564940433074892694381165666223332901378504042054258976157588320273215592098225184437421600 : Int) coeff0641)) (CoefficientMerge.merge (CoefficientMerge.scale (1584833233051683553357332031488333853396763970569203429907906871277291544943865382031338949776517251525828691678735527833499103220027959840 : Int) coeff0642) (CoefficientMerge.merge (CoefficientMerge.scale (941468442193609475080623838869863142959389411236723249440407547425201490906104479329302816913500863108243467723906141079498195233460633600 : Int) coeff0643) (CoefficientMerge.scale (1730954927128511165156943401740634277720588309729993088823446226501956317569150305861856774003819691024945437408827382299717115641622661120 : Int) coeff0644)))))) := by decide +kernel
theorem sparseBlock063_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock063 := by
  rw [sparseBlock063_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted0625_nonneg g t z hg hA hB ht hz hw) (weighted0626_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0627_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0628_nonneg g t z hg hA hB ht hz hw) (weighted0629_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0630_nonneg g t z hg hA hB ht hz hw) (weighted0631_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0632_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0633_nonneg g t z hg hA hB ht hz hw) (weighted0634_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted0635_nonneg g t z hg hA hB ht hz hw) (weighted0636_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0637_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0638_nonneg g t z hg hA hB ht hz hw) (weighted0639_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0640_nonneg g t z hg hA hB ht hz hw) (weighted0641_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0642_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0643_nonneg g t z hg hA hB ht hz hw) (weighted0644_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
