import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff1165 : CoefficientMerge.Poly :=
  [(1704000, 1)]
noncomputable def atom1165 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 8) ^ 2 * (t) ^ 2 * (z) ^ 1)
theorem atom1165_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1165 g t z = CoefficientMerge.eval (monomial g t z) coeff1165 := by
  norm_num [atom1165, coeff1165, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1165_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1165 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1165]
  positivity
theorem weighted1165_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (180034102985667486227921004596892955836468579055664137367777831236822235753969622622689034338451822890313841363391632399288432977702521600 : Int) coeff1165) := by
  rw [CoefficientMerge.eval_scale, ← atom1165_identity]
  exact mul_nonneg (by norm_num) (atom1165_nonneg g t z hg hA hB ht hz hw)

def coeff1166 : CoefficientMerge.Poly :=
  [(2359488, 1)]
noncomputable def atom1166 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 3 * (t) ^ 1 * (z) ^ 2)
theorem atom1166_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1166 g t z = CoefficientMerge.eval (monomial g t z) coeff1166 := by
  norm_num [atom1166, coeff1166, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1166_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1166 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1166]
  positivity
theorem weighted1166_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (16622238423017678853137798778539641250726358554904543873977483819407189064623271353010490020283854432444827000278748221303733985845862400 : Int) coeff1166) := by
  rw [CoefficientMerge.eval_scale, ← atom1166_identity]
  exact mul_nonneg (by norm_num) (atom1166_nonneg g t z hg hA hB ht hz hw)

def coeff1167 : CoefficientMerge.Poly :=
  [(2359680, 1)]
noncomputable def atom1167 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 2 * (g 4) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1167_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1167 g t z = CoefficientMerge.eval (monomial g t z) coeff1167 := by
  norm_num [atom1167, coeff1167, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1167_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1167 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1167]
  positivity
theorem weighted1167_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (99568472686426110180360087707711099751446905239746666687775030390914179783972365204094263038602793143881357993629369017439940847702817280 : Int) coeff1167) := by
  rw [CoefficientMerge.eval_scale, ← atom1167_identity]
  exact mul_nonneg (by norm_num) (atom1167_nonneg g t z hg hA hB ht hz hw)

def coeff1168 : CoefficientMerge.Poly :=
  [(2360448, 1)]
noncomputable def atom1168 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 2 * (g 5) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1168_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1168 g t z = CoefficientMerge.eval (monomial g t z) coeff1168 := by
  norm_num [atom1168, coeff1168, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1168_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1168 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1168]
  positivity
theorem weighted1168_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (199898375629668916094330867686700581773022438622524840830013250339933192106570712116614051740413123374584004312321678031801922983837999840 : Int) coeff1168) := by
  rw [CoefficientMerge.eval_scale, ← atom1168_identity]
  exact mul_nonneg (by norm_num) (atom1168_nonneg g t z hg hA hB ht hz hw)

def coeff1169 : CoefficientMerge.Poly :=
  [(2363520, 1)]
noncomputable def atom1169 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 2 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1169_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1169 g t z = CoefficientMerge.eval (monomial g t z) coeff1169 := by
  norm_num [atom1169, coeff1169, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1169_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1169 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1169]
  positivity
theorem weighted1169_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (108093834348497712337222758697064849599653394691353667468286134471443352325836818544552719109078378874676261586055340134907424631610733520 : Int) coeff1169) := by
  rw [CoefficientMerge.eval_scale, ← atom1169_identity]
  exact mul_nonneg (by norm_num) (atom1169_nonneg g t z hg hA hB ht hz hw)

def coeff1170 : CoefficientMerge.Poly :=
  [(2375808, 1)]
noncomputable def atom1170 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 2 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1170_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1170 g t z = CoefficientMerge.eval (monomial g t z) coeff1170 := by
  norm_num [atom1170, coeff1170, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1170_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1170 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1170]
  positivity
theorem weighted1170_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (101996868113819388824364350152897204234801196129213329504439302062873229892267640025967977119679318969385978741793755146773705140834064720 : Int) coeff1170) := by
  rw [CoefficientMerge.eval_scale, ← atom1170_identity]
  exact mul_nonneg (by norm_num) (atom1170_nonneg g t z hg hA hB ht hz hw)

def coeff1171 : CoefficientMerge.Poly :=
  [(2424960, 1)]
noncomputable def atom1171 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 2 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1171_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1171 g t z = CoefficientMerge.eval (monomial g t z) coeff1171 := by
  norm_num [atom1171, coeff1171, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1171_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1171 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1171]
  positivity
theorem weighted1171_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (61156321497474150367049965733233815867597019831829084272763640608341373600001023274107907763861251576381940137845710757234398691484624720 : Int) coeff1171) := by
  rw [CoefficientMerge.eval_scale, ← atom1171_identity]
  exact mul_nonneg (by norm_num) (atom1171_nonneg g t z hg hA hB ht hz hw)

def coeff1172 : CoefficientMerge.Poly :=
  [(2359872, 1)]
noncomputable def atom1172 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 2 * (t) ^ 1 * (z) ^ 2)
theorem atom1172_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1172 g t z = CoefficientMerge.eval (monomial g t z) coeff1172 := by
  norm_num [atom1172, coeff1172, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1172_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1172 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1172]
  positivity
theorem weighted1172_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (98288447482072486239809798905421731420313519956606438567617562733141585154029426562590814198110510165735965012816898272873717067996160000 : Int) coeff1172) := by
  rw [CoefficientMerge.eval_scale, ← atom1172_identity]
  exact mul_nonneg (by norm_num) (atom1172_nonneg g t z hg hA hB ht hz hw)

def coeff1173 : CoefficientMerge.Poly :=
  [(2360640, 1)]
noncomputable def atom1173 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 1 * (g 5) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1173_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1173 g t z = CoefficientMerge.eval (monomial g t z) coeff1173 := by
  norm_num [atom1173, coeff1173, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1173_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1173 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1173]
  positivity
theorem weighted1173_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (537719202977513860380544902768093052294474280564103304236435000168024861140719729534419941627215346785920703877493631369625702452484921856 : Int) coeff1173) := by
  rw [CoefficientMerge.eval_scale, ← atom1173_identity]
  exact mul_nonneg (by norm_num) (atom1173_nonneg g t z hg hA hB ht hz hw)

def coeff1174 : CoefficientMerge.Poly :=
  [(2363712, 1)]
noncomputable def atom1174 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1174_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1174 g t z = CoefficientMerge.eval (monomial g t z) coeff1174 := by
  norm_num [atom1174, coeff1174, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1174_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1174 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1174]
  positivity
theorem weighted1174_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (360992482661609862012966192251746282595773675345110974479673845620193556794204723279930229032230650004952103482140791580542167447306362480 : Int) coeff1174) := by
  rw [CoefficientMerge.eval_scale, ← atom1174_identity]
  exact mul_nonneg (by norm_num) (atom1174_nonneg g t z hg hA hB ht hz hw)

def coeff1175 : CoefficientMerge.Poly :=
  [(2376000, 1)]
noncomputable def atom1175 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1175_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1175 g t z = CoefficientMerge.eval (monomial g t z) coeff1175 := by
  norm_num [atom1175, coeff1175, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1175_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1175 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1175]
  positivity
theorem weighted1175_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (326646475174169570307245108822454891093045849209800263526116020138021663867981716031345493282731424576242234216964056729376479211804138480 : Int) coeff1175) := by
  rw [CoefficientMerge.eval_scale, ← atom1175_identity]
  exact mul_nonneg (by norm_num) (atom1175_nonneg g t z hg hA hB ht hz hw)

def coeff1176 : CoefficientMerge.Poly :=
  [(2425152, 1)]
noncomputable def atom1176 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1176_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1176 g t z = CoefficientMerge.eval (monomial g t z) coeff1176 := by
  norm_num [atom1176, coeff1176, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1176_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1176 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1176]
  positivity
theorem weighted1176_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (223046791120383335374620792017906787214263569958613619400262273994083767217046411080114530705358077771026355895898732344650192700281334800 : Int) coeff1176) := by
  rw [CoefficientMerge.eval_scale, ← atom1176_identity]
  exact mul_nonneg (by norm_num) (atom1176_nonneg g t z hg hA hB ht hz hw)

def coeff1177 : CoefficientMerge.Poly :=
  [(2361408, 1)]
noncomputable def atom1177 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 5) ^ 2 * (t) ^ 1 * (z) ^ 2)
theorem atom1177_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1177 g t z = CoefficientMerge.eval (monomial g t z) coeff1177 := by
  norm_num [atom1177, coeff1177, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1177_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1177 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1177]
  positivity
theorem weighted1177_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (379871540630325206955972117883207208028815948709946675083710410575996321039941412598501072764514615382800558237196854818037538127408445440 : Int) coeff1177) := by
  rw [CoefficientMerge.eval_scale, ← atom1177_identity]
  exact mul_nonneg (by norm_num) (atom1177_nonneg g t z hg hA hB ht hz hw)

def coeff1178 : CoefficientMerge.Poly :=
  [(2364480, 1)]
noncomputable def atom1178 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1178_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1178 g t z = CoefficientMerge.eval (monomial g t z) coeff1178 := by
  norm_num [atom1178, coeff1178, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1178_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1178 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1178]
  positivity
theorem weighted1178_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (694241185311315054964251676022231387156844601470269474831389697529314555027820960948537897989681654037794986104904417422453602750157987840 : Int) coeff1178) := by
  rw [CoefficientMerge.eval_scale, ← atom1178_identity]
  exact mul_nonneg (by norm_num) (atom1178_nonneg g t z hg hA hB ht hz hw)

def coeff1179 : CoefficientMerge.Poly :=
  [(2376768, 1)]
noncomputable def atom1179 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1179_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1179 g t z = CoefficientMerge.eval (monomial g t z) coeff1179 := by
  norm_num [atom1179, coeff1179, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1179_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1179 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1179]
  positivity
theorem weighted1179_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (640777212423334789889553643556639600060486660614206316896605822732944782140536699355660630161584602522330398864495524260135300944931111040 : Int) coeff1179) := by
  rw [CoefficientMerge.eval_scale, ← atom1179_identity]
  exact mul_nonneg (by norm_num) (atom1179_nonneg g t z hg hA hB ht hz hw)

def coeff1180 : CoefficientMerge.Poly :=
  [(2425920, 1)]
noncomputable def atom1180 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1180_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1180 g t z = CoefficientMerge.eval (monomial g t z) coeff1180 := by
  norm_num [atom1180, coeff1180, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1180_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1180 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1180]
  positivity
theorem weighted1180_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (580293290231895671522058834350158443062581289085855867653798155342104369993809371617255469503144181726563274556851154367008675945906366670 : Int) coeff1180) := by
  rw [CoefficientMerge.eval_scale, ← atom1180_identity]
  exact mul_nonneg (by norm_num) (atom1180_nonneg g t z hg hA hB ht hz hw)

def coeff1181 : CoefficientMerge.Poly :=
  [(2367552, 1)]
noncomputable def atom1181 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 6) ^ 2 * (t) ^ 1 * (z) ^ 2)
theorem atom1181_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1181 g t z = CoefficientMerge.eval (monomial g t z) coeff1181 := by
  norm_num [atom1181, coeff1181, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1181_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1181 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1181]
  positivity
theorem weighted1181_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (336001944262407915380823570224341194918295045579694359237415300075987049773624170269915874971370467537427180208461507053484374623837596800 : Int) coeff1181) := by
  rw [CoefficientMerge.eval_scale, ← atom1181_identity]
  exact mul_nonneg (by norm_num) (atom1181_nonneg g t z hg hA hB ht hz hw)

def coeff1182 : CoefficientMerge.Poly :=
  [(2379840, 1)]
noncomputable def atom1182 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1182_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1182 g t z = CoefficientMerge.eval (monomial g t z) coeff1182 := by
  norm_num [atom1182, coeff1182, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1182_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1182 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1182]
  positivity
theorem weighted1182_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (592911912924690798533798668839260376920912346085883430244420517811662308052058597446636206586787350454150827622014866435855866189182602000 : Int) coeff1182) := by
  rw [CoefficientMerge.eval_scale, ← atom1182_identity]
  exact mul_nonneg (by norm_num) (atom1182_nonneg g t z hg hA hB ht hz hw)

def coeff1183 : CoefficientMerge.Poly :=
  [(2428992, 1)]
noncomputable def atom1183 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1183_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1183 g t z = CoefficientMerge.eval (monomial g t z) coeff1183 := by
  norm_num [atom1183, coeff1183, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1183_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1183 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1183]
  positivity
theorem weighted1183_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (504500085495871690539976548827759870831626354663580305147093243198865871160100495938434409762961045552654354190852106584821959963976518080 : Int) coeff1183) := by
  rw [CoefficientMerge.eval_scale, ← atom1183_identity]
  exact mul_nonneg (by norm_num) (atom1183_nonneg g t z hg hA hB ht hz hw)

def coeff1184 : CoefficientMerge.Poly :=
  [(2392128, 1)]
noncomputable def atom1184 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 7) ^ 2 * (t) ^ 1 * (z) ^ 2)
theorem atom1184_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1184 g t z = CoefficientMerge.eval (monomial g t z) coeff1184 := by
  norm_num [atom1184, coeff1184, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1184_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1184 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1184]
  positivity
theorem weighted1184_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (267971242324821385731540814025307347069909442625741313611536323576951605694986544574480779540507922978019612823999073827548210956583094400 : Int) coeff1184) := by
  rw [CoefficientMerge.eval_scale, ← atom1184_identity]
  exact mul_nonneg (by norm_num) (atom1184_nonneg g t z hg hA hB ht hz hw)

def sparseBlock090 : CoefficientMerge.Poly :=
  [(1704000, 180034102985667486227921004596892955836468579055664137367777831236822235753969622622689034338451822890313841363391632399288432977702521600), (2359488, 16622238423017678853137798778539641250726358554904543873977483819407189064623271353010490020283854432444827000278748221303733985845862400), (2359680, 99568472686426110180360087707711099751446905239746666687775030390914179783972365204094263038602793143881357993629369017439940847702817280), (2359872, 98288447482072486239809798905421731420313519956606438567617562733141585154029426562590814198110510165735965012816898272873717067996160000), (2360448, 199898375629668916094330867686700581773022438622524840830013250339933192106570712116614051740413123374584004312321678031801922983837999840), (2360640, 537719202977513860380544902768093052294474280564103304236435000168024861140719729534419941627215346785920703877493631369625702452484921856), (2361408, 379871540630325206955972117883207208028815948709946675083710410575996321039941412598501072764514615382800558237196854818037538127408445440), (2363520, 108093834348497712337222758697064849599653394691353667468286134471443352325836818544552719109078378874676261586055340134907424631610733520), (2363712, 360992482661609862012966192251746282595773675345110974479673845620193556794204723279930229032230650004952103482140791580542167447306362480), (2364480, 694241185311315054964251676022231387156844601470269474831389697529314555027820960948537897989681654037794986104904417422453602750157987840), (2367552, 336001944262407915380823570224341194918295045579694359237415300075987049773624170269915874971370467537427180208461507053484374623837596800), (2375808, 101996868113819388824364350152897204234801196129213329504439302062873229892267640025967977119679318969385978741793755146773705140834064720), (2376000, 326646475174169570307245108822454891093045849209800263526116020138021663867981716031345493282731424576242234216964056729376479211804138480), (2376768, 640777212423334789889553643556639600060486660614206316896605822732944782140536699355660630161584602522330398864495524260135300944931111040), (2379840, 592911912924690798533798668839260376920912346085883430244420517811662308052058597446636206586787350454150827622014866435855866189182602000), (2392128, 267971242324821385731540814025307347069909442625741313611536323576951605694986544574480779540507922978019612823999073827548210956583094400), (2424960, 61156321497474150367049965733233815867597019831829084272763640608341373600001023274107907763861251576381940137845710757234398691484624720), (2425152, 223046791120383335374620792017906787214263569958613619400262273994083767217046411080114530705358077771026355895898732344650192700281334800), (2425920, 580293290231895671522058834350158443062581289085855867653798155342104369993809371617255469503144181726563274556851154367008675945906366670), (2428992, 504500085495871690539976548827759870831626354663580305147093243198865871160100495938434409762961045552654354190852106584821959963976518080)]
theorem sparseBlock090_data : sparseBlock090 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (180034102985667486227921004596892955836468579055664137367777831236822235753969622622689034338451822890313841363391632399288432977702521600 : Int) coeff1165) (CoefficientMerge.scale (16622238423017678853137798778539641250726358554904543873977483819407189064623271353010490020283854432444827000278748221303733985845862400 : Int) coeff1166)) (CoefficientMerge.merge (CoefficientMerge.scale (99568472686426110180360087707711099751446905239746666687775030390914179783972365204094263038602793143881357993629369017439940847702817280 : Int) coeff1167) (CoefficientMerge.merge (CoefficientMerge.scale (199898375629668916094330867686700581773022438622524840830013250339933192106570712116614051740413123374584004312321678031801922983837999840 : Int) coeff1168) (CoefficientMerge.scale (108093834348497712337222758697064849599653394691353667468286134471443352325836818544552719109078378874676261586055340134907424631610733520 : Int) coeff1169)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (101996868113819388824364350152897204234801196129213329504439302062873229892267640025967977119679318969385978741793755146773705140834064720 : Int) coeff1170) (CoefficientMerge.scale (61156321497474150367049965733233815867597019831829084272763640608341373600001023274107907763861251576381940137845710757234398691484624720 : Int) coeff1171)) (CoefficientMerge.merge (CoefficientMerge.scale (98288447482072486239809798905421731420313519956606438567617562733141585154029426562590814198110510165735965012816898272873717067996160000 : Int) coeff1172) (CoefficientMerge.merge (CoefficientMerge.scale (537719202977513860380544902768093052294474280564103304236435000168024861140719729534419941627215346785920703877493631369625702452484921856 : Int) coeff1173) (CoefficientMerge.scale (360992482661609862012966192251746282595773675345110974479673845620193556794204723279930229032230650004952103482140791580542167447306362480 : Int) coeff1174))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (326646475174169570307245108822454891093045849209800263526116020138021663867981716031345493282731424576242234216964056729376479211804138480 : Int) coeff1175) (CoefficientMerge.scale (223046791120383335374620792017906787214263569958613619400262273994083767217046411080114530705358077771026355895898732344650192700281334800 : Int) coeff1176)) (CoefficientMerge.merge (CoefficientMerge.scale (379871540630325206955972117883207208028815948709946675083710410575996321039941412598501072764514615382800558237196854818037538127408445440 : Int) coeff1177) (CoefficientMerge.merge (CoefficientMerge.scale (694241185311315054964251676022231387156844601470269474831389697529314555027820960948537897989681654037794986104904417422453602750157987840 : Int) coeff1178) (CoefficientMerge.scale (640777212423334789889553643556639600060486660614206316896605822732944782140536699355660630161584602522330398864495524260135300944931111040 : Int) coeff1179)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (580293290231895671522058834350158443062581289085855867653798155342104369993809371617255469503144181726563274556851154367008675945906366670 : Int) coeff1180) (CoefficientMerge.scale (336001944262407915380823570224341194918295045579694359237415300075987049773624170269915874971370467537427180208461507053484374623837596800 : Int) coeff1181)) (CoefficientMerge.merge (CoefficientMerge.scale (592911912924690798533798668839260376920912346085883430244420517811662308052058597446636206586787350454150827622014866435855866189182602000 : Int) coeff1182) (CoefficientMerge.merge (CoefficientMerge.scale (504500085495871690539976548827759870831626354663580305147093243198865871160100495938434409762961045552654354190852106584821959963976518080 : Int) coeff1183) (CoefficientMerge.scale (267971242324821385731540814025307347069909442625741313611536323576951605694986544574480779540507922978019612823999073827548210956583094400 : Int) coeff1184)))))) := by decide +kernel
theorem sparseBlock090_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock090 := by
  rw [sparseBlock090_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted1165_nonneg g t z hg hA hB ht hz hw) (weighted1166_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1167_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1168_nonneg g t z hg hA hB ht hz hw) (weighted1169_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1170_nonneg g t z hg hA hB ht hz hw) (weighted1171_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1172_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1173_nonneg g t z hg hA hB ht hz hw) (weighted1174_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted1175_nonneg g t z hg hA hB ht hz hw) (weighted1176_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1177_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1178_nonneg g t z hg hA hB ht hz hw) (weighted1179_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1180_nonneg g t z hg hA hB ht hz hw) (weighted1181_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1182_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1183_nonneg g t z hg hA hB ht hz hw) (weighted1184_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
