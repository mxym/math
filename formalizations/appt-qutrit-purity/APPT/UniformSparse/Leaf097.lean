import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff1305 : CoefficientMerge.Poly :=
  [(3147264, 1)]
noncomputable def atom1305 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 2 * (g 5) ^ 1 * (z) ^ 3)
theorem atom1305_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1305 g t z = CoefficientMerge.eval (monomial g t z) coeff1305 := by
  norm_num [atom1305, coeff1305, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1305_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1305 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1305]
  positivity
theorem weighted1305_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (79498821123618188999267123391251648766342758659617698606528508310626833471024304102165965011948037642230415892736653412009333341358080000 : Int) coeff1305) := by
  rw [CoefficientMerge.eval_scale, ← atom1305_identity]
  exact mul_nonneg (by norm_num) (atom1305_nonneg g t z hg hA hB ht hz hw)

def coeff1306 : CoefficientMerge.Poly :=
  [(3150336, 1)]
noncomputable def atom1306 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 2 * (g 6) ^ 1 * (z) ^ 3)
theorem atom1306_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1306 g t z = CoefficientMerge.eval (monomial g t z) coeff1306 := by
  norm_num [atom1306, coeff1306, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1306_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1306 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1306]
  positivity
theorem weighted1306_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (55042259565958694712169414781029274297527186725263596697850848211879179255573982044433648067034095560656608010460953963944978329639839040 : Int) coeff1306) := by
  rw [CoefficientMerge.eval_scale, ← atom1306_identity]
  exact mul_nonneg (by norm_num) (atom1306_nonneg g t z hg hA hB ht hz hw)

def coeff1307 : CoefficientMerge.Poly :=
  [(3162624, 1)]
noncomputable def atom1307 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 2 * (g 7) ^ 1 * (z) ^ 3)
theorem atom1307_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1307 g t z = CoefficientMerge.eval (monomial g t z) coeff1307 := by
  norm_num [atom1307, coeff1307, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1307_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1307 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1307]
  positivity
theorem weighted1307_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (43684846992685409412650152568207922178020125946223662240081694437888817368449500043401351227740960990233781083857939197523211035370954560 : Int) coeff1307) := by
  rw [CoefficientMerge.eval_scale, ← atom1307_identity]
  exact mul_nonneg (by norm_num) (atom1307_nonneg g t z hg hA hB ht hz hw)

def coeff1308 : CoefficientMerge.Poly :=
  [(3211776, 1)]
noncomputable def atom1308 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 2 * (g 8) ^ 1 * (z) ^ 3)
theorem atom1308_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1308 g t z = CoefficientMerge.eval (monomial g t z) coeff1308 := by
  norm_num [atom1308, coeff1308, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1308_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1308 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1308]
  positivity
theorem weighted1308_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (24587532965438768625295107586941607222423397564712437254724073354847254536928445012740868983066898013409090842387266698835437336802971840 : Int) coeff1308) := by
  rw [CoefficientMerge.eval_scale, ← atom1308_identity]
  exact mul_nonneg (by norm_num) (atom1308_nonneg g t z hg hA hB ht hz hw)

def coeff1309 : CoefficientMerge.Poly :=
  [(3148032, 1)]
noncomputable def atom1309 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 5) ^ 2 * (z) ^ 3)
theorem atom1309_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1309 g t z = CoefficientMerge.eval (monomial g t z) coeff1309 := by
  norm_num [atom1309, coeff1309, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1309_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1309 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1309]
  positivity
theorem weighted1309_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (124432620062209266433740595386843274124815027190401948295208466945238471715409814535856212141843611756961517512535101902222109002393844480 : Int) coeff1309) := by
  rw [CoefficientMerge.eval_scale, ← atom1309_identity]
  exact mul_nonneg (by norm_num) (atom1309_nonneg g t z hg hA hB ht hz hw)

def coeff1310 : CoefficientMerge.Poly :=
  [(3151104, 1)]
noncomputable def atom1310 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (z) ^ 3)
theorem atom1310_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1310 g t z = CoefficientMerge.eval (monomial g t z) coeff1310 := by
  norm_num [atom1310, coeff1310, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1310_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1310 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1310]
  positivity
theorem weighted1310_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (224134800777912482111241273856774966819313616912984810330700115249218204814409724799059584904485423658555105840326178622439462682765578240 : Int) coeff1310) := by
  rw [CoefficientMerge.eval_scale, ← atom1310_identity]
  exact mul_nonneg (by norm_num) (atom1310_nonneg g t z hg hA hB ht hz hw)

def coeff1311 : CoefficientMerge.Poly :=
  [(3163392, 1)]
noncomputable def atom1311 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (z) ^ 3)
theorem atom1311_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1311 g t z = CoefficientMerge.eval (monomial g t z) coeff1311 := by
  norm_num [atom1311, coeff1311, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1311_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1311 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1311]
  positivity
theorem weighted1311_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (194841978168768907619737846522451989983357495313082067176448945307909210519066996059314386726490964995658689921177504696270575304583075840 : Int) coeff1311) := by
  rw [CoefficientMerge.eval_scale, ← atom1311_identity]
  exact mul_nonneg (by norm_num) (atom1311_nonneg g t z hg hA hB ht hz hw)

def coeff1312 : CoefficientMerge.Poly :=
  [(3212544, 1)]
noncomputable def atom1312 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (z) ^ 3)
theorem atom1312_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1312 g t z = CoefficientMerge.eval (monomial g t z) coeff1312 := by
  norm_num [atom1312, coeff1312, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1312_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1312 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1312]
  positivity
theorem weighted1312_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (176209275314170218435414420611350769682062752258413380686556150112646117960069163764323637483420251693073098321089340120024048878290278090 : Int) coeff1312) := by
  rw [CoefficientMerge.eval_scale, ← atom1312_identity]
  exact mul_nonneg (by norm_num) (atom1312_nonneg g t z hg hA hB ht hz hw)

def coeff1313 : CoefficientMerge.Poly :=
  [(3154176, 1)]
noncomputable def atom1313 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 6) ^ 2 * (z) ^ 3)
theorem atom1313_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1313 g t z = CoefficientMerge.eval (monomial g t z) coeff1313 := by
  norm_num [atom1313, coeff1313, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1313_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1313 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1313]
  positivity
theorem weighted1313_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (104295832399294810936321420106842745121720172646737071684782303622712090876913717922194210945504441359649094247054372296095094369813274560 : Int) coeff1313) := by
  rw [CoefficientMerge.eval_scale, ← atom1313_identity]
  exact mul_nonneg (by norm_num) (atom1313_nonneg g t z hg hA hB ht hz hw)

def coeff1314 : CoefficientMerge.Poly :=
  [(3166464, 1)]
noncomputable def atom1314 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (z) ^ 3)
theorem atom1314_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1314 g t z = CoefficientMerge.eval (monomial g t z) coeff1314 := by
  norm_num [atom1314, coeff1314, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1314_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1314 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1314]
  positivity
theorem weighted1314_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (179259263139389445783805195342358548111007827453428155410022564127073123287049829611980864793342179019867435475340077218537113641079865520 : Int) coeff1314) := by
  rw [CoefficientMerge.eval_scale, ← atom1314_identity]
  exact mul_nonneg (by norm_num) (atom1314_nonneg g t z hg hA hB ht hz hw)

def coeff1315 : CoefficientMerge.Poly :=
  [(3215616, 1)]
noncomputable def atom1315 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (z) ^ 3)
theorem atom1315_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1315 g t z = CoefficientMerge.eval (monomial g t z) coeff1315 := by
  norm_num [atom1315, coeff1315, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1315_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1315 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1315]
  positivity
theorem weighted1315_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (158727550729991614064639288632129847533224642534123938930230365747505241485676595564475629707714372023044314740959431942388981740554593120 : Int) coeff1315) := by
  rw [CoefficientMerge.eval_scale, ← atom1315_identity]
  exact mul_nonneg (by norm_num) (atom1315_nonneg g t z hg hA hB ht hz hw)

def coeff1316 : CoefficientMerge.Poly :=
  [(3178752, 1)]
noncomputable def atom1316 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 7) ^ 2 * (z) ^ 3)
theorem atom1316_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1316 g t z = CoefficientMerge.eval (monomial g t z) coeff1316 := by
  norm_num [atom1316, coeff1316, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1316_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1316 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1316]
  positivity
theorem weighted1316_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (74079454273628296467432202931041740181109279219556782458500541961345147609170978075589485161952781270199430796541974191579561266043080960 : Int) coeff1316) := by
  rw [CoefficientMerge.eval_scale, ← atom1316_identity]
  exact mul_nonneg (by norm_num) (atom1316_nonneg g t z hg hA hB ht hz hw)

def coeff1317 : CoefficientMerge.Poly :=
  [(3227904, 1)]
noncomputable def atom1317 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (z) ^ 3)
theorem atom1317_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1317 g t z = CoefficientMerge.eval (monomial g t z) coeff1317 := by
  norm_num [atom1317, coeff1317, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1317_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1317 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1317]
  positivity
theorem weighted1317_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (114346040282032788036972115315873214773649617514525476701283345177569279468083797828180294736482307409730951333349767045917654734040428160 : Int) coeff1317) := by
  rw [CoefficientMerge.eval_scale, ← atom1317_identity]
  exact mul_nonneg (by norm_num) (atom1317_nonneg g t z hg hA hB ht hz hw)

def coeff1318 : CoefficientMerge.Poly :=
  [(3277056, 1)]
noncomputable def atom1318 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 8) ^ 2 * (z) ^ 3)
theorem atom1318_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1318 g t z = CoefficientMerge.eval (monomial g t z) coeff1318 := by
  norm_num [atom1318, coeff1318, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1318_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1318 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1318]
  positivity
theorem weighted1318_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (46615325025932186248414618223514649585451864545784574184050498535992424922946070328398715118739604996428572462952566823015836010068168960 : Int) coeff1318) := by
  rw [CoefficientMerge.eval_scale, ← atom1318_identity]
  exact mul_nonneg (by norm_num) (atom1318_nonneg g t z hg hA hB ht hz hw)

def coeff1319 : CoefficientMerge.Poly :=
  [(3148800, 1)]
noncomputable def atom1319 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 3 * (z) ^ 3)
theorem atom1319_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1319 g t z = CoefficientMerge.eval (monomial g t z) coeff1319 := by
  norm_num [atom1319, coeff1319, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1319_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1319 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1319]
  positivity
theorem weighted1319_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (38809730222772744029655815078528020015502294340088518193718373578217591136229260222393140908701105005741479995398766526457680942359749120 : Int) coeff1319) := by
  rw [CoefficientMerge.eval_scale, ← atom1319_identity]
  exact mul_nonneg (by norm_num) (atom1319_nonneg g t z hg hA hB ht hz hw)

def coeff1320 : CoefficientMerge.Poly :=
  [(3151872, 1)]
noncomputable def atom1320 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 2 * (g 6) ^ 1 * (z) ^ 3)
theorem atom1320_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1320 g t z = CoefficientMerge.eval (monomial g t z) coeff1320 := by
  norm_num [atom1320, coeff1320, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1320_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1320 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1320]
  positivity
theorem weighted1320_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (110444791133766637638182143948524406800373683035112630369440164716555278338011254003686951969143239654798252017394008601700943762400298240 : Int) coeff1320) := by
  rw [CoefficientMerge.eval_scale, ← atom1320_identity]
  exact mul_nonneg (by norm_num) (atom1320_nonneg g t z hg hA hB ht hz hw)

def coeff1321 : CoefficientMerge.Poly :=
  [(3164160, 1)]
noncomputable def atom1321 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 2 * (g 7) ^ 1 * (z) ^ 3)
theorem atom1321_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1321 g t z = CoefficientMerge.eval (monomial g t z) coeff1321 := by
  norm_num [atom1321, coeff1321, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1321_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1321 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1321]
  positivity
theorem weighted1321_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (92918127527443964852896779209391992980832696518966500802849150916214916831022672283072310400660809059631093737033440375931551980946269440 : Int) coeff1321) := by
  rw [CoefficientMerge.eval_scale, ← atom1321_identity]
  exact mul_nonneg (by norm_num) (atom1321_nonneg g t z hg hA hB ht hz hw)

def coeff1322 : CoefficientMerge.Poly :=
  [(3213312, 1)]
noncomputable def atom1322 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 2 * (g 8) ^ 1 * (z) ^ 3)
theorem atom1322_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1322 g t z = CoefficientMerge.eval (monomial g t z) coeff1322 := by
  norm_num [atom1322, coeff1322, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1322_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1322 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1322]
  positivity
theorem weighted1322_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (91390222414734094349648932256035023454801640150078613546588055673864123866279542410827570397859584074817177175539306244123216965245875270 : Int) coeff1322) := by
  rw [CoefficientMerge.eval_scale, ← atom1322_identity]
  exact mul_nonneg (by norm_num) (atom1322_nonneg g t z hg hA hB ht hz hw)

def coeff1323 : CoefficientMerge.Poly :=
  [(3154944, 1)]
noncomputable def atom1323 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 6) ^ 2 * (z) ^ 3)
theorem atom1323_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1323 g t z = CoefficientMerge.eval (monomial g t z) coeff1323 := by
  norm_num [atom1323, coeff1323, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1323_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1323 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1323]
  positivity
theorem weighted1323_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (105956567611164083383043705479500944455488960760067293534076430607030813994199719997449781291188046744089278379072351814433480499070817920 : Int) coeff1323) := by
  rw [CoefficientMerge.eval_scale, ← atom1323_identity]
  exact mul_nonneg (by norm_num) (atom1323_nonneg g t z hg hA hB ht hz hw)

def coeff1324 : CoefficientMerge.Poly :=
  [(3167232, 1)]
noncomputable def atom1324 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (z) ^ 3)
theorem atom1324_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1324 g t z = CoefficientMerge.eval (monomial g t z) coeff1324 := by
  norm_num [atom1324, coeff1324, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1324_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1324 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1324]
  positivity
theorem weighted1324_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (176196263628825378918181866950898978812970935936032646683590899203622126639508518472185179332299579039602806082523678431613311977522271440 : Int) coeff1324) := by
  rw [CoefficientMerge.eval_scale, ← atom1324_identity]
  exact mul_nonneg (by norm_num) (atom1324_nonneg g t z hg hA hB ht hz hw)

def sparseBlock097 : CoefficientMerge.Poly :=
  [(3147264, 79498821123618188999267123391251648766342758659617698606528508310626833471024304102165965011948037642230415892736653412009333341358080000), (3148032, 124432620062209266433740595386843274124815027190401948295208466945238471715409814535856212141843611756961517512535101902222109002393844480), (3148800, 38809730222772744029655815078528020015502294340088518193718373578217591136229260222393140908701105005741479995398766526457680942359749120), (3150336, 55042259565958694712169414781029274297527186725263596697850848211879179255573982044433648067034095560656608010460953963944978329639839040), (3151104, 224134800777912482111241273856774966819313616912984810330700115249218204814409724799059584904485423658555105840326178622439462682765578240), (3151872, 110444791133766637638182143948524406800373683035112630369440164716555278338011254003686951969143239654798252017394008601700943762400298240), (3154176, 104295832399294810936321420106842745121720172646737071684782303622712090876913717922194210945504441359649094247054372296095094369813274560), (3154944, 105956567611164083383043705479500944455488960760067293534076430607030813994199719997449781291188046744089278379072351814433480499070817920), (3162624, 43684846992685409412650152568207922178020125946223662240081694437888817368449500043401351227740960990233781083857939197523211035370954560), (3163392, 194841978168768907619737846522451989983357495313082067176448945307909210519066996059314386726490964995658689921177504696270575304583075840), (3164160, 92918127527443964852896779209391992980832696518966500802849150916214916831022672283072310400660809059631093737033440375931551980946269440), (3166464, 179259263139389445783805195342358548111007827453428155410022564127073123287049829611980864793342179019867435475340077218537113641079865520), (3167232, 176196263628825378918181866950898978812970935936032646683590899203622126639508518472185179332299579039602806082523678431613311977522271440), (3178752, 74079454273628296467432202931041740181109279219556782458500541961345147609170978075589485161952781270199430796541974191579561266043080960), (3211776, 24587532965438768625295107586941607222423397564712437254724073354847254536928445012740868983066898013409090842387266698835437336802971840), (3212544, 176209275314170218435414420611350769682062752258413380686556150112646117960069163764323637483420251693073098321089340120024048878290278090), (3213312, 91390222414734094349648932256035023454801640150078613546588055673864123866279542410827570397859584074817177175539306244123216965245875270), (3215616, 158727550729991614064639288632129847533224642534123938930230365747505241485676595564475629707714372023044314740959431942388981740554593120), (3227904, 114346040282032788036972115315873214773649617514525476701283345177569279468083797828180294736482307409730951333349767045917654734040428160), (3277056, 46615325025932186248414618223514649585451864545784574184050498535992424922946070328398715118739604996428572462952566823015836010068168960)]
theorem sparseBlock097_data : sparseBlock097 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (79498821123618188999267123391251648766342758659617698606528508310626833471024304102165965011948037642230415892736653412009333341358080000 : Int) coeff1305) (CoefficientMerge.scale (55042259565958694712169414781029274297527186725263596697850848211879179255573982044433648067034095560656608010460953963944978329639839040 : Int) coeff1306)) (CoefficientMerge.merge (CoefficientMerge.scale (43684846992685409412650152568207922178020125946223662240081694437888817368449500043401351227740960990233781083857939197523211035370954560 : Int) coeff1307) (CoefficientMerge.merge (CoefficientMerge.scale (24587532965438768625295107586941607222423397564712437254724073354847254536928445012740868983066898013409090842387266698835437336802971840 : Int) coeff1308) (CoefficientMerge.scale (124432620062209266433740595386843274124815027190401948295208466945238471715409814535856212141843611756961517512535101902222109002393844480 : Int) coeff1309)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (224134800777912482111241273856774966819313616912984810330700115249218204814409724799059584904485423658555105840326178622439462682765578240 : Int) coeff1310) (CoefficientMerge.scale (194841978168768907619737846522451989983357495313082067176448945307909210519066996059314386726490964995658689921177504696270575304583075840 : Int) coeff1311)) (CoefficientMerge.merge (CoefficientMerge.scale (176209275314170218435414420611350769682062752258413380686556150112646117960069163764323637483420251693073098321089340120024048878290278090 : Int) coeff1312) (CoefficientMerge.merge (CoefficientMerge.scale (104295832399294810936321420106842745121720172646737071684782303622712090876913717922194210945504441359649094247054372296095094369813274560 : Int) coeff1313) (CoefficientMerge.scale (179259263139389445783805195342358548111007827453428155410022564127073123287049829611980864793342179019867435475340077218537113641079865520 : Int) coeff1314))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (158727550729991614064639288632129847533224642534123938930230365747505241485676595564475629707714372023044314740959431942388981740554593120 : Int) coeff1315) (CoefficientMerge.scale (74079454273628296467432202931041740181109279219556782458500541961345147609170978075589485161952781270199430796541974191579561266043080960 : Int) coeff1316)) (CoefficientMerge.merge (CoefficientMerge.scale (114346040282032788036972115315873214773649617514525476701283345177569279468083797828180294736482307409730951333349767045917654734040428160 : Int) coeff1317) (CoefficientMerge.merge (CoefficientMerge.scale (46615325025932186248414618223514649585451864545784574184050498535992424922946070328398715118739604996428572462952566823015836010068168960 : Int) coeff1318) (CoefficientMerge.scale (38809730222772744029655815078528020015502294340088518193718373578217591136229260222393140908701105005741479995398766526457680942359749120 : Int) coeff1319)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (110444791133766637638182143948524406800373683035112630369440164716555278338011254003686951969143239654798252017394008601700943762400298240 : Int) coeff1320) (CoefficientMerge.scale (92918127527443964852896779209391992980832696518966500802849150916214916831022672283072310400660809059631093737033440375931551980946269440 : Int) coeff1321)) (CoefficientMerge.merge (CoefficientMerge.scale (91390222414734094349648932256035023454801640150078613546588055673864123866279542410827570397859584074817177175539306244123216965245875270 : Int) coeff1322) (CoefficientMerge.merge (CoefficientMerge.scale (105956567611164083383043705479500944455488960760067293534076430607030813994199719997449781291188046744089278379072351814433480499070817920 : Int) coeff1323) (CoefficientMerge.scale (176196263628825378918181866950898978812970935936032646683590899203622126639508518472185179332299579039602806082523678431613311977522271440 : Int) coeff1324)))))) := by decide +kernel
theorem sparseBlock097_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock097 := by
  rw [sparseBlock097_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted1305_nonneg g t z hg hA hB ht hz hw) (weighted1306_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1307_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1308_nonneg g t z hg hA hB ht hz hw) (weighted1309_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1310_nonneg g t z hg hA hB ht hz hw) (weighted1311_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1312_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1313_nonneg g t z hg hA hB ht hz hw) (weighted1314_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted1315_nonneg g t z hg hA hB ht hz hw) (weighted1316_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1317_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1318_nonneg g t z hg hA hB ht hz hw) (weighted1319_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1320_nonneg g t z hg hA hB ht hz hw) (weighted1321_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1322_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1323_nonneg g t z hg hA hB ht hz hw) (weighted1324_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
