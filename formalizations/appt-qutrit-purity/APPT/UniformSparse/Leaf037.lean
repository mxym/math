import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff0392 : CoefficientMerge.Poly :=
  [(1573137, -4), (1573140, -8), (1573152, -16), (1573200, -8), (1574160, 8), (1577232, 12), (1589520, 16), (1638672, 18)]
noncomputable def atom0392 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![1,2,2] * g 2 * g 4) * t * t * z)
theorem atom0392_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0392 g t z = CoefficientMerge.eval (monomial g t z) coeff0392 := by
  norm_num [atom0392, coeff0392, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0392_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0392 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![1,2,2]
  dsimp only [atom0392]
  positivity
theorem weighted0392_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2215854612018609729570458003828522750095553372640466264013216515512944691910594190834595794339099676489496263698346973653907177596839040 : Int) coeff0392) := by
  rw [CoefficientMerge.eval_scale, ← atom0392_identity]
  exact mul_nonneg (by norm_num) (atom0392_nonneg g t z hg hA hB ht hz hw)

def coeff0393 : CoefficientMerge.Poly :=
  [(2359569, -4), (2359572, -8), (2359584, -16), (2359632, -8), (2360592, 8), (2363664, 12), (2375952, 16), (2425104, 18)]
noncomputable def atom0393 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![1,2,2] * g 2 * g 4) * t * z * z)
theorem atom0393_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0393 g t z = CoefficientMerge.eval (monomial g t z) coeff0393 := by
  norm_num [atom0393, coeff0393, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0393_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0393 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![1,2,2]
  dsimp only [atom0393]
  positivity
theorem weighted0393_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2442167464941700615516865447553329632179965535828618909975550850821283313693936382300478467146347717153814451391239017967657828920908592 : Int) coeff0393) := by
  rw [CoefficientMerge.eval_scale, ← atom0393_identity]
  exact mul_nonneg (by norm_num) (atom0393_nonneg g t z hg hA hB ht hz hw)

def coeff0394 : CoefficientMerge.Poly :=
  [(1048849, -1296), (1048852, -2592), (1048864, -5184), (1048912, -2592), (1049872, 2592), (1052944, 3888), (1065232, 5184), (1114384, 5832), (1310993, 144), (1310996, 288), (1311008, 576), (1311056, 288), (1312016, -288), (1315088, -432), (1327376, -576), (1376528, -648), (1573137, -4), (1573140, -8), (1573152, -16), (1573200, -8), (1574160, 8), (1577232, 12), (1589520, 16), (1638672, 18), (2097425, 144), (2097428, 288), (2097440, 576), (2097488, 288), (2098448, -288), (2101520, -432), (2113808, -576), (2162960, -648), (2359569, -8), (2359572, -16), (2359584, -32), (2359632, -16), (2360592, 16), (2363664, 24), (2375952, 32), (2425104, 36), (3146001, -4), (3146004, -8), (3146016, -16), (3146064, -8), (3147024, 8), (3150096, 12), (3162384, 16), (3211536, 18)]
noncomputable def atom0394 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![1,2,2] * g 2 * g 4) * z * (t+z-18) * (t+z-18))
theorem atom0394_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0394 g t z = CoefficientMerge.eval (monomial g t z) coeff0394 := by
  norm_num [atom0394, coeff0394, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0394_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0394 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![1,2,2]
  dsimp only [atom0394]
  positivity
theorem weighted0394_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1125662402001647440062224912026132172824442064437977245652956581863074953436176817113401132523007579409777613745591504656675575709960220 : Int) coeff0394) := by
  rw [CoefficientMerge.eval_scale, ← atom0394_identity]
  exact mul_nonneg (by norm_num) (atom0394_nonneg g t z hg hA hB ht hz hw)

def coeff0395 : CoefficientMerge.Poly :=
  [(1311761, -4), (1311764, -8), (1311776, -16), (1311824, -8), (1312784, 8), (1315856, 12), (1328144, 16), (1377296, 18)]
noncomputable def atom0395 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![1,2,2] * g 2 * g 5) * t * z)
theorem atom0395_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0395 g t z = CoefficientMerge.eval (monomial g t z) coeff0395 := by
  norm_num [atom0395, coeff0395, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0395_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0395 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![1,2,2]
  dsimp only [atom0395]
  positivity
theorem weighted0395_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (158813956715343288915259477922093027711196752852599778729830644654930804799612646383116009264726949637935827847405023681839379807736089360 : Int) coeff0395) := by
  rw [CoefficientMerge.eval_scale, ← atom0395_identity]
  exact mul_nonneg (by norm_num) (atom0395_nonneg g t z hg hA hB ht hz hw)

def coeff0396 : CoefficientMerge.Poly :=
  [(2098193, -4), (2098196, -8), (2098208, -16), (2098256, -8), (2099216, 8), (2102288, 12), (2114576, 16), (2163728, 18)]
noncomputable def atom0396 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![1,2,2] * g 2 * g 5) * z * z)
theorem atom0396_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0396 g t z = CoefficientMerge.eval (monomial g t z) coeff0396 := by
  norm_num [atom0396, coeff0396, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0396_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0396 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![1,2,2]
  dsimp only [atom0396]
  positivity
theorem weighted0396_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1690394929582474443945349140469395727059644234806614670713037791610856310302107230365336759516063305728511647038539977900948919646361600 : Int) coeff0396) := by
  rw [CoefficientMerge.eval_scale, ← atom0396_identity]
  exact mul_nonneg (by norm_num) (atom0396_nonneg g t z hg hA hB ht hz hw)

def coeff0397 : CoefficientMerge.Poly :=
  [(1573905, -4), (1573908, -8), (1573920, -16), (1573968, -8), (1574928, 8), (1578000, 12), (1590288, 16), (1639440, 18)]
noncomputable def atom0397 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![1,2,2] * g 2 * g 5) * t * t * z)
theorem atom0397_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0397 g t z = CoefficientMerge.eval (monomial g t z) coeff0397 := by
  norm_num [atom0397, coeff0397, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0397_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0397 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![1,2,2]
  dsimp only [atom0397]
  positivity
theorem weighted0397_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (8682064449403954293292487365246875122065503063355784938665496037289937017776609331556092984557342742576855157171641193532953759569745080 : Int) coeff0397) := by
  rw [CoefficientMerge.eval_scale, ← atom0397_identity]
  exact mul_nonneg (by norm_num) (atom0397_nonneg g t z hg hA hB ht hz hw)

def coeff0398 : CoefficientMerge.Poly :=
  [(2360337, -4), (2360340, -8), (2360352, -16), (2360400, -8), (2361360, 8), (2364432, 12), (2376720, 16), (2425872, 18)]
noncomputable def atom0398 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![1,2,2] * g 2 * g 5) * t * z * z)
theorem atom0398_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0398 g t z = CoefficientMerge.eval (monomial g t z) coeff0398 := by
  norm_num [atom0398, coeff0398, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0398_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0398 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![1,2,2]
  dsimp only [atom0398]
  positivity
theorem weighted0398_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4155129726773764288365923658110541085984824973844910981193089911961562428520049574711882652468730512381626334130537287794341401451857080 : Int) coeff0398) := by
  rw [CoefficientMerge.eval_scale, ← atom0398_identity]
  exact mul_nonneg (by norm_num) (atom0398_nonneg g t z hg hA hB ht hz hw)

def coeff0399 : CoefficientMerge.Poly :=
  [(1049617, -1296), (1049620, -2592), (1049632, -5184), (1049680, -2592), (1050640, 2592), (1053712, 3888), (1066000, 5184), (1115152, 5832), (1311761, 144), (1311764, 288), (1311776, 576), (1311824, 288), (1312784, -288), (1315856, -432), (1328144, -576), (1377296, -648), (1573905, -4), (1573908, -8), (1573920, -16), (1573968, -8), (1574928, 8), (1578000, 12), (1590288, 16), (1639440, 18), (2098193, 144), (2098196, 288), (2098208, 576), (2098256, 288), (2099216, -288), (2102288, -432), (2114576, -576), (2163728, -648), (2360337, -8), (2360340, -16), (2360352, -32), (2360400, -16), (2361360, 16), (2364432, 24), (2376720, 32), (2425872, 36), (3146769, -4), (3146772, -8), (3146784, -16), (3146832, -8), (3147792, 8), (3150864, 12), (3163152, 16), (3212304, 18)]
noncomputable def atom0399 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![1,2,2] * g 2 * g 5) * z * (t+z-18) * (t+z-18))
theorem atom0399_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0399 g t z = CoefficientMerge.eval (monomial g t z) coeff0399 := by
  norm_num [atom0399, coeff0399, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0399_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0399 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![1,2,2]
  dsimp only [atom0399]
  positivity
theorem weighted0399_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1477625342958452192787102691680508338334416532892497490512186646007213491657257635883345258051517036557858554578799581359462246344682680 : Int) coeff0399) := by
  rw [CoefficientMerge.eval_scale, ← atom0399_identity]
  exact mul_nonneg (by norm_num) (atom0399_nonneg g t z hg hA hB ht hz hw)

def coeff0400 : CoefficientMerge.Poly :=
  [(1314833, -4), (1314836, -8), (1314848, -16), (1314896, -8), (1315856, 8), (1318928, 12), (1331216, 16), (1380368, 18)]
noncomputable def atom0400 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![1,2,2] * g 2 * g 6) * t * z)
theorem atom0400_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0400 g t z = CoefficientMerge.eval (monomial g t z) coeff0400 := by
  norm_num [atom0400, coeff0400, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0400_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0400 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![1,2,2]
  dsimp only [atom0400]
  positivity
theorem weighted0400_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (80782632129657385455821386957683114213224416868044962826221348322065890725083845505848895424310227321320881315186829269637399517280632320 : Int) coeff0400) := by
  rw [CoefficientMerge.eval_scale, ← atom0400_identity]
  exact mul_nonneg (by norm_num) (atom0400_nonneg g t z hg hA hB ht hz hw)

def coeff0401 : CoefficientMerge.Poly :=
  [(790545, -4), (790548, -8), (790560, -16), (790608, -8), (791568, 8), (794640, 12), (806928, 16), (856080, 18)]
noncomputable def atom0401 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![1,2,2] * g 2 * g 6) * t * t * t)
theorem atom0401_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0401 g t z = CoefficientMerge.eval (monomial g t z) coeff0401 := by
  norm_num [atom0401, coeff0401, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0401_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0401 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![1,2,2]
  dsimp only [atom0401]
  positivity
theorem weighted0401_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2687160015203666031437973723522153156419865004420781698003755663359748663914462084077086645924098917137497843511188546584348131566933760 : Int) coeff0401) := by
  rw [CoefficientMerge.eval_scale, ← atom0401_identity]
  exact mul_nonneg (by norm_num) (atom0401_nonneg g t z hg hA hB ht hz hw)

def coeff0402 : CoefficientMerge.Poly :=
  [(1576977, -4), (1576980, -8), (1576992, -16), (1577040, -8), (1578000, 8), (1581072, 12), (1593360, 16), (1642512, 18)]
noncomputable def atom0402 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![1,2,2] * g 2 * g 6) * t * t * z)
theorem atom0402_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0402 g t z = CoefficientMerge.eval (monomial g t z) coeff0402 := by
  norm_num [atom0402, coeff0402, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0402_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0402 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![1,2,2]
  dsimp only [atom0402]
  positivity
theorem weighted0402_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (11194583074132251822043348140461084962304426443693772787052332506348851169514315156893921500110700000868777274907000604652006120608851200 : Int) coeff0402) := by
  rw [CoefficientMerge.eval_scale, ← atom0402_identity]
  exact mul_nonneg (by norm_num) (atom0402_nonneg g t z hg hA hB ht hz hw)

def coeff0403 : CoefficientMerge.Poly :=
  [(2363409, -4), (2363412, -8), (2363424, -16), (2363472, -8), (2364432, 8), (2367504, 12), (2379792, 16), (2428944, 18)]
noncomputable def atom0403 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![1,2,2] * g 2 * g 6) * t * z * z)
theorem atom0403_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0403 g t z = CoefficientMerge.eval (monomial g t z) coeff0403 := by
  norm_num [atom0403, coeff0403, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0403_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0403 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![1,2,2]
  dsimp only [atom0403]
  positivity
theorem weighted0403_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4893702865199237940150507956888564495079519769509415639235373021107390557700175691629644864593859901712952466291218273062239649739596800 : Int) coeff0403) := by
  rw [CoefficientMerge.eval_scale, ← atom0403_identity]
  exact mul_nonneg (by norm_num) (atom0403_nonneg g t z hg hA hB ht hz hw)

def coeff0404 : CoefficientMerge.Poly :=
  [(802833, -4), (802836, -8), (802848, -16), (802896, -8), (803856, 8), (806928, 12), (819216, 16), (868368, 18)]
noncomputable def atom0404 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![1,2,2] * g 2 * g 7) * t * t * t)
theorem atom0404_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0404 g t z = CoefficientMerge.eval (monomial g t z) coeff0404 := by
  norm_num [atom0404, coeff0404, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0404_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0404 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![1,2,2]
  dsimp only [atom0404]
  positivity
theorem weighted0404_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3003314632650338376914576237965369317958818250510511907530337013609723734124164284319375731756735399850473253282188613521225851111449600 : Int) coeff0404) := by
  rw [CoefficientMerge.eval_scale, ← atom0404_identity]
  exact mul_nonneg (by norm_num) (atom0404_nonneg g t z hg hA hB ht hz hw)

def coeff0405 : CoefficientMerge.Poly :=
  [(1589265, -4), (1589268, -8), (1589280, -16), (1589328, -8), (1590288, 8), (1593360, 12), (1605648, 16), (1654800, 18)]
noncomputable def atom0405 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![1,2,2] * g 2 * g 7) * t * t * z)
theorem atom0405_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0405 g t z = CoefficientMerge.eval (monomial g t z) coeff0405 := by
  norm_num [atom0405, coeff0405, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0405_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0405 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![1,2,2]
  dsimp only [atom0405]
  positivity
theorem weighted0405_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (480724909920896540951510673795811941718527507759427008592294675296521310563263037619596695613796850594565624103933977636252683035648000 : Int) coeff0405) := by
  rw [CoefficientMerge.eval_scale, ← atom0405_identity]
  exact mul_nonneg (by norm_num) (atom0405_nonneg g t z hg hA hB ht hz hw)

def coeff0406 : CoefficientMerge.Poly :=
  [(1064977, -1296), (1064980, -2592), (1064992, -5184), (1065040, -2592), (1066000, 2592), (1069072, 3888), (1081360, 5184), (1130512, 5832), (1327121, 144), (1327124, 288), (1327136, 576), (1327184, 288), (1328144, -288), (1331216, -432), (1343504, -576), (1392656, -648), (1589265, -4), (1589268, -8), (1589280, -16), (1589328, -8), (1590288, 8), (1593360, 12), (1605648, 16), (1654800, 18), (2113553, 144), (2113556, 288), (2113568, 576), (2113616, 288), (2114576, -288), (2117648, -432), (2129936, -576), (2179088, -648), (2375697, -8), (2375700, -16), (2375712, -32), (2375760, -16), (2376720, 16), (2379792, 24), (2392080, 32), (2441232, 36), (3162129, -4), (3162132, -8), (3162144, -16), (3162192, -8), (3163152, 8), (3166224, 12), (3178512, 16), (3227664, 18)]
noncomputable def atom0406 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![1,2,2] * g 2 * g 7) * z * (t+z-18) * (t+z-18))
theorem atom0406_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0406 g t z = CoefficientMerge.eval (monomial g t z) coeff0406 := by
  norm_num [atom0406, coeff0406, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0406_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0406 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![1,2,2]
  dsimp only [atom0406]
  positivity
theorem weighted0406_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (84776926362892168481149184025120065382933971262567993202192283591791451068678028112737219674352515048982566903219989803309460024940800 : Int) coeff0406) := by
  rw [CoefficientMerge.eval_scale, ← atom0406_identity]
  exact mul_nonneg (by norm_num) (atom0406_nonneg g t z hg hA hB ht hz hw)

def coeff0407 : CoefficientMerge.Poly :=
  [(266305, -1296), (266308, -2592), (266320, -5184), (266368, -2592), (267328, 2592), (270400, 3888), (282688, 5184), (331840, 5832), (528449, 144), (528452, 288), (528464, 576), (528512, 288), (529472, -288), (532544, -432), (544832, -576), (593984, -648), (790593, -4), (790596, -8), (790608, -16), (790656, -8), (791616, 8), (794688, 12), (806976, 16), (856128, 18), (1314881, 144), (1314884, 288), (1314896, 576), (1314944, 288), (1315904, -288), (1318976, -432), (1331264, -576), (1380416, -648), (1577025, -8), (1577028, -16), (1577040, -32), (1577088, -16), (1578048, 16), (1581120, 24), (1593408, 32), (1642560, 36), (2363457, -4), (2363460, -8), (2363472, -16), (2363520, -8), (2364480, 8), (2367552, 12), (2379840, 16), (2428992, 18)]
noncomputable def atom0407 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![1,2,2] * g 3 * g 6) * t * (t+z-18) * (t+z-18))
theorem atom0407_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0407 g t z = CoefficientMerge.eval (monomial g t z) coeff0407 := by
  norm_num [atom0407, coeff0407, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0407_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0407 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![1,2,2]
  dsimp only [atom0407]
  positivity
theorem weighted0407_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (288003059294106154561892496517504288390297335312920857553821948320456703859465319049044946058110718933661990259923871760316019254086400 : Int) coeff0407) := by
  rw [CoefficientMerge.eval_scale, ← atom0407_identity]
  exact mul_nonneg (by norm_num) (atom0407_nonneg g t z hg hA hB ht hz hw)

def coeff0408 : CoefficientMerge.Poly :=
  [(16449, -1296), (16452, -2592), (16464, -5184), (16512, -2592), (17472, 2592), (20544, 3888), (32832, 5184), (81984, 5832), (278593, 144), (278596, 288), (278608, 576), (278656, 288), (279616, -288), (282688, -432), (294976, -576), (344128, -648), (540737, -4), (540740, -8), (540752, -16), (540800, -8), (541760, 8), (544832, 12), (557120, 16), (606272, 18), (1065025, 144), (1065028, 288), (1065040, 576), (1065088, 288), (1066048, -288), (1069120, -432), (1081408, -576), (1130560, -648), (1327169, -8), (1327172, -16), (1327184, -32), (1327232, -16), (1328192, 16), (1331264, 24), (1343552, 32), (1392704, 36), (2113601, -4), (2113604, -8), (2113616, -16), (2113664, -8), (2114624, 8), (2117696, 12), (2129984, 16), (2179136, 18)]
noncomputable def atom0408 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![1,2,2] * g 3 * g 7) * (t+z-18) * (t+z-18))
theorem atom0408_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0408 g t z = CoefficientMerge.eval (monomial g t z) coeff0408 := by
  norm_num [atom0408, coeff0408, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0408_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0408 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![1,2,2]
  dsimp only [atom0408]
  positivity
theorem weighted0408_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (44857314028164186205042866980014975216759597239113507965773161899335503816353979532524153356399772137599300948600072274051871240294400 : Int) coeff0408) := by
  rw [CoefficientMerge.eval_scale, ← atom0408_identity]
  exact mul_nonneg (by norm_num) (atom0408_nonneg g t z hg hA hB ht hz hw)

def coeff0409 : CoefficientMerge.Poly :=
  [(1069057, -1296), (1069060, -2592), (1069072, -5184), (1069120, -2592), (1070080, 2592), (1073152, 3888), (1085440, 5184), (1134592, 5832), (1331201, 144), (1331204, 288), (1331216, 576), (1331264, 288), (1332224, -288), (1335296, -432), (1347584, -576), (1396736, -648), (1593345, -4), (1593348, -8), (1593360, -16), (1593408, -8), (1594368, 8), (1597440, 12), (1609728, 16), (1658880, 18), (2117633, 144), (2117636, 288), (2117648, 576), (2117696, 288), (2118656, -288), (2121728, -432), (2134016, -576), (2183168, -648), (2379777, -8), (2379780, -16), (2379792, -32), (2379840, -16), (2380800, 16), (2383872, 24), (2396160, 32), (2445312, 36), (3166209, -4), (3166212, -8), (3166224, -16), (3166272, -8), (3167232, 8), (3170304, 12), (3182592, 16), (3231744, 18)]
noncomputable def atom0409 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![1,2,2] * g 6 * g 7) * z * (t+z-18) * (t+z-18))
theorem atom0409_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0409 g t z = CoefficientMerge.eval (monomial g t z) coeff0409 := by
  norm_num [atom0409, coeff0409, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0409_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0409 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![1,2,2]
  dsimp only [atom0409]
  positivity
theorem weighted0409_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (348741839070522439219671925181984521732428843903203160016650658519965021987229405446462518423833837977148607053251982018539678582681600 : Int) coeff0409) := by
  rw [CoefficientMerge.eval_scale, ← atom0409_identity]
  exact mul_nonneg (by norm_num) (atom0409_nonneg g t z hg hA hB ht hz hw)

def coeff0410 : CoefficientMerge.Poly :=
  [(2129921, -4), (2129924, -8), (2129936, -16), (2129984, -8), (2130944, 8), (2134016, 12), (2146304, 16), (2195456, 18)]
noncomputable def atom0410 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![1,2,2] * g 7 * g 7) * z * z)
theorem atom0410_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0410 g t z = CoefficientMerge.eval (monomial g t z) coeff0410 := by
  norm_num [atom0410, coeff0410, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0410_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0410 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![1,2,2]
  dsimp only [atom0410]
  positivity
theorem weighted0410_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (6651994996458760197015697350751577822457037525506191103964469138256269110071930365227936177222796067339813654631176999887661880397856000 : Int) coeff0410) := by
  rw [CoefficientMerge.eval_scale, ← atom0410_identity]
  exact mul_nonneg (by norm_num) (atom0410_nonneg g t z hg hA hB ht hz hw)

def coeff0411 : CoefficientMerge.Poly :=
  [(2392065, -4), (2392068, -8), (2392080, -16), (2392128, -8), (2393088, 8), (2396160, 12), (2408448, 16), (2457600, 18)]
noncomputable def atom0411 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![1,2,2] * g 7 * g 7) * t * z * z)
theorem atom0411_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0411 g t z = CoefficientMerge.eval (monomial g t z) coeff0411 := by
  norm_num [atom0411, coeff0411, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0411_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0411 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![1,2,2]
  dsimp only [atom0411]
  positivity
theorem weighted0411_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1238423729983049418274412436713343477532615890212180782670543603824498153118823296201394382475393707414498853498257822325027354594496000 : Int) coeff0411) := by
  rw [CoefficientMerge.eval_scale, ← atom0411_identity]
  exact mul_nonneg (by norm_num) (atom0411_nonneg g t z hg hA hB ht hz hw)

def sparseBlock037 : CoefficientMerge.Poly :=
  [(16449, -58135078980500785321735555606099407880920438021891106323642017821538812945994757474151302749894104690328694029385693667171225127421542400), (16452, -116270157961001570643471111212198815761840876043782212647284035643077625891989514948302605499788209380657388058771387334342450254843084800), (16464, -232540315922003141286942222424397631523681752087564425294568071286155251783979029896605210999576418761314776117542774668684900509686169600), (16512, -116270157961001570643471111212198815761840876043782212647284035643077625891989514948302605499788209380657388058771387334342450254843084800), (17472, 116270157961001570643471111212198815761840876043782212647284035643077625891989514948302605499788209380657388058771387334342450254843084800), (20544, 174405236941502355965206666818298223642761314065673318970926053464616438837984272422453908249682314070986082088157081001513675382264627200), (32832, 232540315922003141286942222424397631523681752087564425294568071286155251783979029896605210999576418761314776117542774668684900509686169600), (81984, 261607855412253533947810000227447335464141971098509978456389080196924658256976408633680862374523471106479123132235621502270513073396940800), (266305, -373251964845161576312212675486685557753825346565545431389753245023311888201867053487562250091311491738025939376861337801369560953295974400), (266308, -746503929690323152624425350973371115507650693131090862779506490046623776403734106975124500182622983476051878753722675602739121906591948800), (266320, -1493007859380646305248850701946742231015301386262181725559012980093247552807468213950249000365245966952103757507445351205478243813183897600), (266368, -746503929690323152624425350973371115507650693131090862779506490046623776403734106975124500182622983476051878753722675602739121906591948800), (267328, 746503929690323152624425350973371115507650693131090862779506490046623776403734106975124500182622983476051878753722675602739121906591948800), (270400, 1119755894535484728936638026460056673261476039696636294169259735069935664605601160462686750273934475214077818130584013404108682859887923200), (278593, 6459453220055642813526172845122156431213382002432345147071335313504312549554973052683478083321567187814299336598410407463469458602393600), (278596, 12918906440111285627052345690244312862426764004864690294142670627008625099109946105366956166643134375628598673196820814926938917204787200), (278608, 25837812880222571254104691380488625724853528009729380588285341254017250198219892210733912333286268751257197346393641629853877834409574400), (278656, 12918906440111285627052345690244312862426764004864690294142670627008625099109946105366956166643134375628598673196820814926938917204787200), (279616, -12918906440111285627052345690244312862426764004864690294142670627008625099109946105366956166643134375628598673196820814926938917204787200), (282688, 1473629499720479376808272183411375761721661240254884690117798974152734615158803294792198566115281265388660859497650119983087835437376716800), (294976, -25837812880222571254104691380488625724853528009729380588285341254017250198219892210733912333286268751257197346393641629853877834409574400), (331840, 1679633841803227093404957039690085009892214059544954441253889602604903496908401740694030125410901712821116727195876020106163024289831884800), (344128, -29067539490250392660867777803049703940460219010945553161821008910769406472997378737075651374947052345164347014692846833585612563710771200), (528449, 41472440538351286256912519498520617528202816285060603487750360558145765355763005943062472232367943526447326597429037533485506772588441600), (528452, 82944881076702572513825038997041235056405632570121206975500721116291530711526011886124944464735887052894653194858075066971013545176883200), (528464, 165889762153405145027650077994082470112811265140242413951001442232583061423052023772249888929471774105789306389716150133942027090353766400), (528512, 82944881076702572513825038997041235056405632570121206975500721116291530711526011886124944464735887052894653194858075066971013545176883200), (529472, -82944881076702572513825038997041235056405632570121206975500721116291530711526011886124944464735887052894653194858075066971013545176883200), (532544, -124417321615053858770737558495561852584608448855181810463251081674437296067289017829187416697103830579341979792287112600456520317765324800), (540737, -179429256112656744820171467920059900867038388956454031863092647597342015265415918130096613425599088550397203794400289096207484961177600), (540740, -358858512225313489640342935840119801734076777912908063726185295194684030530831836260193226851198177100794407588800578192414969922355200), (540752, -717717024450626979280685871680239603468153555825816127452370590389368061061663672520386453702396354201588815177601156384829939844710400), (540800, -358858512225313489640342935840119801734076777912908063726185295194684030530831836260193226851198177100794407588800578192414969922355200), (541760, 358858512225313489640342935840119801734076777912908063726185295194684030530831836260193226851198177100794407588800578192414969922355200), (544832, -165351474385067174793189563590322290410210149973373051855412164289791035377255776017859599089194976840138114778332949266653404635470233600), (557120, 717717024450626979280685871680239603468153555825816127452370590389368061061663672520386453702396354201588815177601156384829939844710400), (593984, -186625982422580788156106337743342778876912673282772715694876622511655944100933526743781125045655745869012969688430668900684780476647987200), (606272, 807431652506955351690771605640269553901672750304043143383916914188039068694371631585434760415195898476787417074801300932933682325299200), (790545, -10748640060814664125751894894088612625679460017683126792015022653438994655657848336308346583696395668549991374044754186337392526267735040), (790548, -21497280121629328251503789788177225251358920035366253584030045306877989311315696672616693167392791337099982748089508372674785052535470080), (790560, -42994560243258656503007579576354450502717840070732507168060090613755978622631393345233386334785582674199965496179016745349570105070940160), (790593, -1152012237176424618247569986070017153561189341251683430215287793281826815437861276196179784232442875734647961039695487041264077016345600), (790596, -2304024474352849236495139972140034307122378682503366860430575586563653630875722552392359568464885751469295922079390974082528154032691200), (790608, -26105329070335026724494069732457293865603677400372987304891196480005296573067141777401412304322562840038574592248290320839841360600852480), (790656, -2304024474352849236495139972140034307122378682503366860430575586563653630875722552392359568464885751469295922079390974082528154032691200), (791568, 21497280121629328251503789788177225251358920035366253584030045306877989311315696672616693167392791337099982748089508372674785052535470080), (791616, 2304024474352849236495139972140034307122378682503366860430575586563653630875722552392359568464885751469295922079390974082528154032691200), (794640, 32245920182443992377255684682265837877038380053049380376045067960316983966973545008925039751089187005649974122134262559012177578803205120), (794688, 3456036711529273854742709958210051460683568023755050290645863379845480446313583828588539352697328627203943883119086461123792231049036800), (802833, -12013258530601353507658304951861477271835273002042047630121348054438894936496657137277502927026941599401893013128754454084903404445798400), (802836, -24026517061202707015316609903722954543670546004084095260242696108877789872993314274555005854053883198803786026257508908169806808891596800), (802848, -48053034122405414030633219807445909087341092008168190520485392217755579745986628549110011708107766397607572052515017816339613617783193600), (802896, -24026517061202707015316609903722954543670546004084095260242696108877789872993314274555005854053883198803786026257508908169806808891596800), (803856, 24026517061202707015316609903722954543670546004084095260242696108877789872993314274555005854053883198803786026257508908169806808891596800), (806928, 79034335835062717025982494431938882318223659076858650058424134777072663432121364757065895115866407472405644535565280107604280318408335360), (806976, 4608048948705698472990279944280068614244757365006733720861151173127307261751445104784719136929771502938591844158781948165056308065382400), (819216, 48053034122405414030633219807445909087341092008168190520485392217755579745986628549110011708107766397607572052515017816339613617783193600), (856080, 48368880273665988565883527023398756815557570079574070564067601940475475950460317513387559626633780508474961183201393838518266368204807680), (856128, 5184055067293910782114064937315077191025352035632575435968795069768220669470375742882809029045992940805915824678629691685688346573555200), (868368, 54059663387706090784462372283376647723258728509189214335546066244975027214234957117748763171621237197308518559079395043382065320006092800), (1048849, -1458858472994135082320643485985867295980476915511618510366231730094545139653285154978967867749817822915071787414286590035051546120108445120), (1048852, -2917716945988270164641286971971734591960953831023237020732463460189090279306570309957935735499635645830143574828573180070103092240216890240), (1048864, -5835433891976540329282573943943469183921907662046474041464926920378180558613140619915871470999271291660287149657146360140206184480433780480), (1048912, -2917716945988270164641286971971734591960953831023237020732463460189090279306570309957935735499635645830143574828573180070103092240216890240), (1049617, -1915002444474154041852085088417938806481403826628676747703793893225348685187805896104815454434766079378984686734124257441863071262708753280), (1049620, -3830004888948308083704170176835877612962807653257353495407587786450697370375611792209630908869532158757969373468248514883726142525417506560), (1049632, -7660009777896616167408340353671755225925615306514706990815175572901394740751223584419261817739064317515938746936497029767452285050835013120), (1049680, -3830004888948308083704170176835877612962807653257353495407587786450697370375611792209630908869532158757969373468248514883726142525417506560), (1049872, 2917716945988270164641286971971734591960953831023237020732463460189090279306570309957935735499635645830143574828573180070103092240216890240), (1050640, 3830004888948308083704170176835877612962807653257353495407587786450697370375611792209630908869532158757969373468248514883726142525417506560), (1052944, 4376575418982405246961930457957601887941430746534855531098695190283635418959855464936903603249453468745215362242859770105154638360325335360), (1053712, 5745007333422462125556255265253816419444211479886030243111381679676046055563417688314446363304298238136954060202372772325589213788126259840), (1064977, -109870896566308250351569342496555604736282426756288119190041199534961720585006724434107436697960859503481406706573106785089060192323276800), (1064980, -219741793132616500703138684993111209472564853512576238380082399069923441170013448868214873395921719006962813413146213570178120384646553600), (1064992, -439483586265233001406277369986222418945129707025152476760164798139846882340026897736429746791843438013925626826292427140356240769293107200), (1065025, 6459453220055642813526172845122156431213382002432345147071335313504312549554973052683478083321567187814299336598410407463469458602393600), (1065028, 12918906440111285627052345690244312862426764004864690294142670627008625099109946105366956166643134375628598673196820814926938917204787200), (1065040, -193903980252393929449033993612622583747711325502846857791797057815906190971793556657480961062635450255705616066752571940324242550236979200), (1065088, 12918906440111285627052345690244312862426764004864690294142670627008625099109946105366956166643134375628598673196820814926938917204787200), (1065232, 5835433891976540329282573943943469183921907662046474041464926920378180558613140619915871470999271291660287149657146360140206184480433780480), (1066000, 7879751571029232668111479038664866435398180160027283229195257971971318181921237033287476691134986036522901560349643243337630405435481566720), (1066048, -12918906440111285627052345690244312862426764004864690294142670627008625099109946105366956166643134375628598673196820814926938917204787200), (1069057, -451969423435397081228694815035851940165227781698551295381579253441874668495449309458615423877288654018384594741014568696027423443155353600), (1069060, -903938846870794162457389630071703880330455563397102590763158506883749336990898618917230847754577308036769189482029137392054846886310707200), (1069072, -1478265004042663573860071232653740946452063846525340823956193415162613512226777064532139385415272037563094158844338954428842513195651584000), (1069120, -923317206530961090897968148607070349624095709404399626204372512824262274639563538075281282004542009600212087491824368614445255262117888000), (1070080, 903938846870794162457389630071703880330455563397102590763158506883749336990898618917230847754577308036769189482029137392054846886310707200), (1073152, 1355908270306191243686084445107555820495683345095653886144737760325624005486347928375846271631865962055153784223043706088082270329466060800), (1081360, 439483586265233001406277369986222418945129707025152476760164798139846882340026897736429746791843438013925626826292427140356240769293107200), (1081408, -25837812880222571254104691380488625724853528009729380588285341254017250198219892210733912333286268751257197346393641629853877834409574400), (1085440, 1807877693741588324914779260143407760660911126794205181526317013767498673981797237834461695509154616073538378964058274784109693772621414400), (1114384, 6564863128473607870442895686936402831912146119802283296648042785425453128439783197405355404874180203117823043364289655157731957540488003040), (1115152, 8617511000133693188334382897880724629166317219829045364667072519514069083345126532471669544956447357205431090303559158488383820682189389760), (1130512, 494419034548387126582062041234500221313270920403296536355185397907327742632530259953483465140823867765666330179578980532900770865454745600), (1130560, -29067539490250392660867777803049703940460219010945553161821008910769406472997378737075651374947052345164347014692846833585612563710771200), (1134592, 2033862405459286865529126667661333730743525017643480829217106640488436008229521892563769407447798943082730676334565559132123405494199091200), (1310993, 162095385888237231368960387331763032886719657279068723374025747788282793294809461664329763083313091435007976379365176670561282902234271680), (1310996, 324190771776474462737920774663526065773439314558137446748051495576565586589618923328659526166626182870015952758730353341122565804468543360), (1311008, 648381543552948925475841549327052131546878629116274893496102991153131173179237846657319052333252365740031905517460706682245131608937086720), (1311056, 324190771776474462737920774663526065773439314558137446748051495576565586589618923328659526166626182870015952758730353341122565804468543360), (1311761, -422477777475356039899695124086378910124631030673879476285567701594684476399805485965262319899489345287411679530272955011594955757310051520), (1311764, -844955554950712079799390248172757820249262061347758952571135403189368952799610971930524639798978690574823359060545910023189911514620103040), (1311776, -1689911109901424159598780496345515640498524122695517905142270806378737905599221943861049279597957381149646718121091820046379823029240206080), (1311824, -844955554950712079799390248172757820249262061347758952571135403189368952799610971930524639798978690574823359060545910023189911514620103040), (1312016, -324190771776474462737920774663526065773439314558137446748051495576565586589618923328659526166626182870015952758730353341122565804468543360), (1312784, 844955554950712079799390248172757820249262061347758952571135403189368952799610971930524639798978690574823359060545910023189911514620103040), (1314833, -323130528518629541823285547830732456852897667472179851304885393288263562900335382023395581697240909285283525260747317078549598069122529280), (1314836, -646261057037259083646571095661464913705795334944359702609770786576527125800670764046791163394481818570567050521494634157099196138245058560), (1314848, -1292522114074518167293142191322929827411590669888719405219541573153054251601341528093582326788963637141134101042989268314198392276490117120), (1314881, 41472440538351286256912519498520617528202816285060603487750360558145765355763005943062472232367943526447326597429037533485506772588441600), (1314884, 82944881076702572513825038997041235056405632570121206975500721116291530711526011886124944464735887052894653194858075066971013545176883200), (1314896, -480371294883853938618921017667382443592984069804117288658769344343944064377618740274541274465010044464777744131778484023157169047891292160), (1314944, 82944881076702572513825038997041235056405632570121206975500721116291530711526011886124944464735887052894653194858075066971013545176883200), (1315088, -486286157664711694106881161995289098660158971837206170122077243364848379884428384992989289249939274305023929138095530011683848706702815040), (1315856, 1913694389463327203345656467920601644079688426965998131466473891360580555000087221942578123092949854432802089112313499191884063410175213120), (1315904, -82944881076702572513825038997041235056405632570121206975500721116291530711526011886124944464735887052894653194858075066971013545176883200), (1318928, 969391585555888625469856643492197370558693002416539553914656179864790688701006146070186745091722727855850575782241951235648794207367587840), (1318976, -124417321615053858770737558495561852584608448855181810463251081674437296067289017829187416697103830579341979792287112600456520317765324800), (1327121, 12207877396256472261285482499617289415142491861809791021115688837217968953889636048234159633106762167053489634063678531676562243591475200), (1327124, 24415754792512944522570964999234578830284983723619582042231377674435937907779272096468319266213524334106979268127357063353124487182950400), (1327136, 48831509585025889045141929998469157660569967447239164084462755348871875815558544192936638532427048668213958536254714126706248974365900800), (1327169, -358858512225313489640342935840119801734076777912908063726185295194684030530831836260193226851198177100794407588800578192414969922355200), (1327172, -717717024450626979280685871680239603468153555825816127452370590389368061061663672520386453702396354201588815177601156384829939844710400), (1327184, 22980320743611690564009593255874099623348676611967949787326636493657201785655944751427546358808731625703801637772154750583464607493529600), (1327232, -717717024450626979280685871680239603468153555825816127452370590389368061061663672520386453702396354201588815177601156384829939844710400), (1327376, -648381543552948925475841549327052131546878629116274893496102991153131173179237846657319052333252365740031905517460706682245131608937086720), (1328144, 1665495355108911215076209531346281061668239138971898323100039428704301967691442671764580960331743856815539738852964462983026698542057255680), (1328192, 717717024450626979280685871680239603468153555825816127452370590389368061061663672520386453702396354201588815177601156384829939844710400), (1331201, 50218824826155231247632757226205771129469753522061255042397694826874963166161034384290602653032072668709399415668285410669713715906150400), (1331204, 100437649652310462495265514452411542258939507044122510084795389653749926332322068768581205306064145337418798831336570821339427431812300800), (1331216, 1456773781190369675499816772728901043684042208391535052325785285948900197404316757486042258501771641314811229803471374361847560409340293120), (1331264, -64375536964418742063463534734150568448669527762381179675027496693249082999137459494888103942854034237068124335613177578025354748774400000), (1332224, -100437649652310462495265514452411542258939507044122510084795389653749926332322068768581205306064145337418798831336570821339427431812300800), (1335296, -150656474478465693742898271678617313388409260566183765127193084480624889498483103152871807959096218006128198247004856232009141147718451200), (1343504, -48831509585025889045141929998469157660569967447239164084462755348871875815558544192936638532427048668213958536254714126706248974365900800), (1343552, 1435434048901253958561371743360479206936307111651632254904741180778736122123327345040772907404792708403177630355202312769659879689420800), (1347584, -200875299304620924990531028904823084517879014088245020169590779307499852664644137537162410612128290674837597662673141642678854863624601600), (1376528, -729429236497067541160321742992933647990238457755809255183115865047272569826642577489483933874908911457535893707143295017525773060054222560), (1377296, 1901149998639102179548628058388705095560839638032457643285054657176080143799124686843680439547702053793352557886228297552177300907895231840), (1380368, 1454087378333832938204784965238296055838039503624809330871984269797186033051509219105280117637584091783775863673362926853473191311051381760), (1380416, -186625982422580788156106337743342778876912673282772715694876622511655944100933526743781125045655745869012969688430668900684780476647987200), (1392656, -54935448283154125175784671248277802368141213378144059595020599767480860292503362217053718348980429751740703353286553392544530096161638400), (1392704, 1614863305013910703381543211280539107803345500608086286767833828376078137388743263170869520830391796953574834149602601865867364650598400), (1396736, -225984711717698540614347407517925970082613890849275647690789626720937334247724654729307711938644327009192297370507284348013711721577676800), (1573137, -13366068056081028678530731663418619691679981748313774038664692389504078581387084031791987707448429023597095509775753913242331013227197040), (1573140, -26732136112162057357061463326837239383359963496627548077329384779008157162774168063583975414896858047194191019551507826484662026454394080), (1573152, -53464272224324114714122926653674478766719926993255096154658769558016314325548336127167950829793716094388382039103015652969324052908788160), (1573200, -26732136112162057357061463326837239383359963496627548077329384779008157162774168063583975414896858047194191019551507826484662026454394080), (1573905, -40638759169449625944318360227709533841599678384993129716710730733188602037735467869757752970435439116538854847001763099569664023657711040), (1573908, -81277518338899251888636720455419067683199356769986259433421461466377204075470935739515505940870878233077709694003526199139328047315422080), (1573920, -162555036677798503777273440910838135366398713539972518866842922932754408150941871479031011881741756466155419388007052398278656094630844160), (1573968, -81277518338899251888636720455419067683199356769986259433421461466377204075470935739515505940870878233077709694003526199139328047315422080), (1574160, 26732136112162057357061463326837239383359963496627548077329384779008157162774168063583975414896858047194191019551507826484662026454394080), (1574928, 81277518338899251888636720455419067683199356769986259433421461466377204075470935739515505940870878233077709694003526199139328047315422080), (1576977, -44778332296529007288173392561844339849217705774775091148209330025395404678057260627575686000442800003475109099628002418608024482435404800), (1576980, -89556664593058014576346785123688679698435411549550182296418660050790809356114521255151372000885600006950218199256004837216048964870809600), (1576992, -179113329186116029152693570247377359396870823099100364592837320101581618712229042510302744001771200013900436398512009674432097929741619200), (1577025, -2304024474352849236495139972140034307122378682503366860430575586563653630875722552392359568464885751469295922079390974082528154032691200), (1577028, -4608048948705698472990279944280068614244757365006733720861151173127307261751445104784719136929771502938591844158781948165056308065382400), (1577040, -98772762490469411522327345012248816926924926279563649738140962397045423879617411464720810274745143012827401887573568733546161581001574400), (1577088, -4608048948705698472990279944280068614244757365006733720861151173127307261751445104784719136929771502938591844158781948165056308065382400), (1577232, 40098204168243086035592194990255859075039945244941322115994077168512235744161252095375963122345287070791286529327261739726993039681591120), (1578000, 211472942101406892409301865806817281223234446704529571446550852250356615469320924864424630912191917356566782740261294135925041035843942720), (1578048, 4608048948705698472990279944280068614244757365006733720861151173127307261751445104784719136929771502938591844158781948165056308065382400), (1581072, 134334996889587021864520177685533019547653117324325273444627990076186214034171781882727058001328400010425327298884007255824073447306214400), (1581120, 6912073423058547709485419916420102921367136047510100581291726759690960892627167657177078705394657254407887766238172922247584462098073600), (1589265, -2262007345135154837730639431283728028405845916087980007177947835553251046527764262929335661152597462574192764028615869758248572242355200), (1589268, -4524014690270309675461278862567456056811691832175960014355895671106502093055528525858671322305194925148385528057231739516497144484710400), (1589280, -9048029380540619350922557725134912113623383664351920028711791342213004186111057051717342644610389850296771056114463479032994288969420800), (1589328, -4524014690270309675461278862567456056811691832175960014355895671106502093055528525858671322305194925148385528057231739516497144484710400), (1589520, 53464272224324114714122926653674478766719926993255096154658769558016314325548336127167950829793716094388382039103015652969324052908788160), (1590288, 167079051368068813452734719773405591423210405372148478881198818603860910243997400004889683204046951391303804916064284137795153239115554560), (1593345, -1394967356282089756878687700727938086929715375612812640066602634079860087948917621785850073695335351908594428213007928074158714330726400), (1593348, -2789934712564179513757375401455876173859430751225625280133205268159720175897835243571700147390670703817188856426015856148317428661452800), (1593360, 180319481796393134638370737738316791134369499344913054054104753071921931500016664811947350690447650993988636977745825571410208789145779200), (1593408, 6426163184847217432223184487104261054630083978787842161589097078094894347605054965997738126468872302059994831891548040181795187469312000), (1594368, 2789934712564179513757375401455876173859430751225625280133205268159720175897835243571700147390670703817188856426015856148317428661452800), (1597440, 4184902068846269270636063102183814260789146126838437920199807902239580263846752865357550221086006055725783284639023784222476142992179200), (1605648, 9048029380540619350922557725134912113623383664351920028711791342213004186111057051717342644610389850296771056114463479032994288969420800), (1609728, 5579869425128359027514750802911752347718861502451250560266410536319440351795670487143400294781341407634377712852031712296634857322905600), (1638672, 60147306252364629053388292485383788612559917867411983173991115752768353616241878143063944683517930606186929793990892609590489559522386680), (1639440, 182874416262523316749432621024692902287198552732469083725198288299348709169809605413909888366959476024424846811507933948063488106459699680), (1642512, 201502495334380532796780266528299529321479675986487910166941985114279321051257672824090587001992600015637990948326010883736110170959321600), (1642560, 10368110134587821564228129874630154382050704071265150871937590139536441338940751485765618058091985881611831649357259383371376693147110400), (1654800, 10179033053108196769787877440776776127826306622395910032300765259989629709374939183182010475186688581583867438128771413912118575090598400), (1658880, 6277353103269403905954094653275721391183719190257656880299711853359370395770129298036325331629009083588674926958535676333714214488268800), (2097425, 162095385888237231368960387331763032886719657279068723374025747788282793294809461664329763083313091435007976379365176670561282902234271680), (2097428, 324190771776474462737920774663526065773439314558137446748051495576565586589618923328659526166626182870015952758730353341122565804468543360), (2097440, 648381543552948925475841549327052131546878629116274893496102991153131173179237846657319052333252365740031905517460706682245131608937086720), (2097488, 324190771776474462737920774663526065773439314558137446748051495576565586589618923328659526166626182870015952758730353341122565804468543360), (2098193, 206016469667687217985561391040115617811917403797293179950902725858595317557436670645740370121354200041417585271192979804158767795048859520), (2098196, 412032939335374435971122782080231235623834807594586359901805451717190635114873341291480740242708400082835170542385959608317535590097719040), (2098208, 824065878670748871942245564160462471247669615189172719803610903434381270229746682582961480485416800165670341084771919216635071180195438080), (2098256, 412032939335374435971122782080231235623834807594586359901805451717190635114873341291480740242708400082835170542385959608317535590097719040), (2098448, -324190771776474462737920774663526065773439314558137446748051495576565586589618923328659526166626182870015952758730353341122565804468543360), (2099216, -412032939335374435971122782080231235623834807594586359901805451717190635114873341291480740242708400082835170542385959608317535590097719040), (2101520, -486286157664711694106881161995289098660158971837206170122077243364848379884428384992989289249939274305023929138095530011683848706702815040), (2102288, -618049409003061653956684173120346853435752211391879539852708177575785952672310011937221110364062600124252755813578939412476303385146578560), (2113553, 12207877396256472261285482499617289415142491861809791021115688837217968953889636048234159633106762167053489634063678531676562243591475200), (2113556, 24415754792512944522570964999234578830284983723619582042231377674435937907779272096468319266213524334106979268127357063353124487182950400), (2113568, 48831509585025889045141929998469157660569967447239164084462755348871875815558544192936638532427048668213958536254714126706248974365900800), (2113601, -179429256112656744820171467920059900867038388956454031863092647597342015265415918130096613425599088550397203794400289096207484961177600), (2113604, -358858512225313489640342935840119801734076777912908063726185295194684030530831836260193226851198177100794407588800578192414969922355200), (2113616, 23698037768062317543290279127554339226816830167793765914779007084046569846717608423947932812511127979905390452949755906968294547338240000), (2113664, -358858512225313489640342935840119801734076777912908063726185295194684030530831836260193226851198177100794407588800578192414969922355200), (2113808, -648381543552948925475841549327052131546878629116274893496102991153131173179237846657319052333252365740031905517460706682245131608937086720), (2114576, -848481633463261816464816529159697050077954598912792301845842281108817208137525954679429799751630324499777320352899276279988195667378388480), (2114624, 358858512225313489640342935840119801734076777912908063726185295194684030530831836260193226851198177100794407588800578192414969922355200), (2117633, 50218824826155231247632757226205771129469753522061255042397694826874963166161034384290602653032072668709399415668285410669713715906150400), (2117636, 100437649652310462495265514452411542258939507044122510084795389653749926332322068768581205306064145337418798831336570821339427431812300800), (2117648, 164251667115851508206674581405971216272451538502815647106243712795845945802975229392459931712808004173677128760482106047649168132850176000), (2117696, 100975937420648432729726028856171721961540622210991872180384667596541952378118316522971495146340942603069990442719771688628049886695833600), (2118656, -100437649652310462495265514452411542258939507044122510084795389653749926332322068768581205306064145337418798831336570821339427431812300800), (2121728, -150656474478465693742898271678617313388409260566183765127193084480624889498483103152871807959096218006128198247004856232009141147718451200), (2129921, -26607979985835040788062789403006311289828150102024764415857876553025076440287721460911744708891184269359254618524707999550647521591424000), (2129924, -53215959971670081576125578806012622579656300204049528831715753106050152880575442921823489417782368538718509237049415999101295043182848000), (2129936, -155263429528366052197393087610494402819882567855338221747894261560972181576709430036583617367991785745650977010353546124908839060731596800), (2129984, -52498242947219454596844892934332382976188146648223712704263382515660784819513779249303102964079972184516920421871814842716465103338137600), (2130944, 53215959971670081576125578806012622579656300204049528831715753106050152880575442921823489417782368538718509237049415999101295043182848000), (2134016, -121051359347115802626342660695804150648394563782170726922017149648424623343780973154427176485454737866759833807099017644026912298850329600), (2146304, 106431919943340163152251157612025245159312600408099057663431506212100305761150885843646978835564737077437018474098831998202590086365696000), (2162960, -729429236497067541160321742992933647990238457755809255183115865047272569826642577489483933874908911457535893707143295017525773060054222560), (2163728, -927074113504592480935026259680520280153628317087819309779062266363678929008465017905831665546093900186379133720368409118714455077719867840), (2179088, -54935448283154125175784671248277802368141213378144059595020599767480860292503362217053718348980429751740703353286553392544530096161638400), (2179136, 807431652506955351690771605640269553901672750304043143383916914188039068694371631585434760415195898476787417074801300932933682325299200), (2183168, -225984711717698540614347407517925970082613890849275647690789626720937334247724654729307711938644327009192297370507284348013711721577676800), (2195456, 119735909936257683546282552313528400804226675459111439871360444488612843981294746574102851190010329212116645783361185997977913847161408000), (2359569, -18773969075779981982565261086422375911315398658818293605125856058189732882265160066109122928769451503893478715529688109124035921363316128), (2359572, -37547938151559963965130522172844751822630797317636587210251712116379465764530320132218245857538903007786957431059376218248071842726632256), (2359584, -75095876303119927930261044345689503645261594635273174420503424232758931529060640264436491715077806015573914862118752436496143685453264512), (2359632, -37547938151559963965130522172844751822630797317636587210251712116379465764530320132218245857538903007786957431059376218248071842726632256), (2360337, -28441521650762674695760516165886231050614632158519623848869852815903957647338259385914292674287058341989373773152545802053063576564889760), (2360340, -56883043301525349391521032331772462101229264317039247697739705631807915294676518771828585348574116683978747546305091604106127153129779520), (2360352, -113766086603050698783042064663544924202458528634078495395479411263615830589353037543657170697148233367957495092610183208212254306259559040), (2360400, -56883043301525349391521032331772462101229264317039247697739705631807915294676518771828585348574116683978747546305091604106127153129779520), (2360592, 37547938151559963965130522172844751822630797317636587210251712116379465764530320132218245857538903007786957431059376218248071842726632256), (2361360, 56883043301525349391521032331772462101229264317039247697739705631807915294676518771828585348574116683978747546305091604106127153129779520), (2363409, -19574811460796951760602031827554257980318079078037662556941492084429562230800702766518579458375439606851809865164873092248958598958387200), (2363412, -39149622921593903521204063655108515960636158156075325113882984168859124461601405533037158916750879213703619730329746184497917197916774400), (2363424, -78299245843187807042408127310217031921272316312150650227765968337718248923202811066074317833501758427407239460659492368995834395833548800), (2363457, -1152012237176424618247569986070017153561189341251683430215287793281826815437861276196179784232442875734647961039695487041264077016345600), (2363460, -2304024474352849236495139972140034307122378682503366860430575586563653630875722552392359568464885751469295922079390974082528154032691200), (2363472, -43757671870299601994194343599388584574880915521082058834744135341986431723352850637821878053680650716642211574488528132662973505982156800), (2363520, -2304024474352849236495139972140034307122378682503366860430575586563653630875722552392359568464885751469295922079390974082528154032691200), (2363664, 56321907227339945947695783259267127733946195976454880815377568174569198646795480198327368786308354511680436146589064327372107764089948384), (2364432, 124474187873881927608485612152767209112480054631634196660492542616570997403616183690780036939612054239671741049787383590657107927611443680), (2364480, 2304024474352849236495139972140034307122378682503366860430575586563653630875722552392359568464885751469295922079390974082528154032691200), (2367504, 58724434382390855281806095482662773940954237234112987670824476253288686692402108299555738375126318820555429595494619276746875796875161600), (2367552, 3456036711529273854742709958210051460683568023755050290645863379845480446313583828588539352697328627203943883119086461123792231049036800), (2375697, -678215410903137347849193472200960523063471770100543945617538268734331608549424224901897757394820120391860535225759918426475680199526400), (2375700, -1356430821806274695698386944401921046126943540201087891235076537468663217098848449803795514789640240783721070451519836852951360399052800), (2375712, -2712861643612549391396773888803842092253887080402175782470153074937326434197696899607591029579280481567442140903039673705902720798105600), (2375760, -1356430821806274695698386944401921046126943540201087891235076537468663217098848449803795514789640240783721070451519836852951360399052800), (2375952, 75095876303119927930261044345689503645261594635273174420503424232758931529060640264436491715077806015573914862118752436496143685453264512), (2376720, 115122517424856973478740451607946845248585472174279583286714487801084493806451885993460966211937873608741216163061703045065205666658611840), (2379777, -2789934712564179513757375401455876173859430751225625280133205268159720175897835243571700147390670703817188856426015856148317428661452800), (2379780, -5579869425128359027514750802911752347718861502451250560266410536319440351795670487143400294781341407634377712852031712296634857322905600), (2379792, 69174153225640501030926206120996408795025008617549780944085762071282363045259742766493210516123535973314065640632708699681991721786316800), (2379840, -971820476422660554524470858631683733474104137444516839405259363192133090044225382358681157851569904695785868693249764131578549257523200), (2380800, 5579869425128359027514750802911752347718861502451250560266410536319440351795670487143400294781341407634377712852031712296634857322905600), (2383872, 8369804137692538541272126204367628521578292253676875840399615804479160527693505730715100442172012111451566569278047568444952285984358400), (2392065, -4953694919932197673097649746853373910130463560848723130682174415297992612475293184805577529901574829657995413993031289300109418377984000), (2392068, -9907389839864395346195299493706747820260927121697446261364348830595985224950586369611155059803149659315990827986062578600218836755968000), (2392080, -17101918036116241300993825098609653548267967162992716740258544586254644015703475839614719090027018837064539515069085483494534952713830400), (2392128, -9907389839864395346195299493706747820260927121697446261364348830595985224950586369611155059803149659315990827986062578600218836755968000), (2393088, 9907389839864395346195299493706747820260927121697446261364348830595985224950586369611155059803149659315990827986062578600218836755968000), (2396160, 26020823610053311074322450846383626425829113687448670512579344318532858541017220528703533179267407304242741667683157292493597969779763200), (2408448, 19814779679728790692390598987413495640521854243394892522728697661191970449901172739222310119606299318631981655972125157200437673511936000), (2425104, 84482860841009918921543674888900691600919293964682321223066352261853797970193220297491053179462531767520654219883596491058161646134922576), (2425872, 127986847428432036130922322746488039727765844713338307319914337671567809413022167236614317034291762538952181979186456109238786094542003920), (2428944, 88086651573586282922709143223994160911431355851169481506236714379933030038603162449333607562689478230833144393241928915120313695312742400), (2428992, 5184055067293910782114064937315077191025352035632575435968795069768220669470375742882809029045992940805915824678629691685688346573555200), (2441232, 3051969349064118065321370624904322353785622965452447755278922209304492238472409012058539908276690541763372408515919632919140560897868800), (2445312, 12554706206538807811908189306551442782367438380515313760599423706718740791540258596072650663258018167177349853917071352667428428976537600), (2457600, 22291627139694889528939423860840182595587086023819254088069784868840966756138819331625098884557086733460979362968640801850492382700928000), (3146001, -4502649608006589760248899648104528691297768257751908982611826327452299813744707268453604530092030317639110454982366018626702302839840880), (3146004, -9005299216013179520497799296209057382595536515503817965223652654904599627489414536907209060184060635278220909964732037253404605679681760), (3146016, -18010598432026359040995598592418114765191073031007635930447305309809199254978829073814418120368121270556441819929464074506809211359363520), (3146064, -9005299216013179520497799296209057382595536515503817965223652654904599627489414536907209060184060635278220909964732037253404605679681760), (3146769, -5910501371833808771148410766722033353337666131569989962048746584028853966629030543533381032206068146231434218315198325437848985378730720), (3146772, -11821002743667617542296821533444066706675332263139979924097493168057707933258061087066762064412136292462868436630396650875697970757461440), (3146784, -23642005487335235084593643066888133413350664526279959848194986336115415866516122174133524128824272584925736873260793301751395941514922880), (3146832, -11821002743667617542296821533444066706675332263139979924097493168057707933258061087066762064412136292462868436630396650875697970757461440), (3147024, 9005299216013179520497799296209057382595536515503817965223652654904599627489414536907209060184060635278220909964732037253404605679681760), (3147792, 11821002743667617542296821533444066706675332263139979924097493168057707933258061087066762064412136292462868436630396650875697970757461440), (3150096, 13507948824019769280746698944313586073893304773255726947835478982356899441234121805360813590276090952917331364947098055880106908519522640), (3150864, 17731504115501426313445232300166100060012998394709969886146239752086561899887091630600143096618204438694302654945594976313546956136192160), (3162129, -339107705451568673924596736100480261531735885050271972808769134367165804274712112450948878697410060195930267612879959213237840099763200), (3162132, -678215410903137347849193472200960523063471770100543945617538268734331608549424224901897757394820120391860535225759918426475680199526400), (3162144, -1356430821806274695698386944401921046126943540201087891235076537468663217098848449803795514789640240783721070451519836852951360399052800), (3162192, -678215410903137347849193472200960523063471770100543945617538268734331608549424224901897757394820120391860535225759918426475680199526400), (3162384, 18010598432026359040995598592418114765191073031007635930447305309809199254978829073814418120368121270556441819929464074506809211359363520), (3163152, 24320220898238372432442836539089093936414136296380503793812524604849747475065546399035421886219092705317597408486553220177871621714449280), (3166209, -1394967356282089756878687700727938086929715375612812640066602634079860087948917621785850073695335351908594428213007928074158714330726400), (3166212, -2789934712564179513757375401455876173859430751225625280133205268159720175897835243571700147390670703817188856426015856148317428661452800), (3166224, -4562546308773653005740960594610311563123653847300434641840103133217942938971534149790553658689111227046586910013391834656921337023616000), (3166272, -2789934712564179513757375401455876173859430751225625280133205268159720175897835243571700147390670703817188856426015856148317428661452800), (3167232, 2789934712564179513757375401455876173859430751225625280133205268159720175897835243571700147390670703817188856426015856148317428661452800), (3170304, 4184902068846269270636063102183814260789146126838437920199807902239580263846752865357550221086006055725783284639023784222476142992179200), (3178512, 1356430821806274695698386944401921046126943540201087891235076537468663217098848449803795514789640240783721070451519836852951360399052800), (3182592, 5579869425128359027514750802911752347718861502451250560266410536319440351795670487143400294781341407634377712852031712296634857322905600), (3211536, 20261923236029653921120048416470379110839957159883590421753218473535349161851182708041220385414136429375997047420647083820160362779283960), (3212304, 26597256173252139470167848450249150090019497592064954829219359628129842849830637445900214644927306658041453982418392464470320434204288240), (3227664, 1525984674532059032660685312452161176892811482726223877639461104652246119236204506029269954138345270881686204257959816459570280448934400), (3231744, 6277353103269403905954094653275721391183719190257656880299711853359370395770129298036325331629009083588674926958535676333714214488268800)]
theorem sparseBlock037_data : sparseBlock037 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (2215854612018609729570458003828522750095553372640466264013216515512944691910594190834595794339099676489496263698346973653907177596839040 : Int) coeff0392) (CoefficientMerge.scale (2442167464941700615516865447553329632179965535828618909975550850821283313693936382300478467146347717153814451391239017967657828920908592 : Int) coeff0393)) (CoefficientMerge.merge (CoefficientMerge.scale (1125662402001647440062224912026132172824442064437977245652956581863074953436176817113401132523007579409777613745591504656675575709960220 : Int) coeff0394) (CoefficientMerge.merge (CoefficientMerge.scale (158813956715343288915259477922093027711196752852599778729830644654930804799612646383116009264726949637935827847405023681839379807736089360 : Int) coeff0395) (CoefficientMerge.scale (1690394929582474443945349140469395727059644234806614670713037791610856310302107230365336759516063305728511647038539977900948919646361600 : Int) coeff0396)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (8682064449403954293292487365246875122065503063355784938665496037289937017776609331556092984557342742576855157171641193532953759569745080 : Int) coeff0397) (CoefficientMerge.scale (4155129726773764288365923658110541085984824973844910981193089911961562428520049574711882652468730512381626334130537287794341401451857080 : Int) coeff0398)) (CoefficientMerge.merge (CoefficientMerge.scale (1477625342958452192787102691680508338334416532892497490512186646007213491657257635883345258051517036557858554578799581359462246344682680 : Int) coeff0399) (CoefficientMerge.merge (CoefficientMerge.scale (80782632129657385455821386957683114213224416868044962826221348322065890725083845505848895424310227321320881315186829269637399517280632320 : Int) coeff0400) (CoefficientMerge.scale (2687160015203666031437973723522153156419865004420781698003755663359748663914462084077086645924098917137497843511188546584348131566933760 : Int) coeff0401))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (11194583074132251822043348140461084962304426443693772787052332506348851169514315156893921500110700000868777274907000604652006120608851200 : Int) coeff0402) (CoefficientMerge.scale (4893702865199237940150507956888564495079519769509415639235373021107390557700175691629644864593859901712952466291218273062239649739596800 : Int) coeff0403)) (CoefficientMerge.merge (CoefficientMerge.scale (3003314632650338376914576237965369317958818250510511907530337013609723734124164284319375731756735399850473253282188613521225851111449600 : Int) coeff0404) (CoefficientMerge.merge (CoefficientMerge.scale (480724909920896540951510673795811941718527507759427008592294675296521310563263037619596695613796850594565624103933977636252683035648000 : Int) coeff0405) (CoefficientMerge.scale (84776926362892168481149184025120065382933971262567993202192283591791451068678028112737219674352515048982566903219989803309460024940800 : Int) coeff0406)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (288003059294106154561892496517504288390297335312920857553821948320456703859465319049044946058110718933661990259923871760316019254086400 : Int) coeff0407) (CoefficientMerge.scale (44857314028164186205042866980014975216759597239113507965773161899335503816353979532524153356399772137599300948600072274051871240294400 : Int) coeff0408)) (CoefficientMerge.merge (CoefficientMerge.scale (348741839070522439219671925181984521732428843903203160016650658519965021987229405446462518423833837977148607053251982018539678582681600 : Int) coeff0409) (CoefficientMerge.merge (CoefficientMerge.scale (6651994996458760197015697350751577822457037525506191103964469138256269110071930365227936177222796067339813654631176999887661880397856000 : Int) coeff0410) (CoefficientMerge.scale (1238423729983049418274412436713343477532615890212180782670543603824498153118823296201394382475393707414498853498257822325027354594496000 : Int) coeff0411)))))) := by decide +kernel
theorem sparseBlock037_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock037 := by
  rw [sparseBlock037_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted0392_nonneg g t z hg hA hB ht hz hw) (weighted0393_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0394_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0395_nonneg g t z hg hA hB ht hz hw) (weighted0396_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0397_nonneg g t z hg hA hB ht hz hw) (weighted0398_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0399_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0400_nonneg g t z hg hA hB ht hz hw) (weighted0401_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted0402_nonneg g t z hg hA hB ht hz hw) (weighted0403_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0404_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0405_nonneg g t z hg hA hB ht hz hw) (weighted0406_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0407_nonneg g t z hg hA hB ht hz hw) (weighted0408_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0409_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0410_nonneg g t z hg hA hB ht hz hw) (weighted0411_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
