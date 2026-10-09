import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff0467 : CoefficientMerge.Poly :=
  [(2162690, -8), (2162693, -12), (2162705, -16), (2162753, -14), (2162945, -10), (2163713, -2), (2166785, 2), (2179073, 10), (2228225, 18)]
noncomputable def atom0467 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 0 * g 8) * z * z)
theorem atom0467_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0467 g t z = CoefficientMerge.eval (monomial g t z) coeff0467 := by
  norm_num [atom0467, coeff0467, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0467_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0467 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![2,2,1]
  dsimp only [atom0467]
  positivity
theorem weighted0467_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1292070222153917910114083689161259623179120489100600134971852062153442248515306265617431598387306801823587616058359215689262087872819200 : Int) coeff0467) := by
  rw [CoefficientMerge.eval_scale, ← atom0467_identity]
  exact mul_nonneg (by norm_num) (atom0467_nonneg g t z hg hA hB ht hz hw)

def coeff0468 : CoefficientMerge.Poly :=
  [(65538, -2592), (65541, -3888), (65553, -5184), (65601, -4536), (65793, -3240), (66561, -648), (69633, 648), (81921, 3240), (131073, 5832), (327682, 288), (327685, 432), (327697, 576), (327745, 504), (327937, 360), (328705, 72), (331777, -72), (344065, -360), (393217, -648), (589826, -8), (589829, -12), (589841, -16), (589889, -14), (590081, -10), (590849, -2), (593921, 2), (606209, 10), (655361, 18), (1114114, 288), (1114117, 432), (1114129, 576), (1114177, 504), (1114369, 360), (1115137, 72), (1118209, -72), (1130497, -360), (1179649, -648), (1376258, -16), (1376261, -24), (1376273, -32), (1376321, -28), (1376513, -20), (1377281, -4), (1380353, 4), (1392641, 20), (1441793, 36), (2162690, -8), (2162693, -12), (2162705, -16), (2162753, -14), (2162945, -10), (2163713, -2), (2166785, 2), (2179073, 10), (2228225, 18)]
noncomputable def atom0468 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 0 * g 8) * (t+z-18) * (t+z-18))
theorem atom0468_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0468 g t z = CoefficientMerge.eval (monomial g t z) coeff0468 := by
  norm_num [atom0468, coeff0468, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0468_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0468 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![2,2,1]
  dsimp only [atom0468]
  positivity
theorem weighted0468_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (569811673861522471126394479416314647618846102850519868728547851621252492359604154810362209430772258365885724831353793315370749237964800 : Int) coeff0468) := by
  rw [CoefficientMerge.eval_scale, ← atom0468_identity]
  exact mul_nonneg (by norm_num) (atom0468_nonneg g t z hg hA hB ht hz hw)

def coeff0469 : CoefficientMerge.Poly :=
  [(327682, -2592), (327685, -3888), (327697, -5184), (327745, -4536), (327937, -3240), (328705, -648), (331777, 648), (344065, 3240), (393217, 5832), (589826, 288), (589829, 432), (589841, 576), (589889, 504), (590081, 360), (590849, 72), (593921, -72), (606209, -360), (655361, -648), (851970, -8), (851973, -12), (851985, -16), (852033, -14), (852225, -10), (852993, -2), (856065, 2), (868353, 10), (917505, 18), (1376258, 288), (1376261, 432), (1376273, 576), (1376321, 504), (1376513, 360), (1377281, 72), (1380353, -72), (1392641, -360), (1441793, -648), (1638402, -16), (1638405, -24), (1638417, -32), (1638465, -28), (1638657, -20), (1639425, -4), (1642497, 4), (1654785, 20), (1703937, 36), (2424834, -8), (2424837, -12), (2424849, -16), (2424897, -14), (2425089, -10), (2425857, -2), (2428929, 2), (2441217, 10), (2490369, 18)]
noncomputable def atom0469 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 0 * g 8) * t * (t+z-18) * (t+z-18))
theorem atom0469_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0469 g t z = CoefficientMerge.eval (monomial g t z) coeff0469 := by
  norm_num [atom0469, coeff0469, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0469_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0469 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![2,2,1]
  dsimp only [atom0469]
  positivity
theorem weighted0469_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (228913615600784741652500579384623290640644841578716462657834691071025206040506528119354804646740468115779323144966268328060988198297600 : Int) coeff0469) := by
  rw [CoefficientMerge.eval_scale, ← atom0469_identity]
  exact mul_nonneg (by norm_num) (atom0469_nonneg g t z hg hA hB ht hz hw)

def coeff0470 : CoefficientMerge.Poly :=
  [(1114114, -2592), (1114117, -3888), (1114129, -5184), (1114177, -4536), (1114369, -3240), (1115137, -648), (1118209, 648), (1130497, 3240), (1179649, 5832), (1376258, 288), (1376261, 432), (1376273, 576), (1376321, 504), (1376513, 360), (1377281, 72), (1380353, -72), (1392641, -360), (1441793, -648), (1638402, -8), (1638405, -12), (1638417, -16), (1638465, -14), (1638657, -10), (1639425, -2), (1642497, 2), (1654785, 10), (1703937, 18), (2162690, 288), (2162693, 432), (2162705, 576), (2162753, 504), (2162945, 360), (2163713, 72), (2166785, -72), (2179073, -360), (2228225, -648), (2424834, -16), (2424837, -24), (2424849, -32), (2424897, -28), (2425089, -20), (2425857, -4), (2428929, 4), (2441217, 20), (2490369, 36), (3211266, -8), (3211269, -12), (3211281, -16), (3211329, -14), (3211521, -10), (3212289, -2), (3215361, 2), (3227649, 10), (3276801, 18)]
noncomputable def atom0470 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 0 * g 8) * z * (t+z-18) * (t+z-18))
theorem atom0470_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0470 g t z = CoefficientMerge.eval (monomial g t z) coeff0470 := by
  norm_num [atom0470, coeff0470, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0470_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0470 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![2,2,1]
  dsimp only [atom0470]
  positivity
theorem weighted0470_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (250824336499180416356972029850953601298955407828585713549155182463073629174765725450766797915909244605043964606047403454393807161548800 : Int) coeff0470) := by
  rw [CoefficientMerge.eval_scale, ← atom0470_identity]
  exact mul_nonneg (by norm_num) (atom0470_nonneg g t z hg hA hB ht hz hw)

def coeff0471 : CoefficientMerge.Poly :=
  [(524297, -8), (524300, -12), (524312, -16), (524360, -14), (524552, -10), (525320, -2), (528392, 2), (540680, 10), (589832, 18)]
noncomputable def atom0471 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 1 * g 1) * t * t)
theorem atom0471_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0471 g t z = CoefficientMerge.eval (monomial g t z) coeff0471 := by
  norm_num [atom0471, coeff0471, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0471_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0471 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![2,2,1]
  dsimp only [atom0471]
  positivity
theorem weighted0471_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (6418253448512294157738997117825821184805653910134272915022485074619414078394622716505142129404979185794749172991583027758551682605056000 : Int) coeff0471) := by
  rw [CoefficientMerge.eval_scale, ← atom0471_identity]
  exact mul_nonneg (by norm_num) (atom0471_nonneg g t z hg hA hB ht hz hw)

def coeff0472 : CoefficientMerge.Poly :=
  [(1310729, -8), (1310732, -12), (1310744, -16), (1310792, -14), (1310984, -10), (1311752, -2), (1314824, 2), (1327112, 10), (1376264, 18)]
noncomputable def atom0472 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 1 * g 1) * t * z)
theorem atom0472_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0472 g t z = CoefficientMerge.eval (monomial g t z) coeff0472 := by
  norm_num [atom0472, coeff0472, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0472_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0472 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![2,2,1]
  dsimp only [atom0472]
  positivity
theorem weighted0472_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (12836506897024588315477994235651642369611307820268545830044970149238828156789245433010284258809958371589498345983166055517103365210112000 : Int) coeff0472) := by
  rw [CoefficientMerge.eval_scale, ← atom0472_identity]
  exact mul_nonneg (by norm_num) (atom0472_nonneg g t z hg hA hB ht hz hw)

def coeff0473 : CoefficientMerge.Poly :=
  [(2097161, -8), (2097164, -12), (2097176, -16), (2097224, -14), (2097416, -10), (2098184, -2), (2101256, 2), (2113544, 10), (2162696, 18)]
noncomputable def atom0473 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 1 * g 1) * z * z)
theorem atom0473_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0473 g t z = CoefficientMerge.eval (monomial g t z) coeff0473 := by
  norm_num [atom0473, coeff0473, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0473_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0473 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![2,2,1]
  dsimp only [atom0473]
  positivity
theorem weighted0473_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (6418253448512294157738997117825821184805653910134272915022485074619414078394622716505142129404979185794749172991583027758551682605056000 : Int) coeff0473) := by
  rw [CoefficientMerge.eval_scale, ← atom0473_identity]
  exact mul_nonneg (by norm_num) (atom0473_nonneg g t z hg hA hB ht hz hw)

def coeff0474 : CoefficientMerge.Poly :=
  [(524309, -8), (524312, -12), (524324, -16), (524372, -14), (524564, -10), (525332, -2), (528404, 2), (540692, 10), (589844, 18)]
noncomputable def atom0474 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 1 * g 2) * t * t)
theorem atom0474_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0474 g t z = CoefficientMerge.eval (monomial g t z) coeff0474 := by
  norm_num [atom0474, coeff0474, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0474_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0474 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![2,2,1]
  dsimp only [atom0474]
  positivity
theorem weighted0474_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (43229630087691784513942468388260035399405951567288408770099937631326177266108020159032954626083393622348223501414047103133642920540748800 : Int) coeff0474) := by
  rw [CoefficientMerge.eval_scale, ← atom0474_identity]
  exact mul_nonneg (by norm_num) (atom0474_nonneg g t z hg hA hB ht hz hw)

def coeff0475 : CoefficientMerge.Poly :=
  [(1310741, -8), (1310744, -12), (1310756, -16), (1310804, -14), (1310996, -10), (1311764, -2), (1314836, 2), (1327124, 10), (1376276, 18)]
noncomputable def atom0475 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 1 * g 2) * t * z)
theorem atom0475_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0475 g t z = CoefficientMerge.eval (monomial g t z) coeff0475 := by
  norm_num [atom0475, coeff0475, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0475_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0475 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![2,2,1]
  dsimp only [atom0475]
  positivity
theorem weighted0475_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (72628484912721898790622796709484450121375496950721751890454245478631890405491867492447451907109349826194225121470172553440135006939399680 : Int) coeff0475) := by
  rw [CoefficientMerge.eval_scale, ← atom0475_identity]
  exact mul_nonneg (by norm_num) (atom0475_nonneg g t z hg hA hB ht hz hw)

def coeff0476 : CoefficientMerge.Poly :=
  [(3149829, -8), (3149832, -12), (3149844, -16), (3149892, -14), (3150084, -10), (3150852, -2), (3153924, 2), (3166212, 10), (3215364, 18)]
noncomputable def atom0476 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 1 * g 6) * z * z * z)
theorem atom0476_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0476 g t z = CoefficientMerge.eval (monomial g t z) coeff0476 := by
  norm_num [atom0476, coeff0476, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0476_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0476 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![2,2,1]
  dsimp only [atom0476]
  positivity
theorem weighted0476_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (126391773209133864960201860036778854384655847937244214609029618917834320745396782022847541465533468771033569571492771175136544215654400 : Int) coeff0476) := by
  rw [CoefficientMerge.eval_scale, ← atom0476_identity]
  exact mul_nonneg (by norm_num) (atom0476_nonneg g t z hg hA hB ht hz hw)

def coeff0477 : CoefficientMerge.Poly :=
  [(540677, -8), (540680, -12), (540692, -16), (540740, -14), (540932, -10), (541700, -2), (544772, 2), (557060, 10), (606212, 18)]
noncomputable def atom0477 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 1 * g 7) * t * t)
theorem atom0477_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0477 g t z = CoefficientMerge.eval (monomial g t z) coeff0477 := by
  norm_num [atom0477, coeff0477, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0477_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0477 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![2,2,1]
  dsimp only [atom0477]
  positivity
theorem weighted0477_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5877497946772996628279913638759822960082025710838393597795867189003260302006371587264916105615805300374727637126505664375038786090905600 : Int) coeff0477) := by
  rw [CoefficientMerge.eval_scale, ← atom0477_identity]
  exact mul_nonneg (by norm_num) (atom0477_nonneg g t z hg hA hB ht hz hw)

def coeff0478 : CoefficientMerge.Poly :=
  [(1327109, -8), (1327112, -12), (1327124, -16), (1327172, -14), (1327364, -10), (1328132, -2), (1331204, 2), (1343492, 10), (1392644, 18)]
noncomputable def atom0478 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 1 * g 7) * t * z)
theorem atom0478_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0478 g t z = CoefficientMerge.eval (monomial g t z) coeff0478 := by
  norm_num [atom0478, coeff0478, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0478_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0478 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![2,2,1]
  dsimp only [atom0478]
  positivity
theorem weighted0478_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (9275257876703375955920908847679133863828513171914628339500582538880996343930513635151659254628301804999956015287292151503700769414144000 : Int) coeff0478) := by
  rw [CoefficientMerge.eval_scale, ← atom0478_identity]
  exact mul_nonneg (by norm_num) (atom0478_nonneg g t z hg hA hB ht hz hw)

def coeff0479 : CoefficientMerge.Poly :=
  [(2113541, -8), (2113544, -12), (2113556, -16), (2113604, -14), (2113796, -10), (2114564, -2), (2117636, 2), (2129924, 10), (2179076, 18)]
noncomputable def atom0479 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 1 * g 7) * z * z)
theorem atom0479_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0479 g t z = CoefficientMerge.eval (monomial g t z) coeff0479 := by
  norm_num [atom0479, coeff0479, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0479_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0479 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![2,2,1]
  dsimp only [atom0479]
  positivity
theorem weighted0479_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5363774226061067938937552367837899887211333488130285967336861838698951879315888352579565392302577574471724038238485568162269674964889600 : Int) coeff0479) := by
  rw [CoefficientMerge.eval_scale, ← atom0479_identity]
  exact mul_nonneg (by norm_num) (atom0479_nonneg g t z hg hA hB ht hz hw)

def coeff0480 : CoefficientMerge.Poly :=
  [(1589253, -8), (1589256, -12), (1589268, -16), (1589316, -14), (1589508, -10), (1590276, -2), (1593348, 2), (1605636, 10), (1654788, 18)]
noncomputable def atom0480 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 1 * g 7) * t * t * z)
theorem atom0480_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0480 g t z = CoefficientMerge.eval (monomial g t z) coeff0480 := by
  norm_num [atom0480, coeff0480, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0480_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0480 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![2,2,1]
  dsimp only [atom0480]
  positivity
theorem weighted0480_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (497519043908116223030947588794920570197678367326063654676817434603753163330162294109258655260475619451447924717492847316468478672588800 : Int) coeff0480) := by
  rw [CoefficientMerge.eval_scale, ← atom0480_identity]
  exact mul_nonneg (by norm_num) (atom0480_nonneg g t z hg hA hB ht hz hw)

def coeff0481 : CoefficientMerge.Poly :=
  [(2375685, -8), (2375688, -12), (2375700, -16), (2375748, -14), (2375940, -10), (2376708, -2), (2379780, 2), (2392068, 10), (2441220, 18)]
noncomputable def atom0481 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 1 * g 7) * t * z * z)
theorem atom0481_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0481 g t z = CoefficientMerge.eval (monomial g t z) coeff0481 := by
  norm_num [atom0481, coeff0481, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0481_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0481 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![2,2,1]
  dsimp only [atom0481]
  positivity
theorem weighted0481_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (391652468708672336190693507775385648780394267925000238579392029218572220259192333565747833862106662086936614922670520981647656534087000 : Int) coeff0481) := by
  rw [CoefficientMerge.eval_scale, ← atom0481_identity]
  exact mul_nonneg (by norm_num) (atom0481_nonneg g t z hg hA hB ht hz hw)

def coeff0482 : CoefficientMerge.Poly :=
  [(589829, -8), (589832, -12), (589844, -16), (589892, -14), (590084, -10), (590852, -2), (593924, 2), (606212, 10), (655364, 18)]
noncomputable def atom0482 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 1 * g 8) * t * t)
theorem atom0482_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0482 g t z = CoefficientMerge.eval (monomial g t z) coeff0482 := by
  norm_num [atom0482, coeff0482, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0482_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0482 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![2,2,1]
  dsimp only [atom0482]
  positivity
theorem weighted0482_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (14769276401406131442524396776815099885490283145479434832864241222845810805396717046503310013687594149129962585577222308194394496903680000 : Int) coeff0482) := by
  rw [CoefficientMerge.eval_scale, ← atom0482_identity]
  exact mul_nonneg (by norm_num) (atom0482_nonneg g t z hg hA hB ht hz hw)

def coeff0483 : CoefficientMerge.Poly :=
  [(1376261, -8), (1376264, -12), (1376276, -16), (1376324, -14), (1376516, -10), (1377284, -2), (1380356, 2), (1392644, 10), (1441796, 18)]
noncomputable def atom0483 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 1 * g 8) * t * z)
theorem atom0483_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0483 g t z = CoefficientMerge.eval (monomial g t z) coeff0483 := by
  norm_num [atom0483, coeff0483, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0483_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0483 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![2,2,1]
  dsimp only [atom0483]
  positivity
theorem weighted0483_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (27041955355666968357646117669821194371277944202843318744004776159899186544431127314260880192943997022304436742241470455724220895066216960 : Int) coeff0483) := by
  rw [CoefficientMerge.eval_scale, ← atom0483_identity]
  exact mul_nonneg (by norm_num) (atom0483_nonneg g t z hg hA hB ht hz hw)

def coeff0484 : CoefficientMerge.Poly :=
  [(2162693, -8), (2162696, -12), (2162708, -16), (2162756, -14), (2162948, -10), (2163716, -2), (2166788, 2), (2179076, 10), (2228228, 18)]
noncomputable def atom0484 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 1 * g 8) * z * z)
theorem atom0484_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0484 g t z = CoefficientMerge.eval (monomial g t z) coeff0484 := by
  norm_num [atom0484, coeff0484, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0484_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0484 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![2,2,1]
  dsimp only [atom0484]
  positivity
theorem weighted0484_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (14407572588966499653291763100508462052881444867214482494181333983192044584879902834663844717911893480741620927740232142559681787521310720 : Int) coeff0484) := by
  rw [CoefficientMerge.eval_scale, ← atom0484_identity]
  exact mul_nonneg (by norm_num) (atom0484_nonneg g t z hg hA hB ht hz hw)

def coeff0485 : CoefficientMerge.Poly :=
  [(1638405, -8), (1638408, -12), (1638420, -16), (1638468, -14), (1638660, -10), (1639428, -2), (1642500, 2), (1654788, 10), (1703940, 18)]
noncomputable def atom0485 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 1 * g 8) * t * t * z)
theorem atom0485_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0485 g t z = CoefficientMerge.eval (monomial g t z) coeff0485 := by
  norm_num [atom0485, coeff0485, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0485_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0485 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![2,2,1]
  dsimp only [atom0485]
  positivity
theorem weighted0485_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (109223016451704922849808731051032721303602557058558401424008138267845324299541461371823457960560059435916425559872171168533760646758400 : Int) coeff0485) := by
  rw [CoefficientMerge.eval_scale, ← atom0485_identity]
  exact mul_nonneg (by norm_num) (atom0485_nonneg g t z hg hA hB ht hz hw)

def coeff0486 : CoefficientMerge.Poly :=
  [(2424837, -8), (2424840, -12), (2424852, -16), (2424900, -14), (2425092, -10), (2425860, -2), (2428932, 2), (2441220, 10), (2490372, 18)]
noncomputable def atom0486 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 1 * g 8) * t * z * z)
theorem atom0486_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0486 g t z = CoefficientMerge.eval (monomial g t z) coeff0486 := by
  norm_num [atom0486, coeff0486, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0486_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0486 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![2,2,1]
  dsimp only [atom0486]
  positivity
theorem weighted0486_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (109223016451704922849808731051032721303602557058558401424008138267845324299541461371823457960560059435916425559872171168533760646758400 : Int) coeff0486) := by
  rw [CoefficientMerge.eval_scale, ← atom0486_identity]
  exact mul_nonneg (by norm_num) (atom0486_nonneg g t z hg hA hB ht hz hw)

def sparseBlock043 : CoefficientMerge.Poly :=
  [(65538, -1476951858649066245159614490647087566628049098588547499744396031402286460196093969268458846844561693684375798762869032273440982024804761600), (65541, -2215427787973599367739421735970631349942073647882821249616594047103429690294140953902688270266842540526563698144303548410161473037207142400), (65553, -2953903717298132490319228981294175133256098197177094999488792062804572920392187938536917693689123387368751597525738064546881964049609523200), (65601, -2584665752635865929029325358632403241599085922529958124552693054954001305343164446219802981977982963947657647835020806478521718543408332800), (65793, -1846189823311332806449518113308859458285061373235684374680495039252858075245117461585573558555702117105469748453586290341801227531005952000), (66561, -369237964662266561289903622661771891657012274647136874936099007850571615049023492317114711711140423421093949690717258068360245506201190400), (69633, 369237964662266561289903622661771891657012274647136874936099007850571615049023492317114711711140423421093949690717258068360245506201190400), (81921, 1846189823311332806449518113308859458285061373235684374680495039252858075245117461585573558555702117105469748453586290341801227531005952000), (131073, 3323141681960399051609132603955947024913110471824231874424891070655144535441211430854032405400263810789845547216455322615242209555810713600), (327682, -429238329565115578678879891693044950826323751751083349015285737989176616257426924299983337328288882946724916840322675031507305629453516800), (327685, -643857494347673368018319837539567426239485627626625023522928606983764924386140386449975005992433324420087375260484012547260958444180275200), (327697, -858476659130231157357759783386089901652647503502166698030571475978353232514853848599966674656577765893449833680645350063014611258907033600), (327745, -751167076738952262688039810462828663946066565564395860776750041481059078450497117524970840324505545156768604470564681305137784851543654400), (327937, -536547911956394473348599864616306188532904689688854186269107172486470770321783655374979171660361103683406146050403343789384132036816896000), (328705, -107309582391278894669719972923261237706580937937770837253821434497294154064356731074995834332072220736681229210080668757876826407363379200), (331777, 107309582391278894669719972923261237706580937937770837253821434497294154064356731074995834332072220736681229210080668757876826407363379200), (344065, 536547911956394473348599864616306188532904689688854186269107172486470770321783655374979171660361103683406146050403343789384132036816896000), (393217, 965786241521510052027479756309351139359228441439937535284392910475647386579210579674962508988649986630131062890726018820891437666270412800), (524297, -51346027588098353261911976942606569478445231281074183320179880596955312627156981732041137035239833486357993383932664222068413460840448000), (524300, -77019041382147529892867965413909854217667846921611274980269820895432968940735472598061705552859750229536990075898996333102620191260672000), (524309, -345837040701534276111539747106080283195247612538307270160799501050609418128864161272263637008667148978785788011312376825069143364325990400), (524312, -621447616228498120691133574544333563749761881369609271881559012769824752447610205372477729583480390440894668784833893681740541968169881600), (524324, -691674081403068552223079494212160566390495225076614540321599002101218836257728322544527274017334297957571576022624753650138286728651980800), (524360, -89855548279172118208345959649561496587279154741879820810314791044671797097524718031071989811669708601126488421882162388619723556470784000), (524372, -605214821227684983195194557435640495591683321942037722781399126838566481725512282226461364765167510712875129019796659443871000887570483200), (524552, -64182534485122941577389971178258211848056539101342729150224850746194140783946227165051421294049791857947491729915830277585516826050560000), (524564, -432296300876917845139424683882600353994059515672884087700999376313261772661080201590329546260833936223482235014140471031336429205407488000), (525320, -12836506897024588315477994235651642369611307820268545830044970149238828156789245433010284258809958371589498345983166055517103365210112000), (525332, -86459260175383569027884936776520070798811903134576817540199875262652354532216040318065909252166787244696447002828094206267285841081497600), (528392, 12836506897024588315477994235651642369611307820268545830044970149238828156789245433010284258809958371589498345983166055517103365210112000), (528404, 86459260175383569027884936776520070798811903134576817540199875262652354532216040318065909252166787244696447002828094206267285841081497600), (540677, -47019983574183973026239309110078583680656205686707148782366937512026082416050972698119328844926442402997821097012045315000310288727244800), (540680, -6347440876153017961968992486859663672927769428717994023325555521844982840130231882127571973339871746549239915602237694914948607040307200), (540692, 338256333728549899086946065662443186632747104299469790136265501289209607828978256194090888570981051417486592820116380401335808627952998400), (540740, -82284971254821952795918790942637521441148359951737510369142140646045644228089202221708825478621274205246186919771079301250543005272678400), (540932, -58774979467729966282799136387598229600820257108383935977958671890032603020063715872649161056158053003747276371265056643750387860909056000), (541700, -11754995893545993256559827277519645920164051421676787195591734378006520604012743174529832211231610600749455274253011328750077572181811200), (544772, 11754995893545993256559827277519645920164051421676787195591734378006520604012743174529832211231610600749455274253011328750077572181811200), (557060, 58774979467729966282799136387598229600820257108383935977958671890032603020063715872649161056158053003747276371265056643750387860909056000), (589826, 61368627902133825826909011027440990523554945551866182295628008215485239400789046859891286062815076750417359267099454931958598607205990400), (589829, -26101269358048312799831657673359313298589846836036205219471917459538627341990166082189551015278138067413661783968596067617258064420454400), (589832, -61702754743652282470990813200916417299381627363336305523966163331000276253657395660947161834961504445254065913078173198678803675953152000), (589841, 122737255804267651653818022054881981047109891103732364591256016430970478801578093719782572125630153500834718534198909863917197214411980800), (589844, 541824919155954018170574082559639039021462597883520400535971017798338217903596890118540223050499578816188621656217290925295260619274598400), (589889, 107395098828734195197090769298021733416221154715765819017349014377099168951380832004809750609926384313230378717424046130927547562610483200), (589892, -206769869619685840195341554875411398396863964036712087660099377119841351275554038651046340191626318087819476198081112314721522956651520000), (590081, 76710784877667282283636263784301238154443681939832727869535010269356549250986308574864107578518845938021699083874318664948248259007488000), (590084, -147692764014061314425243967768150998854902831454794348328642412228458108053967170465033100136875941491299625855772223081943944969036800000), (590849, 15342156975533456456727252756860247630888736387966545573907002053871309850197261714972821515703769187604339816774863732989649651801497600), (590852, -29538552802812262885048793553630199770980566290958869665728482445691621610793434093006620027375188298259925171154444616388788993807360000), (593921, -15342156975533456456727252756860247630888736387966545573907002053871309850197261714972821515703769187604339816774863732989649651801497600), (593924, 29538552802812262885048793553630199770980566290958869665728482445691621610793434093006620027375188298259925171154444616388788993807360000), (606209, -76710784877667282283636263784301238154443681939832727869535010269356549250986308574864107578518845938021699083874318664948248259007488000), (606212, 253487727055975253734282413265827812136379294249885433088968021630516793490081859035801590037960436898044723324049325040694643118673100800), (655361, -138079412779801108110545274811742228677998627491698910165163018484841788651775355434755393641333922688439058350973773596906846866213478400), (655364, 265846975225310365965439141982671797938825096618629826991556342011224594497140906837059580246376694684339326540390001547499100944266240000), (851970, -1831308924806277933220004635076986325125158732629731701262677528568201648324052224954838437173923744926234585159730146624487905586380800), (851973, -2746963387209416899830006952615479487687738098944597551894016292852302472486078337432257655760885617389351877739595219936731858379571200), (851985, -3662617849612555866440009270153972650250317465259463402525355057136403296648104449909676874347847489852469170319460293248975811172761600), (852033, -3204790618410986383135008111384726068969027782102030477209685674994352884567091393670967265054366553620910524029527756592853834776166400), (852225, -2289136156007847416525005793846232906406448415787164626578346910710252060405065281193548046467404681157793231449662683280609881982976000), (852993, -457827231201569483305001158769246581281289683157432925315669382142050412081013056238709609293480936231558646289932536656121976396595200), (856065, 457827231201569483305001158769246581281289683157432925315669382142050412081013056238709609293480936231558646289932536656121976396595200), (868353, 2289136156007847416525005793846232906406448415787164626578346910710252060405065281193548046467404681157793231449662683280609881982976000), (917505, 4120445080814125349745010428923219231531607148416896327841024439278453708729117506148386483641328426084027816609392829905097787569356800), (1114114, -486030918133757167512869891301773116052664739470744447325588451677366129021426763783003223881974351606898867507444977278961972382200627200), (1114117, -729046377200635751269304836952659674078997109206116670988382677516049193532140145674504835822961527410348301261167465918442958573300940800), (1114129, -972061836267514335025739782603546232105329478941488894651176903354732258042853527566006447763948703213797735014889954557923944764401254400), (1114177, -850554106734075043147522309778102953092163294073802782819779790435390725787496836620255641793455115312073018138028710238183451668851097600), (1114369, -607538647667196459391087364127216395065830924338430559156985564596707661276783454728754029852467939508623584384306221598702465477750784000), (1115137, -121507729533439291878217472825443279013166184867686111831397112919341532255356690945750805970493587901724716876861244319740493095550156800), (1118209, 121507729533439291878217472825443279013166184867686111831397112919341532255356690945750805970493587901724716876861244319740493095550156800), (1130497, 607538647667196459391087364127216395065830924338430559156985564596707661276783454728754029852467939508623584384306221598702465477750784000), (1179649, 1093569565800953626903957255428989511118495663809175006482574016274073790298210218511757253734442291115522451891751198877664437859951411200), (1310729, -102692055176196706523823953885213138956890462562148366640359761193910625254313963464082274070479666972715986767865328444136826921680896000), (1310732, -154038082764295059785735930827819708435335693843222549960539641790865937881470945196123411105719500459073980151797992666205240382521344000), (1310741, -581027879301775190324982373675875600971003975605774015123633963829055123243934939939579615256874798609553800971761380427521080055515197440), (1310744, -1076925929305056198535121468284239679370286888532957755966170468131403935374530336837533971026271531859762674993372727529555273926634588160), (1310756, -1162055758603550380649964747351751201942007951211548030247267927658110246487869879879159230513749597219107601943522760855042160111030394880), (1310792, -179711096558344236416691919299122993174558309483759641620629582089343594195049436062143979623339417202252976843764324777239447112941568000), (1310804, -1016798788778106583068719153932782301699256957310104526466359436700846465676886144894264326699530897566719151700582415748161890097151595520), (1310984, -128365068970245883154779942356516423696113078202685458300449701492388281567892454330102842588099583715894983459831660555171033652101120000), (1310996, -726284849127218987906227967094844501213754969507217518904542454786318904054918674924474519071093498261942251214701725534401350069393996800), (1311752, -25673013794049176630955988471303284739222615640537091660089940298477656313578490866020568517619916743178996691966332111034206730420224000), (1311764, -145256969825443797581245593418968900242750993901443503780908490957263780810983734984894903814218699652388450242940345106880270013878799360), (1314824, 25673013794049176630955988471303284739222615640537091660089940298477656313578490866020568517619916743178996691966332111034206730420224000), (1314836, 145256969825443797581245593418968900242750993901443503780908490957263780810983734984894903814218699652388450242940345106880270013878799360), (1327109, -74202063013627007647367270781433070910628105375317026716004660311047970751444109081213274037026414439999648122298337212029606155313152000), (1327112, 17061974449805371683729036184366817330170920139709918226442711025816325440726290708282931532559962055895511276384154737126624419131392000), (1327124, 577880723099964972611493425531978359392498758756583465472533134164222962552030456762047970997040669381942954970105051110342137758767692800), (1327172, -129853610273847263382892723867507874093599184406804796753008155544333948815027190892123229564796225269999384214022090121051810771798016000), (1327364, -92752578767033759559209088476791338638285131719146283395005825388809963439305136351516592546283018049999560152872921515037007694141440000), (1328132, -18550515753406751911841817695358267727657026343829256679001165077761992687861027270303318509256603609999912030574584303007401538828288000), (1331204, 18550515753406751911841817695358267727657026343829256679001165077761992687861027270303318509256603609999912030574584303007401538828288000), (1343492, 92752578767033759559209088476791338638285131719146283395005825388809963439305136351516592546283018049999560152872921515037007694141440000), (1376258, 129047543423005605968705799789185110516703334183694708847956317951880424664244742551229226187150761129742935274990276780301049075828326400), (1376261, -22764327710827337908110241674791889195168552347204486680103732351372855359081904687243202262825834483821091025446348475342193546787246080), (1376264, -93446340121561030613149515796124769802331789669285999987247851232491331710967109976945445656748713579042270679200656469382790167012587520), (1376273, 258095086846011211937411599578370221033406668367389417695912635903760849328489485102458452374301522259485870549980553560602098151656652800), (1376276, 874641442738322684508872458053580992244311837867498434124100000056987042587955577835880051240864344514625064310599578670334895803849722880), (1376321, 225833200990259810445235149631073943404230834821465740483923556415790743162428299464651145827513831977050136731232984365526835882699571200), (1376324, -378587374979337557007045647377496721197891218839806462416066866238588611622035782399652322701215958312262114391380586380139092530927037440), (1376513, 161309429278757007460882249736481388145879167729618386059945397439850530830305928189036532733938451412178669093737845975376311344785408000), (1376516, -270419553556669683576461176698211943712779442028433187440047761598991865444311273142608801929439970223044367422414704557242208950662169600), (1377281, 32261885855751401492176449947296277629175833545923677211989079487970106166061185637807306546787690282435733818747569195075262268957081600), (1377284, -54083910711333936715292235339642388742555888405686637488009552319798373088862254628521760385887994044608873484482940911448441790132433920), (1380353, -32261885855751401492176449947296277629175833545923677211989079487970106166061185637807306546787690282435733818747569195075262268957081600), (1380356, 54083910711333936715292235339642388742555888405686637488009552319798373088862254628521760385887994044608873484482940911448441790132433920), (1392641, -161309429278757007460882249736481388145879167729618386059945397439850530830305928189036532733938451412178669093737845975376311344785408000), (1392644, 437374195337330450783037535956436353261692679122896497551058247298849799635060518575338668512749402713043575697585963284308822800116761600), (1441793, -290356972701762613429588049525666498662582501913313094907901715391730955494550670740265758921089212541921604368728122755677360420613734400), (1441796, 486755196402005430437630118056781498683002995651179737392085970878185357799760291656695843472991946401479861360346468203035976111191905280), (1589253, -3980152351264929784247580710359364561581426938608509237414539476830025306641298352874069242083804955611583397739942778531747829380710400), (1589256, -5970228526897394676371371065539046842372140407912763856121809215245037959961947529311103863125707433417375096609914167797621744071065600), (1589268, -7960304702529859568495161420718729123162853877217018474829078953660050613282596705748138484167609911223166795479885557063495658761420800), (1589316, -6965266614713627122433266243128887982767497142564891165475444084452544286622272117529621173646658672320270946044899862430558701416243200), (1589508, -4975190439081162230309475887949205701976783673260636546768174346037531633301622941092586552604756194514479247174928473164684786725888000), (1590276, -995038087816232446061895177589841140395356734652127309353634869207506326660324588218517310520951238902895849434985694632936957345177600), (1593348, 995038087816232446061895177589841140395356734652127309353634869207506326660324588218517310520951238902895849434985694632936957345177600), (1605636, 4975190439081162230309475887949205701976783673260636546768174346037531633301622941092586552604756194514479247174928473164684786725888000), (1638402, -5669212541605999197295785508961601460641960727888149110918596516840992330046230253515811257675121446692820887167839520884126268465152000), (1638405, -9377602944022638178742148111850663961391761548300690877769959881404251089465677071248304550197162645526562735230736650674459487871795200), (1638408, -1310676197420459074197704772612392655643230684702700817088097659214143891594497536461881495526720713230997106718466054022405127761100800), (1638417, -11338425083211998394591571017923202921283921455776298221837193033681984660092460507031622515350242893385641774335679041768252536930304000), (1638420, -1747568263227278765596939696816523540857640912936934422784130212285525188792663381949175327368960950974662808957954738696540170348134400), (1638465, -9921121947810498595267624640682802556123431273804260944107543904471736577580902943652669700931462531712436552543719161547220969814016000), (1638468, -1529122230323868919897322234714458098250435798819817619936113935749834540193580459205528411447840832102829957838210396359472649054617600), (1638657, -7086515677007498996619731886202001825802450909860186388648245646051240412557787816894764072093901808366026108959799401105157835581440000), (1638660, -1092230164517049228498087310510327213036025570585584014240081382678453242995414613718234579605600594359164255598721711685337606467584000), (1639425, -1417303135401499799323946377240400365160490181972037277729649129210248082511557563378952814418780361673205221791959880221031567116288000), (1639428, -218446032903409845699617462102065442607205114117116802848016276535690648599082922743646915921120118871832851119744342337067521293516800), (1642497, 1417303135401499799323946377240400365160490181972037277729649129210248082511557563378952814418780361673205221791959880221031567116288000), (1642500, 218446032903409845699617462102065442607205114117116802848016276535690648599082922743646915921120118871832851119744342337067521293516800), (1654785, 7086515677007498996619731886202001825802450909860186388648245646051240412557787816894764072093901808366026108959799401105157835581440000), (1654788, 10047572954863141243055143908818897476594236182454729798422795205546010182938335907684890374294161744485226900513592963381770222574182400), (1703937, 12755728218613498193915517395163603286444411637748335499566842162892232742604018070410575329769023255058846996127638921989284104046592000), (1703940, 1966014296130688611296557158918588983464846027054051225632146488821215837391746304692822243290081069846495660077699081033607691641651200), (2097161, -51346027588098353261911976942606569478445231281074183320179880596955312627156981732041137035239833486357993383932664222068413460840448000), (2097164, -77019041382147529892867965413909854217667846921611274980269820895432968940735472598061705552859750229536990075898996333102620191260672000), (2097176, -102692055176196706523823953885213138956890462562148366640359761193910625254313963464082274070479666972715986767865328444136826921680896000), (2097224, -89855548279172118208345959649561496587279154741879820810314791044671797097524718031071989811669708601126488421882162388619723556470784000), (2097416, -64182534485122941577389971178258211848056539101342729150224850746194140783946227165051421294049791857947491729915830277585516826050560000), (2098184, -12836506897024588315477994235651642369611307820268545830044970149238828156789245433010284258809958371589498345983166055517103365210112000), (2101256, 12836506897024588315477994235651642369611307820268545830044970149238828156789245433010284258809958371589498345983166055517103365210112000), (2113541, -42910193808488543511500418942703199097690667905042287738694894709591615034527106820636523138420620595773792305907884545298157399719116800), (2113544, -182756227609873689860657235796586798479462756220702457817491318193281767844433065903363413581139035713196728945996540361719273528115200), (2113556, -85820387616977087023000837885406398195381335810084575477389789419183230069054213641273046276841241191547584611815769090596314799438233600), (2113604, -75092839164854951145125733149730598420958668833824003542716065741785326310422436936113915492236086042604136535338797954271775449508454400), (2113796, -53637742260610679389375523678378998872113334881302859673368618386989518793158883525795653923025775744717240382384855681622696749648896000), (2114564, -10727548452122135877875104735675799774422666976260571934673723677397903758631776705159130784605155148943448076476971136324539349929779200), (2117636, 10727548452122135877875104735675799774422666976260571934673723677397903758631776705159130784605155148943448076476971136324539349929779200), (2129924, 53637742260610679389375523678378998872113334881302859673368618386989518793158883525795653923025775744717240382384855681622696749648896000), (2162690, 57342353743640436860884119248454043007715424719023725472553493239167647275333245566398487337237229964736875079423948122828353765639782400), (2162693, -29247050096271341935007925931386631911478421859180271744620432006784885766039354327713026737439302898827654802785934956234923651710812160), (2162696, -57362308994376701000199209085236763308075568024156877459771276455155081607455625118873578285653096424593966019034291211062251163364720640), (2162705, 114684707487280873721768238496908086015430849438047450945106986478335294550666491132796974674474459929473750158847896245656707531279564800), (2162708, -230521161423463994452668209608135392846103117875431719906901343731072713358078445354621515486590295691865934843843714280954908600340971520), (2162753, 100349119051370764506547208684794575263501993258291519576968613168543382731833179741197352840165152438289531388991909214949619089869619200), (2162756, -201706016245530995146084683407118468740340228141002754918538675764688624188318639685293826050766508730382692988363249995835545025298350080), (2162945, 71677942179550546076105149060567553759644280898779656840691866548959559094166556957998109171546537455921093849279935153535442207049728000), (2162948, -144075725889664996532917631005084620528814448672144824941813339831920445848799028346638447179118934807416209277402321425596817875213107200), (2163713, 14335588435910109215221029812113510751928856179755931368138373309791911818833311391599621834309307491184218769855987030707088441409945600), (2163716, -28815145177932999306583526201016924105762889734428964988362667966384089169759805669327689435823786961483241855480464285119363575042621440), (2166785, -14335588435910109215221029812113510751928856179755931368138373309791911818833311391599621834309307491184218769855987030707088441409945600), (2166788, 28815145177932999306583526201016924105762889734428964988362667966384089169759805669327689435823786961483241855480464285119363575042621440), (2179073, -71677942179550546076105149060567553759644280898779656840691866548959559094166556957998109171546537455921093849279935153535442207049728000), (2179076, 240623661958764219433793573626166818498618451458489972353876852928501579676485018693070624240565331147907241965695061652517672024581120000), (2228225, -129020295923190982936989268309021596767359705617803382313245359788127206369499802524396596508783767420657968928703883276363795972689510400), (2228228, 259336306601396993759251735809152316951866007609860684895264011697456802527838251023949204922414082653349176699324178566074272175383592960), (2375685, -3133219749669378689525548062203085190243154143400001908635136233748577762073538668525982670896853296695492919381364167853181252272696000), (2375688, -4699829624504068034288322093304627785364731215100002862952704350622866643110308002788974006345279945043239379072046251779771878409044000), (2375700, -6266439499338757379051096124406170380486308286800003817270272467497155524147077337051965341793706593390985838762728335706362504545392000), (2375748, -5483134561921412706669709108855399082925519750950003340111488409060011083628692669920469674069493269217112608917387293743067191477218000), (2375940, -3916524687086723361906935077753856487803942679250002385793920292185722202591923335657478338621066620869366149226705209816476565340870000), (2376708, -783304937417344672381387015550771297560788535850000477158784058437144440518384667131495667724213324173873229845341041963295313068174000), (2379780, 783304937417344672381387015550771297560788535850000477158784058437144440518384667131495667724213324173873229845341041963295313068174000), (2392068, 3916524687086723361906935077753856487803942679250002385793920292185722202591923335657478338621066620869366149226705209816476565340870000), (2424834, -5844498308793164594931557112692243945908445257887103118049160447977379715120303832167107203828471658606938018856488601894788820171161600), (2424837, -9640531594803386275195805517446627689291488343299121888465805778108832167076787439225248469427187963397738432763710272190453315430809600), (2424840, -1310676197420459074197704772612392655643230684702700817088097659214143891594497536461881495526720713230997106718466054022405127761100800), (2424849, -11688996617586329189863114225384487891816890515774206236098320895954759430240607664334214407656943317213876037712977203789577640342323200), (2424852, -1747568263227278765596939696816523540857640912936934422784130212285525188792663381949175327368960950974662808957954738696540170348134400), (2424897, -10227872040388038041130224947211426905339779201302430456586030783960414501460531706292437606699825402562141532998855053315880435299532800), (2424900, -1529122230323868919897322234714458098250435798819817619936113935749834540193580459205528411447840832102829957838210396359472649054617600), (2425089, -7305622885991455743664446390865304932385556572358878897561450559971724643900379790208884004785589573258672523570610752368486025213952000), (2425092, -1092230164517049228498087310510327213036025570585584014240081382678453242995414613718234579605600594359164255598721711685337606467584000), (2425857, -1461124577198291148732889278173060986477111314471775779512290111994344928780075958041776800957117914651734504714122150473697205042790400), (2425860, -218446032903409845699617462102065442607205114117116802848016276535690648599082922743646915921120118871832851119744342337067521293516800), (2428929, 1461124577198291148732889278173060986477111314471775779512290111994344928780075958041776800957117914651734504714122150473697205042790400), (2428932, 218446032903409845699617462102065442607205114117116802848016276535690648599082922743646915921120118871832851119744342337067521293516800), (2441217, 7305622885991455743664446390865304932385556572358878897561450559971724643900379790208884004785589573258672523570610752368486025213952000), (2441220, 8141974601273151279930570450467268891083122393235588308669137908612753207660876617901695589123520511924023324206791089354995424081150000), (2490369, 13150121194784620338596003503557548878294001830245982015610611007949104359020683622375991208614061231865610542427099354263274845385113600), (2490372, 1966014296130688611296557158918588983464846027054051225632146488821215837391746304692822243290081069846495660077699081033607691641651200), (3149829, -1011134185673070919681614880294230835077246783497953716872236951342674565963174256182780331724267750168268556571942169401092353725235200), (3149832, -1516701278509606379522422320441346252615870175246930575308355427014011848944761384274170497586401625252402834857913254101638530587852800), (3149844, -2022268371346141839363229760588461670154493566995907433744473902685349131926348512365560663448535500336537113143884338802184707450470400), (3149892, -1769484824927874109442826040514903961385181871121419004526414664849680490435554948319865580517468562794469974000898796451911619019161600), (3150084, -1263917732091338649602018600367788543846558479372442146090296189178343207453967820228475414655334687710335695714927711751365442156544000), (3150852, -252783546418267729920403720073557708769311695874488429218059237835668641490793564045695082931066937542067139142985542350273088431308800), (3153924, 252783546418267729920403720073557708769311695874488429218059237835668641490793564045695082931066937542067139142985542350273088431308800), (3166212, 1263917732091338649602018600367788543846558479372442146090296189178343207453967820228475414655334687710335695714927711751365442156544000), (3211266, -2006594691993443330855776238807628810391643262628685708393241459704589033398125803606134383327273956840351716848379227635150457292390400), (3211269, -3009892037990164996283664358211443215587464893943028562589862189556883550097188705409201574990910935260527575272568841452725685938585600), (3211281, -4013189383986886661711552477615257620783286525257371416786482919409178066796251607212268766654547913680703433696758455270300914584780800), (3211329, -3511540710988525828997608417913350418185375709600199989688172554483030808446720156310735170822729424470615504484663648361513300261683200), (3211521, -2508243364991804163569720298509536012989554078285857135491551824630736291747657254507667979159092446050439646060474034543938071615488000), (3212289, -501648672998360832713944059701907202597910815657171427098310364926147258349531450901533595831818489210087929212094806908787614323097600), (3215361, 501648672998360832713944059701907202597910815657171427098310364926147258349531450901533595831818489210087929212094806908787614323097600), (3215364, 2275051917764409569283633480662019378923805262870395862962533140521017773417142076411255746379602437878604252286869881152457795881779200), (3227649, 2508243364991804163569720298509536012989554078285857135491551824630736291747657254507667979159092446050439646060474034543938071615488000), (3276801, 4514838056985247494425496537317164823381197340914542843884793284335325325145783058113802362486366402890791362908853262179088528907878400)]
theorem sparseBlock043_data : sparseBlock043 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1292070222153917910114083689161259623179120489100600134971852062153442248515306265617431598387306801823587616058359215689262087872819200 : Int) coeff0467) (CoefficientMerge.scale (569811673861522471126394479416314647618846102850519868728547851621252492359604154810362209430772258365885724831353793315370749237964800 : Int) coeff0468)) (CoefficientMerge.merge (CoefficientMerge.scale (228913615600784741652500579384623290640644841578716462657834691071025206040506528119354804646740468115779323144966268328060988198297600 : Int) coeff0469) (CoefficientMerge.merge (CoefficientMerge.scale (250824336499180416356972029850953601298955407828585713549155182463073629174765725450766797915909244605043964606047403454393807161548800 : Int) coeff0470) (CoefficientMerge.scale (6418253448512294157738997117825821184805653910134272915022485074619414078394622716505142129404979185794749172991583027758551682605056000 : Int) coeff0471)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (12836506897024588315477994235651642369611307820268545830044970149238828156789245433010284258809958371589498345983166055517103365210112000 : Int) coeff0472) (CoefficientMerge.scale (6418253448512294157738997117825821184805653910134272915022485074619414078394622716505142129404979185794749172991583027758551682605056000 : Int) coeff0473)) (CoefficientMerge.merge (CoefficientMerge.scale (43229630087691784513942468388260035399405951567288408770099937631326177266108020159032954626083393622348223501414047103133642920540748800 : Int) coeff0474) (CoefficientMerge.merge (CoefficientMerge.scale (72628484912721898790622796709484450121375496950721751890454245478631890405491867492447451907109349826194225121470172553440135006939399680 : Int) coeff0475) (CoefficientMerge.scale (126391773209133864960201860036778854384655847937244214609029618917834320745396782022847541465533468771033569571492771175136544215654400 : Int) coeff0476))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (5877497946772996628279913638759822960082025710838393597795867189003260302006371587264916105615805300374727637126505664375038786090905600 : Int) coeff0477) (CoefficientMerge.scale (9275257876703375955920908847679133863828513171914628339500582538880996343930513635151659254628301804999956015287292151503700769414144000 : Int) coeff0478)) (CoefficientMerge.merge (CoefficientMerge.scale (5363774226061067938937552367837899887211333488130285967336861838698951879315888352579565392302577574471724038238485568162269674964889600 : Int) coeff0479) (CoefficientMerge.merge (CoefficientMerge.scale (497519043908116223030947588794920570197678367326063654676817434603753163330162294109258655260475619451447924717492847316468478672588800 : Int) coeff0480) (CoefficientMerge.scale (391652468708672336190693507775385648780394267925000238579392029218572220259192333565747833862106662086936614922670520981647656534087000 : Int) coeff0481)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (14769276401406131442524396776815099885490283145479434832864241222845810805396717046503310013687594149129962585577222308194394496903680000 : Int) coeff0482) (CoefficientMerge.scale (27041955355666968357646117669821194371277944202843318744004776159899186544431127314260880192943997022304436742241470455724220895066216960 : Int) coeff0483)) (CoefficientMerge.merge (CoefficientMerge.scale (14407572588966499653291763100508462052881444867214482494181333983192044584879902834663844717911893480741620927740232142559681787521310720 : Int) coeff0484) (CoefficientMerge.merge (CoefficientMerge.scale (109223016451704922849808731051032721303602557058558401424008138267845324299541461371823457960560059435916425559872171168533760646758400 : Int) coeff0485) (CoefficientMerge.scale (109223016451704922849808731051032721303602557058558401424008138267845324299541461371823457960560059435916425559872171168533760646758400 : Int) coeff0486)))))) := by decide +kernel
theorem sparseBlock043_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock043 := by
  rw [sparseBlock043_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted0467_nonneg g t z hg hA hB ht hz hw) (weighted0468_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0469_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0470_nonneg g t z hg hA hB ht hz hw) (weighted0471_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0472_nonneg g t z hg hA hB ht hz hw) (weighted0473_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0474_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0475_nonneg g t z hg hA hB ht hz hw) (weighted0476_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted0477_nonneg g t z hg hA hB ht hz hw) (weighted0478_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0479_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0480_nonneg g t z hg hA hB ht hz hw) (weighted0481_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0482_nonneg g t z hg hA hB ht hz hw) (weighted0483_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0484_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0485_nonneg g t z hg hA hB ht hz hw) (weighted0486_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
