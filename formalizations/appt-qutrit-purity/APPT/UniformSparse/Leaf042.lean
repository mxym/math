import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff0447 : CoefficientMerge.Poly :=
  [(262465, -1296), (262468, -3888), (262480, -5184), (262528, -2592), (262720, -1296), (263488, -648), (266560, 1944), (278848, 3240), (328000, 5832), (524609, 144), (524612, 432), (524624, 576), (524672, 288), (524864, 144), (525632, 72), (528704, -216), (540992, -360), (590144, -648), (786753, -4), (786756, -12), (786768, -16), (786816, -8), (787008, -4), (787776, -2), (790848, 6), (803136, 10), (852288, 18), (1311041, 144), (1311044, 432), (1311056, 576), (1311104, 288), (1311296, 144), (1312064, 72), (1315136, -216), (1327424, -360), (1376576, -648), (1573185, -8), (1573188, -24), (1573200, -32), (1573248, -16), (1573440, -8), (1574208, -4), (1577280, 12), (1589568, 20), (1638720, 36), (2359617, -4), (2359620, -12), (2359632, -16), (2359680, -8), (2359872, -4), (2360640, -2), (2363712, 6), (2376000, 10), (2425152, 18)]
noncomputable def atom0447 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,1,2] * g 3 * g 4) * t * (t+z-18) * (t+z-18))
theorem atom0447_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0447 g t z = CoefficientMerge.eval (monomial g t z) coeff0447 := by
  norm_num [atom0447, coeff0447, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0447_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0447 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadB_nonneg (outer g) hB ![2,1,2]
  dsimp only [atom0447]
  positivity
theorem weighted0447_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (861757401445100349424489398598522880850031154940309576728996807784991402841367849906508010190493926518650842816383224444278278205196800 : Int) coeff0447) := by
  rw [CoefficientMerge.eval_scale, ← atom0447_identity]
  exact mul_nonneg (by norm_num) (atom0447_nonneg g t z hg hA hB ht hz hw)

def coeff0448 : CoefficientMerge.Poly :=
  [(3, -2592), (6, -3888), (18, -5184), (66, -4536), (258, -3240), (1026, -648), (4098, 648), (16386, 3240), (65538, 5832), (262147, 288), (262150, 432), (262162, 576), (262210, 504), (262402, 360), (263170, 72), (266242, -72), (278530, -360), (327682, -648), (524291, -8), (524294, -12), (524306, -16), (524354, -14), (524546, -10), (525314, -2), (528386, 2), (540674, 10), (589826, 18), (1048579, 288), (1048582, 432), (1048594, 576), (1048642, 504), (1048834, 360), (1049602, 72), (1052674, -72), (1064962, -360), (1114114, -648), (1310723, -16), (1310726, -24), (1310738, -32), (1310786, -28), (1310978, -20), (1311746, -4), (1314818, 4), (1327106, 20), (1376258, 36), (2097155, -8), (2097158, -12), (2097170, -16), (2097218, -14), (2097410, -10), (2098178, -2), (2101250, 2), (2113538, 10), (2162690, 18)]
noncomputable def atom0448 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 0 * g 0) * (t+z-18) * (t+z-18))
theorem atom0448_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0448 g t z = CoefficientMerge.eval (monomial g t z) coeff0448 := by
  norm_num [atom0448, coeff0448, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0448_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0448 g t z := by
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
  dsimp only [atom0448]
  positivity
theorem weighted0448_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (658408983339726674387069883390329528574209546942459976580591041355886859521773809310746228346351873059935454741567425931745404668313600 : Int) coeff0448) := by
  rw [CoefficientMerge.eval_scale, ← atom0448_identity]
  exact mul_nonneg (by norm_num) (atom0448_nonneg g t z hg hA hB ht hz hw)

def coeff0449 : CoefficientMerge.Poly :=
  [(262147, -2592), (262150, -3888), (262162, -5184), (262210, -4536), (262402, -3240), (263170, -648), (266242, 648), (278530, 3240), (327682, 5832), (524291, 288), (524294, 432), (524306, 576), (524354, 504), (524546, 360), (525314, 72), (528386, -72), (540674, -360), (589826, -648), (786435, -8), (786438, -12), (786450, -16), (786498, -14), (786690, -10), (787458, -2), (790530, 2), (802818, 10), (851970, 18), (1310723, 288), (1310726, 432), (1310738, 576), (1310786, 504), (1310978, 360), (1311746, 72), (1314818, -72), (1327106, -360), (1376258, -648), (1572867, -16), (1572870, -24), (1572882, -32), (1572930, -28), (1573122, -20), (1573890, -4), (1576962, 4), (1589250, 20), (1638402, 36), (2359299, -8), (2359302, -12), (2359314, -16), (2359362, -14), (2359554, -10), (2360322, -2), (2363394, 2), (2375682, 10), (2424834, 18)]
noncomputable def atom0449 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 0 * g 0) * t * (t+z-18) * (t+z-18))
theorem atom0449_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0449 g t z = CoefficientMerge.eval (monomial g t z) coeff0449 := by
  norm_num [atom0449, coeff0449, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0449_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0449 g t z := by
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
  dsimp only [atom0449]
  positivity
theorem weighted0449_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (126655674079728560438328376493953652446107348474059935962977672728994917434004496161064712891286904025488810703492398136637602217036800 : Int) coeff0449) := by
  rw [CoefficientMerge.eval_scale, ← atom0449_identity]
  exact mul_nonneg (by norm_num) (atom0449_nonneg g t z hg hA hB ht hz hw)

def coeff0450 : CoefficientMerge.Poly :=
  [(524294, -8), (524297, -12), (524309, -16), (524357, -14), (524549, -10), (525317, -2), (528389, 2), (540677, 10), (589829, 18)]
noncomputable def atom0450 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 0 * g 1) * t * t)
theorem atom0450_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0450 g t z = CoefficientMerge.eval (monomial g t z) coeff0450 := by
  norm_num [atom0450, coeff0450, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0450_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0450 g t z := by
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
  dsimp only [atom0450]
  positivity
theorem weighted0450_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (7864791631036845303138505937941868004866019090638020030340052733482501721063107760565960147206480176532580899480216323787467686828544000 : Int) coeff0450) := by
  rw [CoefficientMerge.eval_scale, ← atom0450_identity]
  exact mul_nonneg (by norm_num) (atom0450_nonneg g t z hg hA hB ht hz hw)

def coeff0451 : CoefficientMerge.Poly :=
  [(1310726, -8), (1310729, -12), (1310741, -16), (1310789, -14), (1310981, -10), (1311749, -2), (1314821, 2), (1327109, 10), (1376261, 18)]
noncomputable def atom0451 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 0 * g 1) * t * z)
theorem atom0451_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0451 g t z = CoefficientMerge.eval (monomial g t z) coeff0451 := by
  norm_num [atom0451, coeff0451, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0451_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0451 g t z := by
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
  dsimp only [atom0451]
  positivity
theorem weighted0451_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (15611675895181555958253429937019199028345865723262373461548647734304732502354979860231271940826046973929830072552593740990277505412756480 : Int) coeff0451) := by
  rw [CoefficientMerge.eval_scale, ← atom0451_identity]
  exact mul_nonneg (by norm_num) (atom0451_nonneg g t z hg hA hB ht hz hw)

def coeff0452 : CoefficientMerge.Poly :=
  [(2097158, -8), (2097161, -12), (2097173, -16), (2097221, -14), (2097413, -10), (2098181, -2), (2101253, 2), (2113541, 10), (2162693, 18)]
noncomputable def atom0452 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 0 * g 1) * z * z)
theorem atom0452_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0452 g t z = CoefficientMerge.eval (monomial g t z) coeff0452 := by
  norm_num [atom0452, coeff0452, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0452_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0452 g t z := by
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
  dsimp only [atom0452]
  positivity
theorem weighted0452_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (7784413006050260461086809565429281819841832806579141732854962235781664783170482380157190081478546694668504975516440731424198195854684160 : Int) coeff0452) := by
  rw [CoefficientMerge.eval_scale, ← atom0452_identity]
  exact mul_nonneg (by norm_num) (atom0452_nonneg g t z hg hA hB ht hz hw)

def coeff0453 : CoefficientMerge.Poly :=
  [(262150, -2592), (262153, -3888), (262165, -5184), (262213, -4536), (262405, -3240), (263173, -648), (266245, 648), (278533, 3240), (327685, 5832), (524294, 288), (524297, 432), (524309, 576), (524357, 504), (524549, 360), (525317, 72), (528389, -72), (540677, -360), (589829, -648), (786438, -8), (786441, -12), (786453, -16), (786501, -14), (786693, -10), (787461, -2), (790533, 2), (802821, 10), (851973, 18), (1310726, 288), (1310729, 432), (1310741, 576), (1310789, 504), (1310981, 360), (1311749, 72), (1314821, -72), (1327109, -360), (1376261, -648), (1572870, -16), (1572873, -24), (1572885, -32), (1572933, -28), (1573125, -20), (1573893, -4), (1576965, 4), (1589253, 20), (1638405, 36), (2359302, -8), (2359305, -12), (2359317, -16), (2359365, -14), (2359557, -10), (2360325, -2), (2363397, 2), (2375685, 10), (2424837, 18)]
noncomputable def atom0453 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 0 * g 1) * t * (t+z-18) * (t+z-18))
theorem atom0453_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0453 g t z = CoefficientMerge.eval (monomial g t z) coeff0453 := by
  norm_num [atom0453, coeff0453, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0453_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0453 g t z := by
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
  dsimp only [atom0453]
  positivity
theorem weighted0453_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (333423452072767868340683953434723797528094879875607189479544770170378241637903446745833951972405546435819265584105852988968185120665600 : Int) coeff0453) := by
  rw [CoefficientMerge.eval_scale, ← atom0453_identity]
  exact mul_nonneg (by norm_num) (atom0453_nonneg g t z hg hA hB ht hz hw)

def coeff0454 : CoefficientMerge.Poly :=
  [(1048582, -2592), (1048585, -3888), (1048597, -5184), (1048645, -4536), (1048837, -3240), (1049605, -648), (1052677, 648), (1064965, 3240), (1114117, 5832), (1310726, 288), (1310729, 432), (1310741, 576), (1310789, 504), (1310981, 360), (1311749, 72), (1314821, -72), (1327109, -360), (1376261, -648), (1572870, -8), (1572873, -12), (1572885, -16), (1572933, -14), (1573125, -10), (1573893, -2), (1576965, 2), (1589253, 10), (1638405, 18), (2097158, 288), (2097161, 432), (2097173, 576), (2097221, 504), (2097413, 360), (2098181, 72), (2101253, -72), (2113541, -360), (2162693, -648), (2359302, -16), (2359305, -24), (2359317, -32), (2359365, -28), (2359557, -20), (2360325, -4), (2363397, 4), (2375685, 20), (2424837, 36), (3145734, -8), (3145737, -12), (3145749, -16), (3145797, -14), (3145989, -10), (3146757, -2), (3149829, 2), (3162117, 10), (3211269, 18)]
noncomputable def atom0454 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 0 * g 1) * z * (t+z-18) * (t+z-18))
theorem atom0454_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0454 g t z = CoefficientMerge.eval (monomial g t z) coeff0454 := by
  norm_num [atom0454, coeff0454, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0454_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0454 g t z := by
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
  dsimp only [atom0454]
  positivity
theorem weighted0454_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (88877692179766538506843414711507899923419399562513596270189511561055400015344737747650501625286991065383481077331200005639153581603840 : Int) coeff0454) := by
  rw [CoefficientMerge.eval_scale, ← atom0454_identity]
  exact mul_nonneg (by norm_num) (atom0454_nonneg g t z hg hA hB ht hz hw)

def coeff0455 : CoefficientMerge.Poly :=
  [(524306, -8), (524309, -12), (524321, -16), (524369, -14), (524561, -10), (525329, -2), (528401, 2), (540689, 10), (589841, 18)]
noncomputable def atom0455 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 0 * g 2) * t * t)
theorem atom0455_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0455 g t z = CoefficientMerge.eval (monomial g t z) coeff0455 := by
  norm_num [atom0455, coeff0455, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0455_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0455 g t z := by
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
  dsimp only [atom0455]
  positivity
theorem weighted0455_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (52827965276912183127386686605735799309847286425365782719102222698244522751156390924712440908186492238619735180905655930582327791325163520 : Int) coeff0455) := by
  rw [CoefficientMerge.eval_scale, ← atom0455_identity]
  exact mul_nonneg (by norm_num) (atom0455_nonneg g t z hg hA hB ht hz hw)

def coeff0456 : CoefficientMerge.Poly :=
  [(1310738, -8), (1310741, -12), (1310753, -16), (1310801, -14), (1310993, -10), (1311761, -2), (1314833, 2), (1327121, 10), (1376273, 18)]
noncomputable def atom0456 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 0 * g 2) * t * z)
theorem atom0456_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0456 g t z = CoefficientMerge.eval (monomial g t z) coeff0456 := by
  norm_num [atom0456, coeff0456, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0456_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0456 g t z := by
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
  dsimp only [atom0456]
  positivity
theorem weighted0456_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (42279288567131586929195616458930372399603078561283583827277744854918655346596926588703620964802055889651401418421661256296098837392696320 : Int) coeff0456) := by
  rw [CoefficientMerge.eval_scale, ← atom0456_identity]
  exact mul_nonneg (by norm_num) (atom0456_nonneg g t z hg hA hB ht hz hw)

def coeff0457 : CoefficientMerge.Poly :=
  [(2097170, -8), (2097173, -12), (2097185, -16), (2097233, -14), (2097425, -10), (2098193, -2), (2101265, 2), (2113553, 10), (2162705, 18)]
noncomputable def atom0457 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 0 * g 2) * z * z)
theorem atom0457_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0457 g t z = CoefficientMerge.eval (monomial g t z) coeff0457 := by
  norm_num [atom0457, coeff0457, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0457_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0457 g t z := by
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
  dsimp only [atom0457]
  positivity
theorem weighted0457_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (7499148391072274636553033340194290656470098259151413204903837414094043102613894815520134912047774747806056544470925218635659697016135904 : Int) coeff0457) := by
  rw [CoefficientMerge.eval_scale, ← atom0457_identity]
  exact mul_nonneg (by norm_num) (atom0457_nonneg g t z hg hA hB ht hz hw)

def coeff0458 : CoefficientMerge.Poly :=
  [(1572882, -8), (1572885, -12), (1572897, -16), (1572945, -14), (1573137, -10), (1573905, -2), (1576977, 2), (1589265, 10), (1638417, 18)]
noncomputable def atom0458 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 0 * g 2) * t * t * z)
theorem atom0458_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0458 g t z = CoefficientMerge.eval (monomial g t z) coeff0458 := by
  norm_num [atom0458, coeff0458, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0458_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0458 g t z := by
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
  dsimp only [atom0458]
  positivity
theorem weighted0458_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (995608281753030503455433560802383657456459944564731152874913659897354903331030309708611918842416579659451867842142501545694101058193920 : Int) coeff0458) := by
  rw [CoefficientMerge.eval_scale, ← atom0458_identity]
  exact mul_nonneg (by norm_num) (atom0458_nonneg g t z hg hA hB ht hz hw)

def coeff0459 : CoefficientMerge.Poly :=
  [(2359314, -8), (2359317, -12), (2359329, -16), (2359377, -14), (2359569, -10), (2360337, -2), (2363409, 2), (2375697, 10), (2424849, 18)]
noncomputable def atom0459 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 0 * g 2) * t * z * z)
theorem atom0459_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0459 g t z = CoefficientMerge.eval (monomial g t z) coeff0459 := by
  norm_num [atom0459, coeff0459, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0459_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0459 g t z := by
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
  dsimp only [atom0459]
  positivity
theorem weighted0459_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1018148846465176937315852899613355598448966913944228667199958134787502552371387874568039372481516717679262547895153496681844490433781760 : Int) coeff0459) := by
  rw [CoefficientMerge.eval_scale, ← atom0459_identity]
  exact mul_nonneg (by norm_num) (atom0459_nonneg g t z hg hA hB ht hz hw)

def coeff0460 : CoefficientMerge.Poly :=
  [(540674, -8), (540677, -12), (540689, -16), (540737, -14), (540929, -10), (541697, -2), (544769, 2), (557057, 10), (606209, 18)]
noncomputable def atom0460 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 0 * g 7) * t * t)
theorem atom0460_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0460 g t z = CoefficientMerge.eval (monomial g t z) coeff0460 := by
  norm_num [atom0460, coeff0460, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0460_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0460 g t z := by
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
  dsimp only [atom0460]
  positivity
theorem weighted0460_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (7741726110164512147773718206347325146849974383231592981774279386921726310935448102404688097863652487204027093444792297176890228989542400 : Int) coeff0460) := by
  rw [CoefficientMerge.eval_scale, ← atom0460_identity]
  exact mul_nonneg (by norm_num) (atom0460_nonneg g t z hg hA hB ht hz hw)

def coeff0461 : CoefficientMerge.Poly :=
  [(1327106, -8), (1327109, -12), (1327121, -16), (1327169, -14), (1327361, -10), (1328129, -2), (1331201, 2), (1343489, 10), (1392641, 18)]
noncomputable def atom0461 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 0 * g 7) * t * z)
theorem atom0461_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0461 g t z = CoefficientMerge.eval (monomial g t z) coeff0461 := by
  norm_num [atom0461, coeff0461, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0461_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0461 g t z := by
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
  dsimp only [atom0461]
  positivity
theorem weighted0461_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (14170024051611885613676648062288687211758835871372981787151730036588360551244351309813167574696843295299328499425353063241957588627968000 : Int) coeff0461) := by
  rw [CoefficientMerge.eval_scale, ← atom0461_identity]
  exact mul_nonneg (by norm_num) (atom0461_nonneg g t z hg hA hB ht hz hw)

def coeff0462 : CoefficientMerge.Poly :=
  [(2113538, -8), (2113541, -12), (2113553, -16), (2113601, -14), (2113793, -10), (2114561, -2), (2117633, 2), (2129921, 10), (2179073, 18)]
noncomputable def atom0462 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 0 * g 7) * z * z)
theorem atom0462_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0462 g t z = CoefficientMerge.eval (monomial g t z) coeff0462 := by
  norm_num [atom0462, coeff0462, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0462_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0462 g t z := by
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
  dsimp only [atom0462]
  positivity
theorem weighted0462_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (7525241743894893962049389574681946992258460925545236619461561451071142646690906672438498233671463001820087897321755541976093610508595200 : Int) coeff0462) := by
  rw [CoefficientMerge.eval_scale, ← atom0462_identity]
  exact mul_nonneg (by norm_num) (atom0462_nonneg g t z hg hA hB ht hz hw)

def coeff0463 : CoefficientMerge.Poly :=
  [(327682, -8), (327685, -12), (327697, -16), (327745, -14), (327937, -10), (328705, -2), (331777, 2), (344065, 10), (393217, 18)]
noncomputable def atom0463 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 0 * g 8) * t)
theorem atom0463_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0463 g t z = CoefficientMerge.eval (monomial g t z) coeff0463 := by
  norm_num [atom0463, coeff0463, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0463_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0463 g t z := by
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
  dsimp only [atom0463]
  positivity
theorem weighted0463_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (91387556983484502796778805460387925271337423922971514960687431735335400525033416283777128908807662574179431477133912578474747493567488000 : Int) coeff0463) := by
  rw [CoefficientMerge.eval_scale, ← atom0463_identity]
  exact mul_nonneg (by norm_num) (atom0463_nonneg g t z hg hA hB ht hz hw)

def coeff0464 : CoefficientMerge.Poly :=
  [(1114114, -8), (1114117, -12), (1114129, -16), (1114177, -14), (1114369, -10), (1115137, -2), (1118209, 2), (1130497, 10), (1179649, 18)]
noncomputable def atom0464 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 0 * g 8) * z)
theorem atom0464_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0464 g t z = CoefficientMerge.eval (monomial g t z) coeff0464 := by
  norm_num [atom0464, coeff0464, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0464_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0464 g t z := by
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
  dsimp only [atom0464]
  positivity
theorem weighted0464_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (90958473505436894106801828669134099230567354187896826944656795004578976421792432378511828668212538987113800239413386634296599861011046400 : Int) coeff0464) := by
  rw [CoefficientMerge.eval_scale, ← atom0464_identity]
  exact mul_nonneg (by norm_num) (atom0464_nonneg g t z hg hA hB ht hz hw)

def coeff0465 : CoefficientMerge.Poly :=
  [(589826, -8), (589829, -12), (589841, -16), (589889, -14), (590081, -10), (590849, -2), (593921, 2), (606209, 10), (655361, 18)]
noncomputable def atom0465 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 0 * g 8) * t * t)
theorem atom0465_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0465 g t z = CoefficientMerge.eval (monomial g t z) coeff0465 := by
  norm_num [atom0465, coeff0465, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0465_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0465 g t z := by
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
  dsimp only [atom0465]
  positivity
theorem weighted0465_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1268232251151272982893140534091602620914116614929784134081261132666974242779696048658248251687577713653274769518329996568253886064128000 : Int) coeff0465) := by
  rw [CoefficientMerge.eval_scale, ← atom0465_identity]
  exact mul_nonneg (by norm_num) (atom0465_nonneg g t z hg hA hB ht hz hw)

def coeff0466 : CoefficientMerge.Poly :=
  [(1376258, -8), (1376261, -12), (1376273, -16), (1376321, -14), (1376513, -10), (1377281, -2), (1380353, 2), (1392641, 10), (1441793, 18)]
noncomputable def atom0466 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadB (outer g) ![2,2,1] * g 0 * g 8) * t * z)
theorem atom0466_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0466 g t z = CoefficientMerge.eval (monomial g t z) coeff0466 := by
  norm_num [atom0466, coeff0466, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0466_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0466 g t z := by
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
  dsimp only [atom0466]
  positivity
theorem weighted0466_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2560302473305190893007224223252862244093237104030384269053113194820416491295002314275679850074884515476862385576689212257515973936947200 : Int) coeff0466) := by
  rw [CoefficientMerge.eval_scale, ← atom0466_identity]
  exact mul_nonneg (by norm_num) (atom0466_nonneg g t z hg hA hB ht hz hw)

def sparseBlock042 : CoefficientMerge.Poly :=
  [(3, -1706596084816571540011285137747734138064351145674856259296891979194458739880437713733454223873744054971352698690142768015084088900268851200), (6, -2559894127224857310016927706621601207096526718512284388945337968791688109820656570600181335810616082457029048035214152022626133350403276800), (18, -3413192169633143080022570275495468276128702291349712518593783958388917479760875427466908447747488109942705397380285536030168177800537702400), (66, -2986543148429000195019748991058534741612614504930998453769560963590302794790765999033544891779052096199867222707749844026397155575470489600), (258, -2133245106020714425014106422184667672580438932093570324121114973993073424850547142166817779842180068714190873362678460018855111125336064000), (1026, -426649021204142885002821284436933534516087786418714064824222994798614684970109428433363555968436013742838174672535692003771022225067212800), (4098, 426649021204142885002821284436933534516087786418714064824222994798614684970109428433363555968436013742838174672535692003771022225067212800), (16386, 2133245106020714425014106422184667672580438932093570324121114973993073424850547142166817779842180068714190873362678460018855111125336064000), (65538, 3839841190837285965025391559932401810644790077768426583418006953187532164730984855900272003715924123685543572052821228033939200025604915200), (262147, -138669720012815146432671025455912962910937897725334880760827907803059410446668796967984822050466315792805586377880877301821988402085068800), (262150, -1072238167791837034388059345486673527559228775225576156272221905986209517995448929417178836588174650050851915960823686900138518435892838400), (262153, -1296350381658921472108579210954206124789232892956360752696470066422430603488168600947802405268712764542465304591003556421108303749147852800), (262162, -277339440025630292865342050911825925821875795450669761521655815606118820893337593935969644100932631585611172755761754603643976804170137600), (262165, -1728467175545228629478105614605608166385643857275147670261960088563240804650891467930403207024950352723287072788004741894811071665530470400), (262210, -242672010022426506257174294547847685094141321019336041331448838655353968281670394693973438588316052637409776161291535278188479703648870400), (262213, -1512408778602075050793342412779907145587438375115754211479215077492835704069530034439102806146831558632876188689504149157959687707339161600), (262402, -173337150016018933040838781819891203638672372156668600951034884753824263058335996209981027563082894741006982972351096627277485502606336000), (262405, -1080291984715767893423816009128505103991027410796967293913725055352025502906807167456502004390593970452054420492502963684256919790956544000), (262465, -1116837592272850052854138260583685653581640376802641211440779862889348858082412733478834381206880128768171492290032658879784648553935052800), (262468, -3350512776818550158562414781751056960744921130407923634322339588668046574247238200436503143620640386304514476870097976639353945661805158400), (262480, -4467350369091400211416553042334742614326561507210564845763119451557395432329650933915337524827520515072685969160130635519138594215740211200), (262528, -2233675184545700105708276521167371307163280753605282422881559725778697716164825466957668762413760257536342984580065317759569297107870105600), (262720, -1116837592272850052854138260583685653581640376802641211440779862889348858082412733478834381206880128768171492290032658879784648553935052800), (263170, -34667430003203786608167756363978240727734474431333720190206976950764852611667199241996205512616578948201396594470219325455497100521267200), (263173, -216058396943153578684763201825701020798205482159393458782745011070405100581361433491300400878118794090410884098500592736851383958191308800), (263488, -558418796136425026427069130291842826790820188401320605720389931444674429041206366739417190603440064384085746145016329439892324276967526400), (266242, 34667430003203786608167756363978240727734474431333720190206976950764852611667199241996205512616578948201396594470219325455497100521267200), (266245, 216058396943153578684763201825701020798205482159393458782745011070405100581361433491300400878118794090410884098500592736851383958191308800), (266560, 1675256388409275079281207390875528480372460565203961817161169794334023287123619100218251571810320193152257238435048988319676972830902579200), (278530, 173337150016018933040838781819891203638672372156668600951034884753824263058335996209981027563082894741006982972351096627277485502606336000), (278533, 1080291984715767893423816009128505103991027410796967293913725055352025502906807167456502004390593970452054420492502963684256919790956544000), (278848, 2792093980682125132135345651459214133954100942006603028601949657223372145206031833697085953017200321920428730725081647199461621384837632000), (327682, -419093585839041942900720636407299235621089121501768637973636661325799530695262537092251181656912090059622882466839326698698506043848499200), (327685, 847874888686568174601523150906654083927800252358882949516455918809621098931851906016378060997377195923544779160898383689965485700911923200), (327697, -1462200911735752044748460887366206804341398782767544239370998907765366408400534660540434062540922601186870903634142601255595959897079808000), (327745, -1279425797768783039154903276445430953798723934921601209449624044294695607350467827972879804723307276038512040679874776098646464909944832000), (327937, -913875569834845027967788054603879252713374239229715149606874317353354005250334162837771289088076625741794314771339125784747474935674880000), (328000, 5025769165227825237843622172626585441117381695611885451483509383002069861370857300654754715430960579456771715305146964959030918492707737600), (328705, -182775113966969005593557610920775850542674847845943029921374863470670801050066832567554257817615325148358862954267825156949494987134976000), (331777, 182775113966969005593557610920775850542674847845943029921374863470670801050066832567554257817615325148358862954267825156949494987134976000), (344065, 913875569834845027967788054603879252713374239229715149606874317353354005250334162837771289088076625741794314771339125784747474935674880000), (393217, 1644976025702721050342018498286982654884073630613487269292373771236037209450601493107988320358537926335229766588410426412545454884214784000), (524291, 31209562268244012011142013363136015675885239984989581744692841415103441344819104419900667485919813374861293844673271255897666201160089600), (524294, 79921964551028401673721951130369533162991032656555082944427734063864081840439987208123498219280676023547242059390661954369595121863475200), (524297, 49661431722993575485513396628498264473744759018606065491082707911813379734816995867408745485601433941882951938571132605784643730185011200), (524306, -360204597678809440996809466119614363127007811432947098263432098755749299319612918557898192293652311159235293757898704932863289928281128960), (524309, -567720341025621430214622377097498572419841091746247971974449728496516433367454029940004296917435994940926219586106361025941741855655280640), (524321, -845247444430594930038186985691772788957556582805852523505635563171912364018502254795399054530983875817915762894490494889317244661202616320), (524354, 54616733969427021019498523385488027432799169973731768053212472476431022353433432734826168100359673406007264228178224697820915852030156800), (524357, 57938337010159171399765629399914641886035552188373743072929825897115609690619828511976869733201672932196777261666321373415417685215846400), (524369, -739591513876770563783413612480301190337862009955120958067431117775423318516189472945974172714610891340676292532679183028152589078552289280), (524546, 39011952835305015013927516703920019594856549981236977180866051768879301681023880524875834357399766718576617305841589069872082751450112000), (524549, 41384526435827979571261163857081887061453965848838387909235589926511149779014163222840621238001194951569126615475943838153869775154176000), (524561, -528279652769121831273866866057357993098472864253657827191022226982445227511563909247124409081864922386197351809056559305823277913251635200), (524609, 124093065808094450317126473398187294842404486311404579048975540321038762009156970386537153467431125418685721365559184319976072061548339200), (524612, 372279197424283350951379420194561884527213458934213737146926620963116286027470911159611460402293376256057164096677552959928216184645017600), (524624, 496372263232377801268505893592749179369617945245618316195902161284155048036627881546148613869724501674742885462236737279904288246193356800), (524672, 248186131616188900634252946796374589684808972622809158097951080642077524018313940773074306934862250837371442731118368639952144123096678400), (524864, 124093065808094450317126473398187294842404486311404579048975540321038762009156970386537153467431125418685721365559184319976072061548339200), (525314, 7802390567061003002785503340784003918971309996247395436173210353775860336204776104975166871479953343715323461168317813974416550290022400), (525317, 8276905287165595914252232771416377412290793169767677581847117985302229955802832644568124247600238990313825323095188767630773955030835200), (525329, -105655930553824366254773373211471598619694572850731565438204445396489045502312781849424881816372984477239470361811311861164655582650327040), (525632, 62046532904047225158563236699093647421202243155702289524487770160519381004578485193268576733715562709342860682779592159988036030774169600), (528386, -7802390567061003002785503340784003918971309996247395436173210353775860336204776104975166871479953343715323461168317813974416550290022400), (528389, -8276905287165595914252232771416377412290793169767677581847117985302229955802832644568124247600238990313825323095188767630773955030835200), (528401, 105655930553824366254773373211471598619694572850731565438204445396489045502312781849424881816372984477239470361811311861164655582650327040), (528704, -186139598712141675475689710097280942263606729467106868573463310481558143013735455579805730201146688128028582048338776479964108092322508800), (540674, -100945761716621112196117262354698620769656345047089721035060286864253112168507465344113339140308986616208834053399927447287204583366451200), (540677, -134285239757802125344545782333249788823653658447617503690526942569571865510239540451696878412365024798017451736813451404276552523028684800), (540689, 404412035006489636909487374755800790748873274121952339482633756791697606536596739608649399516046482590932918313939882550993034249418956800), (540737, -108384165542303170068832054888862552055899641365242301744839911416904168353096273433665633370091134820856379308227092160476463205853593600), (540929, -77417261101645121477737182063473251468499743832315929817742793869217263109354481024046880978636524872040270934447922971768902289895424000), (540992, -310232664520236125792816183495468237106011215778511447622438850802596905022892425966342883668577813546714303413897960799940180153870848000), (541697, -15483452220329024295547436412694650293699948766463185963548558773843452621870896204809376195727304974408054186889584594353780457979084800), (544769, 15483452220329024295547436412694650293699948766463185963548558773843452621870896204809376195727304974408054186889584594353780457979084800), (557057, 77417261101645121477737182063473251468499743832315929817742793869217263109354481024046880978636524872040270934447922971768902289895424000), (589826, -80367373112759210888214654339788856238054722885664831998208982245318536968080553334042487856820201802664109306661500298315780041123225600), (589829, -89710934598305639022987781351846628161586537907066507845599195459723760515581846385012097248653083476663725142076658867496012228047052800), (589841, 930611658965998928566670110357778745642625289817707542798539830445729821636339899866291964320355616876702836944008526805389838066826895360), (589889, -17755251516117821760503967477282436692797632609016977877137655857337639398915744681215475523626087991145846773256619951955554404897792000), (590081, -12682322511512729828931405340916026209141166149297841340812611326669742427796960486582482516875777136532747695183299965682538860641280000), (590144, -558418796136425026427069130291842826790820188401320605720389931444674429041206366739417190603440064384085746145016329439892324276967526400), (590849, -2536464502302545965786281068183205241828233229859568268162522265333948485559392097316496503375155427306549539036659993136507772128256000), (593921, 2536464502302545965786281068183205241828233229859568268162522265333948485559392097316496503375155427306549539036659993136507772128256000), (606209, 152033392494473948488858333055167878852440705047466515012749640291260816024635026329866868278421521906205235377189561314866562982453043200), (655361, 22828180520722913692076529613648847176454099068736114413462700388005536370034528875848468530376398845758945851329939938228569949154304000), (786435, -1013245392637828483506627011951629219568858787792479487703821381831959339472035969288517703130295232203910485627939185093100817736294400), (786438, -4187255705538885671985412145405234209578047220693576747392090234110964942311281527899448170474687219792419853114755601551396707569766400), (786441, -4001081424873214420088207441216685570337138558507286273754537242044538899654841360950007423668866557229831187009270235867618221447987200), (786450, -2026490785275656967013254023903258439137717575584958975407642763663918678944071938577035406260590464407820971255878370186201635472588800), (786453, -5334775233164285893450943254955580760449518078009715031672716322726051866206455147933343231558488742973108249345693647823490961930649600), (786498, -1773179437116199846136597270915351134245502878636839103481687418205928844076062946254905980478016656356843349848893573912926431038515200), (786501, -4667928329018750156769575348086133165393328318258500652713626782385295382930648254441675327613677650101469718177481941845554591689318400), (786690, -1266556740797285604383283764939536524461073484740599359629776727289949174340044961610647128912869040254888107034923981366376022170368000), (786693, -3334234520727678683406839534347237975280948798756071894795447701703782416379034467458339519724055464358192655841058529889681851206656000), (786753, -3447029605780401397697957594394091523400124619761238306915987231139965611365471399626032040761975706074603371265532897777113112820787200), (786756, -10341088817341204193093872783182274570200373859283714920747961693419896834096414198878096122285927118223810113796598693331339338462361600), (786768, -13788118423121605590791830377576366093600498479044953227663948924559862445461885598504128163047902824298413485062131591108452451283148800), (786816, -6894059211560802795395915188788183046800249239522476613831974462279931222730942799252064081523951412149206742531065795554226225641574400), (787008, -3447029605780401397697957594394091523400124619761238306915987231139965611365471399626032040761975706074603371265532897777113112820787200), (787458, -253311348159457120876656752987907304892214696948119871925955345457989834868008992322129425782573808050977621406984796273275204434073600), (787461, -666846904145535736681367906869447595056189759751214378959089540340756483275806893491667903944811092871638531168211705977936370241331200), (787776, -1723514802890200698848978797197045761700062309880619153457993615569982805682735699813016020380987853037301685632766448888556556410393600), (790530, 253311348159457120876656752987907304892214696948119871925955345457989834868008992322129425782573808050977621406984796273275204434073600), (790533, 666846904145535736681367906869447595056189759751214378959089540340756483275806893491667903944811092871638531168211705977936370241331200), (790848, 5170544408670602096546936391591137285100186929641857460373980846709948417048207099439048061142963559111905056898299346665669669231180800), (802818, 1266556740797285604383283764939536524461073484740599359629776727289949174340044961610647128912869040254888107034923981366376022170368000), (802821, 3334234520727678683406839534347237975280948798756071894795447701703782416379034467458339519724055464358192655841058529889681851206656000), (803136, 8617574014451003494244893985985228808500311549403095767289968077849914028413678499065080101904939265186508428163832244442782782051968000), (851970, 2279802133435114087889910776891165744029932272533078847333598109121908513812080930899164832043164272458798592662863166459476839906662400), (851973, 6001622137309821630132311161825028355505707837760929410631805863066808349482262041425011135503299835844746780513905353801427332171980800), (852288, 15511633226011806289640809174773411855300560788925572381121942540129845251144621298317144183428890677335715170694898039997009007693542400), (1048579, 189621787201841282223476126416414904229372349519428473255210219910495415542270857081494913763749339441261410965571418668342676544474316800), (1048582, 54061702672807055525476058692393879742555440613107468350484115899487526473632725380332270432880128320418133495914657587897328733194321920), (1048585, -345556467194932301714607196398342714902254625499052862298496820949383395259660340362865150319115821262210974428663705621925029125275729920), (1048594, 379243574403682564446952252832829808458744699038856946510420439820990831084541714162989827527498678882522821931142837336685353088948633600), (1048597, -460741956259909735619476261864456953203006167332070483064662427932511193679547120483820200425487761682947965904884940829233372167034306560), (1048642, 331838127603222243891083221228726082401401611658999828196617884843366977198973999892616099086561344022207469189749982669599683952830054400), (1048645, -403149211727421018667041729131399834052630396415561672681579624440947294469603730423342675372301791472579470166774323225579200646155018240), (1048834, 237027234002301602779345158020518630286715436899285591569012774888119269427838571351868642204686674301576763706964273335428345680592896000), (1048837, -287963722662443584762172663665285595751878854582544051915414017457819496049716950302387625265929851051842478690553088018270857604396441600), (1049602, 47405446800460320555869031604103726057343087379857118313802554977623853885567714270373728440937334860315352741392854667085669136118579200), (1049605, -57592744532488716952434532733057119150375770916508810383082803491563899209943390060477525053185970210368495738110617603654171520879288320), (1052674, -47405446800460320555869031604103726057343087379857118313802554977623853885567714270373728440937334860315352741392854667085669136118579200), (1052677, 57592744532488716952434532733057119150375770916508810383082803491563899209943390060477525053185970210368495738110617603654171520879288320), (1064962, -237027234002301602779345158020518630286715436899285591569012774888119269427838571351868642204686674301576763706964273335428345680592896000), (1064965, 287963722662443584762172663665285595751878854582544051915414017457819496049716950302387625265929851051842478690553088018270857604396441600), (1114114, -1154316809247638037857235913790006328360626619921888680381477354835246496344448887461458185314136325639748576587842785078143821113155584000), (1114117, -573166981272844276709711149432095118413426312006182629888136308630872624172018677997844218539876735952049141229965081178671654644218961920), (1114129, -1455335576086990305708829258706145587689077667006349231114508720073263622748678918056189258691400623793820803830614186148745597776176742400), (1114177, -1273418629076116517495225601367877389227942958630555577225195130064105669905094053299165601354975545819593203351787412880152398054154649600), (1114369, -909584735054368941068018286691340992305673541878968269446567950045789764217924323785118286682125389871138002394133866342965998610110464000), (1115137, -181916947010873788213603657338268198461134708375793653889313590009157952843584864757023657336425077974227600478826773268593199722022092800), (1118209, 181916947010873788213603657338268198461134708375793653889313590009157952843584864757023657336425077974227600478826773268593199722022092800), (1130497, 909584735054368941068018286691340992305673541878968269446567950045789764217924323785118286682125389871138002394133866342965998610110464000), (1179649, 1637252523097864093922432916044413786150212375382142885003822310082421575592263782813212916027825701768048404309440959417338797498198835200), (1310723, 25942290401526198616045454296013379447291563609449901932048113084256346468644913945414697659148998390381810206740731848443702963813580800), (1310726, 35642757985566759430128623973981205810206532106254651501606460890599548480263009170395393598250572594480465768184219107190247948671918080), (1310729, -4906016425083807740909336205058295041096219961880302094698563103677456834056542621589979335709387486638374312890317998212959745572679680), (1310738, -286349727734000298201474023079416220302241501271368866754125732670836549835485584818799572400118450336447590933891826353481384771514408960), (1310741, -513892818039024120138226512447242195516698569351243408720264355730593806604571842559896757358570520658001316104913692406503799042809262080), (1310753, -676468617074105390867129863342885958393649256980537341236443917678698485545550825419257935436832894234422422694746580100737581398283141120), (1310786, 45399008202670847578079545018023414032760236316537328381084197897448606320128599404475720903510747183168167861796280734776480186673766400), (1310789, -5723685829264442364394225572568010881278923288860352443814990287623699639732633058521642558327618734411436698372037664581786369834792960), (1310801, -591910039939842217008738630425025213594443099857970173581888427968861174852356972241850693507228782455119619857903257588145383723497748480), (1310978, 32427863001907748270056817870016724309114454511812377415060141355320433085806142431768372073936247987977262758425914810554628704766976000), (1310981, -4088347020903173117424446837548579200913516634900251745582135919731214028380452184658316113091156238865311927408598331844133121310566400), (1310993, -422792885671315869291956164589303723996030785612835838272777448549186553465969265887036209648020558896514014184216612562960988373926963200), (1311041, 124093065808094450317126473398187294842404486311404579048975540321038762009156970386537153467431125418685721365559184319976072061548339200), (1311044, 372279197424283350951379420194561884527213458934213737146926620963116286027470911159611460402293376256057164096677552959928216184645017600), (1311056, 496372263232377801268505893592749179369617945245618316195902161284155048036627881546148613869724501674742885462236737279904288246193356800), (1311104, 248186131616188900634252946796374589684808972622809158097951080642077524018313940773074306934862250837371442731118368639952144123096678400), (1311296, 124093065808094450317126473398187294842404486311404579048975540321038762009156970386537153467431125418685721365559184319976072061548339200), (1311746, 6485572600381549654011363574003344861822890902362475483012028271064086617161228486353674414787249597595452551685182962110925740953395200), (1311749, -817669404180634623484889367509715840182703326980050349116427183946242805676090436931663222618231247773062385481719666368826624262113280), (1311761, -84558577134263173858391232917860744799206157122567167654555489709837310693193853177407241929604111779302802836843322512592197674785392640), (1312064, 62046532904047225158563236699093647421202243155702289524487770160519381004578485193268576733715562709342860682779592159988036030774169600), (1314818, -6485572600381549654011363574003344861822890902362475483012028271064086617161228486353674414787249597595452551685182962110925740953395200), (1314821, 817669404180634623484889367509715840182703326980050349116427183946242805676090436931663222618231247773062385481719666368826624262113280), (1314833, 84558577134263173858391232917860744799206157122567167654555489709837310693193853177407241929604111779302802836843322512592197674785392640), (1315136, -186139598712141675475689710097280942263606729467106868573463310481558143013735455579805730201146688128028582048338776479964108092322508800), (1327106, -145788055414802833179470002368326222003185141482796231712273981648027317495760952910273712671510994350371890753828739316490289413790720000), (1327109, -165951941598439454246695329909915667340192513821575529700238624519329112586551763533099694783270963304726630065695638427059357942225049600), (1327121, 196072500845525699473129795592684728607889411670868129678349767963772784646059644930025528452871066171724758193410963551089666955879475200), (1327169, -198380336722566398591473072872041620964623702199221745020124220512237047717420918337384346045755806134190598991954942885387406240791552000), (1327361, -141700240516118856136766480622886872117588358713729817871517300365883605512443513098131675746968432952993284994253530632419575886279680000), (1327424, -310232664520236125792816183495468237106011215778511447622438850802596905022892425966342883668577813546714303413897960799940180153870848000), (1328129, -28340048103223771227353296124577374423517671742745963574303460073176721102488702619626335149393686590598656998850706126483915177255936000), (1331201, 28340048103223771227353296124577374423517671742745963574303460073176721102488702619626335149393686590598656998850706126483915177255936000), (1343489, 141700240516118856136766480622886872117588358713729817871517300365883605512443513098131675746968432952993284994253530632419575886279680000), (1376258, -78852573189875474030160065952053001709151914953505353499533159998140111484811074891388508533684322502173972049780160357058459460076134400), (1376261, -23364605042036579104722686371446904367474515305544158086589513682328812644455213838923189197334532955764787157584793549770752068884346880), (1376273, 720062354635485510437405508688700907287363620438618360586149596271409132378024641568254299765238853766095427362362875217209523490077378560), (1376321, -35844234626272672502101139125540071417305319456425379766743584727485830878130032399859517901048383216676073398073648971605223635117260800), (1376513, -25603024733051908930072242232528622440932371040303842690531131948204164912950023142756798500748845154768623855766892122575159739369472000), (1376576, -558418796136425026427069130291842826790820188401320605720389931444674429041206366739417190603440064384085746145016329439892324276967526400), (1377281, -5120604946610381786014448446505724488186474208060768538106226389640832982590004628551359700149769030953724771153378424515031947873894400), (1380353, 5120604946610381786014448446505724488186474208060768538106226389640832982590004628551359700149769030953724771153378424515031947873894400), (1392641, 280663457662065849976251907353724992252591416725017514859262272606794654835348346719393814845292024470156536845423247260930396334672896000), (1441793, 46085444519493436074130036018551520393678267872546916842956037506767496843310041656962237301347921278583522940380405820635287530865049600), (1572867, -2026490785275656967013254023903258439137717575584958975407642763663918678944071938577035406260590464407820971255878370186201635472588800), (1572870, -9085532948515903652025571608502531618543449637887262264945696560710373084745320957780100353951670368107907554848160803147906643792363520), (1572873, -9068695155903627302258535858971465939755309911764735702751348622821742599493819574871820866841177007244264146946514871802906285875220480), (1572882, -12017847824575557961669976534225586137927114707687767173814594806506676584536386354822966163260513566091256885248896752737956079410728960), (1572885, -24038892922241202444476583874923891809151265883796421438167428749197248972630789816332437515230568298905774610034396514285537593865287680), (1572897, -15929732508048488055286936972838138519303359113035698445998618558357678453296484955337790701478665274551229885474280024731105616931102720), (1572930, -3546358874232399692273194541830702268491005757273678206963374836411857688152125892509811960956033312713686699697787147825852862077030400), (1572933, -10580144348554231852634958502133376929714528230392191653209906726625366366076122837350457677981373175118308171437600683770057333521090560), (1572945, -13938515944542427048376069851233371204390439223906236140248791238562968646634424335920566863793832115232326149789995021639717414814714880), (1573122, -2533113481594571208766567529879073048922146969481198719259553454579898348680089923221294257825738080509776214069847962732752044340736000), (1573125, -7557245963253022751882113215809554949796091593137279752292790519018118832911516312393184055700980839370220122455429059835755238229350400), (1573137, -9956082817530305034554335608023836574564599445647311528749136598973549033310303097086119188424165796594518678421425015456941010581939200), (1573185, -6894059211560802795395915188788183046800249239522476613831974462279931222730942799252064081523951412149206742531065795554226225641574400), (1573188, -20682177634682408386187745566364549140400747718567429841495923386839793668192828397756192244571854236447620227593197386662678676924723200), (1573200, -27576236846243211181583660755152732187200996958089906455327897849119724890923771197008256326095805648596826970124263182216904902566297600), (1573248, -13788118423121605590791830377576366093600498479044953227663948924559862445461885598504128163047902824298413485062131591108452451283148800), (1573440, -6894059211560802795395915188788183046800249239522476613831974462279931222730942799252064081523951412149206742531065795554226225641574400), (1573890, -506622696318914241753313505975814609784429393896239743851910690915979669736017984644258851565147616101955242813969592546550408868147200), (1573893, -1511449192650604550376422643161910989959218318627455950458558103803623766582303262478636811140196167874044024491085811967151047645870080), (1573905, -1991216563506061006910867121604767314912919889129462305749827319794709806662060619417223837684833159318903735684285003091388202116387840), (1574208, -3447029605780401397697957594394091523400124619761238306915987231139965611365471399626032040761975706074603371265532897777113112820787200), (1576962, 506622696318914241753313505975814609784429393896239743851910690915979669736017984644258851565147616101955242813969592546550408868147200), (1576965, 1511449192650604550376422643161910989959218318627455950458558103803623766582303262478636811140196167874044024491085811967151047645870080), (1576977, 1991216563506061006910867121604767314912919889129462305749827319794709806662060619417223837684833159318903735684285003091388202116387840), (1577280, 10341088817341204193093872783182274570200373859283714920747961693419896834096414198878096122285927118223810113796598693331339338462361600), (1589250, 2533113481594571208766567529879073048922146969481198719259553454579898348680089923221294257825738080509776214069847962732752044340736000), (1589253, 7557245963253022751882113215809554949796091593137279752292790519018118832911516312393184055700980839370220122455429059835755238229350400), (1589265, 9956082817530305034554335608023836574564599445647311528749136598973549033310303097086119188424165796594518678421425015456941010581939200), (1589568, 17235148028902006988489787971970457617000623098806191534579936155699828056827356998130160203809878530373016856327664488885565564103936000), (1638402, 4559604266870228175779821553782331488059864545066157694667196218243817027624161861798329664086328544917597185325726332918953679813324800), (1638405, 13603042733855440953387803788457198909632964867647103554127022934232613899240729362307731300261765510866396220419772307704359428812830720), (1638417, 17920949071554549062197804094442905834216279002165160751748445878152388259958545574755014539163498433870133621158565027822493819047490560), (1638720, 31023266452023612579281618349546823710601121577851144762243885080259690502289242596634288366857781354671430341389796079994018015387084800), (2097155, -5267271866717813395096559067122636228593676375539679812644728330847094876174190474485969826770814984479483637932539407453963237346508800), (2097158, -44579436500706040691368411687203933723680389941938737855992211052940005375205860281663130923901942607236822710758949360950454191355330560), (2097161, -55017793050943980898085359629779969071184813067943827205537677835004044591416861854901264275618580195776395880790210374654264003003351040), (2097170, -70527730862013823882617384855799597708948138824290665264520155974446534573259539473133018949923827951407419631632480563993204050822104832), (2097173, -163346838094125936836083546255371446639220929867075394732896286082467243353255886926109971312064737234707873041371383123166935034864765568), (2097185, -119986374257156394184848533443108650503521572146422611278461398625504689641822317048322158592764395964896904711534803498170555152258174464), (2097218, -9217725766756173441418978367464613400038933657194439672128274578982416033304833330350447196848926222839096366381943963044435665356390400), (2097221, -64187425226101311047766252901409963916382281912601131739793957474171385356653005497384808321555010228405795194255245437096641336837242880), (2097233, -104988077475011844911742466762720069190581375628119784868653723797316603436594527417281888768668846469284791622592953060899235758225902656), (2097410, -6584089833397266743870698833903295285742095469424599765805910413558868595217738093107462283463518730599354547415674259317454046683136000), (2097413, -45848160875786650748404466358149974225987344223286522671281398195836703826180718212417720229682150163146996567325175312211886669169459200), (2097425, -74991483910722746365530333401942906564700982591514132049038374140940431026138948155201349120477747478060565444709252186356596970161359040), (2098178, -1316817966679453348774139766780659057148419093884919953161182082711773719043547618621492456692703746119870909483134851863490809336627200), (2098181, -9169632175157330149680893271629994845197468844657304534256279639167340765236143642483544045936430032629399313465035062442377333833891840), (2098193, -14998296782144549273106066680388581312940196518302826409807674828188086205227789631040269824095549495612113088941850437271319394032271808), (2101250, 1316817966679453348774139766780659057148419093884919953161182082711773719043547618621492456692703746119870909483134851863490809336627200), (2101253, 9169632175157330149680893271629994845197468844657304534256279639167340765236143642483544045936430032629399313465035062442377333833891840), (2101265, 14998296782144549273106066680388581312940196518302826409807674828188086205227789631040269824095549495612113088941850437271319394032271808), (2113538, -53617844117761884952524417763552280652325591934937293189886581195010272578309515286400523585908185283961348631158370076491294837385625600), (2113541, -44454740050952076796188208538033389681114186883256316762257339217017007934110161856844258574375405858694058200535891191501236656933683200), (2113553, -45412383991595557027259899792968245311434392217209653862346609076197851320915558603814622618265660551060840912438836485260900797976164160), (2113601, -105353384414528515468691454045547257891618452957633312672461860314995997053672693414138975271400482025481230562504577587665310547120332800), (2113793, -75252417438948939620493895746819469922584609255452366194615614510711426466909066724384982336714630018200878973217555419760936105085952000), (2114561, -15050483487789787924098779149363893984516921851090473238923122902142285293381813344876996467342926003640175794643511083952187221017190400), (2117633, 15050483487789787924098779149363893984516921851090473238923122902142285293381813344876996467342926003640175794643511083952187221017190400), (2129921, 75252417438948939620493895746819469922584609255452366194615614510711426466909066724384982336714630018200878973217555419760936105085952000), (2162690, 11851361700115080138967257901025931514335771844964279578450638744405963471391928567593432110234333715078838185348213666771417284029644800), (2162693, 82526689576415971347128039444669953606777219601915740808306516752506066887125292782351896413427870293664593821185315561981396004505026560), (2162705, 134984671039300943457954600123497231816461768664725437688269073453692775847050106679362428416859945460509017800476653935441874546290446272), (2179073, 135454351390108091316889012344275045860652296659814259150308106119280567640436320103892968206086334032761582151791599755569684989154713600), (2359299, -1013245392637828483506627011951629219568858787792479487703821381831959339472035969288517703130295232203910485627939185093100817736294400), (2359302, -5609298780415150288094906780789360608352757613693794287715122419087851342556797331861856196479279076838555550352054801641623164875427840), (2359305, -6134146037187611344252449394292875168499204148007612584239085519509868500023115066893619462675754342799034732865219036002957907406479360), (2359314, -10171681556997072465540077220810103226729452887138788313007307841963939097915174935121350386112724205841921354417106343640957558942842880), (2359317, -20396647540498938373460167321084100739386541831340894118718278310129855295154141250674631753345873069216530218562134008186077761747353600), (2359329, -16290381543442830997053646393813689575183470623107658675199330156600040837942205993088629959704267482868200766322455946909511846940508160), (2359362, -1773179437116199846136597270915351134245502878636839103481687418205928844076062946254905980478016656356843349848893573912926431038515200), (2359365, -7156503710052213234961190960008354363249071506008881348278933106094846583360300911375889373121713399932207188342755542003450891974225920), (2359377, -14254083850512477122421940594586978378285536795219201340799413887025035733199430243952551214741234047509675670532148953545822866072944640), (2359554, -1266556740797285604383283764939536524461073484740599359629776727289949174340044961610647128912869040254888107034923981366376022170368000), (2359557, -5111788364323009453543707828577395973749336790006343820199237932924890416685929222411349552229795285665862277387682530002464922838732800), (2359569, -10181488464651769373158528996133555984489669139442286671999581347875025523713878745680393724815167176792625478951534966818444904337817600), (2359617, -3447029605780401397697957594394091523400124619761238306915987231139965611365471399626032040761975706074603371265532897777113112820787200), (2359620, -10341088817341204193093872783182274570200373859283714920747961693419896834096414198878096122285927118223810113796598693331339338462361600), (2359632, -13788118423121605590791830377576366093600498479044953227663948924559862445461885598504128163047902824298413485062131591108452451283148800), (2359680, -6894059211560802795395915188788183046800249239522476613831974462279931222730942799252064081523951412149206742531065795554226225641574400), (2359872, -3447029605780401397697957594394091523400124619761238306915987231139965611365471399626032040761975706074603371265532897777113112820787200), (2360322, -253311348159457120876656752987907304892214696948119871925955345457989834868008992322129425782573808050977621406984796273275204434073600), (2360325, -1022357672864601890708741565715479194749867358001268764039847586584978083337185844482269910445959057133172455477536506000492984567746560), (2360337, -2036297692930353874631705799226711196897933827888457334399916269575005104742775749136078744963033435358525095790306993363688980867563520), (2360640, -1723514802890200698848978797197045761700062309880619153457993615569982805682735699813016020380987853037301685632766448888556556410393600), (2363394, 253311348159457120876656752987907304892214696948119871925955345457989834868008992322129425782573808050977621406984796273275204434073600), (2363397, 1022357672864601890708741565715479194749867358001268764039847586584978083337185844482269910445959057133172455477536506000492984567746560), (2363409, 2036297692930353874631705799226711196897933827888457334399916269575005104742775749136078744963033435358525095790306993363688980867563520), (2363712, 5170544408670602096546936391591137285100186929641857460373980846709948417048207099439048061142963559111905056898299346665669669231180800), (2375682, 1266556740797285604383283764939536524461073484740599359629776727289949174340044961610647128912869040254888107034923981366376022170368000), (2375685, 5111788364323009453543707828577395973749336790006343820199237932924890416685929222411349552229795285665862277387682530002464922838732800), (2375697, 10181488464651769373158528996133555984489669139442286671999581347875025523713878745680393724815167176792625478951534966818444904337817600), (2376000, 8617574014451003494244893985985228808500311549403095767289968077849914028413678499065080101904939265186508428163832244442782782051968000), (2424834, 2279802133435114087889910776891165744029932272533078847333598109121908513812080930899164832043164272458798592662863166459476839906662400), (2424837, 9201219055781417016378674091439312752748806222011418876358628279264802750034672600340429194013631514198552099297828554004436861109719040), (2424849, 18326679236373184871685352193040400772081404450996116009599246426175045942684981742224708704667300918226725862112762940273200827808071680), (2425152, 15511633226011806289640809174773411855300560788925572381121942540129845251144621298317144183428890677335715170694898039997009007693542400), (3145734, -711021537438132308054747317692063199387355196500108770161516092488443200122757901981204013002295928523067848618649600045113228652830720), (3145737, -1066532306157198462082120976538094799081032794750163155242274138732664800184136852971806019503443892784601772927974400067669842979246080), (3145749, -1422043074876264616109494635384126398774710393000217540323032184976886400245515803962408026004591857046135697237299200090226457305661440), (3145797, -1244287690516731539095807805961110598927871593875190347782653161854775600214826328467107022754017874915368735082636800078948150142453760), (3145989, -888776921797665385068434147115078999234193995625135962701895115610554000153447377476505016252869910653834810773312000056391535816038400), (3146757, -177755384359533077013686829423015799846838799125027192540379023122110800030689475495301003250573982130766962154662400011278307163207680), (3149829, 177755384359533077013686829423015799846838799125027192540379023122110800030689475495301003250573982130766962154662400011278307163207680), (3162117, 888776921797665385068434147115078999234193995625135962701895115610554000153447377476505016252869910653834810773312000056391535816038400), (3211269, 1599798459235797693123181464807142198621549192125244732863411208098997200276205279457709029255165839176902659391961600101504764468869120)]
theorem sparseBlock042_data : sparseBlock042 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (861757401445100349424489398598522880850031154940309576728996807784991402841367849906508010190493926518650842816383224444278278205196800 : Int) coeff0447) (CoefficientMerge.scale (658408983339726674387069883390329528574209546942459976580591041355886859521773809310746228346351873059935454741567425931745404668313600 : Int) coeff0448)) (CoefficientMerge.merge (CoefficientMerge.scale (126655674079728560438328376493953652446107348474059935962977672728994917434004496161064712891286904025488810703492398136637602217036800 : Int) coeff0449) (CoefficientMerge.merge (CoefficientMerge.scale (7864791631036845303138505937941868004866019090638020030340052733482501721063107760565960147206480176532580899480216323787467686828544000 : Int) coeff0450) (CoefficientMerge.scale (15611675895181555958253429937019199028345865723262373461548647734304732502354979860231271940826046973929830072552593740990277505412756480 : Int) coeff0451)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (7784413006050260461086809565429281819841832806579141732854962235781664783170482380157190081478546694668504975516440731424198195854684160 : Int) coeff0452) (CoefficientMerge.scale (333423452072767868340683953434723797528094879875607189479544770170378241637903446745833951972405546435819265584105852988968185120665600 : Int) coeff0453)) (CoefficientMerge.merge (CoefficientMerge.scale (88877692179766538506843414711507899923419399562513596270189511561055400015344737747650501625286991065383481077331200005639153581603840 : Int) coeff0454) (CoefficientMerge.merge (CoefficientMerge.scale (52827965276912183127386686605735799309847286425365782719102222698244522751156390924712440908186492238619735180905655930582327791325163520 : Int) coeff0455) (CoefficientMerge.scale (42279288567131586929195616458930372399603078561283583827277744854918655346596926588703620964802055889651401418421661256296098837392696320 : Int) coeff0456))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (7499148391072274636553033340194290656470098259151413204903837414094043102613894815520134912047774747806056544470925218635659697016135904 : Int) coeff0457) (CoefficientMerge.scale (995608281753030503455433560802383657456459944564731152874913659897354903331030309708611918842416579659451867842142501545694101058193920 : Int) coeff0458)) (CoefficientMerge.merge (CoefficientMerge.scale (1018148846465176937315852899613355598448966913944228667199958134787502552371387874568039372481516717679262547895153496681844490433781760 : Int) coeff0459) (CoefficientMerge.merge (CoefficientMerge.scale (7741726110164512147773718206347325146849974383231592981774279386921726310935448102404688097863652487204027093444792297176890228989542400 : Int) coeff0460) (CoefficientMerge.scale (14170024051611885613676648062288687211758835871372981787151730036588360551244351309813167574696843295299328499425353063241957588627968000 : Int) coeff0461)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (7525241743894893962049389574681946992258460925545236619461561451071142646690906672438498233671463001820087897321755541976093610508595200 : Int) coeff0462) (CoefficientMerge.scale (91387556983484502796778805460387925271337423922971514960687431735335400525033416283777128908807662574179431477133912578474747493567488000 : Int) coeff0463)) (CoefficientMerge.merge (CoefficientMerge.scale (90958473505436894106801828669134099230567354187896826944656795004578976421792432378511828668212538987113800239413386634296599861011046400 : Int) coeff0464) (CoefficientMerge.merge (CoefficientMerge.scale (1268232251151272982893140534091602620914116614929784134081261132666974242779696048658248251687577713653274769518329996568253886064128000 : Int) coeff0465) (CoefficientMerge.scale (2560302473305190893007224223252862244093237104030384269053113194820416491295002314275679850074884515476862385576689212257515973936947200 : Int) coeff0466)))))) := by decide +kernel
theorem sparseBlock042_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock042 := by
  rw [sparseBlock042_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted0447_nonneg g t z hg hA hB ht hz hw) (weighted0448_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0449_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0450_nonneg g t z hg hA hB ht hz hw) (weighted0451_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0452_nonneg g t z hg hA hB ht hz hw) (weighted0453_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0454_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0455_nonneg g t z hg hA hB ht hz hw) (weighted0456_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted0457_nonneg g t z hg hA hB ht hz hw) (weighted0458_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0459_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0460_nonneg g t z hg hA hB ht hz hw) (weighted0461_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0462_nonneg g t z hg hA hB ht hz hw) (weighted0463_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0464_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0465_nonneg g t z hg hA hB ht hz hw) (weighted0466_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
