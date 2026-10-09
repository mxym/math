import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff0210 : CoefficientMerge.Poly :=
  [(278530, -1296), (278533, -3888), (278545, -5184), (278593, -2592), (278785, -1296), (279553, 1296), (282625, 1944), (294913, 3240), (344065, 5832), (540674, 144), (540677, 432), (540689, 576), (540737, 288), (540929, 144), (541697, -144), (544769, -216), (557057, -360), (606209, -648), (802818, -4), (802821, -12), (802833, -16), (802881, -8), (803073, -4), (803841, 4), (806913, 6), (819201, 10), (868353, 18), (1327106, 144), (1327109, 432), (1327121, 576), (1327169, 288), (1327361, 144), (1328129, -144), (1331201, -216), (1343489, -360), (1392641, -648), (1589250, -8), (1589253, -24), (1589265, -32), (1589313, -16), (1589505, -8), (1590273, 8), (1593345, 12), (1605633, 20), (1654785, 36), (2375682, -4), (2375685, -12), (2375697, -16), (2375745, -8), (2375937, -4), (2376705, 4), (2379777, 6), (2392065, 10), (2441217, 18)]
noncomputable def atom0210 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![2,1,2] * g 0 * g 7) * t * (t+z-18) * (t+z-18))
theorem atom0210_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0210 g t z = CoefficientMerge.eval (monomial g t z) coeff0210 := by
  norm_num [atom0210, coeff0210, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0210_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0210 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![2,1,2]
  dsimp only [atom0210]
  positivity
theorem weighted0210_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (302080738150252967485449493446916340005744127353062104684207886265115573923787642368587503594370296892888646707200229565699803959193600 : Int) coeff0210) := by
  rw [CoefficientMerge.eval_scale, ← atom0210_identity]
  exact mul_nonneg (by norm_num) (atom0210_nonneg g t z hg hA hB ht hz hw)

def coeff0211 : CoefficientMerge.Poly :=
  [(1064962, -1296), (1064965, -3888), (1064977, -5184), (1065025, -2592), (1065217, -1296), (1065985, 1296), (1069057, 1944), (1081345, 3240), (1130497, 5832), (1327106, 144), (1327109, 432), (1327121, 576), (1327169, 288), (1327361, 144), (1328129, -144), (1331201, -216), (1343489, -360), (1392641, -648), (1589250, -4), (1589253, -12), (1589265, -16), (1589313, -8), (1589505, -4), (1590273, 4), (1593345, 6), (1605633, 10), (1654785, 18), (2113538, 144), (2113541, 432), (2113553, 576), (2113601, 288), (2113793, 144), (2114561, -144), (2117633, -216), (2129921, -360), (2179073, -648), (2375682, -8), (2375685, -24), (2375697, -32), (2375745, -16), (2375937, -8), (2376705, 8), (2379777, 12), (2392065, 20), (2441217, 36), (3162114, -4), (3162117, -12), (3162129, -16), (3162177, -8), (3162369, -4), (3163137, 4), (3166209, 6), (3178497, 10), (3227649, 18)]
noncomputable def atom0211 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![2,1,2] * g 0 * g 7) * z * (t+z-18) * (t+z-18))
theorem atom0211_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0211 g t z = CoefficientMerge.eval (monomial g t z) coeff0211 := by
  norm_num [atom0211, coeff0211, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0211_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0211 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![2,1,2]
  dsimp only [atom0211]
  positivity
theorem weighted0211_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (163148273291279799429114868895717717650837002958922201457408091698378673983090694721753866238418258219389472070936148492432118082421760 : Int) coeff0211) := by
  rw [CoefficientMerge.eval_scale, ← atom0211_identity]
  exact mul_nonneg (by norm_num) (atom0211_nonneg g t z hg hA hB ht hz hw)

def coeff0212 : CoefficientMerge.Poly :=
  [(262165, -1296), (262168, -3888), (262180, -5184), (262228, -2592), (262420, -1296), (263188, 1296), (266260, 1944), (278548, 3240), (327700, 5832), (524309, 144), (524312, 432), (524324, 576), (524372, 288), (524564, 144), (525332, -144), (528404, -216), (540692, -360), (589844, -648), (786453, -4), (786456, -12), (786468, -16), (786516, -8), (786708, -4), (787476, 4), (790548, 6), (802836, 10), (851988, 18), (1310741, 144), (1310744, 432), (1310756, 576), (1310804, 288), (1310996, 144), (1311764, -144), (1314836, -216), (1327124, -360), (1376276, -648), (1572885, -8), (1572888, -24), (1572900, -32), (1572948, -16), (1573140, -8), (1573908, 8), (1576980, 12), (1589268, 20), (1638420, 36), (2359317, -4), (2359320, -12), (2359332, -16), (2359380, -8), (2359572, -4), (2360340, 4), (2363412, 6), (2375700, 10), (2424852, 18)]
noncomputable def atom0212 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![2,1,2] * g 1 * g 2) * t * (t+z-18) * (t+z-18))
theorem atom0212_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0212 g t z = CoefficientMerge.eval (monomial g t z) coeff0212 := by
  norm_num [atom0212, coeff0212, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0212_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0212 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![2,1,2]
  dsimp only [atom0212]
  positivity
theorem weighted0212_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2074364573271987607256884602126563582690968847153188271508225891425439020994667652690839752536602182429238539225206994222545853944524800 : Int) coeff0212) := by
  rw [CoefficientMerge.eval_scale, ← atom0212_identity]
  exact mul_nonneg (by norm_num) (atom0212_nonneg g t z hg hA hB ht hz hw)

def coeff0213 : CoefficientMerge.Poly :=
  [(1048597, -1296), (1048600, -3888), (1048612, -5184), (1048660, -2592), (1048852, -1296), (1049620, 1296), (1052692, 1944), (1064980, 3240), (1114132, 5832), (1310741, 144), (1310744, 432), (1310756, 576), (1310804, 288), (1310996, 144), (1311764, -144), (1314836, -216), (1327124, -360), (1376276, -648), (1572885, -4), (1572888, -12), (1572900, -16), (1572948, -8), (1573140, -4), (1573908, 4), (1576980, 6), (1589268, 10), (1638420, 18), (2097173, 144), (2097176, 432), (2097188, 576), (2097236, 288), (2097428, 144), (2098196, -144), (2101268, -216), (2113556, -360), (2162708, -648), (2359317, -8), (2359320, -24), (2359332, -32), (2359380, -16), (2359572, -8), (2360340, 8), (2363412, 12), (2375700, 20), (2424852, 36), (3145749, -4), (3145752, -12), (3145764, -16), (3145812, -8), (3146004, -4), (3146772, 4), (3149844, 6), (3162132, 10), (3211284, 18)]
noncomputable def atom0213 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![2,1,2] * g 1 * g 2) * z * (t+z-18) * (t+z-18))
theorem atom0213_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0213 g t z = CoefficientMerge.eval (monomial g t z) coeff0213 := by
  norm_num [atom0213, coeff0213, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0213_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0213 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![2,1,2]
  dsimp only [atom0213]
  positivity
theorem weighted0213_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1182218810111979854753029093676072737724960110582129993910943802781910247334087964322061401651322203373179575838365216316580423778124800 : Int) coeff0213) := by
  rw [CoefficientMerge.eval_scale, ← atom0213_identity]
  exact mul_nonneg (by norm_num) (atom0213_nonneg g t z hg hA hB ht hz hw)

def coeff0214 : CoefficientMerge.Poly :=
  [(786693, -4), (786696, -12), (786708, -16), (786756, -8), (786948, -4), (787716, 4), (790788, 6), (803076, 10), (852228, 18)]
noncomputable def atom0214 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![2,1,2] * g 1 * g 4) * t * t * t)
theorem atom0214_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0214 g t z = CoefficientMerge.eval (monomial g t z) coeff0214 := by
  norm_num [atom0214, coeff0214, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0214_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0214 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![2,1,2]
  dsimp only [atom0214]
  positivity
theorem weighted0214_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1620433412216461472169057616185086061967715336423315220917135199552744537153608712989697868214146417962384326661753311774689053283968000 : Int) coeff0214) := by
  rw [CoefficientMerge.eval_scale, ← atom0214_identity]
  exact mul_nonneg (by norm_num) (atom0214_nonneg g t z hg hA hB ht hz hw)

def coeff0215 : CoefficientMerge.Poly :=
  [(1573125, -4), (1573128, -12), (1573140, -16), (1573188, -8), (1573380, -4), (1574148, 4), (1577220, 6), (1589508, 10), (1638660, 18)]
noncomputable def atom0215 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![2,1,2] * g 1 * g 4) * t * t * z)
theorem atom0215_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0215 g t z = CoefficientMerge.eval (monomial g t z) coeff0215 := by
  norm_num [atom0215, coeff0215, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0215_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0215 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![2,1,2]
  dsimp only [atom0215]
  positivity
theorem weighted0215_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4861300236649384416507172848555258185903146009269945662751405598658233611460826138969093604642439253887152979985259935324067159851904000 : Int) coeff0215) := by
  rw [CoefficientMerge.eval_scale, ← atom0215_identity]
  exact mul_nonneg (by norm_num) (atom0215_nonneg g t z hg hA hB ht hz hw)

def coeff0216 : CoefficientMerge.Poly :=
  [(2359557, -4), (2359560, -12), (2359572, -16), (2359620, -8), (2359812, -4), (2360580, 4), (2363652, 6), (2375940, 10), (2425092, 18)]
noncomputable def atom0216 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![2,1,2] * g 1 * g 4) * t * z * z)
theorem atom0216_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0216 g t z = CoefficientMerge.eval (monomial g t z) coeff0216 := by
  norm_num [atom0216, coeff0216, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0216_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0216 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![2,1,2]
  dsimp only [atom0216]
  positivity
theorem weighted0216_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4861300236649384416507172848555258185903146009269945662751405598658233611460826138969093604642439253887152979985259935324067159851904000 : Int) coeff0216) := by
  rw [CoefficientMerge.eval_scale, ← atom0216_identity]
  exact mul_nonneg (by norm_num) (atom0216_nonneg g t z hg hA hB ht hz hw)

def coeff0217 : CoefficientMerge.Poly :=
  [(3145989, -4), (3145992, -12), (3146004, -16), (3146052, -8), (3146244, -4), (3147012, 4), (3150084, 6), (3162372, 10), (3211524, 18)]
noncomputable def atom0217 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![2,1,2] * g 1 * g 4) * z * z * z)
theorem atom0217_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0217 g t z = CoefficientMerge.eval (monomial g t z) coeff0217 := by
  norm_num [atom0217, coeff0217, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0217_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0217 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![2,1,2]
  dsimp only [atom0217]
  positivity
theorem weighted0217_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1620433412216461472169057616185086061967715336423315220917135199552744537153608712989697868214146417962384326661753311774689053283968000 : Int) coeff0217) := by
  rw [CoefficientMerge.eval_scale, ← atom0217_identity]
  exact mul_nonneg (by norm_num) (atom0217_nonneg g t z hg hA hB ht hz hw)

def coeff0218 : CoefficientMerge.Poly :=
  [(790533, -4), (790536, -12), (790548, -16), (790596, -8), (790788, -4), (791556, 4), (794628, 6), (806916, 10), (856068, 18)]
noncomputable def atom0218 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![2,1,2] * g 1 * g 6) * t * t * t)
theorem atom0218_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0218 g t z = CoefficientMerge.eval (monomial g t z) coeff0218 := by
  norm_num [atom0218, coeff0218, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0218_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0218 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![2,1,2]
  dsimp only [atom0218]
  positivity
theorem weighted0218_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (126391773209133864960201860036778854384655847937244214609029618917834320745396782022847541465533468771033569571492771175136544215654400 : Int) coeff0218) := by
  rw [CoefficientMerge.eval_scale, ← atom0218_identity]
  exact mul_nonneg (by norm_num) (atom0218_nonneg g t z hg hA hB ht hz hw)

def coeff0219 : CoefficientMerge.Poly :=
  [(1576965, -4), (1576968, -12), (1576980, -16), (1577028, -8), (1577220, -4), (1577988, 4), (1581060, 6), (1593348, 10), (1642500, 18)]
noncomputable def atom0219 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![2,1,2] * g 1 * g 6) * t * t * z)
theorem atom0219_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0219 g t z = CoefficientMerge.eval (monomial g t z) coeff0219 := by
  norm_num [atom0219, coeff0219, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0219_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0219 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![2,1,2]
  dsimp only [atom0219]
  positivity
theorem weighted0219_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (379175319627401594880605580110336563153967543811732643827088856753502962236190346068542624396600406313100708714478313525409632646963200 : Int) coeff0219) := by
  rw [CoefficientMerge.eval_scale, ← atom0219_identity]
  exact mul_nonneg (by norm_num) (atom0219_nonneg g t z hg hA hB ht hz hw)

def coeff0220 : CoefficientMerge.Poly :=
  [(2363397, -4), (2363400, -12), (2363412, -16), (2363460, -8), (2363652, -4), (2364420, 4), (2367492, 6), (2379780, 10), (2428932, 18)]
noncomputable def atom0220 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![2,1,2] * g 1 * g 6) * t * z * z)
theorem atom0220_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0220 g t z = CoefficientMerge.eval (monomial g t z) coeff0220 := by
  norm_num [atom0220, coeff0220, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0220_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0220 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![2,1,2]
  dsimp only [atom0220]
  positivity
theorem weighted0220_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (379175319627401594880605580110336563153967543811732643827088856753502962236190346068542624396600406313100708714478313525409632646963200 : Int) coeff0220) := by
  rw [CoefficientMerge.eval_scale, ← atom0220_identity]
  exact mul_nonneg (by norm_num) (atom0220_nonneg g t z hg hA hB ht hz hw)

def coeff0221 : CoefficientMerge.Poly :=
  [(802821, -4), (802824, -12), (802836, -16), (802884, -8), (803076, -4), (803844, 4), (806916, 6), (819204, 10), (868356, 18)]
noncomputable def atom0221 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![2,1,2] * g 1 * g 7) * t * t * t)
theorem atom0221_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0221 g t z = CoefficientMerge.eval (monomial g t z) coeff0221 := by
  norm_num [atom0221, coeff0221, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0221_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0221 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![2,1,2]
  dsimp only [atom0221]
  positivity
theorem weighted0221_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (124675308034434056640542940813500365623296638397426680431871567757299757244554321702428855458182707728297503433206705973267414238924800 : Int) coeff0221) := by
  rw [CoefficientMerge.eval_scale, ← atom0221_identity]
  exact mul_nonneg (by norm_num) (atom0221_nonneg g t z hg hA hB ht hz hw)

def coeff0222 : CoefficientMerge.Poly :=
  [(2375685, -4), (2375688, -12), (2375700, -16), (2375748, -8), (2375940, -4), (2376708, 4), (2379780, 6), (2392068, 10), (2441220, 18)]
noncomputable def atom0222 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![2,1,2] * g 1 * g 7) * t * z * z)
theorem atom0222_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0222 g t z = CoefficientMerge.eval (monomial g t z) coeff0222 := by
  norm_num [atom0222, coeff0222, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0222_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0222 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![2,1,2]
  dsimp only [atom0222]
  positivity
theorem weighted0222_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (120136678552553017099764116322921673441469994476288628054619998449189510367927828173659452323736394195150298652822884562953297447557800 : Int) coeff0222) := by
  rw [CoefficientMerge.eval_scale, ← atom0222_identity]
  exact mul_nonneg (by norm_num) (atom0222_nonneg g t z hg hA hB ht hz hw)

def coeff0223 : CoefficientMerge.Poly :=
  [(1376261, -4), (1376264, -12), (1376276, -16), (1376324, -8), (1376516, -4), (1377284, 4), (1380356, 6), (1392644, 10), (1441796, 18)]
noncomputable def atom0223 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![2,1,2] * g 1 * g 8) * t * z)
theorem atom0223_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0223 g t z = CoefficientMerge.eval (monomial g t z) coeff0223 := by
  norm_num [atom0223, coeff0223, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0223_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0223 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![2,1,2]
  dsimp only [atom0223]
  positivity
theorem weighted0223_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (530583151014605916106118724890416416237776061061499696091559796971219228970560474052917591141110206108992768835275079630960407099491840 : Int) coeff0223) := by
  rw [CoefficientMerge.eval_scale, ← atom0223_identity]
  exact mul_nonneg (by norm_num) (atom0223_nonneg g t z hg hA hB ht hz hw)

def coeff0224 : CoefficientMerge.Poly :=
  [(2162693, -4), (2162696, -12), (2162708, -16), (2162756, -8), (2162948, -4), (2163716, 4), (2166788, 6), (2179076, 10), (2228228, 18)]
noncomputable def atom0224 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![2,1,2] * g 1 * g 8) * z * z)
theorem atom0224_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0224 g t z = CoefficientMerge.eval (monomial g t z) coeff0224 := by
  norm_num [atom0224, coeff0224, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0224_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0224 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![2,1,2]
  dsimp only [atom0224]
  positivity
theorem weighted0224_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (361703812439631789232633676306637832608838278264952338682907239653766220516814211839465295775700668388341657836990165634712709382369280 : Int) coeff0224) := by
  rw [CoefficientMerge.eval_scale, ← atom0224_identity]
  exact mul_nonneg (by norm_num) (atom0224_nonneg g t z hg hA hB ht hz hw)

def coeff0225 : CoefficientMerge.Poly :=
  [(528401, -4), (528404, -12), (528416, -16), (528464, -8), (528656, -4), (529424, 4), (532496, 6), (544784, 10), (593936, 18)]
noncomputable def atom0225 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![2,1,2] * g 2 * g 6) * t * t)
theorem atom0225_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0225 g t z = CoefficientMerge.eval (monomial g t z) coeff0225 := by
  norm_num [atom0225, coeff0225, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0225_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0225 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![2,1,2]
  dsimp only [atom0225]
  positivity
theorem weighted0225_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (30033996974471439599236730607646656279075212032084873588133445658884268632271520538063836156521970008503322334981305470439363564784778240 : Int) coeff0225) := by
  rw [CoefficientMerge.eval_scale, ← atom0225_identity]
  exact mul_nonneg (by norm_num) (atom0225_nonneg g t z hg hA hB ht hz hw)

def coeff0226 : CoefficientMerge.Poly :=
  [(1314833, -4), (1314836, -12), (1314848, -16), (1314896, -8), (1315088, -4), (1315856, 4), (1318928, 6), (1331216, 10), (1380368, 18)]
noncomputable def atom0226 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![2,1,2] * g 2 * g 6) * t * z)
theorem atom0226_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0226 g t z = CoefficientMerge.eval (monomial g t z) coeff0226 := by
  norm_num [atom0226, coeff0226, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0226_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0226 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![2,1,2]
  dsimp only [atom0226]
  positivity
theorem weighted0226_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (115739470610472713688421666705563418458903813180334970265171016930394534972025219352802288037347028868978352476038000418392398094442383360 : Int) coeff0226) := by
  rw [CoefficientMerge.eval_scale, ← atom0226_identity]
  exact mul_nonneg (by norm_num) (atom0226_nonneg g t z hg hA hB ht hz hw)

def coeff0227 : CoefficientMerge.Poly :=
  [(1052689, -1296), (1052692, -3888), (1052704, -5184), (1052752, -2592), (1052944, -1296), (1053712, 1296), (1056784, 1944), (1069072, 3240), (1118224, 5832), (1314833, 144), (1314836, 432), (1314848, 576), (1314896, 288), (1315088, 144), (1315856, -144), (1318928, -216), (1331216, -360), (1380368, -648), (1576977, -4), (1576980, -12), (1576992, -16), (1577040, -8), (1577232, -4), (1578000, 4), (1581072, 6), (1593360, 10), (1642512, 18), (2101265, 144), (2101268, 432), (2101280, 576), (2101328, 288), (2101520, 144), (2102288, -144), (2105360, -216), (2117648, -360), (2166800, -648), (2363409, -8), (2363412, -24), (2363424, -32), (2363472, -16), (2363664, -8), (2364432, 8), (2367504, 12), (2379792, 20), (2428944, 36), (3149841, -4), (3149844, -12), (3149856, -16), (3149904, -8), (3150096, -4), (3150864, 4), (3153936, 6), (3166224, 10), (3215376, 18)]
noncomputable def atom0227 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![2,1,2] * g 2 * g 6) * z * (t+z-18) * (t+z-18))
theorem atom0227_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0227 g t z = CoefficientMerge.eval (monomial g t z) coeff0227 := by
  norm_num [atom0227, coeff0227, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0227_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0227 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![2,1,2]
  dsimp only [atom0227]
  positivity
theorem weighted0227_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1008899277224378567431135524498994446920020494022627104953674042781872188742241319651353512754073805959031338234131842909462450188188400 : Int) coeff0227) := by
  rw [CoefficientMerge.eval_scale, ← atom0227_identity]
  exact mul_nonneg (by norm_num) (atom0227_nonneg g t z hg hA hB ht hz hw)

def coeff0228 : CoefficientMerge.Poly :=
  [(540689, -4), (540692, -12), (540704, -16), (540752, -8), (540944, -4), (541712, 4), (544784, 6), (557072, 10), (606224, 18)]
noncomputable def atom0228 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![2,1,2] * g 2 * g 7) * t * t)
theorem atom0228_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0228 g t z = CoefficientMerge.eval (monomial g t z) coeff0228 := by
  norm_num [atom0228, coeff0228, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0228_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0228 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![2,1,2]
  dsimp only [atom0228]
  positivity
theorem weighted0228_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (137189975124878832879664413489416398832143284444758612498116497779010473918268945808316716333979696307784816749787477782089048017854873600 : Int) coeff0228) := by
  rw [CoefficientMerge.eval_scale, ← atom0228_identity]
  exact mul_nonneg (by norm_num) (atom0228_nonneg g t z hg hA hB ht hz hw)

def coeff0229 : CoefficientMerge.Poly :=
  [(1327121, -4), (1327124, -12), (1327136, -16), (1327184, -8), (1327376, -4), (1328144, 4), (1331216, 6), (1343504, 10), (1392656, 18)]
noncomputable def atom0229 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![2,1,2] * g 2 * g 7) * t * z)
theorem atom0229_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0229 g t z = CoefficientMerge.eval (monomial g t z) coeff0229 := by
  norm_num [atom0229, coeff0229, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0229_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0229 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![2,1,2]
  dsimp only [atom0229]
  positivity
theorem weighted0229_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (263665218522360712275411231563524885376842850855357342144823875986631950809124750039051781580155349083586183838026762970671086228669798400 : Int) coeff0229) := by
  rw [CoefficientMerge.eval_scale, ← atom0229_identity]
  exact mul_nonneg (by norm_num) (atom0229_nonneg g t z hg hA hB ht hz hw)

def sparseBlock018 : CoefficientMerge.Poly :=
  [(262165, -2688376486960495939004922444356026403167495625910531999874660755287368971209089277887328319287436428428293146835868264512419426712104140800), (262168, -8065129460881487817014767333068079209502486877731595999623982265862106913627267833661984957862309285284879440507604793537258280136312422400), (262180, -10753505947841983756019689777424105612669982503642127999498643021149475884836357111549313277149745713713172587343473058049677706848416563200), (262228, -5376752973920991878009844888712052806334991251821063999749321510574737942418178555774656638574872856856586293671736529024838853424208281600), (262420, -2688376486960495939004922444356026403167495625910531999874660755287368971209089277887328319287436428428293146835868264512419426712104140800), (263188, 2688376486960495939004922444356026403167495625910531999874660755287368971209089277887328319287436428428293146835868264512419426712104140800), (266260, 4032564730440743908507383666534039604751243438865797999811991132931053456813633916830992478931154642642439720253802396768629140068156211200), (278530, -391496636642727845861142543507203576647444389049568487670733420599589783805228784509689404658303904773183686132531497517146945931114905600), (278533, -1174489909928183537583427630521610729942333167148705463012200261798769351415686353529068213974911714319551058397594492551440837793344716800), (278545, -1565986546570911383444570174028814306589777556198273950682933682398359135220915138038757618633215619092734744530125990068587783724459622400), (278548, 6720941217401239847512306110890066007918739064776329999686651888218422428022723194718320798218591071070732867089670661281048566780260352000), (278593, -782993273285455691722285087014407153294888778099136975341466841199179567610457569019378809316607809546367372265062995034293891862229811200), (278785, -391496636642727845861142543507203576647444389049568487670733420599589783805228784509689404658303904773183686132531497517146945931114905600), (279553, 391496636642727845861142543507203576647444389049568487670733420599589783805228784509689404658303904773183686132531497517146945931114905600), (282625, 587244954964091768791713815260805364971166583574352731506100130899384675707843176764534106987455857159775529198797246275720418896672358400), (294913, 978741591606819614652856358768008941618610972623921219176833551498974459513071961274223511645759761932959215331328743792867364827787264000), (327700, 12097694191322231725522150999602118814253730316597393999435973398793160370440901750492977436793463927927319160761407190305887420204468633600), (344065, 1761734864892275306375141445782416094913499750723058194518300392698154027123529530293602320962367571479326587596391738827161256690017075200), (524309, 298708498551166215444991382706225155907499513990059111097184528365263219023232141987480924365270714269810349648429807168046602968011571200), (524312, 896125495653498646334974148118675467722498541970177333291553585095789657069696425962442773095812142809431048945289421504139808904034713600), (524324, 1194833994204664861779965530824900623629998055960236444388738113461052876092928567949923697461082857079241398593719228672186411872046284800), (524372, 597416997102332430889982765412450311814999027980118222194369056730526438046464283974961848730541428539620699296859614336093205936023142400), (524564, 298708498551166215444991382706225155907499513990059111097184528365263219023232141987480924365270714269810349648429807168046602968011571200), (525332, -298708498551166215444991382706225155907499513990059111097184528365263219023232141987480924365270714269810349648429807168046602968011571200), (528401, -120135987897885758396946922430586625116300848128339494352533782635537074529086082152255344626087880034013289339925221881757454259139112960), (528404, -808470711520406598358327841351097609210151815370107149703378140454506052122106459437987420426169711506755392492420376397342267229434695680), (528416, -480543951591543033587787689722346500465203392513357977410135130542148298116344328609021378504351520136053157359700887527029817036556451840), (528464, -240271975795771516793893844861173250232601696256678988705067565271074149058172164304510689252175760068026578679850443763514908518278225920), (528656, -120135987897885758396946922430586625116300848128339494352533782635537074529086082152255344626087880034013289339925221881757454259139112960), (529424, 120135987897885758396946922430586625116300848128339494352533782635537074529086082152255344626087880034013289339925221881757454259139112960), (532496, 180203981846828637595420383645879937674451272192509241528800673953305611793629123228383016939131820051019934009887832822636181388708669440), (540674, 43499626293636427317904727056355952960827154338840943074525935622176642645025420501076600517589322752575965125836833057460771770123878400), (540677, 130498878880909281953714181169067858882481463016522829223577806866529927935076261503229801552767968257727895377510499172382315310371635200), (540689, -374761395324969622247038745732241783485264520423670677694362248627335325092974101228960463265561494220835406495802578898513104990923980800), (540692, -2393050947876461533168451418638559675754468198312251127720359294261283734577307704668502906920933141367943675118524251305185083634287411200), (540704, -2195039601998061326074630615830662381314292551116137799969863964464167582692303132933067461343675140924557067996599644513424768285677977600), (540737, 86999252587272854635809454112711905921654308677681886149051871244353285290050841002153201035178645505151930251673666114921543540247756800), (540752, -1097519800999030663037315307915331190657146275558068899984931982232083791346151566466533730671837570462278533998299822256712384142838988800), (540929, 43499626293636427317904727056355952960827154338840943074525935622176642645025420501076600517589322752575965125836833057460771770123878400), (540944, -548759900499515331518657653957665595328573137779034449992465991116041895673075783233266865335918785231139266999149911128356192071419494400), (541697, -43499626293636427317904727056355952960827154338840943074525935622176642645025420501076600517589322752575965125836833057460771770123878400), (541712, 548759900499515331518657653957665595328573137779034449992465991116041895673075783233266865335918785231139266999149911128356192071419494400), (544769, -65249439440454640976857090584533929441240731508261414611788903433264963967538130751614900776383984128863947688755249586191157655185817600), (544784, 1123479820493987393270353787012964955783611826989400410870033443262905529832328880230538659569097877931742123848537921396927923754977024000), (557057, -108749065734091068294761817640889882402067885847102357686314839055441606612563551252691501293973306881439912814592082643651929425309696000), (557072, 1371899751248788328796644134894163988321432844447586124981164977790104739182689458083167163339796963077848167497874777820890480178548736000), (589844, -1344188243480247969502461222178013201583747812955265999937330377643684485604544638943664159643718214214146573417934132256209713356052070400), (593936, 540611945540485912786261150937639813023353816577527724586402021859916835380887369685149050817395460153059802029663498467908544166126008320), (606209, -195748318321363922930571271753601788323722194524784243835366710299794891902614392254844702329151952386591843066265748758573472965557452800), (606224, 2469419552247818991833959442809495178978579120005655024966096960022188530528841024549700894011634533540126701496174600077602864321387724800), (786453, -8297458293087950429027538408506254330763875388612753086032903565701756083978670610763359010146408729716954156900827976890183415778099200), (786456, -24892374879263851287082615225518762992291626165838259258098710697105268251936011832290077030439226189150862470702483930670550247334297600), (786468, -33189833172351801716110153634025017323055501554451012344131614262807024335914682443053436040585634918867816627603311907560733663112396800), (786516, -16594916586175900858055076817012508661527750777225506172065807131403512167957341221526718020292817459433908313801655953780366831556198400), (786693, -6481733648865845888676230464740344247870861345693260883668540798210978148614434851958791472856585671849537306647013247098756213135872000), (786696, -19445200946597537666028691394221032743612584037079782651005622394632934445843304555876374418569757015548611919941039741296268639407616000), (786708, -34224392888551333983732460267467631322247320771385796620707066758545668678436410018598524901572751417115103383488880965285208268321587200), (786756, -12963467297731691777352460929480688495741722691386521767337081596421956297228869703917582945713171343699074613294026494197512426271744000), (786948, -6481733648865845888676230464740344247870861345693260883668540798210978148614434851958791472856585671849537306647013247098756213135872000), (787476, 8297458293087950429027538408506254330763875388612753086032903565701756083978670610763359010146408729716954156900827976890183415778099200), (787716, 6481733648865845888676230464740344247870861345693260883668540798210978148614434851958791472856585671849537306647013247098756213135872000), (790533, -505567092836535459840807440147115417538623391748976858436118475671337282981587128091390165862133875084134278285971084700546176862617600), (790536, -1516701278509606379522422320441346252615870175246930575308355427014011848944761384274170497586401625252402834857913254101638530587852800), (790548, 10423919068285783804178077852170919825991319515923222195304881445867284994041657403779477851771077594238894122207357626533090416216678400), (790596, -1011134185673070919681614880294230835077246783497953716872236951342674565963174256182780331724267750168268556571942169401092353725235200), (790788, 9217033380462233373173538256963400954267668626790914467066692721645129939940065149846797043422744632690171681684548785947588142841190400), (791556, 505567092836535459840807440147115417538623391748976858436118475671337282981587128091390165862133875084134278285971084700546176862617600), (794628, 758350639254803189761211160220673126307935087623465287654177713507005924472380692137085248793200812626201417428956627050819265293926400), (802818, -1208322952601011869941797973787665360022976509412248418736831545060462295695150569474350014377481187571554586828800918262799215836774400), (802821, -4123670089940771836387565684616997542562116081826451977937980906210585916063668995232765464965174393627853774219229578681467304466022400), (802824, -1496103696413208679686515289762004387479559660769120165182458813087597086934651860429146265498192492739570041198480471679208970867097600), (802833, -4833291810404047479767191895150661440091906037648993674947326180241849182780602277897400057509924750286218347315203673051196863347097600), (802836, 18748840804168931166320158968249629976936942257173055828172313830137594094033807379669535838035098500639625337320762646653179911622451200), (802881, -2416645905202023739883595947575330720045953018824496837473663090120924591390301138948700028754962375143109173657601836525598431673548800), (802884, -997402464275472453124343526508002924986373107179413443454972542058398057956434573619430843665461661826380027465653647786139313911398400), (803073, -1208322952601011869941797973787665360022976509412248418736831545060462295695150569474350014377481187571554586828800918262799215836774400), (803076, 15705632890026878495128404398596859157183966810643445487443865724498246342557869843087263260308733348710653252884706293853820875883980800), (803841, 1208322952601011869941797973787665360022976509412248418736831545060462295695150569474350014377481187571554586828800918262799215836774400), (803844, 498701232137736226562171763254001462493186553589706721727486271029199028978217286809715421832730830913190013732826823893069656955699200), (806913, 1812484428901517804912696960681498040034464764118372628105247317590693443542725854211525021566221781357331880243201377394198823755161600), (806916, 2011969580297942989445276245248790737586338309757002228681525595722141750921293750443048547404430934080120716314167947590969927590092800), (819201, 3020807381502529674854494934469163400057441273530621046842078862651155739237876423685875035943702968928886467072002295656998039591936000), (819204, 1246753080344340566405429408135003656232966383974266804318715677572997572445543217024288554581827077282975034332067059732674142389248000), (851988, 37338562318895776930623922838278144488437439248757388887148066045657902377904017748435115545658839283726293706053725896005825371001446400), (852228, 29167801419896306499043037091331549115418876055619673976508433591949401668764956833814561627854635523322917879911559611944402959111424000), (856068, 2275051917764409569283633480662019378923805262870395862962533140521017773417142076411255746379602437878604252286869881152457795881779200), (868353, 5437453286704553414738090882044494120103394292355117884315741952772080330628177562634575064698665344071995640729604132182596471265484800), (868356, 2244155544619813019529772934643006581219339491153680247773688219631395630401977790643719398247288739109355061797720707518813456300646400), (1048597, -1532155577905125891759925705404190268091548303314440472108583168405355680544978001761391576540113575571640730286521320346288229216449740800), (1048600, -4596466733715377675279777116212570804274644909943321416325749505216067041634934005284174729620340726714922190859563961038864687649349222400), (1048612, -6128622311620503567039702821616761072366193213257761888434332673621422722179912007045566306160454302286562921146085281385152916865798963200), (1048660, -3064311155810251783519851410808380536183096606628880944217166336810711361089956003522783153080227151143281460573042640692576458432899481600), (1048852, -1532155577905125891759925705404190268091548303314440472108583168405355680544978001761391576540113575571640730286521320346288229216449740800), (1049620, 1532155577905125891759925705404190268091548303314440472108583168405355680544978001761391576540113575571640730286521320346288229216449740800), (1052689, -1307533463282794623390751639750696803208346560253324728019961559445306356609944750268154152529279652522904614351434868410663335443892166400), (1052692, -1624367022990695032532366361145805007487717225788313475897009925727885549012367248162375092777668594211252747624522624712557662507001888000), (1052704, -5230133853131178493563006559002787212833386241013298912079846237781225426439779001072616610117118610091618457405739473642653341775568665600), (1052752, -2615066926565589246781503279501393606416693120506649456039923118890612713219889500536308305058559305045809228702869736821326670887784332800), (1052944, -1307533463282794623390751639750696803208346560253324728019961559445306356609944750268154152529279652522904614351434868410663335443892166400), (1053712, 1307533463282794623390751639750696803208346560253324728019961559445306356609944750268154152529279652522904614351434868410663335443892166400), (1056784, 1961300194924191935086127459626045204812519840379987092029942339167959534914917125402231228793919478784356921527152302615995003165838249600), (1064962, -211440162185498620060132870088850162075484755834763173088800886841098761482085540359393010644990062652328755803933248446192025034818600960), (1064965, -634320486556495860180398610266550486226454267504289519266402660523296284446256621078179031934970187956986267411799745338576075104455802880), (1064977, -845760648741994480240531480355400648301939023339052692355203547364395045928342161437572042579960250609315023215732993784768100139274403840), (1064980, 3830388944762814729399814263510475670228870758286101180271457921013389201362445004403478941350283938929101825716303300865720573041124352000), (1065025, -422880324370997240120265740177700324150969511669526346177601773682197522964171080718786021289980125304657511607866496892384050069637201920), (1065217, -211440162185498620060132870088850162075484755834763173088800886841098761482085540359393010644990062652328755803933248446192025034818600960), (1065985, 211440162185498620060132870088850162075484755834763173088800886841098761482085540359393010644990062652328755803933248446192025034818600960), (1069057, 317160243278247930090199305133275243113227133752144759633201330261648142223128310539089515967485093978493133705899872669288037552227901440), (1069072, 3268833658206986558476879099376742008020866400633311820049903898613265891524861875670385381323199131307261535878587171026658338609730416000), (1081345, 528600405463746550150332175222125405188711889586907932722002217102746903705213850898482526612475156630821889509833121115480062587046502400), (1114132, 6894700100573066512919665674318856206411967364914982124488624257824100562452401007926262094430511090072383286289345941558297031474023833600), (1118224, 5883900584772575805258382378878135614437559521139961276089827017503878604744751376206693686381758436353070764581456907847985009497514748800), (1130497, 951480729834743790270597915399825729339681401256434278899603990784944426669384931617268547902455281935479401117699618007864112656683704320), (1310741, 468948007207291314529427572195579630139893769913885830220360435965858294639340808849857766203061111555548208569154398317634183992061542400), (1310744, 1406844021621873943588282716586738890419681309741657490661081307897574883918022426549573298609183334666644625707463194952902551976184627200), (1310756, 1875792028829165258117710288782318520559575079655543320881441743863433178557363235399431064812244446222192834276617593270536735968246169600), (1310804, 937896014414582629058855144391159260279787539827771660440720871931716589278681617699715532406122223111096417138308796635268367984123084800), (1310996, 468948007207291314529427572195579630139893769913885830220360435965858294639340808849857766203061111555548208569154398317634183992061542400), (1311764, -468948007207291314529427572195579630139893769913885830220360435965858294639340808849857766203061111555548208569154398317634183992061542400), (1314833, -317676386521580341043603151294398473479132301582081577947355005560988544709218127381414246312801487417812897198437016294606999550670403840), (1314836, -1656451170375677994924950812176564865647237559617073479172605670631753076086665595419029388242996129586761004449042646360272274640103525120), (1314848, -1270705546086321364174412605177593893916529206328326311789420022243954178836872509525656985251205949671251588793748065178427998202681615360), (1314896, -635352773043160682087206302588796946958264603164163155894710011121977089418436254762828492625602974835625794396874032589213999101340807680), (1315088, -317676386521580341043603151294398473479132301582081577947355005560988544709218127381414246312801487417812897198437016294606999550670403840), (1315856, 317676386521580341043603151294398473479132301582081577947355005560988544709218127381414246312801487417812897198437016294606999550670403840), (1318928, 476514579782370511565404726941597710218698452373122366921032508341482817063827191072121369469202231126719345797655524441910499326005605760), (1327106, 66992977647580718435697268177339304302547682764925740084392700826743171698590480541009157255921551936168049104051638440370996773992611840), (1327109, 200978932942742155307091804532017912907643048294777220253178102480229515095771441623027471767764655808504147312154915321112990321977835520), (1327121, -786688963499119975358855853544742324297180672361726408241724700639555116442137077992170497296935188589672538935900498121200357818708746240), (1327124, -4336352640286556833628503709251247699871848635049002681288787601754229146307849022593265794469516967891904727479207151442138494724191436800), (1327136, -4218643496357771396406579705016398166029485613685717474317182015786111212945996000624828505282485585337378941408428207530737379658716774400), (1327169, 133985955295161436871394536354678608605095365529851480168785401653486343397180961082018314511843103872336098208103276880741993547985223680), (1327184, -2109321748178885698203289852508199083014742806842858737158591007893055606472998000312414252641242792668689470704214103765368689829358387200), (1327361, 66992977647580718435697268177339304302547682764925740084392700826743171698590480541009157255921551936168049104051638440370996773992611840), (1327376, -1054660874089442849101644926254099541507371403421429368579295503946527803236499000156207126320621396334344735352107051882684344914679193600), (1328129, -66992977647580718435697268177339304302547682764925740084392700826743171698590480541009157255921551936168049104051638440370996773992611840), (1328144, 1054660874089442849101644926254099541507371403421429368579295503946527803236499000156207126320621396334344735352107051882684344914679193600), (1331201, -100489466471371077653545902266008956453821524147388610126589051240114757547885720811513735883882327904252073656077457660556495160988917760), (1331216, 2376182277438115126261475267617145495958887859087347997737330769822263066627793818687846305262935813046049346024253118560544016248694800000), (1343489, -167482444118951796089243170443348260756369206912314350210981752066857929246476201352522893139803879840420122760129096100927491934981529600), (1343504, 2636652185223607122754112315635248853768428508553573421448238759866319508091247500390517815801553490835861838380267629706710862286697984000), (1376261, -2122332604058423664424474899561665664951104244245998784366239187884876915882241896211670364564440824435971075341100318523841628397967360), (1376264, -6366997812175270993273424698684996994853312732737996353098717563654630747646725688635011093693322473307913226023300955571524885193902080), (1376276, -2118755362849044610040121974478354998289326381589470231129086918597901833540562607409206629372032765297710822862559193703449194477868810240), (1376324, -4244665208116847328848949799123331329902208488491997568732478375769753831764483792423340729128881648871942150682200637047683256795934720), (1376516, -2122332604058423664424474899561665664951104244245998784366239187884876915882241896211670364564440824435971075341100318523841628397967360), (1377284, 2122332604058423664424474899561665664951104244245998784366239187884876915882241896211670364564440824435971075341100318523841628397967360), (1380356, 3183498906087635496636712349342498497426656366368998176549358781827315373823362844317505546846661236653956613011650477785762442596951040), (1380368, 1429543739347111534696214180824793130656095357119367100763097525024448451191481573216364108407606693380158037392966573325731497978016817280), (1392641, -301468399414113232960637706798026869361464572442165830379767153720344272643657162434541207651646983712756220968232372981669485482966753280), (1392644, 5305831510146059161061187248904164162377760610614996960915597969712192289705604740529175911411102061089927688352750796309604070994918400), (1392656, 4745973933402492820957402168143447936783171315396432158606829767759375114564245500702932068442796283504551309084481733472079552116056371200), (1441796, 9550496718262906489910137048027495492279969099106994529648076345481946121470088532952516640539983709961869839034951433357287327790853120), (1572885, -21323791826623820277067193191716799612427591219554026147709582342531153157293693078814963626898106272926626617155116819046688526668697600), (1572888, -63971375479871460831201579575150398837282773658662078443128747027593459471881079236444890880694318818779879851465350457140065580006092800), (1572900, -85295167306495281108268772766867198449710364878216104590838329370124612629174772315259854507592425091706506468620467276186754106674790400), (1572948, -42647583653247640554134386383433599224855182439108052295419164685062306314587386157629927253796212545853253234310233638093377053337395200), (1573125, -19445200946597537666028691394221032743612584037079782651005622394632934445843304555876374418569757015548611919941039741296268639407616000), (1573128, -58335602839792612998086074182663098230837752111239347953016867183898803337529913667629123255709271046645835759823119223888805918222848000), (1573140, -99104595613013970941181958768600930586877927367873156751732071921062890940666911302320461301177134335121074296919275784231763084299161600), (1573188, -38890401893195075332057382788442065487225168074159565302011244789265868891686609111752748837139514031097223839882079482592537278815232000), (1573380, -19445200946597537666028691394221032743612584037079782651005622394632934445843304555876374418569757015548611919941039741296268639407616000), (1573908, 21323791826623820277067193191716799612427591219554026147709582342531153157293693078814963626898106272926626617155116819046688526668697600), (1574148, 19445200946597537666028691394221032743612584037079782651005622394632934445843304555876374418569757015548611919941039741296268639407616000), (1576965, -1516701278509606379522422320441346252615870175246930575308355427014011848944761384274170497586401625252402834857913254101638530587852800), (1576968, -4550103835528819138567266961324038757847610525740791725925066281042035546834284152822511492759204875757208504573739762304915591763558400), (1576977, -4035597108897514269724542097995977787680081976090508419814696171127488754968965278605414051016295223836125352936527371637849800752753600), (1576980, 13812091299204762088337474211821881045137660200071791660886863292358216075254598245309521296952667236871952527491440097249929265393374400), (1576992, -16142388435590057078898168391983911150720327904362033679258784684509955019875861114421656204065180895344501411746109486551399203011014400), (1577028, -3033402557019212759044844640882692505231740350493861150616710854028023697889522768548340995172803250504805669715826508203277061175705600), (1577040, -8071194217795028539449084195991955575360163952181016839629392342254977509937930557210828102032590447672250705873054743275699601505507200), (1577220, 27651100141386700119520614770890202862803005880372743401200078164935389819820195449540391130268233898070515045053646357842764428523571200), (1577232, -4035597108897514269724542097995977787680081976090508419814696171127488754968965278605414051016295223836125352936527371637849800752753600), (1577988, 1516701278509606379522422320441346252615870175246930575308355427014011848944761384274170497586401625252402834857913254101638530587852800), (1578000, 4035597108897514269724542097995977787680081976090508419814696171127488754968965278605414051016295223836125352936527371637849800752753600), (1581060, 2275051917764409569283633480662019378923805262870395862962533140521017773417142076411255746379602437878604252286869881152457795881779200), (1581072, 6053395663346271404586813146993966681520122964135762629722044256691233132453447917908121076524442835754188029404791057456774701129130400), (1589250, -3069238998367142937600055423158201590649301030660185643303295456914439287322663917835715493708635408020667061941346430495326904003235840), (1589253, -9207716995101428812800166269474604771947903091980556929909886370743317861967991753507146481125906224062001185824039291485980712009707520), (1589265, -12276955993468571750400221692632806362597204122640742573213181827657757149290655671342861974834541632082668247765385721981307616012943360), (1589268, 53309479566559550692667982979291999031068978048885065369273955856327882893234232697037409067245265682316566542887792047616721316671744000), (1589313, -6138477996734285875200110846316403181298602061320371286606590913828878574645327835671430987417270816041334123882692860990653808006471680), (1589505, -3069238998367142937600055423158201590649301030660185643303295456914439287322663917835715493708635408020667061941346430495326904003235840), (1589508, 48613002366493844165071728485552581859031460092699456627514055986582336114608261389690936046424392538871529799852599353240671598519040000), (1590273, 3069238998367142937600055423158201590649301030660185643303295456914439287322663917835715493708635408020667061941346430495326904003235840), (1593345, 4603858497550714406400083134737302385973951545990278464954943185371658930983995876753573240562953112031000592912019645742990356004853760), (1593348, 3791753196274015948806055801103365631539675438117326438270888567535029622361903460685426243966004063131007087144783135254096326469632000), (1593360, 10088992772243785674311355244989944469200204940226271049536740427818721887422413196513535127540738059590313382341318429094624501881884000), (1605633, 7673097495917857344000138557895503976623252576650464108258238642286098218306659794589288734271588520051667654853366076238317260008089600), (1638420, 95957063219807191246802369362725598255924160487993117664693120541390189207821618854667336321041478228169819777198025685710098370009139200), (1638660, 87503404259688919497129111273994647346256628166859021929525300775848205006294870501443684883563906569968753639734678835833208877334272000), (1642500, 6825155753293228707850900441986058136771415788611187588887599421563053320251426229233767239138807313635812756860609643457373387645337600), (1642512, 18160186990038814213760439440981900044560368892407287889166132770073699397360343753724363229573328507262564088214373172370324103387391200), (1654785, 13811575492652143219200249404211907157921854637970835394864829556114976792951987630260719721688859336093001778736058937228971068014561280), (2097173, 170239508656125099084436189489354474232394255923826719123175907600595075616108666862376841837790397285737858920724591149587581024049971200), (2097176, 510718525968375297253308568468063422697182767771480157369527722801785226848326000587130525513371191857213576762173773448762743072149913600), (2097188, 680958034624500396337744757957417896929577023695306876492703630402380302464434667449507367351161589142951435682898364598350324096199884800), (2097236, 340479017312250198168872378978708948464788511847653438246351815201190151232217333724753683675580794571475717841449182299175162048099942400), (2097428, 170239508656125099084436189489354474232394255923826719123175907600595075616108666862376841837790397285737858920724591149587581024049971200), (2098196, -170239508656125099084436189489354474232394255923826719123175907600595075616108666862376841837790397285737858920724591149587581024049971200), (2101265, 145281495920310513710083515527855200356482951139258303113329062160589595178882750029794905836586628058100512705714985378962592827099129600), (2101268, 180485224776743892503596262349533889720857469532034830655223325080876172112485249795819454753074288245694749736058069412506406945222432000), (2101280, 581125983681242054840334062111420801425931804557033212453316248642358380715531000119179623346346512232402050822859941515850371308396518400), (2101328, 290562991840621027420167031055710400712965902278516606226658124321179190357765500059589811673173256116201025411429970757925185654198259200), (2101520, 145281495920310513710083515527855200356482951139258303113329062160589595178882750029794905836586628058100512705714985378962592827099129600), (2102288, -145281495920310513710083515527855200356482951139258303113329062160589595178882750029794905836586628058100512705714985378962592827099129600), (2105360, -217922243880465770565125273291782800534724426708887454669993593240884392768324125044692358754879942087150769058572478068443889240648694400), (2113538, 23493351353944291117792541120983351341720528426084797009866765204566529053565060039932556738332229183592083978214805382910225003868733440), (2113541, 70480054061832873353377623362950054025161585278254391029600295613699587160695180119797670214996687550776251934644416148730675011606200320), (2113553, 93973405415777164471170164483933405366882113704339188039467060818266116214260240159730226953328916734368335912859221531640900015474933760), (2113556, -425598771640312747711090473723386185580985639809566797807939769001487689040271667155942104594475993214344647301811477873968952560124928000), (2113601, 46986702707888582235585082241966702683441056852169594019733530409133058107130120079865113476664458367184167956429610765820450007737466880), (2113793, 23493351353944291117792541120983351341720528426084797009866765204566529053565060039932556738332229183592083978214805382910225003868733440), (2114561, -23493351353944291117792541120983351341720528426084797009866765204566529053565060039932556738332229183592083978214805382910225003868733440), (2117633, -35240027030916436676688811681475027012580792639127195514800147806849793580347590059898835107498343775388125967322208074365337505803100160), (2117648, -363203739800776284275208788819638000891207377848145757783322655401473987947206875074487264591466570145251281764287463447406482067747824000), (2129921, -58733378384860727794481352802458378354301321065211992524666913011416322633912650099831391845830572958980209945537013457275562509671833600), (2162693, -1446815249758527156930534705226551330435353113059809354731628958615064882067256847357861183102802673553366631347960662538850837529477120), (2162696, -4340445749275581470791604115679653991306059339179428064194886875845194646201770542073583549308408020660099894043881987616552512588431360), (2162708, -771865049951597054507684991523001339367515564109459473473218100037138099800758028270127233002467998480033831668652502823299517958342778880), (2162756, -2893630499517054313861069410453102660870706226119618709463257917230129764134513694715722366205605347106733262695921325077701675058954240), (2162948, -1446815249758527156930534705226551330435353113059809354731628958615064882067256847357861183102802673553366631347960662538850837529477120), (2163716, 1446815249758527156930534705226551330435353113059809354731628958615064882067256847357861183102802673553366631347960662538850837529477120), (2166788, 2170222874637790735395802057839826995653029669589714032097443437922597323100885271036791774654204010330049947021940993808276256294215680), (2166800, -653766731641397311695375819875348401604173280126662364009980779722653178304972375134077076264639826261452307175717434205331667721946083200), (2179073, -105720081092749310030066435044425081037742377917381586544400443420549380741042770179696505322495031326164377901966624223096012517409300480), (2179076, 3617038124396317892326336763066378326088382782649523386829072396537662205168142118394652957757006683883416578369901656347127093823692800), (2228228, 6510668623913372206187406173519480986959089008769142096292330313767791969302655813110375323962612030990149841065822981424828768882647040), (2359317, -17755208773983789267051771157914836232563556273269793037320453987957038062651374325339850223356986356702390763607749707422826806003097600), (2359320, -53265626321951367801155313473744508697690668819809379111961361963871114187954122976019550670070959070107172290823249122268480418009292800), (2359332, -71020835095935157068207084631659344930254225093079172149281815951828152250605497301359400893427945426809563054430998829691307224012390400), (2359380, -35510417547967578534103542315829672465127112546539586074640907975914076125302748650679700446713972713404781527215499414845653612006195200), (2359557, -19445200946597537666028691394221032743612584037079782651005622394632934445843304555876374418569757015548611919941039741296268639407616000), (2359560, -58335602839792612998086074182663098230837752111239347953016867183898803337529913667629123255709271046645835759823119223888805918222848000), (2359572, -95536012560373939931166536734798967207013892421588923641342943566488775846024592548845347897636014418896838443371908672607901363633561600), (2359620, -38890401893195075332057382788442065487225168074159565302011244789265868891686609111752748837139514031097223839882079482592537278815232000), (2359812, -19445200946597537666028691394221032743612584037079782651005622394632934445843304555876374418569757015548611919941039741296268639407616000), (2360340, 17755208773983789267051771157914836232563556273269793037320453987957038062651374325339850223356986356702390763607749707422826806003097600), (2360580, 19445200946597537666028691394221032743612584037079782651005622394632934445843304555876374418569757015548611919941039741296268639407616000), (2363397, -1516701278509606379522422320441346252615870175246930575308355427014011848944761384274170497586401625252402834857913254101638530587852800), (2363400, -4550103835528819138567266961324038757847610525740791725925066281042035546834284152822511492759204875757208504573739762304915591763558400), (2363409, -8071194217795028539449084195991955575360163952181016839629392342254977509937930557210828102032590447672250705873054743275699601505507200), (2363412, -3647574606447827235859285132868997387698638147626083264140917752885422831615775720719390961407898308972777311639192685099412717863286400), (2363424, -32284776871180114157796336783967822301440655808724067358517569369019910039751722228843312408130361790689002823492218973102798406022028800), (2363460, -3033402557019212759044844640882692505231740350493861150616710854028023697889522768548340995172803250504805669715826508203277061175705600), (2363472, -16142388435590057078898168391983911150720327904362033679258784684509955019875861114421656204065180895344501411746109486551399203011014400), (2363652, 27651100141386700119520614770890202862803005880372743401200078164935389819820195449540391130268233898070515045053646357842764428523571200), (2363664, -8071194217795028539449084195991955575360163952181016839629392342254977509937930557210828102032590447672250705873054743275699601505507200), (2364420, 1516701278509606379522422320441346252615870175246930575308355427014011848944761384274170497586401625252402834857913254101638530587852800), (2364432, 8071194217795028539449084195991955575360163952181016839629392342254977509937930557210828102032590447672250705873054743275699601505507200), (2367492, 2275051917764409569283633480662019378923805262870395862962533140521017773417142076411255746379602437878604252286869881152457795881779200), (2367504, 12106791326692542809173626293987933363040245928271525259444088513382466264906895835816242153048885671508376058809582114913549402258260800), (2375682, -2513509138931250265374716924953407101229672533083626030396096278647491687559876127248380944284827253326670363396290106202256160496148480), (2375685, -8021074131003962864523207240151907997454897577156032603406768829739233104151339694439780642149427336760612284800161856858581671278676640), (2375688, -1441640142630636205197169395875060081297639933715463536655439981390274124415133938083913427884836730341803583833874614755439569370693600), (2375697, -10054036555725001061498867699813628404918690132334504121584385114589966750239504508993523777139309013306681453585160424809024641984593920), (2375700, 42465835078118624894033202033620343806345370771553864544427214994705562990741590562571074321212683584633572130574208115549814255846819200), (2375745, -5027018277862500530749433849906814202459345066167252060792192557294983375119752254496761888569654506653340726792580212404512320992296960), (2375748, -961093428420424136798112930583373387531759955810309024436959987593516082943422625389275618589891153561202389222583076503626379580462400), (2375937, -2513509138931250265374716924953407101229672533083626030396096278647491687559876127248380944284827253326670363396290106202256160496148480), (2375940, 48132455652283632096672672020260895165265580114794302115295575992785578073136550076996298237129446962090928605241307814988858408728808800), (2376705, 2513509138931250265374716924953407101229672533083626030396096278647491687559876127248380944284827253326670363396290106202256160496148480), (2376708, 480546714210212068399056465291686693765879977905154512218479993796758041471711312694637809294945576780601194611291538251813189790231200), (2379777, 3770263708396875398062075387430110651844508799625439045594144417971237531339814190872571416427240879990005545094435159303384240744222720), (2379780, 4512573267589334051404640499040895672188495404975058206598608558230166684569470429727382957908422428301908879061720442631816111154978800), (2379792, 20177985544487571348622710489979888938400409880452542099073480855637443774844826393027070255081476119180626764682636858189249003763768000), (2392065, 6283772847328125663436792312383517753074181332709065075990240696618729218899690318120952360712068133316675908490725265505640401240371200), (2392068, 1201366785525530170997641163229216734414699944762886280546199984491895103679278281736594523237363941951502986528228845629532974475578000), (2424852, 79898439482927051701732970210616763046536003229714068667942042945806671281931184464029326005106438605160758436234873683402720627013939200), (2425092, 87503404259688919497129111273994647346256628166859021929525300775848205006294870501443684883563906569968753639734678835833208877334272000), (2428932, 6825155753293228707850900441986058136771415788611187588887599421563053320251426229233767239138807313635812756860609643457373387645337600), (2428944, 36320373980077628427520878881963800089120737784814575778332265540147398794720687507448726459146657014525128176428746344740648206774782400), (2441217, 11310791125190626194186226162290331955533526398876317136782433253913712594019442572617714249281722639970016635283305477910152722232668160), (2441220, 2162460213945954307795754093812590121946459900573195304983159972085411186622700907125870141827255095512705375750811922133159354056040400), (3145749, -4728875240447919419012116374704290950899840442328519975643775211127640989336351857288245606605288813492718303353460865266321695112499200), (3145752, -14186625721343758257036349124112872852699521326985559926931325633382922968009055571864736819815866440478154910060382595798965085337497600), (3145764, -18915500961791677676048465498817163803599361769314079902575100844510563957345407429152982426421155253970873213413843461065286780449996800), (3145812, -9457750480895838838024232749408581901799680884657039951287550422255281978672703714576491213210577626985436606706921730532643390224998400), (3145989, -6481733648865845888676230464740344247870861345693260883668540798210978148614434851958791472856585671849537306647013247098756213135872000), (3145992, -19445200946597537666028691394221032743612584037079782651005622394632934445843304555876374418569757015548611919941039741296268639407616000), (3146004, -30655809835911302973717038233665667942383285825101563510317938403971553583794091265123411498031631500890867529941513853661346547655987200), (3146052, -12963467297731691777352460929480688495741722691386521767337081596421956297228869703917582945713171343699074613294026494197512426271744000), (3146244, -6481733648865845888676230464740344247870861345693260883668540798210978148614434851958791472856585671849537306647013247098756213135872000), (3146772, 4728875240447919419012116374704290950899840442328519975643775211127640989336351857288245606605288813492718303353460865266321695112499200), (3147012, 6481733648865845888676230464740344247870861345693260883668540798210978148614434851958791472856585671849537306647013247098756213135872000), (3149841, -4035597108897514269724542097995977787680081976090508419814696171127488754968965278605414051016295223836125352936527371637849800752753600), (3149844, -5013478466020663680655451731931496936690485264778745295978425696691004780902368049883873743140952451269298603779390817014066859589512000), (3149856, -16142388435590057078898168391983911150720327904362033679258784684509955019875861114421656204065180895344501411746109486551399203011014400), (3149904, -8071194217795028539449084195991955575360163952181016839629392342254977509937930557210828102032590447672250705873054743275699601505507200), (3150084, 9722600473298768833014345697110516371806292018539891325502811197316467222921652277938187209284878507774305959970519870648134319703808000), (3150096, -4035597108897514269724542097995977787680081976090508419814696171127488754968965278605414051016295223836125352936527371637849800752753600), (3150864, 4035597108897514269724542097995977787680081976090508419814696171127488754968965278605414051016295223836125352936527371637849800752753600), (3153936, 6053395663346271404586813146993966681520122964135762629722044256691233132453447917908121076524442835754188029404791057456774701129130400), (3162114, -652593093165119197716459475582870870603348011835688805829632366793514695932362778887015464953673032877557888283744593969728472329687040), (3162117, -1957779279495357593149378426748612611810044035507066417488897100380544087797088336661046394861019098632673664851233781909185416989061120), (3162129, -2610372372660476790865837902331483482413392047342755223318529467174058783729451115548061859814692131510231553134978375878913889318748160), (3162132, 11822188101119798547530290936760727377249601105821299939109438027819102473340879643220614016513222033731795758383652163165804237781248000), (3162177, -1305186186330238395432918951165741741206696023671377611659264733587029391864725557774030929907346065755115776567489187939456944659374080), (3162369, -652593093165119197716459475582870870603348011835688805829632366793514695932362778887015464953673032877557888283744593969728472329687040), (3162372, 16204334122164614721690576161850860619677153364233152209171351995527445371536087129896978682141464179623843266617533117746890532839680000), (3163137, 652593093165119197716459475582870870603348011835688805829632366793514695932362778887015464953673032877557888283744593969728472329687040), (3166209, 978889639747678796574689213374306305905022017753533208744448550190272043898544168330523197430509549316336832425616890954592708494530560), (3166224, 10088992772243785674311355244989944469200204940226271049536740427818721887422413196513535127540738059590313382341318429094624501881884000), (3178497, 1631482732912797994291148688957177176508370029589222014574080916983786739830906947217538662384182582193894720709361484924321180824217600), (3211284, 21279938582015637385554523686169309279049281990478339890396988450074384452013583357797105229723799660717232365090573893698447628006246400), (3211524, 29167801419896306499043037091331549115418876055619673976508433591949401668764956833814561627854635523322917879911559611944402959111424000), (3215376, 18160186990038814213760439440981900044560368892407287889166132770073699397360343753724363229573328507262564088214373172370324103387391200), (3227649, 2936668919243036389724067640122918917715066053260599626233345650570816131695632504991569592291528647949010497276850672863778125483591680)]
theorem sparseBlock018_data : sparseBlock018 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (302080738150252967485449493446916340005744127353062104684207886265115573923787642368587503594370296892888646707200229565699803959193600 : Int) coeff0210) (CoefficientMerge.scale (163148273291279799429114868895717717650837002958922201457408091698378673983090694721753866238418258219389472070936148492432118082421760 : Int) coeff0211)) (CoefficientMerge.merge (CoefficientMerge.scale (2074364573271987607256884602126563582690968847153188271508225891425439020994667652690839752536602182429238539225206994222545853944524800 : Int) coeff0212) (CoefficientMerge.merge (CoefficientMerge.scale (1182218810111979854753029093676072737724960110582129993910943802781910247334087964322061401651322203373179575838365216316580423778124800 : Int) coeff0213) (CoefficientMerge.scale (1620433412216461472169057616185086061967715336423315220917135199552744537153608712989697868214146417962384326661753311774689053283968000 : Int) coeff0214)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (4861300236649384416507172848555258185903146009269945662751405598658233611460826138969093604642439253887152979985259935324067159851904000 : Int) coeff0215) (CoefficientMerge.scale (4861300236649384416507172848555258185903146009269945662751405598658233611460826138969093604642439253887152979985259935324067159851904000 : Int) coeff0216)) (CoefficientMerge.merge (CoefficientMerge.scale (1620433412216461472169057616185086061967715336423315220917135199552744537153608712989697868214146417962384326661753311774689053283968000 : Int) coeff0217) (CoefficientMerge.merge (CoefficientMerge.scale (126391773209133864960201860036778854384655847937244214609029618917834320745396782022847541465533468771033569571492771175136544215654400 : Int) coeff0218) (CoefficientMerge.scale (379175319627401594880605580110336563153967543811732643827088856753502962236190346068542624396600406313100708714478313525409632646963200 : Int) coeff0219))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (379175319627401594880605580110336563153967543811732643827088856753502962236190346068542624396600406313100708714478313525409632646963200 : Int) coeff0220) (CoefficientMerge.scale (124675308034434056640542940813500365623296638397426680431871567757299757244554321702428855458182707728297503433206705973267414238924800 : Int) coeff0221)) (CoefficientMerge.merge (CoefficientMerge.scale (120136678552553017099764116322921673441469994476288628054619998449189510367927828173659452323736394195150298652822884562953297447557800 : Int) coeff0222) (CoefficientMerge.merge (CoefficientMerge.scale (530583151014605916106118724890416416237776061061499696091559796971219228970560474052917591141110206108992768835275079630960407099491840 : Int) coeff0223) (CoefficientMerge.scale (361703812439631789232633676306637832608838278264952338682907239653766220516814211839465295775700668388341657836990165634712709382369280 : Int) coeff0224)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (30033996974471439599236730607646656279075212032084873588133445658884268632271520538063836156521970008503322334981305470439363564784778240 : Int) coeff0225) (CoefficientMerge.scale (115739470610472713688421666705563418458903813180334970265171016930394534972025219352802288037347028868978352476038000418392398094442383360 : Int) coeff0226)) (CoefficientMerge.merge (CoefficientMerge.scale (1008899277224378567431135524498994446920020494022627104953674042781872188742241319651353512754073805959031338234131842909462450188188400 : Int) coeff0227) (CoefficientMerge.merge (CoefficientMerge.scale (137189975124878832879664413489416398832143284444758612498116497779010473918268945808316716333979696307784816749787477782089048017854873600 : Int) coeff0228) (CoefficientMerge.scale (263665218522360712275411231563524885376842850855357342144823875986631950809124750039051781580155349083586183838026762970671086228669798400 : Int) coeff0229)))))) := by decide +kernel
theorem sparseBlock018_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock018 := by
  rw [sparseBlock018_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted0210_nonneg g t z hg hA hB ht hz hw) (weighted0211_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0212_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0213_nonneg g t z hg hA hB ht hz hw) (weighted0214_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0215_nonneg g t z hg hA hB ht hz hw) (weighted0216_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0217_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0218_nonneg g t z hg hA hB ht hz hw) (weighted0219_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted0220_nonneg g t z hg hA hB ht hz hw) (weighted0221_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0222_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0223_nonneg g t z hg hA hB ht hz hw) (weighted0224_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0225_nonneg g t z hg hA hB ht hz hw) (weighted0226_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0227_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0228_nonneg g t z hg hA hB ht hz hw) (weighted0229_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
