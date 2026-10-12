import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff0136 : CoefficientMerge.Poly :=
  [(262147, -648), (262150, -1296), (262162, -1944), (262210, -1296), (262402, -648), (266242, 648), (278530, 1296), (327682, 1944), (524291, 72), (524294, 144), (524306, 216), (524354, 144), (524546, 72), (528386, -72), (540674, -144), (589826, -216), (786435, -2), (786438, -4), (786450, -6), (786498, -4), (786690, -2), (790530, 2), (802818, 4), (851970, 6), (1310723, 72), (1310726, 144), (1310738, 216), (1310786, 144), (1310978, 72), (1314818, -72), (1327106, -144), (1376258, -216), (1572867, -4), (1572870, -8), (1572882, -12), (1572930, -8), (1573122, -4), (1576962, 4), (1589250, 8), (1638402, 12), (2359299, -2), (2359302, -4), (2359314, -6), (2359362, -4), (2359554, -2), (2363394, 2), (2375682, 4), (2424834, 6)]
noncomputable def atom0136 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![1,1,1] * g 0 * g 0) * t * (t+z-18) * (t+z-18))
theorem atom0136_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0136 g t z = CoefficientMerge.eval (monomial g t z) coeff0136 := by
  norm_num [atom0136, coeff0136, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0136_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0136 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![1,1,1]
  dsimp only [atom0136]
  positivity
theorem weighted0136_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (246592141707692774429646570541821948907952807824759419897220394947806789135157433402937411282067989914040360932936782601444598136320000 : Int) coeff0136) := by
  rw [CoefficientMerge.eval_scale, ← atom0136_identity]
  exact mul_nonneg (by norm_num) (atom0136_nonneg g t z hg hA hB ht hz hw)

def coeff0137 : CoefficientMerge.Poly :=
  [(1048579, -648), (1048582, -1296), (1048594, -1944), (1048642, -1296), (1048834, -648), (1052674, 648), (1064962, 1296), (1114114, 1944), (1310723, 72), (1310726, 144), (1310738, 216), (1310786, 144), (1310978, 72), (1314818, -72), (1327106, -144), (1376258, -216), (1572867, -2), (1572870, -4), (1572882, -6), (1572930, -4), (1573122, -2), (1576962, 2), (1589250, 4), (1638402, 6), (2097155, 72), (2097158, 144), (2097170, 216), (2097218, 144), (2097410, 72), (2101250, -72), (2113538, -144), (2162690, -216), (2359299, -4), (2359302, -8), (2359314, -12), (2359362, -8), (2359554, -4), (2363394, 4), (2375682, 8), (2424834, 12), (3145731, -2), (3145734, -4), (3145746, -6), (3145794, -4), (3145986, -2), (3149826, 2), (3162114, 4), (3211266, 6)]
noncomputable def atom0137 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![1,1,1] * g 0 * g 0) * z * (t+z-18) * (t+z-18))
theorem atom0137_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0137 g t z = CoefficientMerge.eval (monomial g t z) coeff0137 := by
  norm_num [atom0137, coeff0137, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0137_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0137 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![1,1,1]
  dsimp only [atom0137]
  positivity
theorem weighted0137_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (739931881463197601068629151041094834653731436860856342093003974424407500194961185202262991105272343705296199791688834969294937148467200 : Int) coeff0137) := by
  rw [CoefficientMerge.eval_scale, ← atom0137_identity]
  exact mul_nonneg (by norm_num) (atom0137_nonneg g t z hg hA hB ht hz hw)

def coeff0138 : CoefficientMerge.Poly :=
  [(262153, -648), (262156, -1296), (262168, -1944), (262216, -1296), (262408, -648), (266248, 648), (278536, 1296), (327688, 1944), (524297, 72), (524300, 144), (524312, 216), (524360, 144), (524552, 72), (528392, -72), (540680, -144), (589832, -216), (786441, -2), (786444, -4), (786456, -6), (786504, -4), (786696, -2), (790536, 2), (802824, 4), (851976, 6), (1310729, 72), (1310732, 144), (1310744, 216), (1310792, 144), (1310984, 72), (1314824, -72), (1327112, -144), (1376264, -216), (1572873, -4), (1572876, -8), (1572888, -12), (1572936, -8), (1573128, -4), (1576968, 4), (1589256, 8), (1638408, 12), (2359305, -2), (2359308, -4), (2359320, -6), (2359368, -4), (2359560, -2), (2363400, 2), (2375688, 4), (2424840, 6)]
noncomputable def atom0138 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![1,1,1] * g 1 * g 1) * t * (t+z-18) * (t+z-18))
theorem atom0138_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0138 g t z = CoefficientMerge.eval (monomial g t z) coeff0138 := by
  norm_num [atom0138, coeff0138, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0138_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0138 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![1,1,1]
  dsimp only [atom0138]
  positivity
theorem weighted0138_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1357474706032470060741145226421140447914607759484861284856337739701828015673227358250317772696555888352318895605179408761948989948108800 : Int) coeff0138) := by
  rw [CoefficientMerge.eval_scale, ← atom0138_identity]
  exact mul_nonneg (by norm_num) (atom0138_nonneg g t z hg hA hB ht hz hw)

def coeff0139 : CoefficientMerge.Poly :=
  [(1048585, -648), (1048588, -1296), (1048600, -1944), (1048648, -1296), (1048840, -648), (1052680, 648), (1064968, 1296), (1114120, 1944), (1310729, 72), (1310732, 144), (1310744, 216), (1310792, 144), (1310984, 72), (1314824, -72), (1327112, -144), (1376264, -216), (1572873, -2), (1572876, -4), (1572888, -6), (1572936, -4), (1573128, -2), (1576968, 2), (1589256, 4), (1638408, 6), (2097161, 72), (2097164, 144), (2097176, 216), (2097224, 144), (2097416, 72), (2101256, -72), (2113544, -144), (2162696, -216), (2359305, -4), (2359308, -8), (2359320, -12), (2359368, -8), (2359560, -4), (2363400, 4), (2375688, 8), (2424840, 12), (3145737, -2), (3145740, -4), (3145752, -6), (3145800, -4), (3145992, -2), (3149832, 2), (3162120, 4), (3211272, 6)]
noncomputable def atom0139 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![1,1,1] * g 1 * g 1) * z * (t+z-18) * (t+z-18))
theorem atom0139_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0139 g t z = CoefficientMerge.eval (monomial g t z) coeff0139 := by
  norm_num [atom0139, coeff0139, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0139_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0139 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![1,1,1]
  dsimp only [atom0139]
  positivity
theorem weighted0139_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1357474706032470060741145226421140447914607759484861284856337739701828015673227358250317772696555888352318895605179408761948989948108800 : Int) coeff0139) := by
  rw [CoefficientMerge.eval_scale, ← atom0139_identity]
  exact mul_nonneg (by norm_num) (atom0139_nonneg g t z hg hA hB ht hz hw)

def coeff0140 : CoefficientMerge.Poly :=
  [(524321, -2), (524324, -4), (524336, -6), (524384, -4), (524576, -2), (528416, 2), (540704, 4), (589856, 6)]
noncomputable def atom0140 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![1,1,1] * g 2 * g 2) * t * t)
theorem atom0140_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0140 g t z = CoefficientMerge.eval (monomial g t z) coeff0140 := by
  norm_num [atom0140, coeff0140, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0140_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0140 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![1,1,1]
  dsimp only [atom0140]
  positivity
theorem weighted0140_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (310060986112564582909163092544323893146524008026235280114471080101528051789261089872325872564467318763204176902477251803283901498973798400 : Int) coeff0140) := by
  rw [CoefficientMerge.eval_scale, ← atom0140_identity]
  exact mul_nonneg (by norm_num) (atom0140_nonneg g t z hg hA hB ht hz hw)

def coeff0141 : CoefficientMerge.Poly :=
  [(1310753, -2), (1310756, -4), (1310768, -6), (1310816, -4), (1311008, -2), (1314848, 2), (1327136, 4), (1376288, 6)]
noncomputable def atom0141 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![1,1,1] * g 2 * g 2) * t * z)
theorem atom0141_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0141 g t z = CoefficientMerge.eval (monomial g t z) coeff0141 := by
  norm_num [atom0141, coeff0141, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0141_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0141 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![1,1,1]
  dsimp only [atom0141]
  positivity
theorem weighted0141_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (189586216740421875344788665640665273404681200868668035503285622346029792191539558241004409255947184978960245565515047351532390088118784000 : Int) coeff0141) := by
  rw [CoefficientMerge.eval_scale, ← atom0141_identity]
  exact mul_nonneg (by norm_num) (atom0141_nonneg g t z hg hA hB ht hz hw)

def coeff0142 : CoefficientMerge.Poly :=
  [(2097185, -2), (2097188, -4), (2097200, -6), (2097248, -4), (2097440, -2), (2101280, 2), (2113568, 4), (2162720, 6)]
noncomputable def atom0142 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![1,1,1] * g 2 * g 2) * z * z)
theorem atom0142_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0142 g t z = CoefficientMerge.eval (monomial g t z) coeff0142 := by
  norm_num [atom0142, coeff0142, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0142_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0142 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![1,1,1]
  dsimp only [atom0142]
  positivity
theorem weighted0142_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (53779159914843166035865966502118957696830341069360112315091253618783567175131749464034963363476313803463113031722003640151963858094592000 : Int) coeff0142) := by
  rw [CoefficientMerge.eval_scale, ← atom0142_identity]
  exact mul_nonneg (by norm_num) (atom0142_nonneg g t z hg hA hB ht hz hw)

def coeff0143 : CoefficientMerge.Poly :=
  [(33, -648), (36, -1296), (48, -1944), (96, -1296), (288, -648), (4128, 648), (16416, 1296), (65568, 1944), (262177, 72), (262180, 144), (262192, 216), (262240, 144), (262432, 72), (266272, -72), (278560, -144), (327712, -216), (524321, -2), (524324, -4), (524336, -6), (524384, -4), (524576, -2), (528416, 2), (540704, 4), (589856, 6), (1048609, 72), (1048612, 144), (1048624, 216), (1048672, 144), (1048864, 72), (1052704, -72), (1064992, -144), (1114144, -216), (1310753, -4), (1310756, -8), (1310768, -12), (1310816, -8), (1311008, -4), (1314848, 4), (1327136, 8), (1376288, 12), (2097185, -2), (2097188, -4), (2097200, -6), (2097248, -4), (2097440, -2), (2101280, 2), (2113568, 4), (2162720, 6)]
noncomputable def atom0143 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![1,1,1] * g 2 * g 2) * (t+z-18) * (t+z-18))
theorem atom0143_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0143 g t z = CoefficientMerge.eval (monomial g t z) coeff0143 := by
  norm_num [atom0143, coeff0143, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0143_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0143 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![1,1,1]
  dsimp only [atom0143]
  positivity
theorem weighted0143_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1719192578517404556681253287987192704237845095079231977663422783796370315950911718328713861562392924391434151756726633706974378019635200 : Int) coeff0143) := by
  rw [CoefficientMerge.eval_scale, ← atom0143_identity]
  exact mul_nonneg (by norm_num) (atom0143_nonneg g t z hg hA hB ht hz hw)

def coeff0144 : CoefficientMerge.Poly :=
  [(786465, -2), (786468, -4), (786480, -6), (786528, -4), (786720, -2), (790560, 2), (802848, 4), (852000, 6)]
noncomputable def atom0144 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![1,1,1] * g 2 * g 2) * t * t * t)
theorem atom0144_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0144 g t z = CoefficientMerge.eval (monomial g t z) coeff0144 := by
  norm_num [atom0144, coeff0144, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0144_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0144 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![1,1,1]
  dsimp only [atom0144]
  positivity
theorem weighted0144_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (17529342296698724027675976678559525975459231416322343096768616670086809391431207735757865937739671706648812279062711998875752353000652800 : Int) coeff0144) := by
  rw [CoefficientMerge.eval_scale, ← atom0144_identity]
  exact mul_nonneg (by norm_num) (atom0144_nonneg g t z hg hA hB ht hz hw)

def coeff0145 : CoefficientMerge.Poly :=
  [(262177, -648), (262180, -1296), (262192, -1944), (262240, -1296), (262432, -648), (266272, 648), (278560, 1296), (327712, 1944), (524321, 72), (524324, 144), (524336, 216), (524384, 144), (524576, 72), (528416, -72), (540704, -144), (589856, -216), (786465, -2), (786468, -4), (786480, -6), (786528, -4), (786720, -2), (790560, 2), (802848, 4), (852000, 6), (1310753, 72), (1310756, 144), (1310768, 216), (1310816, 144), (1311008, 72), (1314848, -72), (1327136, -144), (1376288, -216), (1572897, -4), (1572900, -8), (1572912, -12), (1572960, -8), (1573152, -4), (1576992, 4), (1589280, 8), (1638432, 12), (2359329, -2), (2359332, -4), (2359344, -6), (2359392, -4), (2359584, -2), (2363424, 2), (2375712, 4), (2424864, 6)]
noncomputable def atom0145 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![1,1,1] * g 2 * g 2) * t * (t+z-18) * (t+z-18))
theorem atom0145_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0145 g t z = CoefficientMerge.eval (monomial g t z) coeff0145 := by
  norm_num [atom0145, coeff0145, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0145_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0145 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![1,1,1]
  dsimp only [atom0145]
  positivity
theorem weighted0145_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2940810095589541078155221206171423147893508535826468770542769973090559996544097445169782205079327027555524650056484647966660218510592000 : Int) coeff0145) := by
  rw [CoefficientMerge.eval_scale, ← atom0145_identity]
  exact mul_nonneg (by norm_num) (atom0145_nonneg g t z hg hA hB ht hz hw)

def coeff0146 : CoefficientMerge.Poly :=
  [(3145761, -2), (3145764, -4), (3145776, -6), (3145824, -4), (3146016, -2), (3149856, 2), (3162144, 4), (3211296, 6)]
noncomputable def atom0146 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![1,1,1] * g 2 * g 2) * z * z * z)
theorem atom0146_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0146 g t z = CoefficientMerge.eval (monomial g t z) coeff0146 := by
  norm_num [atom0146, coeff0146, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0146_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0146 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![1,1,1]
  dsimp only [atom0146]
  positivity
theorem weighted0146_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (548712292563809926925010451888284760932965635858971659300519441111336182436012028418009813112925902144700379565736932373443392883097600 : Int) coeff0146) := by
  rw [CoefficientMerge.eval_scale, ← atom0146_identity]
  exact mul_nonneg (by norm_num) (atom0146_nonneg g t z hg hA hB ht hz hw)

def coeff0147 : CoefficientMerge.Poly :=
  [(1048609, -648), (1048612, -1296), (1048624, -1944), (1048672, -1296), (1048864, -648), (1052704, 648), (1064992, 1296), (1114144, 1944), (1310753, 72), (1310756, 144), (1310768, 216), (1310816, 144), (1311008, 72), (1314848, -72), (1327136, -144), (1376288, -216), (1572897, -2), (1572900, -4), (1572912, -6), (1572960, -4), (1573152, -2), (1576992, 2), (1589280, 4), (1638432, 6), (2097185, 72), (2097188, 144), (2097200, 216), (2097248, 144), (2097440, 72), (2101280, -72), (2113568, -144), (2162720, -216), (2359329, -4), (2359332, -8), (2359344, -12), (2359392, -8), (2359584, -4), (2363424, 4), (2375712, 8), (2424864, 12), (3145761, -2), (3145764, -4), (3145776, -6), (3145824, -4), (3146016, -2), (3149856, 2), (3162144, 4), (3211296, 6)]
noncomputable def atom0147 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![1,1,1] * g 2 * g 2) * z * (t+z-18) * (t+z-18))
theorem atom0147_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0147 g t z = CoefficientMerge.eval (monomial g t z) coeff0147 := by
  norm_num [atom0147, coeff0147, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0147_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0147 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![1,1,1]
  dsimp only [atom0147]
  positivity
theorem weighted0147_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1276622166478162516252463334178488819985769200157692290521946895688958708742486029902441287292053000203505087117694292350236869749913600 : Int) coeff0147) := by
  rw [CoefficientMerge.eval_scale, ← atom0147_identity]
  exact mul_nonneg (by norm_num) (atom0147_nonneg g t z hg hA hB ht hz hw)

def coeff0148 : CoefficientMerge.Poly :=
  [(278545, -648), (278548, -1296), (278560, -1944), (278608, -1296), (278800, -648), (282640, 648), (294928, 1296), (344080, 1944), (540689, 72), (540692, 144), (540704, 216), (540752, 144), (540944, 72), (544784, -72), (557072, -144), (606224, -216), (802833, -2), (802836, -4), (802848, -6), (802896, -4), (803088, -2), (806928, 2), (819216, 4), (868368, 6), (1327121, 72), (1327124, 144), (1327136, 216), (1327184, 144), (1327376, 72), (1331216, -72), (1343504, -144), (1392656, -216), (1589265, -4), (1589268, -8), (1589280, -12), (1589328, -8), (1589520, -4), (1593360, 4), (1605648, 8), (1654800, 12), (2375697, -2), (2375700, -4), (2375712, -6), (2375760, -4), (2375952, -2), (2379792, 2), (2392080, 4), (2441232, 6)]
noncomputable def atom0148 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![1,1,1] * g 2 * g 7) * t * (t+z-18) * (t+z-18))
theorem atom0148_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0148 g t z = CoefficientMerge.eval (monomial g t z) coeff0148 := by
  norm_num [atom0148, coeff0148, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0148_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0148 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![1,1,1]
  dsimp only [atom0148]
  positivity
theorem weighted0148_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5136450193108658107714185747764536786884592650551778913929111970729899719969551560524544936282596244579169544967735156512382351797068800 : Int) coeff0148) := by
  rw [CoefficientMerge.eval_scale, ← atom0148_identity]
  exact mul_nonneg (by norm_num) (atom0148_nonneg g t z hg hA hB ht hz hw)

def coeff0149 : CoefficientMerge.Poly :=
  [(3162129, -2), (3162132, -4), (3162144, -6), (3162192, -4), (3162384, -2), (3166224, 2), (3178512, 4), (3227664, 6)]
noncomputable def atom0149 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![1,1,1] * g 2 * g 7) * z * z * z)
theorem atom0149_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0149 g t z = CoefficientMerge.eval (monomial g t z) coeff0149 := by
  norm_num [atom0149, coeff0149, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0149_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0149 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![1,1,1]
  dsimp only [atom0149]
  positivity
theorem weighted0149_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (331575430627824418842037944150208772425013534393020723933012003614328199507457470527846495528882128125802441725390356781774477492354560 : Int) coeff0149) := by
  rw [CoefficientMerge.eval_scale, ← atom0149_identity]
  exact mul_nonneg (by norm_num) (atom0149_nonneg g t z hg hA hB ht hz hw)

def coeff0150 : CoefficientMerge.Poly :=
  [(1064977, -648), (1064980, -1296), (1064992, -1944), (1065040, -1296), (1065232, -648), (1069072, 648), (1081360, 1296), (1130512, 1944), (1327121, 72), (1327124, 144), (1327136, 216), (1327184, 144), (1327376, 72), (1331216, -72), (1343504, -144), (1392656, -216), (1589265, -2), (1589268, -4), (1589280, -6), (1589328, -4), (1589520, -2), (1593360, 2), (1605648, 4), (1654800, 6), (2113553, 72), (2113556, 144), (2113568, 216), (2113616, 144), (2113808, 72), (2117648, -72), (2129936, -144), (2179088, -216), (2375697, -4), (2375700, -8), (2375712, -12), (2375760, -8), (2375952, -4), (2379792, 4), (2392080, 8), (2441232, 12), (3162129, -2), (3162132, -4), (3162144, -6), (3162192, -4), (3162384, -2), (3166224, 2), (3178512, 4), (3227664, 6)]
noncomputable def atom0150 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![1,1,1] * g 2 * g 7) * z * (t+z-18) * (t+z-18))
theorem atom0150_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0150 g t z = CoefficientMerge.eval (monomial g t z) coeff0150 := by
  norm_num [atom0150, coeff0150, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0150_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0150 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![1,1,1]
  dsimp only [atom0150]
  positivity
theorem weighted0150_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4603039381317121799340833599624332913140289175946894924537134754372537881359042512160062978270878287506032741110725996190295474193254400 : Int) coeff0150) := by
  rw [CoefficientMerge.eval_scale, ← atom0150_identity]
  exact mul_nonneg (by norm_num) (atom0150_nonneg g t z hg hA hB ht hz hw)

def coeff0151 : CoefficientMerge.Poly :=
  [(589841, -2), (589844, -4), (589856, -6), (589904, -4), (590096, -2), (593936, 2), (606224, 4), (655376, 6)]
noncomputable def atom0151 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![1,1,1] * g 2 * g 8) * t * t)
theorem atom0151_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0151 g t z = CoefficientMerge.eval (monomial g t z) coeff0151 := by
  norm_num [atom0151, coeff0151, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0151_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0151 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![1,1,1]
  dsimp only [atom0151]
  positivity
theorem weighted0151_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (508471697253349177324801589849857646497485767288900470379885683551691172754174838749760044266578711961950433426084974372979358937269657600 : Int) coeff0151) := by
  rw [CoefficientMerge.eval_scale, ← atom0151_identity]
  exact mul_nonneg (by norm_num) (atom0151_nonneg g t z hg hA hB ht hz hw)

def coeff0152 : CoefficientMerge.Poly :=
  [(1376273, -2), (1376276, -4), (1376288, -6), (1376336, -4), (1376528, -2), (1380368, 2), (1392656, 4), (1441808, 6)]
noncomputable def atom0152 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![1,1,1] * g 2 * g 8) * t * z)
theorem atom0152_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0152 g t z = CoefficientMerge.eval (monomial g t z) coeff0152 := by
  norm_num [atom0152, coeff0152, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0152_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0152 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![1,1,1]
  dsimp only [atom0152]
  positivity
theorem weighted0152_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (690993252927483730933711966525179658641980616079783398722757262287087228186871012700858992896328102495631442778716079078205970742943539200 : Int) coeff0152) := by
  rw [CoefficientMerge.eval_scale, ← atom0152_identity]
  exact mul_nonneg (by norm_num) (atom0152_nonneg g t z hg hA hB ht hz hw)

def coeff0153 : CoefficientMerge.Poly :=
  [(2162705, -2), (2162708, -4), (2162720, -6), (2162768, -4), (2162960, -2), (2166800, 2), (2179088, 4), (2228240, 6)]
noncomputable def atom0153 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![1,1,1] * g 2 * g 8) * z * z)
theorem atom0153_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0153 g t z = CoefficientMerge.eval (monomial g t z) coeff0153 := by
  norm_num [atom0153, coeff0153, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0153_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0153 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![1,1,1]
  dsimp only [atom0153]
  positivity
theorem weighted0153_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (90382990229817355516855341809567187013179976123523699006607313539460928061869013676408435196244852104378662776931480409011528004387635200 : Int) coeff0153) := by
  rw [CoefficientMerge.eval_scale, ← atom0153_identity]
  exact mul_nonneg (by norm_num) (atom0153_nonneg g t z hg hA hB ht hz hw)

def coeff0154 : CoefficientMerge.Poly :=
  [(851985, -2), (851988, -4), (852000, -6), (852048, -4), (852240, -2), (856080, 2), (868368, 4), (917520, 6)]
noncomputable def atom0154 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![1,1,1] * g 2 * g 8) * t * t * t)
theorem atom0154_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0154 g t z = CoefficientMerge.eval (monomial g t z) coeff0154 := by
  norm_num [atom0154, coeff0154, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0154_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0154 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![1,1,1]
  dsimp only [atom0154]
  positivity
theorem weighted0154_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (8286786261552013964131040583746896379568231445213838291699652681827460698454695232668739339114505005021783890413500539979108818970163200 : Int) coeff0154) := by
  rw [CoefficientMerge.eval_scale, ← atom0154_identity]
  exact mul_nonneg (by norm_num) (atom0154_nonneg g t z hg hA hB ht hz hw)

def coeff0155 : CoefficientMerge.Poly :=
  [(1638417, -2), (1638420, -4), (1638432, -6), (1638480, -4), (1638672, -2), (1642512, 2), (1654800, 4), (1703952, 6)]
noncomputable def atom0155 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((quadA (outer g) ![1,1,1] * g 2 * g 8) * t * t * z)
theorem atom0155_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0155 g t z = CoefficientMerge.eval (monomial g t z) coeff0155 := by
  norm_num [atom0155, coeff0155, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0155_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0155 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hq := quadA_nonneg (outer g) hA ![1,1,1]
  dsimp only [atom0155]
  positivity
theorem weighted0155_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (13822882724416813290784124313614188833219313618393443684913571136883935948291852955591981259396729961462270901459791259785893387935641600 : Int) coeff0155) := by
  rw [CoefficientMerge.eval_scale, ← atom0155_identity]
  exact mul_nonneg (by norm_num) (atom0155_nonneg g t z hg hA hB ht hz hw)

def sparseBlock011 : CoefficientMerge.Poly :=
  [(33, -1114036790879278152729452130615700872346123621611342321525897963900047964736190793477006582292430615005649330338358858642119396956723609600), (36, -2228073581758556305458904261231401744692247243222684643051795927800095929472381586954013164584861230011298660676717717284238793913447219200), (48, -3342110372637834458188356391847102617038370864834026964577693891700143894208572380431019746877291845016947991015076575926358190870170828800), (96, -2228073581758556305458904261231401744692247243222684643051795927800095929472381586954013164584861230011298660676717717284238793913447219200), (288, -1114036790879278152729452130615700872346123621611342321525897963900047964736190793477006582292430615005649330338358858642119396956723609600), (4128, 1114036790879278152729452130615700872346123621611342321525897963900047964736190793477006582292430615005649330338358858642119396956723609600), (16416, 2228073581758556305458904261231401744692247243222684643051795927800095929472381586954013164584861230011298660676717717284238793913447219200), (65568, 3342110372637834458188356391847102617038370864834026964577693891700143894208572380431019746877291845016947991015076575926358190870170828800), (262147, -159791707826584917830410977711100622892353419470444104093398815926178799359582016845103442510780057464298153884543035125736099592335360000), (262150, -319583415653169835660821955422201245784706838940888208186797631852357598719164033690206885021560114928596307769086070251472199184670720000), (262153, -879643609509040599360262106720899010248665828146190112586906855326784554156251328146205916707368215652302644352156256877742945486374502400), (262156, -1759287219018081198720524213441798020497331656292380225173813710653569108312502656292411833414736431304605288704312513755485890972749004800), (262162, -479375123479754753491232933133301868677060258411332312280196447778536398078746050535310327532340172392894461653629105377208298777006080000), (262168, -2638930828527121798080786320162697030745997484438570337760720565980353662468753984438617750122104646956907933056468770633228836459123507200), (262177, -1781863076288769490563533104864004325129868684369847060919948502129344215012109500750351470858911623299796714310117734255493666377449881600), (262180, -3563726152577538981127066209728008650259737368739694121839897004258688430024219001500702941717823246599593428620235468510987332754899763200), (262192, -5345589228866308471690599314592012975389606053109541182759845506388032645036328502251054412576734869899390142930353202766480999132349644800), (262210, -319583415653169835660821955422201245784706838940888208186797631852357598719164033690206885021560114928596307769086070251472199184670720000), (262216, -1759287219018081198720524213441798020497331656292380225173813710653569108312502656292411833414736431304605288704312513755485890972749004800), (262240, -3563726152577538981127066209728008650259737368739694121839897004258688430024219001500702941717823246599593428620235468510987332754899763200), (262402, -159791707826584917830410977711100622892353419470444104093398815926178799359582016845103442510780057464298153884543035125736099592335360000), (262408, -879643609509040599360262106720899010248665828146190112586906855326784554156251328146205916707368215652302644352156256877742945486374502400), (262432, -1781863076288769490563533104864004325129868684369847060919948502129344215012109500750351470858911623299796714310117734255493666377449881600), (266242, 159791707826584917830410977711100622892353419470444104093398815926178799359582016845103442510780057464298153884543035125736099592335360000), (266248, 879643609509040599360262106720899010248665828146190112586906855326784554156251328146205916707368215652302644352156256877742945486374502400), (266272, 1781863076288769490563533104864004325129868684369847060919948502129344215012109500750351470858911623299796714310117734255493666377449881600), (278530, 319583415653169835660821955422201245784706838940888208186797631852357598719164033690206885021560114928596307769086070251472199184670720000), (278536, 1759287219018081198720524213441798020497331656292380225173813710653569108312502656292411833414736431304605288704312513755485890972749004800), (278545, -3328419725134410453798792364551419837901216037557552736226064557032975018540269411219905118711122366487301865139092381420023763964500582400), (278548, -6656839450268820907597584729102839675802432075115105472452129114065950037080538822439810237422244732974603730278184762840047527929001164800), (278560, -6421533022825692380269310883926250863443910743932964086838296666840236625596589232159012414415543852862312166797041675749083959138601984000), (278608, -6656839450268820907597584729102839675802432075115105472452129114065950037080538822439810237422244732974603730278184762840047527929001164800), (278800, -3328419725134410453798792364551419837901216037557552736226064557032975018540269411219905118711122366487301865139092381420023763964500582400), (282640, 3328419725134410453798792364551419837901216037557552736226064557032975018540269411219905118711122366487301865139092381420023763964500582400), (294928, 6656839450268820907597584729102839675802432075115105472452129114065950037080538822439810237422244732974603730278184762840047527929001164800), (327682, 479375123479754753491232933133301868677060258411332312280196447778536398078746050535310327532340172392894461653629105377208298777006080000), (327688, 2638930828527121798080786320162697030745997484438570337760720565980353662468753984438617750122104646956907933056468770633228836459123507200), (327712, 5345589228866308471690599314592012975389606053109541182759845506388032645036328502251054412576734869899390142930353202766480999132349644800), (344080, 9985259175403231361396377093654259513703648112672658208678193671098925055620808233659715356133367099461905595417277144260071291893501747200), (524291, 17754634202953879758934553079011180321372602163382678232599868436242088817731335205011493612308895273810905987171448347304011065815040000), (524294, 35509268405907759517869106158022360642745204326765356465199736872484177635462670410022987224617790547621811974342896694608022131630080000), (524297, 97738178834337844373362456302322112249851758682910012509656317258531617128472369794022879634152023961366960483572917430860327276263833600), (524300, 195476357668675688746724912604644224499703517365820025019312634517063234256944739588045759268304047922733920967145834861720654552527667200), (524306, 53263902608861639276803659237033540964117806490148034697799605308726266453194005615034480836926685821432717961514345041912033197445120000), (524312, 293214536503013533120087368906966336749555276048730037528968951775594851385417109382068638902456071884100881450718752292580981828791500800), (524321, -411822030499717017304512764820279705053191091663123272705189567708128524459248987129084854086347877391193447304401062220382216021224243200), (524324, -823644060999434034609025529640559410106382183326246545410379135416257048918497974258169708172695754782386894608802124440764432042448486400), (524336, -1235466091499151051913538294460839115159573274989369818115568703124385573377746961387254562259043632173580341913203186661146648063672729600), (524354, 35509268405907759517869106158022360642745204326765356465199736872484177635462670410022987224617790547621811974342896694608022131630080000), (524360, 195476357668675688746724912604644224499703517365820025019312634517063234256944739588045759268304047922733920967145834861720654552527667200), (524384, -823644060999434034609025529640559410106382183326246545410379135416257048918497974258169708172695754782386894608802124440764432042448486400), (524546, 17754634202953879758934553079011180321372602163382678232599868436242088817731335205011493612308895273810905987171448347304011065815040000), (524552, 97738178834337844373362456302322112249851758682910012509656317258531617128472369794022879634152023961366960483572917430860327276263833600), (524576, -411822030499717017304512764820279705053191091663123272705189567708128524459248987129084854086347877391193447304401062220382216021224243200), (528386, -17754634202953879758934553079011180321372602163382678232599868436242088817731335205011493612308895273810905987171448347304011065815040000), (528392, -97738178834337844373362456302322112249851758682910012509656317258531617128472369794022879634152023961366960483572917430860327276263833600), (528416, 411822030499717017304512764820279705053191091663123272705189567708128524459248987129084854086347877391193447304401062220382216021224243200), (540674, -35509268405907759517869106158022360642745204326765356465199736872484177635462670410022987224617790547621811974342896694608022131630080000), (540680, -195476357668675688746724912604644224499703517365820025019312634517063234256944739588045759268304047922733920967145834861720654552527667200), (540689, 369824413903823383755421373839046648655690670839728081802896061892552779837807712357767235412346929609700207237676931268891529329388953600), (540692, 739648827807646767510842747678093297311381341679456163605792123785105559675615424715534470824693859219400414475353862537783058658777907200), (540704, 1933117302710904185875289651157699356073454195845430790819067321093915388431921111331471414409736543611487516321832918247439020030615347200), (540752, 739648827807646767510842747678093297311381341679456163605792123785105559675615424715534470824693859219400414475353862537783058658777907200), (540944, 369824413903823383755421373839046648655690670839728081802896061892552779837807712357767235412346929609700207237676931268891529329388953600), (544784, -369824413903823383755421373839046648655690670839728081802896061892552779837807712357767235412346929609700207237676931268891529329388953600), (557072, -739648827807646767510842747678093297311381341679456163605792123785105559675615424715534470824693859219400414475353862537783058658777907200), (589826, -53263902608861639276803659237033540964117806490148034697799605308726266453194005615034480836926685821432717961514345041912033197445120000), (589832, -293214536503013533120087368906966336749555276048730037528968951775594851385417109382068638902456071884100881450718752292580981828791500800), (589841, -1016943394506698354649603179699715292994971534577800940759771367103382345508349677499520088533157423923900866852169948745958717874539315200), (589844, -2033886789013396709299206359399430585989943069155601881519542734206764691016699354999040177066314847847801733704339897491917435749078630400), (589856, -1815364092020944012035271244638306763825341328744033004163745398185761463147302071111305703340428639598122258643306659576729505559945216000), (589904, -2033886789013396709299206359399430585989943069155601881519542734206764691016699354999040177066314847847801733704339897491917435749078630400), (590096, -1016943394506698354649603179699715292994971534577800940759771367103382345508349677499520088533157423923900866852169948745958717874539315200), (593936, 1016943394506698354649603179699715292994971534577800940759771367103382345508349677499520088533157423923900866852169948745958717874539315200), (606224, 924413547301926558032942237882290640022871056636417636110854548529106351503276217925738470829274059018701111991309103685242847760911769600), (655376, 3050830183520095063948809539099145878984914603733402822279314101310147036525049032498560265599472271771702600556509846237876153623617945600), (786435, -493184283415385548859293141083643897815905615649518839794440789895613578270314866805874822564135979828080721865873565202889196272640000), (786438, -986368566830771097718586282167287795631811231299037679588881579791227156540629733611749645128271959656161443731747130405778392545280000), (786441, -2714949412064940121482290452842280895829215518969722569712675479403656031346454716500635545393111776704637791210358817523897979896217600), (786444, -5429898824129880242964580905684561791658431037939445139425350958807312062692909433001271090786223553409275582420717635047795959792435200), (786450, -1479552850246156646577879423250931693447716846948556519383322369686840734810944600417624467692407939484242165597620695608667588817920000), (786456, -8144848236194820364446871358526842687487646556909167709138026438210968094039364149501906636179335330113913373631076452571693939688652800), (786465, -40940304784576530211662395769461898246705479904297623734622773286354738775950610361855296285637997468408673858238393293684825143022489600), (786468, -81880609569153060423324791538923796493410959808595247469245546572709477551901220723710592571275994936817347716476786587369650286044979200), (786480, -122820914353729590634987187308385694740116439712892871203868319859064216327851831085565888856913992405226021574715179881054475429067468800), (786498, -986368566830771097718586282167287795631811231299037679588881579791227156540629733611749645128271959656161443731747130405778392545280000), (786504, -5429898824129880242964580905684561791658431037939445139425350958807312062692909433001271090786223553409275582420717635047795959792435200), (786528, -81880609569153060423324791538923796493410959808595247469245546572709477551901220723710592571275994936817347716476786587369650286044979200), (786690, -493184283415385548859293141083643897815905615649518839794440789895613578270314866805874822564135979828080721865873565202889196272640000), (786696, -2714949412064940121482290452842280895829215518969722569712675479403656031346454716500635545393111776704637791210358817523897979896217600), (786720, -40940304784576530211662395769461898246705479904297623734622773286354738775950610361855296285637997468408673858238393293684825143022489600), (790530, 493184283415385548859293141083643897815905615649518839794440789895613578270314866805874822564135979828080721865873565202889196272640000), (790536, 2714949412064940121482290452842280895829215518969722569712675479403656031346454716500635545393111776704637791210358817523897979896217600), (790560, 40940304784576530211662395769461898246705479904297623734622773286354738775950610361855296285637997468408673858238393293684825143022489600), (802818, 986368566830771097718586282167287795631811231299037679588881579791227156540629733611749645128271959656161443731747130405778392545280000), (802824, 5429898824129880242964580905684561791658431037939445139425350958807312062692909433001271090786223553409275582420717635047795959792435200), (802833, -10272900386217316215428371495529073573769185301103557827858223941459799439939103121049089872565192489158339089935470313024764703594137600), (802836, -20545800772434632430856742991058147147538370602207115655716447882919598879878206242098179745130384978316678179870940626049529407188275200), (802848, 51061908410501111777039677052336575772103403905284573985670874748330079232083911360563322953580417469342330446670375648295356175262566400), (802896, -20545800772434632430856742991058147147538370602207115655716447882919598879878206242098179745130384978316678179870940626049529407188275200), (803088, -10272900386217316215428371495529073573769185301103557827858223941459799439939103121049089872565192489158339089935470313024764703594137600), (806928, 10272900386217316215428371495529073573769185301103557827858223941459799439939103121049089872565192489158339089935470313024764703594137600), (819216, 20545800772434632430856742991058147147538370602207115655716447882919598879878206242098179745130384978316678179870940626049529407188275200), (851970, 1479552850246156646577879423250931693447716846948556519383322369686840734810944600417624467692407939484242165597620695608667588817920000), (851976, 8144848236194820364446871358526842687487646556909167709138026438210968094039364149501906636179335330113913373631076452571693939688652800), (851985, -16573572523104027928262081167493792759136462890427676583399305363654921396909390465337478678229010010043567780827001079958217637940326400), (851988, -33147145046208055856524162334987585518272925780855353166798610727309842793818780930674957356458020020087135561654002159916435275880652800), (852000, 73100196784417506850200943805904316462707051041609841453670403768099452137123659689553452822226962375095318232234176641179822515246489600), (852048, -33147145046208055856524162334987585518272925780855353166798610727309842793818780930674957356458020020087135561654002159916435275880652800), (852240, -16573572523104027928262081167493792759136462890427676583399305363654921396909390465337478678229010010043567780827001079958217637940326400), (856080, 16573572523104027928262081167493792759136462890427676583399305363654921396909390465337478678229010010043567780827001079958217637940326400), (868368, 63965846204860004502809276821574806239580481684166026650373282551689241113636090293822226974153597487562152831460413098990729386663065600), (917520, 49720717569312083784786243502481378277409388671283029750197916090964764190728171396012436034687030030130703342481003239874652913820979200), (1048579, -479475859188152045492471689874629452855617971085834909676266575427016060126334848011066418236216478721031937465014365060103119272206745600), (1048582, -958951718376304090984943379749258905711235942171669819352533150854032120252669696022132836472432957442063874930028730120206238544413491200), (1048585, -879643609509040599360262106720899010248665828146190112586906855326784554156251328146205916707368215652302644352156256877742945486374502400), (1048588, -1759287219018081198720524213441798020497331656292380225173813710653569108312502656292411833414736431304605288704312513755485890972749004800), (1048594, -1438427577564456136477415069623888358566853913257504729028799726281048180379004544033199254708649436163095812395043095180309357816620236800), (1048600, -2638930828527121798080786320162697030745997484438570337760720565980353662468753984438617750122104646956907933056468770633228836459123507200), (1048609, -703469298224596182450546003812582880645653594856479901866455147973106580516665303657114556132758053575688037525781583816051336380530278400), (1048612, -1406938596449192364901092007625165761291307189712959803732910295946213161033330607314229112265516107151376075051563167632102672761060556800), (1048624, -2110407894673788547351638011437748641936960784569439705599365443919319741549995910971343668398274160727064112577344751448154009141590835200), (1048642, -958951718376304090984943379749258905711235942171669819352533150854032120252669696022132836472432957442063874930028730120206238544413491200), (1048648, -1759287219018081198720524213441798020497331656292380225173813710653569108312502656292411833414736431304605288704312513755485890972749004800), (1048672, -1406938596449192364901092007625165761291307189712959803732910295946213161033330607314229112265516107151376075051563167632102672761060556800), (1048834, -479475859188152045492471689874629452855617971085834909676266575427016060126334848011066418236216478721031937465014365060103119272206745600), (1048840, -879643609509040599360262106720899010248665828146190112586906855326784554156251328146205916707368215652302644352156256877742945486374502400), (1048864, -703469298224596182450546003812582880645653594856479901866455147973106580516665303657114556132758053575688037525781583816051336380530278400), (1052674, 479475859188152045492471689874629452855617971085834909676266575427016060126334848011066418236216478721031937465014365060103119272206745600), (1052680, 879643609509040599360262106720899010248665828146190112586906855326784554156251328146205916707368215652302644352156256877742945486374502400), (1052704, 703469298224596182450546003812582880645653594856479901866455147973106580516665303657114556132758053575688037525781583816051336380530278400), (1064962, 958951718376304090984943379749258905711235942171669819352533150854032120252669696022132836472432957442063874930028730120206238544413491200), (1064968, 1759287219018081198720524213441798020497331656292380225173813710653569108312502656292411833414736431304605288704312513755485890972749004800), (1064977, -2982769519093494925972860172556567727714907386013587911100063320833404547120659547879720809919529130303909216239750445531311467277228851200), (1064980, -5965539038186989851945720345113135455429814772027175822200126641666809094241319095759441619839058260607818432479500891062622934554457702400), (1064992, -7541369960831292413017488510044537421853414968327803929567279666554000480328648036324933317493071283760351573667688168961831729070625996800), (1065040, -5965539038186989851945720345113135455429814772027175822200126641666809094241319095759441619839058260607818432479500891062622934554457702400), (1065232, -2982769519093494925972860172556567727714907386013587911100063320833404547120659547879720809919529130303909216239750445531311467277228851200), (1069072, 2982769519093494925972860172556567727714907386013587911100063320833404547120659547879720809919529130303909216239750445531311467277228851200), (1081360, 5965539038186989851945720345113135455429814772027175822200126641666809094241319095759441619839058260607818432479500891062622934554457702400), (1114114, 1438427577564456136477415069623888358566853913257504729028799726281048180379004544033199254708649436163095812395043095180309357816620236800), (1114120, 2638930828527121798080786320162697030745997484438570337760720565980353662468753984438617750122104646956907933056468770633228836459123507200), (1114144, 2110407894673788547351638011437748641936960784569439705599365443919319741549995910971343668398274160727064112577344751448154009141590835200), (1130512, 8948308557280484777918580517669703183144722158040763733300189962500213641361978643639162429758587390911727648719251336593934401831686553600), (1310723, 71029729668304107035875851953970008416441265617364334863296154594799428831768540539574428971888504020592232372173044465093246540504678400), (1310726, 142059459336608214071751703907940016832882531234728669726592309189598857663537081079148857943777008041184464744346088930186493081009356800), (1310729, 195476357668675688746724912604644224499703517365820025019312634517063234256944739588045759268304047922733920967145834861720654552527667200), (1310732, 390952715337351377493449825209288448999407034731640050038625269034126468513889479176091518536608095845467841934291669723441309105055334400), (1310738, 213089189004912321107627555861910025249323796852093004589888463784398286495305621618723286915665512061776697116519133395279739621514035200), (1310744, 586429073006027066240174737813932673499110552097460075057937903551189702770834218764137277804912143768201762901437504585161963657583001600), (1310753, -82394080926038710118949057528085655939005785126793402520565321275119718866248753150123582507404579656836086661516117535076087333559705600), (1310756, -164788161852077420237898115056171311878011570253586805041130642550239437732497506300247165014809159313672173323032235070152174667119411200), (1310768, -247182242778116130356847172584256967817017355380380207561695963825359156598746259450370747522213738970508259984548352605228262000679116800), (1310786, 142059459336608214071751703907940016832882531234728669726592309189598857663537081079148857943777008041184464744346088930186493081009356800), (1310792, 390952715337351377493449825209288448999407034731640050038625269034126468513889479176091518536608095845467841934291669723441309105055334400), (1310816, -164788161852077420237898115056171311878011570253586805041130642550239437732497506300247165014809159313672173323032235070152174667119411200), (1310978, 71029729668304107035875851953970008416441265617364334863296154594799428831768540539574428971888504020592232372173044465093246540504678400), (1310984, 195476357668675688746724912604644224499703517365820025019312634517063234256944739588045759268304047922733920967145834861720654552527667200), (1311008, -82394080926038710118949057528085655939005785126793402520565321275119718866248753150123582507404579656836086661516117535076087333559705600), (1314818, -71029729668304107035875851953970008416441265617364334863296154594799428831768540539574428971888504020592232372173044465093246540504678400), (1314824, -195476357668675688746724912604644224499703517365820025019312634517063234256944739588045759268304047922733920967145834861720654552527667200), (1314848, 82394080926038710118949057528085655939005785126793402520565321275119718866248753150123582507404579656836086661516117535076087333559705600), (1327106, -142059459336608214071751703907940016832882531234728669726592309189598857663537081079148857943777008041184464744346088930186493081009356800), (1327112, -390952715337351377493449825209288448999407034731640050038625269034126468513889479176091518536608095845467841934291669723441309105055334400), (1327121, 701243249358656153307961393011998618401791491507904516369569764207375507295658773233291769847850166310134564597649202994592803471303270400), (1327124, 1402486498717312306615922786023997236803582983015809032739139528414751014591317546466583539695700332620269129195298405989185606942606540800), (1327136, 2268517909928045880161782294092167167083386044777300354149839935172365959619473826000122474558359658244075867115979844053930585081029222400), (1327184, 1402486498717312306615922786023997236803582983015809032739139528414751014591317546466583539695700332620269129195298405989185606942606540800), (1327376, 701243249358656153307961393011998618401791491507904516369569764207375507295658773233291769847850166310134564597649202994592803471303270400), (1331216, -701243249358656153307961393011998618401791491507904516369569764207375507295658773233291769847850166310134564597649202994592803471303270400), (1343504, -1402486498717312306615922786023997236803582983015809032739139528414751014591317546466583539695700332620269129195298405989185606942606540800), (1376258, -213089189004912321107627555861910025249323796852093004589888463784398286495305621618723286915665512061776697116519133395279739621514035200), (1376264, -586429073006027066240174737813932673499110552097460075057937903551189702770834218764137277804912143768201762901437504585161963657583001600), (1376273, -1381986505854967461867423933050359317283961232159566797445514524574174456373742025401717985792656204991262885557432158156411941485887078400), (1376276, -2763973011709934923734847866100718634567922464319133594891029049148348912747484050803435971585312409982525771114864316312823882971774156800), (1376288, -3898777274786786255245424626566820984034866341098320184774847609897164212522479816754783209855754876003280396687748121864007562456982118400), (1376336, -2763973011709934923734847866100718634567922464319133594891029049148348912747484050803435971585312409982525771114864316312823882971774156800), (1376528, -1381986505854967461867423933050359317283961232159566797445514524574174456373742025401717985792656204991262885557432158156411941485887078400), (1380368, 1381986505854967461867423933050359317283961232159566797445514524574174456373742025401717985792656204991262885557432158156411941485887078400), (1392656, 660243263633966463810963687064722779362547989795420045782319756526222390860507731103560662041761911052122077321916707329045472557864345600), (1441808, 4145959517564902385602271799151077951851883696478700392336543573722523369121226076205153957377968614973788656672296474469235824457661235200), (1572867, -2466232329757166299855844584249477464939274105020750363774889528640042156930552104016275627338816647066753843315124800344368266842214400), (1572870, -4932464659514332599711689168498954929878548210041500727549779057280084313861104208032551254677633294133507686630249600688736533684428800), (1572873, -8144848236194820364446871358526842687487646556909167709138026438210968094039364149501906636179335330113913373631076452571693939688652800), (1572876, -16289696472389640728893742717053685374975293113818335418276052876421936188078728299003813272358670660227826747262152905143387879377305600), (1572882, -7398696989271498899567533752748432394817822315062251091324668585920126470791656312048826882016449941200261529945374401033104800526643200), (1572888, -24434544708584461093340614075580528062462939670727503127414079314632904282118092448505719908538005990341740120893229357715081819065958400), (1572897, -14316484715314489345125811493042670231545572543621259663214973683740157403661361840484011394901414110629108774461327176567114613542195200), (1572900, -28632969430628978690251622986085340463091145087242519326429947367480314807322723680968022789802828221258217548922654353134229227084390400), (1572912, -42949454145943468035377434479128010694636717630863778989644921051220472210984085521452034184704242331887326323383981529701343840626585600), (1572930, -4932464659514332599711689168498954929878548210041500727549779057280084313861104208032551254677633294133507686630249600688736533684428800), (1572936, -16289696472389640728893742717053685374975293113818335418276052876421936188078728299003813272358670660227826747262152905143387879377305600), (1572960, -28632969430628978690251622986085340463091145087242519326429947367480314807322723680968022789802828221258217548922654353134229227084390400), (1573122, -2466232329757166299855844584249477464939274105020750363774889528640042156930552104016275627338816647066753843315124800344368266842214400), (1573128, -8144848236194820364446871358526842687487646556909167709138026438210968094039364149501906636179335330113913373631076452571693939688652800), (1573152, -14316484715314489345125811493042670231545572543621259663214973683740157403661361840484011394901414110629108774461327176567114613542195200), (1576962, 2466232329757166299855844584249477464939274105020750363774889528640042156930552104016275627338816647066753843315124800344368266842214400), (1576968, 8144848236194820364446871358526842687487646556909167709138026438210968094039364149501906636179335330113913373631076452571693939688652800), (1576992, 14316484715314489345125811493042670231545572543621259663214973683740157403661361840484011394901414110629108774461327176567114613542195200), (1589250, 4932464659514332599711689168498954929878548210041500727549779057280084313861104208032551254677633294133507686630249600688736533684428800), (1589256, 16289696472389640728893742717053685374975293113818335418276052876421936188078728299003813272358670660227826747262152905143387879377305600), (1589265, -29751879535068876029538410190306812973818948954100905504790717391664674642596291266418305701672141553328743662092392618430120355574784000), (1589268, -59503759070137752059076820380613625947637897908201811009581434783329349285192582532836611403344283106657487324184785236860240711149568000), (1589280, -60622669174577649398363607584835098458365701775060197187942204807513709120466150118286894315213596438728013437354523502156131839639961600), (1589328, -59503759070137752059076820380613625947637897908201811009581434783329349285192582532836611403344283106657487324184785236860240711149568000), (1589520, -29751879535068876029538410190306812973818948954100905504790717391664674642596291266418305701672141553328743662092392618430120355574784000), (1593360, 29751879535068876029538410190306812973818948954100905504790717391664674642596291266418305701672141553328743662092392618430120355574784000), (1605648, 59503759070137752059076820380613625947637897908201811009581434783329349285192582532836611403344283106657487324184785236860240711149568000), (1638402, 7398696989271498899567533752748432394817822315062251091324668585920126470791656312048826882016449941200261529945374401033104800526643200), (1638408, 24434544708584461093340614075580528062462939670727503127414079314632904282118092448505719908538005990341740120893229357715081819065958400), (1638417, -27645765448833626581568248627228377666438627236786887369827142273767871896583705911183962518793459922924541802919582519571786775871283200), (1638420, -55291530897667253163136497254456755332877254473573774739654284547535743793167411822367925037586919845849083605839165039143573551742566400), (1638432, -39987842200557411709327311402557122304679164079496883119836505770083143478767032212099853371676137436886299085374766029014016486987264000), (1638480, -55291530897667253163136497254456755332877254473573774739654284547535743793167411822367925037586919845849083605839165039143573551742566400), (1638672, -27645765448833626581568248627228377666438627236786887369827142273767871896583705911183962518793459922924541802919582519571786775871283200), (1642512, 27645765448833626581568248627228377666438627236786887369827142273767871896583705911183962518793459922924541802919582519571786775871283200), (1654800, 144547169502873881251751727825377194254334101335876491254026436722529767720956285621622842142603344505835314592116342894433934618466918400), (1703952, 82937296346500879744704745881685132999315881710360662109481426821303615689751117733551887556380379768773625408758747558715360327613849600), (2097155, 53275095465350227276941298874958828095068663453981656630696286158557340014037205334562935359579608746781326385001596117789235474689638400), (2097158, 106550190930700454553882597749917656190137326907963313261392572317114680028074410669125870719159217493562652770003192235578470949379276800), (2097161, 97738178834337844373362456302322112249851758682910012509656317258531617128472369794022879634152023961366960483572917430860327276263833600), (2097164, 195476357668675688746724912604644224499703517365820025019312634517063234256944739588045759268304047922733920967145834861720654552527667200), (2097170, 159825286396050681830823896624876484285205990361944969892088858475672020042111616003688806078738826240343979155004788353367706424068915200), (2097176, 293214536503013533120087368906966336749555276048730037528968951775594851385417109382068638902456071884100881450718752292580981828791500800), (2097185, -19079909000293440014917079519361105763160989917524843667929176315554847952706328211751581765049597441056728094483471498500821850234675200), (2097188, -38159818000586880029834159038722211526321979835049687335858352631109695905412656423503163530099194882113456188966942997001643700469350400), (2097200, -57239727000880320044751238558083317289482969752574531003787528946664543858118984635254745295148792323170184283450414495502465550704025600), (2097218, 106550190930700454553882597749917656190137326907963313261392572317114680028074410669125870719159217493562652770003192235578470949379276800), (2097224, 195476357668675688746724912604644224499703517365820025019312634517063234256944739588045759268304047922733920967145834861720654552527667200), (2097248, -38159818000586880029834159038722211526321979835049687335858352631109695905412656423503163530099194882113456188966942997001643700469350400), (2097410, 53275095465350227276941298874958828095068663453981656630696286158557340014037205334562935359579608746781326385001596117789235474689638400), (2097416, 97738178834337844373362456302322112249851758682910012509656317258531617128472369794022879634152023961366960483572917430860327276263833600), (2097440, -19079909000293440014917079519361105763160989917524843667929176315554847952706328211751581765049597441056728094483471498500821850234675200), (2101250, -53275095465350227276941298874958828095068663453981656630696286158557340014037205334562935359579608746781326385001596117789235474689638400), (2101256, -97738178834337844373362456302322112249851758682910012509656317258531617128472369794022879634152023961366960483572917430860327276263833600), (2101280, 19079909000293440014917079519361105763160989917524843667929176315554847952706328211751581765049597441056728094483471498500821850234675200), (2113538, -106550190930700454553882597749917656190137326907963313261392572317114680028074410669125870719159217493562652770003192235578470949379276800), (2113544, -195476357668675688746724912604644224499703517365820025019312634517063234256944739588045759268304047922733920967145834861720654552527667200), (2113553, 331418835454832769552540019172951969746100820668176434566673702314822727457851060875524534435503236700434357359972271725701274141914316800), (2113556, 662837670909665539105080038345903939492201641336352869133347404629645454915702121751049068871006473400868714719944543451402548283828633600), (2113568, 1032416324365085188687454216557578120764624441839578991035879459575577878278965839050076766836608904983416528268883758174105466126212300800), (2113616, 662837670909665539105080038345903939492201641336352869133347404629645454915702121751049068871006473400868714719944543451402548283828633600), (2113808, 331418835454832769552540019172951969746100820668176434566673702314822727457851060875524534435503236700434357359972271725701274141914316800), (2117648, -331418835454832769552540019172951969746100820668176434566673702314822727457851060875524534435503236700434357359972271725701274141914316800), (2129936, -662837670909665539105080038345903939492201641336352869133347404629645454915702121751049068871006473400868714719944543451402548283828633600), (2162690, -159825286396050681830823896624876484285205990361944969892088858475672020042111616003688806078738826240343979155004788353367706424068915200), (2162696, -293214536503013533120087368906966336749555276048730037528968951775594851385417109382068638902456071884100881450718752292580981828791500800), (2162705, -180765980459634711033710683619134374026359952247047398013214627078921856123738027352816870392489704208757325553862960818023056008775270400), (2162708, -361531960919269422067421367238268748052719904494094796026429254157843712247476054705633740784979408417514651107725921636046112017550540800), (2162720, -485058214378023813056380812299319804789596886988567663035856352290101024513095097423195865882320320303101792378138467958566702475621785600), (2162768, -361531960919269422067421367238268748052719904494094796026429254157843712247476054705633740784979408417514651107725921636046112017550540800), (2162960, -180765980459634711033710683619134374026359952247047398013214627078921856123738027352816870392489704208757325553862960818023056008775270400), (2166800, 180765980459634711033710683619134374026359952247047398013214627078921856123738027352816870392489704208757325553862960818023056008775270400), (2179088, -632724545445228886590198690280587161185582557510434507673591852786624470126077127920939862521530301683788420972190893541057710408192409600), (2228240, 542297941378904133101132050857403122079079856741142194039643881236765568371214082058450611177469112626271976661588882454069168026325811200), (2359299, -3452911809268175953133809745248023236430831363092944208166456687593243579050159607614926786985225354649265521032628905080068944866508800), (2359302, -6905823618536351906267619490496046472861662726185888416332913375186487158100319215229853573970450709298531042065257810160137889733017600), (2359305, -8144848236194820364446871358526842687487646556909167709138026438210968094039364149501906636179335330113913373631076452571693939688652800), (2359308, -16289696472389640728893742717053685374975293113818335418276052876421936188078728299003813272358670660227826747262152905143387879377305600), (2359314, -10358735427804527859401429235744069709292494089278832624499370062779730737150478822844780360955676063947796563097886715240206834599526400), (2359320, -24434544708584461093340614075580528062462939670727503127414079314632904282118092448505719908538005990341740120893229357715081819065958400), (2359329, -10988108857091732221320295749056801575730093872283706703173327528936954828058139009949329559326866055925069648583746465334267916020838400), (2359332, -21976217714183464442640591498113603151460187744567413406346655057873909656116278019898659118653732111850139297167492930668535832041676800), (2359344, -32964326571275196663960887247170404727190281616851120109519982586810864484174417029847988677980598167775208945751239396002803748062515200), (2359362, -6905823618536351906267619490496046472861662726185888416332913375186487158100319215229853573970450709298531042065257810160137889733017600), (2359368, -16289696472389640728893742717053685374975293113818335418276052876421936188078728299003813272358670660227826747262152905143387879377305600), (2359392, -21976217714183464442640591498113603151460187744567413406346655057873909656116278019898659118653732111850139297167492930668535832041676800), (2359554, -3452911809268175953133809745248023236430831363092944208166456687593243579050159607614926786985225354649265521032628905080068944866508800), (2359560, -8144848236194820364446871358526842687487646556909167709138026438210968094039364149501906636179335330113913373631076452571693939688652800), (2359584, -10988108857091732221320295749056801575730093872283706703173327528936954828058139009949329559326866055925069648583746465334267916020838400), (2363394, 3452911809268175953133809745248023236430831363092944208166456687593243579050159607614926786985225354649265521032628905080068944866508800), (2363400, 8144848236194820364446871358526842687487646556909167709138026438210968094039364149501906636179335330113913373631076452571693939688652800), (2363424, 10988108857091732221320295749056801575730093872283706703173327528936954828058139009949329559326866055925069648583746465334267916020838400), (2375682, 6905823618536351906267619490496046472861662726185888416332913375186487158100319215229853573970450709298531042065257810160137889733017600), (2375688, 16289696472389640728893742717053685374975293113818335418276052876421936188078728299003813272358670660227826747262152905143387879377305600), (2375697, -28685057911485803412791705894026405226330342004891137526006762958949950965375273169689341785648705639182470054378374297785946600367155200), (2375700, -57370115822971606825583411788052810452660684009782275052013525917899901930750546339378683571297411278364940108756748595571893200734310400), (2375712, -64078956020273945795734526183965612527530838270105999171673633818975943240009541489169366238292384805697270865967629962689303969059788800), (2375760, -57370115822971606825583411788052810452660684009782275052013525917899901930750546339378683571297411278364940108756748595571893200734310400), (2375952, -28685057911485803412791705894026405226330342004891137526006762958949950965375273169689341785648705639182470054378374297785946600367155200), (2379792, 28685057911485803412791705894026405226330342004891137526006762958949950965375273169689341785648705639182470054378374297785946600367155200), (2392080, 57370115822971606825583411788052810452660684009782275052013525917899901930750546339378683571297411278364940108756748595571893200734310400), (2424834, 10358735427804527859401429235744069709292494089278832624499370062779730737150478822844780360955676063947796563097886715240206834599526400), (2424840, 24434544708584461093340614075580528062462939670727503127414079314632904282118092448505719908538005990341740120893229357715081819065958400), (2424864, 32964326571275196663960887247170404727190281616851120109519982586810864484174417029847988677980598167775208945751239396002803748062515200), (2441232, 86055173734457410238375117682079215678991026014673412578020288876849852896125819509068025356946116917547410163135122893357839801101465600), (3145731, -1479863762926395202137258302082189669307462873721712684186007948848815000389922370404525982210544687410592399583377669938589874296934400), (3145734, -2959727525852790404274516604164379338614925747443425368372015897697630000779844740809051964421089374821184799166755339877179748593868800), (3145737, -2714949412064940121482290452842280895829215518969722569712675479403656031346454716500635545393111776704637791210358817523897979896217600), (3145740, -5429898824129880242964580905684561791658431037939445139425350958807312062692909433001271090786223553409275582420717635047795959792435200), (3145746, -4439591288779185606411774906246569007922388621165138052558023846546445001169767111213577946631634062231777198750133009815769622890803200), (3145752, -8144848236194820364446871358526842687487646556909167709138026438210968094039364149501906636179335330113913373631076452571693939688652800), (3145761, -3650668918083944886354947572133547161837469672033327899644932673600589782356996116640902200809957804696410933366862449447360525266022400), (3145764, -7301337836167889772709895144267094323674939344066655799289865347201179564713992233281804401619915609392821866733724898894721050532044800), (3145776, -10952006754251834659064842716400641485512409016099983698934798020801769347070988349922706602429873414089232800100587348342081575798067200), (3145794, -2959727525852790404274516604164379338614925747443425368372015897697630000779844740809051964421089374821184799166755339877179748593868800), (3145800, -5429898824129880242964580905684561791658431037939445139425350958807312062692909433001271090786223553409275582420717635047795959792435200), (3145824, -7301337836167889772709895144267094323674939344066655799289865347201179564713992233281804401619915609392821866733724898894721050532044800), (3145986, -1479863762926395202137258302082189669307462873721712684186007948848815000389922370404525982210544687410592399583377669938589874296934400), (3145992, -2714949412064940121482290452842280895829215518969722569712675479403656031346454716500635545393111776704637791210358817523897979896217600), (3146016, -3650668918083944886354947572133547161837469672033327899644932673600589782356996116640902200809957804696410933366862449447360525266022400), (3149826, 1479863762926395202137258302082189669307462873721712684186007948848815000389922370404525982210544687410592399583377669938589874296934400), (3149832, 2714949412064940121482290452842280895829215518969722569712675479403656031346454716500635545393111776704637791210358817523897979896217600), (3149856, 3650668918083944886354947572133547161837469672033327899644932673600589782356996116640902200809957804696410933366862449447360525266022400), (3162114, 2959727525852790404274516604164379338614925747443425368372015897697630000779844740809051964421089374821184799166755339877179748593868800), (3162120, 5429898824129880242964580905684561791658431037939445139425350958807312062692909433001271090786223553409275582420717635047795959792435200), (3162129, -9869229623889892436365743087549083371130605420679831296940293515973732161732999965375818947599520831263670365672232705944139903371217920), (3162132, -19738459247779784872731486175098166742261210841359662593880587031947464323465999930751637895199041662527340731344465411888279806742435840), (3162144, -22306351035501787536387334118380155789716876917972838091531015200720016920485007662845652441178646884398189230282973218937698659581608960), (3162192, -19738459247779784872731486175098166742261210841359662593880587031947464323465999930751637895199041662527340731344465411888279806742435840), (3162384, -9869229623889892436365743087549083371130605420679831296940293515973732161732999965375818947599520831263670365672232705944139903371217920), (3166224, 9869229623889892436365743087549083371130605420679831296940293515973732161732999965375818947599520831263670365672232705944139903371217920), (3178512, 19738459247779784872731486175098166742261210841359662593880587031947464323465999930751637895199041662527340731344465411888279806742435840), (3211266, 4439591288779185606411774906246569007922388621165138052558023846546445001169767111213577946631634062231777198750133009815769622890803200), (3211272, 8144848236194820364446871358526842687487646556909167709138026438210968094039364149501906636179335330113913373631076452571693939688652800), (3211296, 10952006754251834659064842716400641485512409016099983698934798020801769347070988349922706602429873414089232800100587348342081575798067200), (3227664, 29607688871669677309097229262647250113391816262039493890820880547921196485198999896127456842798562493791011097016698117832419710113653760)]
theorem sparseBlock011_data : sparseBlock011 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (246592141707692774429646570541821948907952807824759419897220394947806789135157433402937411282067989914040360932936782601444598136320000 : Int) coeff0136) (CoefficientMerge.scale (739931881463197601068629151041094834653731436860856342093003974424407500194961185202262991105272343705296199791688834969294937148467200 : Int) coeff0137)) (CoefficientMerge.merge (CoefficientMerge.scale (1357474706032470060741145226421140447914607759484861284856337739701828015673227358250317772696555888352318895605179408761948989948108800 : Int) coeff0138) (CoefficientMerge.merge (CoefficientMerge.scale (1357474706032470060741145226421140447914607759484861284856337739701828015673227358250317772696555888352318895605179408761948989948108800 : Int) coeff0139) (CoefficientMerge.scale (310060986112564582909163092544323893146524008026235280114471080101528051789261089872325872564467318763204176902477251803283901498973798400 : Int) coeff0140)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (189586216740421875344788665640665273404681200868668035503285622346029792191539558241004409255947184978960245565515047351532390088118784000 : Int) coeff0141) (CoefficientMerge.scale (53779159914843166035865966502118957696830341069360112315091253618783567175131749464034963363476313803463113031722003640151963858094592000 : Int) coeff0142)) (CoefficientMerge.merge (CoefficientMerge.scale (1719192578517404556681253287987192704237845095079231977663422783796370315950911718328713861562392924391434151756726633706974378019635200 : Int) coeff0143) (CoefficientMerge.merge (CoefficientMerge.scale (17529342296698724027675976678559525975459231416322343096768616670086809391431207735757865937739671706648812279062711998875752353000652800 : Int) coeff0144) (CoefficientMerge.scale (2940810095589541078155221206171423147893508535826468770542769973090559996544097445169782205079327027555524650056484647966660218510592000 : Int) coeff0145))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (548712292563809926925010451888284760932965635858971659300519441111336182436012028418009813112925902144700379565736932373443392883097600 : Int) coeff0146) (CoefficientMerge.scale (1276622166478162516252463334178488819985769200157692290521946895688958708742486029902441287292053000203505087117694292350236869749913600 : Int) coeff0147)) (CoefficientMerge.merge (CoefficientMerge.scale (5136450193108658107714185747764536786884592650551778913929111970729899719969551560524544936282596244579169544967735156512382351797068800 : Int) coeff0148) (CoefficientMerge.merge (CoefficientMerge.scale (331575430627824418842037944150208772425013534393020723933012003614328199507457470527846495528882128125802441725390356781774477492354560 : Int) coeff0149) (CoefficientMerge.scale (4603039381317121799340833599624332913140289175946894924537134754372537881359042512160062978270878287506032741110725996190295474193254400 : Int) coeff0150)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (508471697253349177324801589849857646497485767288900470379885683551691172754174838749760044266578711961950433426084974372979358937269657600 : Int) coeff0151) (CoefficientMerge.scale (690993252927483730933711966525179658641980616079783398722757262287087228186871012700858992896328102495631442778716079078205970742943539200 : Int) coeff0152)) (CoefficientMerge.merge (CoefficientMerge.scale (90382990229817355516855341809567187013179976123523699006607313539460928061869013676408435196244852104378662776931480409011528004387635200 : Int) coeff0153) (CoefficientMerge.merge (CoefficientMerge.scale (8286786261552013964131040583746896379568231445213838291699652681827460698454695232668739339114505005021783890413500539979108818970163200 : Int) coeff0154) (CoefficientMerge.scale (13822882724416813290784124313614188833219313618393443684913571136883935948291852955591981259396729961462270901459791259785893387935641600 : Int) coeff0155)))))) := by decide +kernel
theorem sparseBlock011_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock011 := by
  rw [sparseBlock011_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted0136_nonneg g t z hg hA hB ht hz hw) (weighted0137_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0138_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0139_nonneg g t z hg hA hB ht hz hw) (weighted0140_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0141_nonneg g t z hg hA hB ht hz hw) (weighted0142_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0143_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0144_nonneg g t z hg hA hB ht hz hw) (weighted0145_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted0146_nonneg g t z hg hA hB ht hz hw) (weighted0147_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0148_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0149_nonneg g t z hg hA hB ht hz hw) (weighted0150_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0151_nonneg g t z hg hA hB ht hz hw) (weighted0152_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0153_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0154_nonneg g t z hg hA hB ht hz hw) (weighted0155_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
