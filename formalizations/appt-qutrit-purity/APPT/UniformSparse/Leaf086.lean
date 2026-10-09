import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff1085 : CoefficientMerge.Poly :=
  [(790800, 1)]
noncomputable def atom1085 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (t) ^ 3)
theorem atom1085_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1085 g t z = CoefficientMerge.eval (monomial g t z) coeff1085 := by
  norm_num [atom1085, coeff1085, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1085_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1085 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1085]
  positivity
theorem weighted1085_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (112973027595385244554008671282392778193785569292989055225154554534350866516816024907753138823351302981070284155257379337041710785160582400 : Int) coeff1085) := by
  rw [CoefficientMerge.eval_scale, ← atom1085_identity]
  exact mul_nonneg (by norm_num) (atom1085_nonneg g t z hg hA hB ht hz hw)

def coeff1086 : CoefficientMerge.Poly :=
  [(803088, 1)]
noncomputable def atom1086 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (t) ^ 3)
theorem atom1086_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1086 g t z = CoefficientMerge.eval (monomial g t z) coeff1086 := by
  norm_num [atom1086, coeff1086, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1086_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1086 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1086]
  positivity
theorem weighted1086_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (80452201032555334497811126436158347337691605360242185651628596175502428973351414454597707650203406301307527369197568568625982655393030400 : Int) coeff1086) := by
  rw [CoefficientMerge.eval_scale, ← atom1086_identity]
  exact mul_nonneg (by norm_num) (atom1086_nonneg g t z hg hA hB ht hz hw)

def coeff1087 : CoefficientMerge.Poly :=
  [(852240, 1)]
noncomputable def atom1087 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (t) ^ 3)
theorem atom1087_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1087 g t z = CoefficientMerge.eval (monomial g t z) coeff1087 := by
  norm_num [atom1087, coeff1087, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1087_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1087 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1087]
  positivity
theorem weighted1087_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (71444107839211690371092575477775559779153917347951571685669373341308555650655533553909351336216832552462874284752453853190262138198329600 : Int) coeff1087) := by
  rw [CoefficientMerge.eval_scale, ← atom1087_identity]
  exact mul_nonneg (by norm_num) (atom1087_nonneg g t z hg hA hB ht hz hw)

def coeff1088 : CoefficientMerge.Poly :=
  [(1573392, 1)]
noncomputable def atom1088 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 2 * (t) ^ 2 * (z) ^ 1)
theorem atom1088_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1088 g t z = CoefficientMerge.eval (monomial g t z) coeff1088 := by
  norm_num [atom1088, coeff1088, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1088_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1088 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1088]
  positivity
theorem weighted1088_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (265484341748382003144255462493684307843532701130747399159991700391046570883234397389641839061642897988970717916095597559375644589323667200 : Int) coeff1088) := by
  rw [CoefficientMerge.eval_scale, ← atom1088_identity]
  exact mul_nonneg (by norm_num) (atom1088_nonneg g t z hg hA hB ht hz hw)

def coeff1089 : CoefficientMerge.Poly :=
  [(1574160, 1)]
noncomputable def atom1089 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 5) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1089_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1089 g t z = CoefficientMerge.eval (monomial g t z) coeff1089 := by
  norm_num [atom1089, coeff1089, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1089_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1089 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1089]
  positivity
theorem weighted1089_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (395737036943494136042249353696961541505951793716672166774642317488925303173108115694198601675810729727802925824333944943828352276359801472 : Int) coeff1089) := by
  rw [CoefficientMerge.eval_scale, ← atom1089_identity]
  exact mul_nonneg (by norm_num) (atom1089_nonneg g t z hg hA hB ht hz hw)

def coeff1090 : CoefficientMerge.Poly :=
  [(1577232, 1)]
noncomputable def atom1090 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1090_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1090 g t z = CoefficientMerge.eval (monomial g t z) coeff1090 := by
  norm_num [atom1090, coeff1090, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1090_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1090 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1090]
  positivity
theorem weighted1090_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (304264262553929958375141584589661371916589133861295120847881792356747751715374521108930195072964116211410298024884229075927002118154648400 : Int) coeff1090) := by
  rw [CoefficientMerge.eval_scale, ← atom1090_identity]
  exact mul_nonneg (by norm_num) (atom1090_nonneg g t z hg hA hB ht hz hw)

def coeff1091 : CoefficientMerge.Poly :=
  [(1589520, 1)]
noncomputable def atom1091 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1091_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1091 g t z = CoefficientMerge.eval (monomial g t z) coeff1091 := by
  norm_num [atom1091, coeff1091, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1091_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1091 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1091]
  positivity
theorem weighted1091_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (285908534159922062518465775392823223425229430556732702991164187271547756939141083916281446260638686191711033314305198909398845253170582560 : Int) coeff1091) := by
  rw [CoefficientMerge.eval_scale, ← atom1091_identity]
  exact mul_nonneg (by norm_num) (atom1091_nonneg g t z hg hA hB ht hz hw)

def coeff1092 : CoefficientMerge.Poly :=
  [(1638672, 1)]
noncomputable def atom1092 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1092_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1092 g t z = CoefficientMerge.eval (monomial g t z) coeff1092 := by
  norm_num [atom1092, coeff1092, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1092_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1092 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1092]
  positivity
theorem weighted1092_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (185199476303127039284412498001764764407537152293144360843240113372643187206129236541150872723470572082885318256218859599987044173240823400 : Int) coeff1092) := by
  rw [CoefficientMerge.eval_scale, ← atom1092_identity]
  exact mul_nonneg (by norm_num) (atom1092_nonneg g t z hg hA hB ht hz hw)

def coeff1093 : CoefficientMerge.Poly :=
  [(788496, 1)]
noncomputable def atom1093 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 5) ^ 2 * (t) ^ 3)
theorem atom1093_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1093 g t z = CoefficientMerge.eval (monomial g t z) coeff1093 := by
  norm_num [atom1093, coeff1093, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1093_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1093 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1093]
  positivity
theorem weighted1093_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (127706628544200183030636802391377985833230875129622226238255645852509671868550761675926834596353243180026156010540076567285005792637491200 : Int) coeff1093) := by
  rw [CoefficientMerge.eval_scale, ← atom1093_identity]
  exact mul_nonneg (by norm_num) (atom1093_nonneg g t z hg hA hB ht hz hw)

def coeff1094 : CoefficientMerge.Poly :=
  [(791568, 1)]
noncomputable def atom1094 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (t) ^ 3)
theorem atom1094_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1094 g t z = CoefficientMerge.eval (monomial g t z) coeff1094 := by
  norm_num [atom1094, coeff1094, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1094_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1094 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1094]
  positivity
theorem weighted1094_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (199312284672684824413277319691469176027793126760745812686343908828336360147557181088209474710314340741314919862715888278289824199281694720 : Int) coeff1094) := by
  rw [CoefficientMerge.eval_scale, ← atom1094_identity]
  exact mul_nonneg (by norm_num) (atom1094_nonneg g t z hg hA hB ht hz hw)

def coeff1095 : CoefficientMerge.Poly :=
  [(803856, 1)]
noncomputable def atom1095 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (t) ^ 3)
theorem atom1095_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1095 g t z = CoefficientMerge.eval (monomial g t z) coeff1095 := by
  norm_num [atom1095, coeff1095, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1095_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1095 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1095]
  positivity
theorem weighted1095_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (150426967362856754107206471120489028984769334211078842220540283463111569413119676266593633367601250140819898328165263415039859490874316800 : Int) coeff1095) := by
  rw [CoefficientMerge.eval_scale, ← atom1095_identity]
  exact mul_nonneg (by norm_num) (atom1095_nonneg g t z hg hA hB ht hz hw)

def coeff1096 : CoefficientMerge.Poly :=
  [(853008, 1)]
noncomputable def atom1096 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (t) ^ 3)
theorem atom1096_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1096 g t z = CoefficientMerge.eval (monomial g t z) coeff1096 := by
  norm_num [atom1096, coeff1096, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1096_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1096 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1096]
  positivity
theorem weighted1096_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (152073114411661399845603727091165255961387024371697310371259658916630311842227552173515286907716283648623102224110831730132887712518451200 : Int) coeff1096) := by
  rw [CoefficientMerge.eval_scale, ← atom1096_identity]
  exact mul_nonneg (by norm_num) (atom1096_nonneg g t z hg hA hB ht hz hw)

def coeff1097 : CoefficientMerge.Poly :=
  [(1574928, 1)]
noncomputable def atom1097 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 5) ^ 2 * (t) ^ 2 * (z) ^ 1)
theorem atom1097_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1097 g t z = CoefficientMerge.eval (monomial g t z) coeff1097 := by
  norm_num [atom1097, coeff1097, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1097_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1097 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1097]
  positivity
theorem weighted1097_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (199716480255840761428945880774991034673650554114266469021343850042072292996256254557461587663712889707491107211013482333084089857531152960 : Int) coeff1097) := by
  rw [CoefficientMerge.eval_scale, ← atom1097_identity]
  exact mul_nonneg (by norm_num) (atom1097_nonneg g t z hg hA hB ht hz hw)

def coeff1098 : CoefficientMerge.Poly :=
  [(1578000, 1)]
noncomputable def atom1098 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1098_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1098 g t z = CoefficientMerge.eval (monomial g t z) coeff1098 := by
  norm_num [atom1098, coeff1098, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1098_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1098 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1098]
  positivity
theorem weighted1098_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (257605835091549997540522380174100738907635297302569761673395174313508765624333298860403476002838084708281037475086906353164220953511526240 : Int) coeff1098) := by
  rw [CoefficientMerge.eval_scale, ← atom1098_identity]
  exact mul_nonneg (by norm_num) (atom1098_nonneg g t z hg hA hB ht hz hw)

def coeff1099 : CoefficientMerge.Poly :=
  [(1590288, 1)]
noncomputable def atom1099 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1099_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1099 g t z = CoefficientMerge.eval (monomial g t z) coeff1099 := by
  norm_num [atom1099, coeff1099, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1099_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1099 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1099]
  positivity
theorem weighted1099_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (202653438440645594159265057625884204794122196800706009439181107747159786692206758012348035862196802813896411636411246459144281622634465280 : Int) coeff1099) := by
  rw [CoefficientMerge.eval_scale, ← atom1099_identity]
  exact mul_nonneg (by norm_num) (atom1099_nonneg g t z hg hA hB ht hz hw)

def coeff1100 : CoefficientMerge.Poly :=
  [(1639440, 1)]
noncomputable def atom1100 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1100_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1100 g t z = CoefficientMerge.eval (monomial g t z) coeff1100 := by
  norm_num [atom1100, coeff1100, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1100_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1100 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1100]
  positivity
theorem weighted1100_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (130781664634485349353663681798396428906056095257894358296123103577394036830833887488909501485873974937930270219579212885217927356092673280 : Int) coeff1100) := by
  rw [CoefficientMerge.eval_scale, ← atom1100_identity]
  exact mul_nonneg (by norm_num) (atom1100_nonneg g t z hg hA hB ht hz hw)

def coeff1101 : CoefficientMerge.Poly :=
  [(794640, 1)]
noncomputable def atom1101 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 6) ^ 2 * (t) ^ 3)
theorem atom1101_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1101 g t z = CoefficientMerge.eval (monomial g t z) coeff1101 := by
  norm_num [atom1101, coeff1101, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1101_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1101 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1101]
  positivity
theorem weighted1101_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (75013977125102854630612814964135298201263919665895521801240439552350513930647816751296748454052724433196190782192136934222445582146145280 : Int) coeff1101) := by
  rw [CoefficientMerge.eval_scale, ← atom1101_identity]
  exact mul_nonneg (by norm_num) (atom1101_nonneg g t z hg hA hB ht hz hw)

def coeff1102 : CoefficientMerge.Poly :=
  [(806928, 1)]
noncomputable def atom1102 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (t) ^ 3)
theorem atom1102_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1102 g t z = CoefficientMerge.eval (monomial g t z) coeff1102 := by
  norm_num [atom1102, coeff1102, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1102_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1102 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1102]
  positivity
theorem weighted1102_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (73197742872581857766943963877112765549031947819839517650199408251959185750407565166203040913573415789702443503532538275160903189985085440 : Int) coeff1102) := by
  rw [CoefficientMerge.eval_scale, ← atom1102_identity]
  exact mul_nonneg (by norm_num) (atom1102_nonneg g t z hg hA hB ht hz hw)

def coeff1103 : CoefficientMerge.Poly :=
  [(856080, 1)]
noncomputable def atom1103 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (t) ^ 3)
theorem atom1103_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1103 g t z = CoefficientMerge.eval (monomial g t z) coeff1103 := by
  norm_num [atom1103, coeff1103, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1103_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1103 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1103]
  positivity
theorem weighted1103_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (68938198558502681688835684870522428998914309248567628147264034898302184343150004016031069605102376309644782931680924264990020948207096320 : Int) coeff1103) := by
  rw [CoefficientMerge.eval_scale, ← atom1103_identity]
  exact mul_nonneg (by norm_num) (atom1103_nonneg g t z hg hA hB ht hz hw)

def coeff1104 : CoefficientMerge.Poly :=
  [(1581072, 1)]
noncomputable def atom1104 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 6) ^ 2 * (t) ^ 2 * (z) ^ 1)
theorem atom1104_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1104 g t z = CoefficientMerge.eval (monomial g t z) coeff1104 := by
  norm_num [atom1104, coeff1104, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1104_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1104 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1104]
  positivity
theorem weighted1104_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (74757041037307610881090415617182422226967005476970368525996104292468888664863562213657723140068137456282493431081365728222726929508608000 : Int) coeff1104) := by
  rw [CoefficientMerge.eval_scale, ← atom1104_identity]
  exact mul_nonneg (by norm_num) (atom1104_nonneg g t z hg hA hB ht hz hw)

def sparseBlock086 : CoefficientMerge.Poly :=
  [(788496, 127706628544200183030636802391377985833230875129622226238255645852509671868550761675926834596353243180026156010540076567285005792637491200), (790800, 112973027595385244554008671282392778193785569292989055225154554534350866516816024907753138823351302981070284155257379337041710785160582400), (791568, 199312284672684824413277319691469176027793126760745812686343908828336360147557181088209474710314340741314919862715888278289824199281694720), (794640, 75013977125102854630612814964135298201263919665895521801240439552350513930647816751296748454052724433196190782192136934222445582146145280), (803088, 80452201032555334497811126436158347337691605360242185651628596175502428973351414454597707650203406301307527369197568568625982655393030400), (803856, 150426967362856754107206471120489028984769334211078842220540283463111569413119676266593633367601250140819898328165263415039859490874316800), (806928, 73197742872581857766943963877112765549031947819839517650199408251959185750407565166203040913573415789702443503532538275160903189985085440), (852240, 71444107839211690371092575477775559779153917347951571685669373341308555650655533553909351336216832552462874284752453853190262138198329600), (853008, 152073114411661399845603727091165255961387024371697310371259658916630311842227552173515286907716283648623102224110831730132887712518451200), (856080, 68938198558502681688835684870522428998914309248567628147264034898302184343150004016031069605102376309644782931680924264990020948207096320), (1573392, 265484341748382003144255462493684307843532701130747399159991700391046570883234397389641839061642897988970717916095597559375644589323667200), (1574160, 395737036943494136042249353696961541505951793716672166774642317488925303173108115694198601675810729727802925824333944943828352276359801472), (1574928, 199716480255840761428945880774991034673650554114266469021343850042072292996256254557461587663712889707491107211013482333084089857531152960), (1577232, 304264262553929958375141584589661371916589133861295120847881792356747751715374521108930195072964116211410298024884229075927002118154648400), (1578000, 257605835091549997540522380174100738907635297302569761673395174313508765624333298860403476002838084708281037475086906353164220953511526240), (1581072, 74757041037307610881090415617182422226967005476970368525996104292468888664863562213657723140068137456282493431081365728222726929508608000), (1589520, 285908534159922062518465775392823223425229430556732702991164187271547756939141083916281446260638686191711033314305198909398845253170582560), (1590288, 202653438440645594159265057625884204794122196800706009439181107747159786692206758012348035862196802813896411636411246459144281622634465280), (1638672, 185199476303127039284412498001764764407537152293144360843240113372643187206129236541150872723470572082885318256218859599987044173240823400), (1639440, 130781664634485349353663681798396428906056095257894358296123103577394036830833887488909501485873974937930270219579212885217927356092673280)]
theorem sparseBlock086_data : sparseBlock086 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (112973027595385244554008671282392778193785569292989055225154554534350866516816024907753138823351302981070284155257379337041710785160582400 : Int) coeff1085) (CoefficientMerge.scale (80452201032555334497811126436158347337691605360242185651628596175502428973351414454597707650203406301307527369197568568625982655393030400 : Int) coeff1086)) (CoefficientMerge.merge (CoefficientMerge.scale (71444107839211690371092575477775559779153917347951571685669373341308555650655533553909351336216832552462874284752453853190262138198329600 : Int) coeff1087) (CoefficientMerge.merge (CoefficientMerge.scale (265484341748382003144255462493684307843532701130747399159991700391046570883234397389641839061642897988970717916095597559375644589323667200 : Int) coeff1088) (CoefficientMerge.scale (395737036943494136042249353696961541505951793716672166774642317488925303173108115694198601675810729727802925824333944943828352276359801472 : Int) coeff1089)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (304264262553929958375141584589661371916589133861295120847881792356747751715374521108930195072964116211410298024884229075927002118154648400 : Int) coeff1090) (CoefficientMerge.scale (285908534159922062518465775392823223425229430556732702991164187271547756939141083916281446260638686191711033314305198909398845253170582560 : Int) coeff1091)) (CoefficientMerge.merge (CoefficientMerge.scale (185199476303127039284412498001764764407537152293144360843240113372643187206129236541150872723470572082885318256218859599987044173240823400 : Int) coeff1092) (CoefficientMerge.merge (CoefficientMerge.scale (127706628544200183030636802391377985833230875129622226238255645852509671868550761675926834596353243180026156010540076567285005792637491200 : Int) coeff1093) (CoefficientMerge.scale (199312284672684824413277319691469176027793126760745812686343908828336360147557181088209474710314340741314919862715888278289824199281694720 : Int) coeff1094))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (150426967362856754107206471120489028984769334211078842220540283463111569413119676266593633367601250140819898328165263415039859490874316800 : Int) coeff1095) (CoefficientMerge.scale (152073114411661399845603727091165255961387024371697310371259658916630311842227552173515286907716283648623102224110831730132887712518451200 : Int) coeff1096)) (CoefficientMerge.merge (CoefficientMerge.scale (199716480255840761428945880774991034673650554114266469021343850042072292996256254557461587663712889707491107211013482333084089857531152960 : Int) coeff1097) (CoefficientMerge.merge (CoefficientMerge.scale (257605835091549997540522380174100738907635297302569761673395174313508765624333298860403476002838084708281037475086906353164220953511526240 : Int) coeff1098) (CoefficientMerge.scale (202653438440645594159265057625884204794122196800706009439181107747159786692206758012348035862196802813896411636411246459144281622634465280 : Int) coeff1099)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (130781664634485349353663681798396428906056095257894358296123103577394036830833887488909501485873974937930270219579212885217927356092673280 : Int) coeff1100) (CoefficientMerge.scale (75013977125102854630612814964135298201263919665895521801240439552350513930647816751296748454052724433196190782192136934222445582146145280 : Int) coeff1101)) (CoefficientMerge.merge (CoefficientMerge.scale (73197742872581857766943963877112765549031947819839517650199408251959185750407565166203040913573415789702443503532538275160903189985085440 : Int) coeff1102) (CoefficientMerge.merge (CoefficientMerge.scale (68938198558502681688835684870522428998914309248567628147264034898302184343150004016031069605102376309644782931680924264990020948207096320 : Int) coeff1103) (CoefficientMerge.scale (74757041037307610881090415617182422226967005476970368525996104292468888664863562213657723140068137456282493431081365728222726929508608000 : Int) coeff1104)))))) := by decide +kernel
theorem sparseBlock086_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock086 := by
  rw [sparseBlock086_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted1085_nonneg g t z hg hA hB ht hz hw) (weighted1086_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1087_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1088_nonneg g t z hg hA hB ht hz hw) (weighted1089_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1090_nonneg g t z hg hA hB ht hz hw) (weighted1091_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1092_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1093_nonneg g t z hg hA hB ht hz hw) (weighted1094_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted1095_nonneg g t z hg hA hB ht hz hw) (weighted1096_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1097_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1098_nonneg g t z hg hA hB ht hz hw) (weighted1099_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1100_nonneg g t z hg hA hB ht hz hw) (weighted1101_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1102_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1103_nonneg g t z hg hA hB ht hz hw) (weighted1104_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
