import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff1145 : CoefficientMerge.Poly :=
  [(1638720, 1)]
noncomputable def atom1145 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1145_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1145 g t z = CoefficientMerge.eval (monomial g t z) coeff1145 := by
  norm_num [atom1145, coeff1145, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1145_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1145 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1145]
  positivity
theorem weighted1145_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (164449872333319511861414855561124347391571714417880842830028699330566585676999713262465586322288307554377411529268223219433664598656969200 : Int) coeff1145) := by
  rw [CoefficientMerge.eval_scale, ← atom1145_identity]
  exact mul_nonneg (by norm_num) (atom1145_nonneg g t z hg hA hB ht hz hw)

def coeff1146 : CoefficientMerge.Poly :=
  [(788544, 1)]
noncomputable def atom1146 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 5) ^ 2 * (t) ^ 3)
theorem atom1146_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1146 g t z = CoefficientMerge.eval (monomial g t z) coeff1146 := by
  norm_num [atom1146, coeff1146, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1146_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1146 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1146]
  positivity
theorem weighted1146_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (131287706798445241559164379378428958876239509543023554768588454494963107340212457410811553109385837518873157015497016694647259663252736000 : Int) coeff1146) := by
  rw [CoefficientMerge.eval_scale, ← atom1146_identity]
  exact mul_nonneg (by norm_num) (atom1146_nonneg g t z hg hA hB ht hz hw)

def coeff1147 : CoefficientMerge.Poly :=
  [(791616, 1)]
noncomputable def atom1147 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (t) ^ 3)
theorem atom1147_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1147 g t z = CoefficientMerge.eval (monomial g t z) coeff1147 := by
  norm_num [atom1147, coeff1147, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1147_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1147 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1147]
  positivity
theorem weighted1147_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (235583070204005259690693591890973790879588419845487753152744074425246790178148296155869152592594452044730222689349014263294177183465907200 : Int) coeff1147) := by
  rw [CoefficientMerge.eval_scale, ← atom1147_identity]
  exact mul_nonneg (by norm_num) (atom1147_nonneg g t z hg hA hB ht hz hw)

def coeff1148 : CoefficientMerge.Poly :=
  [(803904, 1)]
noncomputable def atom1148 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (t) ^ 3)
theorem atom1148_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1148 g t z = CoefficientMerge.eval (monomial g t z) coeff1148 := by
  norm_num [atom1148, coeff1148, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1148_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1148 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1148]
  positivity
theorem weighted1148_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (206024493066763670504545022293857404596945710330885312586364059901188214968673152730075119642815260353984613329200595381231240596346675200 : Int) coeff1148) := by
  rw [CoefficientMerge.eval_scale, ← atom1148_identity]
  exact mul_nonneg (by norm_num) (atom1148_nonneg g t z hg hA hB ht hz hw)

def coeff1149 : CoefficientMerge.Poly :=
  [(853056, 1)]
noncomputable def atom1149 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (t) ^ 3)
theorem atom1149_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1149 g t z = CoefficientMerge.eval (monomial g t z) coeff1149 := by
  norm_num [atom1149, coeff1149, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1149_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1149 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1149]
  positivity
theorem weighted1149_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (180083170380981572814625647312108082247979527802686455299969929285737906273988396007794111071599958159086647972366804884286441634992371200 : Int) coeff1149) := by
  rw [CoefficientMerge.eval_scale, ← atom1149_identity]
  exact mul_nonneg (by norm_num) (atom1149_nonneg g t z hg hA hB ht hz hw)

def coeff1150 : CoefficientMerge.Poly :=
  [(1574976, 1)]
noncomputable def atom1150 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 5) ^ 2 * (t) ^ 2 * (z) ^ 1)
theorem atom1150_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1150 g t z = CoefficientMerge.eval (monomial g t z) coeff1150 := by
  norm_num [atom1150, coeff1150, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1150_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1150 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1150]
  positivity
theorem weighted1150_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (390804558507517223165634726164870470937466682180640325189891005315872558663052232503694888663843221121202464715587754671701078003411896320 : Int) coeff1150) := by
  rw [CoefficientMerge.eval_scale, ← atom1150_identity]
  exact mul_nonneg (by norm_num) (atom1150_nonneg g t z hg hA hB ht hz hw)

def coeff1151 : CoefficientMerge.Poly :=
  [(1578048, 1)]
noncomputable def atom1151 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1151_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1151 g t z = CoefficientMerge.eval (monomial g t z) coeff1151 := by
  norm_num [atom1151, coeff1151, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1151_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1151 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1151]
  positivity
theorem weighted1151_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (708667583160185770502471550816345709555434442394218275396867910263440774106469799280395549313441355942179539476782286965854174483760760320 : Int) coeff1151) := by
  rw [CoefficientMerge.eval_scale, ← atom1151_identity]
  exact mul_nonneg (by norm_num) (atom1151_nonneg g t z hg hA hB ht hz hw)

def coeff1152 : CoefficientMerge.Poly :=
  [(1590336, 1)]
noncomputable def atom1152 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1152_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1152 g t z = CoefficientMerge.eval (monomial g t z) coeff1152 := by
  norm_num [atom1152, coeff1152, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1152_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1152 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1152]
  positivity
theorem weighted1152_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (648875431184857033246177637841575402305646389302369708307561130462693562180867659877303502500962448076189651873642377833810137403685957120 : Int) coeff1152) := by
  rw [CoefficientMerge.eval_scale, ← atom1152_identity]
  exact mul_nonneg (by norm_num) (atom1152_nonneg g t z hg hA hB ht hz hw)

def coeff1153 : CoefficientMerge.Poly :=
  [(1639488, 1)]
noncomputable def atom1153 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1153_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1153 g t z = CoefficientMerge.eval (monomial g t z) coeff1153 := by
  norm_num [atom1153, coeff1153, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1153_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1153 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1153]
  positivity
theorem weighted1153_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (557029076696691566528672296538990935043751028915209698616408038416589816116927277128238242173607168049831058841543973738258727722621809920 : Int) coeff1153) := by
  rw [CoefficientMerge.eval_scale, ← atom1153_identity]
  exact mul_nonneg (by norm_num) (atom1153_nonneg g t z hg hA hB ht hz hw)

def coeff1154 : CoefficientMerge.Poly :=
  [(794688, 1)]
noncomputable def atom1154 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 6) ^ 2 * (t) ^ 3)
theorem atom1154_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1154 g t z = CoefficientMerge.eval (monomial g t z) coeff1154 := by
  norm_num [atom1154, coeff1154, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1154_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1154 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1154]
  positivity
theorem weighted1154_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (113235183194105382199884447232682793125641595734913049070768348544112545806667665625682060428131082707761457436974597331808475568314598400 : Int) coeff1154) := by
  rw [CoefficientMerge.eval_scale, ← atom1154_identity]
  exact mul_nonneg (by norm_num) (atom1154_nonneg g t z hg hA hB ht hz hw)

def coeff1155 : CoefficientMerge.Poly :=
  [(806976, 1)]
noncomputable def atom1155 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (t) ^ 3)
theorem atom1155_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1155 g t z = CoefficientMerge.eval (monomial g t z) coeff1155 := by
  norm_num [atom1155, coeff1155, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1155_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1155 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1155]
  positivity
theorem weighted1155_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (184549637814014228930073621895521525183806523800397107583888946558818643147742921673422915742177885605820247274032572806394938481174835200 : Int) coeff1155) := by
  rw [CoefficientMerge.eval_scale, ← atom1155_identity]
  exact mul_nonneg (by norm_num) (atom1155_nonneg g t z hg hA hB ht hz hw)

def coeff1156 : CoefficientMerge.Poly :=
  [(856128, 1)]
noncomputable def atom1156 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (t) ^ 3)
theorem atom1156_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1156 g t z = CoefficientMerge.eval (monomial g t z) coeff1156 := by
  norm_num [atom1156, coeff1156, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1156_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1156 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1156]
  positivity
theorem weighted1156_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (160013806252966018057566767321534993341718598688790787182150216378211300974387401703555113569587777824424450555451287328894180557008396800 : Int) coeff1156) := by
  rw [CoefficientMerge.eval_scale, ← atom1156_identity]
  exact mul_nonneg (by norm_num) (atom1156_nonneg g t z hg hA hB ht hz hw)

def coeff1157 : CoefficientMerge.Poly :=
  [(1581120, 1)]
noncomputable def atom1157 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 6) ^ 2 * (t) ^ 2 * (z) ^ 1)
theorem atom1157_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1157 g t z = CoefficientMerge.eval (monomial g t z) coeff1157 := by
  norm_num [atom1157, coeff1157, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1157_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1157 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1157]
  positivity
theorem weighted1157_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (341478083507415669060609358988006238985554353392922151034270510183483231802135864871949106509399944338438657651804813146839673622983603200 : Int) coeff1157) := by
  rw [CoefficientMerge.eval_scale, ← atom1157_identity]
  exact mul_nonneg (by norm_num) (atom1157_nonneg g t z hg hA hB ht hz hw)

def coeff1158 : CoefficientMerge.Poly :=
  [(1593408, 1)]
noncomputable def atom1158 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1158_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1158 g t z = CoefficientMerge.eval (monomial g t z) coeff1158 := by
  norm_num [atom1158, coeff1158, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1158_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1158 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1158]
  positivity
theorem weighted1158_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (591727500724236422098131116209764161501393866271751244071870164940929764794730120436061409683350378286355480105801190888195414293185945600 : Int) coeff1158) := by
  rw [CoefficientMerge.eval_scale, ← atom1158_identity]
  exact mul_nonneg (by norm_num) (atom1158_nonneg g t z hg hA hB ht hz hw)

def coeff1159 : CoefficientMerge.Poly :=
  [(1642560, 1)]
noncomputable def atom1159 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1159_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1159 g t z = CoefficientMerge.eval (monomial g t z) coeff1159 := by
  norm_num [atom1159, coeff1159, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1159_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1159 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1159]
  positivity
theorem weighted1159_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (497103016860155580527993706638944569939642155634069945034041228403306930941466978020864303589845870565986730252119868046355429083293228800 : Int) coeff1159) := by
  rw [CoefficientMerge.eval_scale, ← atom1159_identity]
  exact mul_nonneg (by norm_num) (atom1159_nonneg g t z hg hA hB ht hz hw)

def coeff1160 : CoefficientMerge.Poly :=
  [(819264, 1)]
noncomputable def atom1160 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 7) ^ 2 * (t) ^ 3)
theorem atom1160_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1160 g t z = CoefficientMerge.eval (monomial g t z) coeff1160 := by
  norm_num [atom1160, coeff1160, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1160_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1160 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1160]
  positivity
theorem weighted1160_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (79758946604563034507832263148878883528769202917356259278145472451773790081855966275075431725839825570357523812795260866103865103015724800 : Int) coeff1160) := by
  rw [CoefficientMerge.eval_scale, ← atom1160_identity]
  exact mul_nonneg (by norm_num) (atom1160_nonneg g t z hg hA hB ht hz hw)

def coeff1161 : CoefficientMerge.Poly :=
  [(868416, 1)]
noncomputable def atom1161 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (t) ^ 3)
theorem atom1161_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1161 g t z = CoefficientMerge.eval (monomial g t z) coeff1161 := by
  norm_num [atom1161, coeff1161, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1161_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1161 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1161]
  positivity
theorem weighted1161_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (123989872850306897853277776070622192836305022529404124167832029139916744800409463166990695204042241257534031582235437926776186386799302400 : Int) coeff1161) := by
  rw [CoefficientMerge.eval_scale, ← atom1161_identity]
  exact mul_nonneg (by norm_num) (atom1161_nonneg g t z hg hA hB ht hz hw)

def coeff1162 : CoefficientMerge.Poly :=
  [(1605696, 1)]
noncomputable def atom1162 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 7) ^ 2 * (t) ^ 2 * (z) ^ 1)
theorem atom1162_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1162 g t z = CoefficientMerge.eval (monomial g t z) coeff1162 := by
  norm_num [atom1162, coeff1162, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1162_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1162 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1162]
  positivity
theorem weighted1162_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (264734800298942482987193848055267476539111463137866691893990694473536237239450174996406091052927841382144535079667266507784659660586188800 : Int) coeff1162) := by
  rw [CoefficientMerge.eval_scale, ← atom1162_identity]
  exact mul_nonneg (by norm_num) (atom1162_nonneg g t z hg hA hB ht hz hw)

def coeff1163 : CoefficientMerge.Poly :=
  [(1654848, 1)]
noncomputable def atom1163 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1163_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1163 g t z = CoefficientMerge.eval (monomial g t z) coeff1163 := by
  norm_num [atom1163, coeff1163, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1163_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1163 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1163]
  positivity
theorem weighted1163_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (431602258800000340234860306013844597188692888715134392359264797506909950597056797901948093945688637842369744173654550661061078808214956800 : Int) coeff1163) := by
  rw [CoefficientMerge.eval_scale, ← atom1163_identity]
  exact mul_nonneg (by norm_num) (atom1163_nonneg g t z hg hA hB ht hz hw)

def coeff1164 : CoefficientMerge.Poly :=
  [(917568, 1)]
noncomputable def atom1164 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 8) ^ 2 * (t) ^ 3)
theorem atom1164_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1164 g t z = CoefficientMerge.eval (monomial g t z) coeff1164 := by
  norm_num [atom1164, coeff1164, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1164_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1164 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1164]
  positivity
theorem weighted1164_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (52326714968554948620211079402119724250035373635122681477674573905651989795909931400899959943535531083368868503064069146917688715510476800 : Int) coeff1164) := by
  rw [CoefficientMerge.eval_scale, ← atom1164_identity]
  exact mul_nonneg (by norm_num) (atom1164_nonneg g t z hg hA hB ht hz hw)

def sparseBlock089 : CoefficientMerge.Poly :=
  [(788544, 131287706798445241559164379378428958876239509543023554768588454494963107340212457410811553109385837518873157015497016694647259663252736000), (791616, 235583070204005259690693591890973790879588419845487753152744074425246790178148296155869152592594452044730222689349014263294177183465907200), (794688, 113235183194105382199884447232682793125641595734913049070768348544112545806667665625682060428131082707761457436974597331808475568314598400), (803904, 206024493066763670504545022293857404596945710330885312586364059901188214968673152730075119642815260353984613329200595381231240596346675200), (806976, 184549637814014228930073621895521525183806523800397107583888946558818643147742921673422915742177885605820247274032572806394938481174835200), (819264, 79758946604563034507832263148878883528769202917356259278145472451773790081855966275075431725839825570357523812795260866103865103015724800), (853056, 180083170380981572814625647312108082247979527802686455299969929285737906273988396007794111071599958159086647972366804884286441634992371200), (856128, 160013806252966018057566767321534993341718598688790787182150216378211300974387401703555113569587777824424450555451287328894180557008396800), (868416, 123989872850306897853277776070622192836305022529404124167832029139916744800409463166990695204042241257534031582235437926776186386799302400), (917568, 52326714968554948620211079402119724250035373635122681477674573905651989795909931400899959943535531083368868503064069146917688715510476800), (1574976, 390804558507517223165634726164870470937466682180640325189891005315872558663052232503694888663843221121202464715587754671701078003411896320), (1578048, 708667583160185770502471550816345709555434442394218275396867910263440774106469799280395549313441355942179539476782286965854174483760760320), (1581120, 341478083507415669060609358988006238985554353392922151034270510183483231802135864871949106509399944338438657651804813146839673622983603200), (1590336, 648875431184857033246177637841575402305646389302369708307561130462693562180867659877303502500962448076189651873642377833810137403685957120), (1593408, 591727500724236422098131116209764161501393866271751244071870164940929764794730120436061409683350378286355480105801190888195414293185945600), (1605696, 264734800298942482987193848055267476539111463137866691893990694473536237239450174996406091052927841382144535079667266507784659660586188800), (1638720, 164449872333319511861414855561124347391571714417880842830028699330566585676999713262465586322288307554377411529268223219433664598656969200), (1639488, 557029076696691566528672296538990935043751028915209698616408038416589816116927277128238242173607168049831058841543973738258727722621809920), (1642560, 497103016860155580527993706638944569939642155634069945034041228403306930941466978020864303589845870565986730252119868046355429083293228800), (1654848, 431602258800000340234860306013844597188692888715134392359264797506909950597056797901948093945688637842369744173654550661061078808214956800)]
theorem sparseBlock089_data : sparseBlock089 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (164449872333319511861414855561124347391571714417880842830028699330566585676999713262465586322288307554377411529268223219433664598656969200 : Int) coeff1145) (CoefficientMerge.scale (131287706798445241559164379378428958876239509543023554768588454494963107340212457410811553109385837518873157015497016694647259663252736000 : Int) coeff1146)) (CoefficientMerge.merge (CoefficientMerge.scale (235583070204005259690693591890973790879588419845487753152744074425246790178148296155869152592594452044730222689349014263294177183465907200 : Int) coeff1147) (CoefficientMerge.merge (CoefficientMerge.scale (206024493066763670504545022293857404596945710330885312586364059901188214968673152730075119642815260353984613329200595381231240596346675200 : Int) coeff1148) (CoefficientMerge.scale (180083170380981572814625647312108082247979527802686455299969929285737906273988396007794111071599958159086647972366804884286441634992371200 : Int) coeff1149)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (390804558507517223165634726164870470937466682180640325189891005315872558663052232503694888663843221121202464715587754671701078003411896320 : Int) coeff1150) (CoefficientMerge.scale (708667583160185770502471550816345709555434442394218275396867910263440774106469799280395549313441355942179539476782286965854174483760760320 : Int) coeff1151)) (CoefficientMerge.merge (CoefficientMerge.scale (648875431184857033246177637841575402305646389302369708307561130462693562180867659877303502500962448076189651873642377833810137403685957120 : Int) coeff1152) (CoefficientMerge.merge (CoefficientMerge.scale (557029076696691566528672296538990935043751028915209698616408038416589816116927277128238242173607168049831058841543973738258727722621809920 : Int) coeff1153) (CoefficientMerge.scale (113235183194105382199884447232682793125641595734913049070768348544112545806667665625682060428131082707761457436974597331808475568314598400 : Int) coeff1154))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (184549637814014228930073621895521525183806523800397107583888946558818643147742921673422915742177885605820247274032572806394938481174835200 : Int) coeff1155) (CoefficientMerge.scale (160013806252966018057566767321534993341718598688790787182150216378211300974387401703555113569587777824424450555451287328894180557008396800 : Int) coeff1156)) (CoefficientMerge.merge (CoefficientMerge.scale (341478083507415669060609358988006238985554353392922151034270510183483231802135864871949106509399944338438657651804813146839673622983603200 : Int) coeff1157) (CoefficientMerge.merge (CoefficientMerge.scale (591727500724236422098131116209764161501393866271751244071870164940929764794730120436061409683350378286355480105801190888195414293185945600 : Int) coeff1158) (CoefficientMerge.scale (497103016860155580527993706638944569939642155634069945034041228403306930941466978020864303589845870565986730252119868046355429083293228800 : Int) coeff1159)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (79758946604563034507832263148878883528769202917356259278145472451773790081855966275075431725839825570357523812795260866103865103015724800 : Int) coeff1160) (CoefficientMerge.scale (123989872850306897853277776070622192836305022529404124167832029139916744800409463166990695204042241257534031582235437926776186386799302400 : Int) coeff1161)) (CoefficientMerge.merge (CoefficientMerge.scale (264734800298942482987193848055267476539111463137866691893990694473536237239450174996406091052927841382144535079667266507784659660586188800 : Int) coeff1162) (CoefficientMerge.merge (CoefficientMerge.scale (431602258800000340234860306013844597188692888715134392359264797506909950597056797901948093945688637842369744173654550661061078808214956800 : Int) coeff1163) (CoefficientMerge.scale (52326714968554948620211079402119724250035373635122681477674573905651989795909931400899959943535531083368868503064069146917688715510476800 : Int) coeff1164)))))) := by decide +kernel
theorem sparseBlock089_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock089 := by
  rw [sparseBlock089_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted1145_nonneg g t z hg hA hB ht hz hw) (weighted1146_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1147_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1148_nonneg g t z hg hA hB ht hz hw) (weighted1149_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1150_nonneg g t z hg hA hB ht hz hw) (weighted1151_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1152_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1153_nonneg g t z hg hA hB ht hz hw) (weighted1154_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted1155_nonneg g t z hg hA hB ht hz hw) (weighted1156_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1157_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1158_nonneg g t z hg hA hB ht hz hw) (weighted1159_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1160_nonneg g t z hg hA hB ht hz hw) (weighted1161_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1162_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1163_nonneg g t z hg hA hB ht hz hw) (weighted1164_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
