import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff0905 : CoefficientMerge.Poly :=
  [(528512, 1)]
noncomputable def atom0905 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 2 * (g 6) ^ 1 * (t) ^ 2)
theorem atom0905_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0905 g t z = CoefficientMerge.eval (monomial g t z) coeff0905 := by
  norm_num [atom0905, coeff0905, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0905_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0905 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0905]
  positivity
theorem weighted0905_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (838053979964210027713455841136339166966701956252069464745749868527244424951387066769917944961719853518165924992448370206336594940736556800 : Int) coeff0905) := by
  rw [CoefficientMerge.eval_scale, ← atom0905_identity]
  exact mul_nonneg (by norm_num) (atom0905_nonneg g t z hg hA hB ht hz hw)

def coeff0906 : CoefficientMerge.Poly :=
  [(540800, 1)]
noncomputable def atom0906 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 2 * (g 7) ^ 1 * (t) ^ 2)
theorem atom0906_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0906 g t z = CoefficientMerge.eval (monomial g t z) coeff0906 := by
  norm_num [atom0906, coeff0906, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0906_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0906 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0906]
  positivity
theorem weighted0906_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (359374224604933178676671400795718624374585196735435517256546664150046088447220902586336635621140244026511297848988638267517990301130592000 : Int) coeff0906) := by
  rw [CoefficientMerge.eval_scale, ← atom0906_identity]
  exact mul_nonneg (by norm_num) (atom0906_nonneg g t z hg hA hB ht hz hw)

def coeff0907 : CoefficientMerge.Poly :=
  [(589952, 1)]
noncomputable def atom0907 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 2 * (g 8) ^ 1 * (t) ^ 2)
theorem atom0907_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0907 g t z = CoefficientMerge.eval (monomial g t z) coeff0907 := by
  norm_num [atom0907, coeff0907, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0907_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0907 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0907]
  positivity
theorem weighted0907_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1925707151497568728520620526669065677956273019518996512694788665235341139781742159360574836478670306919752342528112650878806825539104608000 : Int) coeff0907) := by
  rw [CoefficientMerge.eval_scale, ← atom0907_identity]
  exact mul_nonneg (by norm_num) (atom0907_nonneg g t z hg hA hB ht hz hw)

def coeff0908 : CoefficientMerge.Poly :=
  [(1311872, 1)]
noncomputable def atom0908 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 2 * (g 5) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0908_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0908 g t z = CoefficientMerge.eval (monomial g t z) coeff0908 := by
  norm_num [atom0908, coeff0908, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0908_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0908 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0908]
  positivity
theorem weighted0908_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1340479297298677268531013446193006873290616059566219365297549931797750982370780279503641205631336180553818053884151067050525871839362465600 : Int) coeff0908) := by
  rw [CoefficientMerge.eval_scale, ← atom0908_identity]
  exact mul_nonneg (by norm_num) (atom0908_nonneg g t z hg hA hB ht hz hw)

def coeff0909 : CoefficientMerge.Poly :=
  [(1314944, 1)]
noncomputable def atom0909 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 2 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0909_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0909 g t z = CoefficientMerge.eval (monomial g t z) coeff0909 := by
  norm_num [atom0909, coeff0909, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0909_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0909 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0909]
  positivity
theorem weighted0909_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2772115647282303276978334417745536002686009400258179040999651515822231917289982819598667150067094664807089747229376098295276108454929145440 : Int) coeff0909) := by
  rw [CoefficientMerge.eval_scale, ← atom0909_identity]
  exact mul_nonneg (by norm_num) (atom0909_nonneg g t z hg hA hB ht hz hw)

def coeff0910 : CoefficientMerge.Poly :=
  [(1327232, 1)]
noncomputable def atom0910 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 2 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0910_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0910 g t z = CoefficientMerge.eval (monomial g t z) coeff0910 := by
  norm_num [atom0910, coeff0910, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0910_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0910 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0910]
  positivity
theorem weighted0910_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1638880760921465335663869366611125372537440637089381743714766682034514677504098179184962904728160102092113614941600398881335213313908947040 : Int) coeff0910) := by
  rw [CoefficientMerge.eval_scale, ← atom0910_identity]
  exact mul_nonneg (by norm_num) (atom0910_nonneg g t z hg hA hB ht hz hw)

def coeff0911 : CoefficientMerge.Poly :=
  [(1376384, 1)]
noncomputable def atom0911 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 2 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0911_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0911 g t z = CoefficientMerge.eval (monomial g t z) coeff0911 := by
  norm_num [atom0911, coeff0911, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0911_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0911 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0911]
  positivity
theorem weighted0911_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4996413110909116053416236977451320077595060084369272299970523744125427128443090440397508972516401911536938316709586324812775123579668102240 : Int) coeff0911) := by
  rw [CoefficientMerge.eval_scale, ← atom0911_identity]
  exact mul_nonneg (by norm_num) (atom0911_nonneg g t z hg hA hB ht hz hw)

def coeff0912 : CoefficientMerge.Poly :=
  [(525632, 1)]
noncomputable def atom0912 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 1 * (g 5) ^ 1 * (t) ^ 2)
theorem atom0912_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0912 g t z = CoefficientMerge.eval (monomial g t z) coeff0912 := by
  norm_num [atom0912, coeff0912, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0912_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0912 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0912]
  positivity
theorem weighted0912_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (484292505263488553260437313959151404386231506294562526342556987696244003499025027623973233597936972055005955723909935797401580460030720000 : Int) coeff0912) := by
  rw [CoefficientMerge.eval_scale, ← atom0912_identity]
  exact mul_nonneg (by norm_num) (atom0912_nonneg g t z hg hA hB ht hz hw)

def coeff0913 : CoefficientMerge.Poly :=
  [(528704, 1)]
noncomputable def atom0913 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (t) ^ 2)
theorem atom0913_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0913 g t z = CoefficientMerge.eval (monomial g t z) coeff0913 := by
  norm_num [atom0913, coeff0913, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0913_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0913 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0913]
  positivity
theorem weighted0913_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3052226842482688149286657246188998240100660602994891714338858853442879625694256875126156033001548330141613975192860570956941987082265811200 : Int) coeff0913) := by
  rw [CoefficientMerge.eval_scale, ← atom0913_identity]
  exact mul_nonneg (by norm_num) (atom0913_nonneg g t z hg hA hB ht hz hw)

def coeff0914 : CoefficientMerge.Poly :=
  [(540992, 1)]
noncomputable def atom0914 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (t) ^ 2)
theorem atom0914_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0914 g t z = CoefficientMerge.eval (monomial g t z) coeff0914 := by
  norm_num [atom0914, coeff0914, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0914_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0914 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0914]
  positivity
theorem weighted0914_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2792183498340503022226843428225545933558961342094131196961628563874433226941099499774312552333638607134807907148712839343816306291194451200 : Int) coeff0914) := by
  rw [CoefficientMerge.eval_scale, ← atom0914_identity]
  exact mul_nonneg (by norm_num) (atom0914_nonneg g t z hg hA hB ht hz hw)

def coeff0915 : CoefficientMerge.Poly :=
  [(590144, 1)]
noncomputable def atom0915 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (t) ^ 2)
theorem atom0915_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0915 g t z = CoefficientMerge.eval (monomial g t z) coeff0915 := by
  norm_num [atom0915, coeff0915, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0915_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0915 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0915]
  positivity
theorem weighted0915_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5296086107319202838082346730059674181568284641445065168515019174904410170185245749133758055693570584284888578887570015263036382121471379200 : Int) coeff0915) := by
  rw [CoefficientMerge.eval_scale, ← atom0915_identity]
  exact mul_nonneg (by norm_num) (atom0915_nonneg g t z hg hA hB ht hz hw)

def coeff0916 : CoefficientMerge.Poly :=
  [(1312064, 1)]
noncomputable def atom0916 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 1 * (g 5) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0916_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0916 g t z = CoefficientMerge.eval (monomial g t z) coeff0916 := by
  norm_num [atom0916, coeff0916, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0916_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0916 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0916]
  positivity
theorem weighted0916_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1223311438211313823264187382941767266048278320656582194909376904464614295897502999860762233696748493052329339137783687316189818567875442432 : Int) coeff0916) := by
  rw [CoefficientMerge.eval_scale, ← atom0916_identity]
  exact mul_nonneg (by norm_num) (atom0916_nonneg g t z hg hA hB ht hz hw)

def coeff0917 : CoefficientMerge.Poly :=
  [(1315136, 1)]
noncomputable def atom0917 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0917_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0917 g t z = CoefficientMerge.eval (monomial g t z) coeff0917 := by
  norm_num [atom0917, coeff0917, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0917_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0917 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0917]
  positivity
theorem weighted0917_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5870912414909906073332898932223161312589893319100975377087392984205901882465514702247601883172097615599153439823290584102343263957472364640 : Int) coeff0917) := by
  rw [CoefficientMerge.eval_scale, ← atom0917_identity]
  exact mul_nonneg (by norm_num) (atom0917_nonneg g t z hg hA hB ht hz hw)

def coeff0918 : CoefficientMerge.Poly :=
  [(1327424, 1)]
noncomputable def atom0918 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0918_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0918 g t z = CoefficientMerge.eval (monomial g t z) coeff0918 := by
  norm_num [atom0918, coeff0918, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0918_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0918 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0918]
  positivity
theorem weighted0918_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4925200198345192262675565945307549751391274659109940696435549399690998789152015228741456919597040098377089104634262518752014968237176326240 : Int) coeff0918) := by
  rw [CoefficientMerge.eval_scale, ← atom0918_identity]
  exact mul_nonneg (by norm_num) (atom0918_nonneg g t z hg hA hB ht hz hw)

def coeff0919 : CoefficientMerge.Poly :=
  [(1376576, 1)]
noncomputable def atom0919 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0919_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0919 g t z = CoefficientMerge.eval (monomial g t z) coeff0919 := by
  norm_num [atom0919, coeff0919, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0919_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0919 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0919]
  positivity
theorem weighted0919_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (9965854332811534737582022923418302745035618140937566954953436562320698788850949930321492535036511941189518015169448436009293157632734688800 : Int) coeff0919) := by
  rw [CoefficientMerge.eval_scale, ← atom0919_identity]
  exact mul_nonneg (by norm_num) (atom0919_nonneg g t z hg hA hB ht hz hw)

def coeff0920 : CoefficientMerge.Poly :=
  [(526400, 1)]
noncomputable def atom0920 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 5) ^ 2 * (t) ^ 2)
theorem atom0920_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0920 g t z = CoefficientMerge.eval (monomial g t z) coeff0920 := by
  norm_num [atom0920, coeff0920, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0920_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0920 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0920]
  positivity
theorem weighted0920_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (466698001406288267462645901167398866876033640525342205655870313978613075880616138915216574307943939017528400408231103301560778225097420800 : Int) coeff0920) := by
  rw [CoefficientMerge.eval_scale, ← atom0920_identity]
  exact mul_nonneg (by norm_num) (atom0920_nonneg g t z hg hA hB ht hz hw)

def coeff0921 : CoefficientMerge.Poly :=
  [(529472, 1)]
noncomputable def atom0921 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (t) ^ 2)
theorem atom0921_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0921 g t z = CoefficientMerge.eval (monomial g t z) coeff0921 := by
  norm_num [atom0921, coeff0921, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0921_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0921 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0921]
  positivity
theorem weighted0921_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1772097031200087967869107019122847473552782699920394571560483589674298619383120249199821002376761097084282217254277654720130513977184358400 : Int) coeff0921) := by
  rw [CoefficientMerge.eval_scale, ← atom0921_identity]
  exact mul_nonneg (by norm_num) (atom0921_nonneg g t z hg hA hB ht hz hw)

def coeff0922 : CoefficientMerge.Poly :=
  [(541760, 1)]
noncomputable def atom0922 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (t) ^ 2)
theorem atom0922_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0922 g t z = CoefficientMerge.eval (monomial g t z) coeff0922 := by
  norm_num [atom0922, coeff0922, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0922_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0922 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0922]
  positivity
theorem weighted0922_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1753894043978712495275210420927298250264982666586605096618014739807168435752317325999723190769463277948537244206277398373190958127633100800 : Int) coeff0922) := by
  rw [CoefficientMerge.eval_scale, ← atom0922_identity]
  exact mul_nonneg (by norm_num) (atom0922_nonneg g t z hg hA hB ht hz hw)

def coeff0923 : CoefficientMerge.Poly :=
  [(590912, 1)]
noncomputable def atom0923 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (t) ^ 2)
theorem atom0923_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0923 g t z = CoefficientMerge.eval (monomial g t z) coeff0923 := by
  norm_num [atom0923, coeff0923, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0923_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0923 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0923]
  positivity
theorem weighted0923_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2101568178709631319528016398342390591386632916008478129166291487378631740131069038116203539372821979025457566305784612441193622866983168000 : Int) coeff0923) := by
  rw [CoefficientMerge.eval_scale, ← atom0923_identity]
  exact mul_nonneg (by norm_num) (atom0923_nonneg g t z hg hA hB ht hz hw)

def coeff0924 : CoefficientMerge.Poly :=
  [(1312832, 1)]
noncomputable def atom0924 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 5) ^ 2 * (t) ^ 1 * (z) ^ 1)
theorem atom0924_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0924 g t z = CoefficientMerge.eval (monomial g t z) coeff0924 := by
  norm_num [atom0924, coeff0924, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0924_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0924 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0924]
  positivity
theorem weighted0924_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1156069676545993934010231254877973329658573571073489025812662285142031210704005488660608123055851480579350741909853135429359591880438743040 : Int) coeff0924) := by
  rw [CoefficientMerge.eval_scale, ← atom0924_identity]
  exact mul_nonneg (by norm_num) (atom0924_nonneg g t z hg hA hB ht hz hw)

def sparseBlock077 : CoefficientMerge.Poly :=
  [(525632, 484292505263488553260437313959151404386231506294562526342556987696244003499025027623973233597936972055005955723909935797401580460030720000), (526400, 466698001406288267462645901167398866876033640525342205655870313978613075880616138915216574307943939017528400408231103301560778225097420800), (528512, 838053979964210027713455841136339166966701956252069464745749868527244424951387066769917944961719853518165924992448370206336594940736556800), (528704, 3052226842482688149286657246188998240100660602994891714338858853442879625694256875126156033001548330141613975192860570956941987082265811200), (529472, 1772097031200087967869107019122847473552782699920394571560483589674298619383120249199821002376761097084282217254277654720130513977184358400), (540800, 359374224604933178676671400795718624374585196735435517256546664150046088447220902586336635621140244026511297848988638267517990301130592000), (540992, 2792183498340503022226843428225545933558961342094131196961628563874433226941099499774312552333638607134807907148712839343816306291194451200), (541760, 1753894043978712495275210420927298250264982666586605096618014739807168435752317325999723190769463277948537244206277398373190958127633100800), (589952, 1925707151497568728520620526669065677956273019518996512694788665235341139781742159360574836478670306919752342528112650878806825539104608000), (590144, 5296086107319202838082346730059674181568284641445065168515019174904410170185245749133758055693570584284888578887570015263036382121471379200), (590912, 2101568178709631319528016398342390591386632916008478129166291487378631740131069038116203539372821979025457566305784612441193622866983168000), (1311872, 1340479297298677268531013446193006873290616059566219365297549931797750982370780279503641205631336180553818053884151067050525871839362465600), (1312064, 1223311438211313823264187382941767266048278320656582194909376904464614295897502999860762233696748493052329339137783687316189818567875442432), (1312832, 1156069676545993934010231254877973329658573571073489025812662285142031210704005488660608123055851480579350741909853135429359591880438743040), (1314944, 2772115647282303276978334417745536002686009400258179040999651515822231917289982819598667150067094664807089747229376098295276108454929145440), (1315136, 5870912414909906073332898932223161312589893319100975377087392984205901882465514702247601883172097615599153439823290584102343263957472364640), (1327232, 1638880760921465335663869366611125372537440637089381743714766682034514677504098179184962904728160102092113614941600398881335213313908947040), (1327424, 4925200198345192262675565945307549751391274659109940696435549399690998789152015228741456919597040098377089104634262518752014968237176326240), (1376384, 4996413110909116053416236977451320077595060084369272299970523744125427128443090440397508972516401911536938316709586324812775123579668102240), (1376576, 9965854332811534737582022923418302745035618140937566954953436562320698788850949930321492535036511941189518015169448436009293157632734688800)]
theorem sparseBlock077_data : sparseBlock077 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (838053979964210027713455841136339166966701956252069464745749868527244424951387066769917944961719853518165924992448370206336594940736556800 : Int) coeff0905) (CoefficientMerge.scale (359374224604933178676671400795718624374585196735435517256546664150046088447220902586336635621140244026511297848988638267517990301130592000 : Int) coeff0906)) (CoefficientMerge.merge (CoefficientMerge.scale (1925707151497568728520620526669065677956273019518996512694788665235341139781742159360574836478670306919752342528112650878806825539104608000 : Int) coeff0907) (CoefficientMerge.merge (CoefficientMerge.scale (1340479297298677268531013446193006873290616059566219365297549931797750982370780279503641205631336180553818053884151067050525871839362465600 : Int) coeff0908) (CoefficientMerge.scale (2772115647282303276978334417745536002686009400258179040999651515822231917289982819598667150067094664807089747229376098295276108454929145440 : Int) coeff0909)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1638880760921465335663869366611125372537440637089381743714766682034514677504098179184962904728160102092113614941600398881335213313908947040 : Int) coeff0910) (CoefficientMerge.scale (4996413110909116053416236977451320077595060084369272299970523744125427128443090440397508972516401911536938316709586324812775123579668102240 : Int) coeff0911)) (CoefficientMerge.merge (CoefficientMerge.scale (484292505263488553260437313959151404386231506294562526342556987696244003499025027623973233597936972055005955723909935797401580460030720000 : Int) coeff0912) (CoefficientMerge.merge (CoefficientMerge.scale (3052226842482688149286657246188998240100660602994891714338858853442879625694256875126156033001548330141613975192860570956941987082265811200 : Int) coeff0913) (CoefficientMerge.scale (2792183498340503022226843428225545933558961342094131196961628563874433226941099499774312552333638607134807907148712839343816306291194451200 : Int) coeff0914))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (5296086107319202838082346730059674181568284641445065168515019174904410170185245749133758055693570584284888578887570015263036382121471379200 : Int) coeff0915) (CoefficientMerge.scale (1223311438211313823264187382941767266048278320656582194909376904464614295897502999860762233696748493052329339137783687316189818567875442432 : Int) coeff0916)) (CoefficientMerge.merge (CoefficientMerge.scale (5870912414909906073332898932223161312589893319100975377087392984205901882465514702247601883172097615599153439823290584102343263957472364640 : Int) coeff0917) (CoefficientMerge.merge (CoefficientMerge.scale (4925200198345192262675565945307549751391274659109940696435549399690998789152015228741456919597040098377089104634262518752014968237176326240 : Int) coeff0918) (CoefficientMerge.scale (9965854332811534737582022923418302745035618140937566954953436562320698788850949930321492535036511941189518015169448436009293157632734688800 : Int) coeff0919)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (466698001406288267462645901167398866876033640525342205655870313978613075880616138915216574307943939017528400408231103301560778225097420800 : Int) coeff0920) (CoefficientMerge.scale (1772097031200087967869107019122847473552782699920394571560483589674298619383120249199821002376761097084282217254277654720130513977184358400 : Int) coeff0921)) (CoefficientMerge.merge (CoefficientMerge.scale (1753894043978712495275210420927298250264982666586605096618014739807168435752317325999723190769463277948537244206277398373190958127633100800 : Int) coeff0922) (CoefficientMerge.merge (CoefficientMerge.scale (2101568178709631319528016398342390591386632916008478129166291487378631740131069038116203539372821979025457566305784612441193622866983168000 : Int) coeff0923) (CoefficientMerge.scale (1156069676545993934010231254877973329658573571073489025812662285142031210704005488660608123055851480579350741909853135429359591880438743040 : Int) coeff0924)))))) := by decide +kernel
theorem sparseBlock077_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock077 := by
  rw [sparseBlock077_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted0905_nonneg g t z hg hA hB ht hz hw) (weighted0906_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0907_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0908_nonneg g t z hg hA hB ht hz hw) (weighted0909_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0910_nonneg g t z hg hA hB ht hz hw) (weighted0911_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0912_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0913_nonneg g t z hg hA hB ht hz hw) (weighted0914_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted0915_nonneg g t z hg hA hB ht hz hw) (weighted0916_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0917_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0918_nonneg g t z hg hA hB ht hz hw) (weighted0919_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0920_nonneg g t z hg hA hB ht hz hw) (weighted0921_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0922_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0923_nonneg g t z hg hA hB ht hz hw) (weighted0924_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
