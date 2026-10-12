import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff1045 : CoefficientMerge.Poly :=
  [(561152, 1)]
noncomputable def atom1045 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 1 * (g 7) ^ 2 * (t) ^ 2)
theorem atom1045_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1045 g t z = CoefficientMerge.eval (monomial g t z) coeff1045 := by
  norm_num [atom1045, coeff1045, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1045_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1045 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1045]
  positivity
theorem weighted1045_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1733732591080601713856633380846960540875274162643690777830094002779942163385728591868647647394068750648763681491065556613223214656827084800 : Int) coeff1045) := by
  rw [CoefficientMerge.eval_scale, ← atom1045_identity]
  exact mul_nonneg (by norm_num) (atom1045_nonneg g t z hg hA hB ht hz hw)

def coeff1046 : CoefficientMerge.Poly :=
  [(610304, 1)]
noncomputable def atom1046 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (t) ^ 2)
theorem atom1046_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1046 g t z = CoefficientMerge.eval (monomial g t z) coeff1046 := by
  norm_num [atom1046, coeff1046, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1046_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1046 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1046]
  positivity
theorem weighted1046_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2872443756960626520436266143879262373596782258085528502343856638641272650072056781439201200069894432956587102904630411162839118633279718400 : Int) coeff1046) := by
  rw [CoefficientMerge.eval_scale, ← atom1046_identity]
  exact mul_nonneg (by norm_num) (atom1046_nonneg g t z hg hA hB ht hz hw)

def coeff1047 : CoefficientMerge.Poly :=
  [(1347584, 1)]
noncomputable def atom1047 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 1 * (g 7) ^ 2 * (t) ^ 1 * (z) ^ 1)
theorem atom1047_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1047 g t z = CoefficientMerge.eval (monomial g t z) coeff1047 := by
  norm_num [atom1047, coeff1047, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1047_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1047 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1047]
  positivity
theorem weighted1047_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3400650050794848066838573629827387990248649751663203294941893171493684892243312966721025094511983213395674851728415626347134668952250163200 : Int) coeff1047) := by
  rw [CoefficientMerge.eval_scale, ← atom1047_identity]
  exact mul_nonneg (by norm_num) (atom1047_nonneg g t z hg hA hB ht hz hw)

def coeff1048 : CoefficientMerge.Poly :=
  [(1396736, 1)]
noncomputable def atom1048 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom1048_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1048 g t z = CoefficientMerge.eval (monomial g t z) coeff1048 := by
  norm_num [atom1048, coeff1048, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1048_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1048 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1048]
  positivity
theorem weighted1048_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5093584859723694692941584788884427761843432479549144856254774939012158352802097566526492139927676320067464250947414811865538333635547494400 : Int) coeff1048) := by
  rw [CoefficientMerge.eval_scale, ← atom1048_identity]
  exact mul_nonneg (by norm_num) (atom1048_nonneg g t z hg hA hB ht hz hw)

def coeff1049 : CoefficientMerge.Poly :=
  [(659456, 1)]
noncomputable def atom1049 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 1 * (g 8) ^ 2 * (t) ^ 2)
theorem atom1049_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1049 g t z = CoefficientMerge.eval (monomial g t z) coeff1049 := by
  norm_num [atom1049, coeff1049, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1049_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1049 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1049]
  positivity
theorem weighted1049_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (974860217496150502294379492557711204486379199103552124518053103784688569006193054733548077901697747552864501785135500473186768881395097600 : Int) coeff1049) := by
  rw [CoefficientMerge.eval_scale, ← atom1049_identity]
  exact mul_nonneg (by norm_num) (atom1049_nonneg g t z hg hA hB ht hz hw)

def coeff1050 : CoefficientMerge.Poly :=
  [(1445888, 1)]
noncomputable def atom1050 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 1 * (g 8) ^ 2 * (t) ^ 1 * (z) ^ 1)
theorem atom1050_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1050 g t z = CoefficientMerge.eval (monomial g t z) coeff1050 := by
  norm_num [atom1050, coeff1050, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1050_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1050 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1050]
  positivity
theorem weighted1050_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1598139203265084282612026926262410386694817044401530460081650933733003498623702258971683230484016217180046527292384116727706336375734681600 : Int) coeff1050) := by
  rw [CoefficientMerge.eval_scale, ← atom1050_identity]
  exact mul_nonneg (by norm_num) (atom1050_nonneg g t z hg hA hB ht hz hw)

def coeff1051 : CoefficientMerge.Poly :=
  [(2109440, 1)]
noncomputable def atom1051 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 3 * (z) ^ 2)
theorem atom1051_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1051 g t z = CoefficientMerge.eval (monomial g t z) coeff1051 := by
  norm_num [atom1051, coeff1051, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1051_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1051 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1051]
  positivity
theorem weighted1051_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (411470457701146173556205367284300899333144094344895561734688044161718365414498435462387511512842880445945482570465727331120769453250425600 : Int) coeff1051) := by
  rw [CoefficientMerge.eval_scale, ← atom1051_identity]
  exact mul_nonneg (by norm_num) (atom1051_nonneg g t z hg hA hB ht hz hw)

def coeff1052 : CoefficientMerge.Poly :=
  [(2121728, 1)]
noncomputable def atom1052 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 2 * (g 7) ^ 1 * (z) ^ 2)
theorem atom1052_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1052 g t z = CoefficientMerge.eval (monomial g t z) coeff1052 := by
  norm_num [atom1052, coeff1052, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1052_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1052 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1052]
  positivity
theorem weighted1052_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1735941994431665575780137383096030885584936992969510738200066364406900910054918550669904355932549855774215160169918279654056757139578258400 : Int) coeff1052) := by
  rw [CoefficientMerge.eval_scale, ← atom1052_identity]
  exact mul_nonneg (by norm_num) (atom1052_nonneg g t z hg hA hB ht hz hw)

def coeff1053 : CoefficientMerge.Poly :=
  [(2170880, 1)]
noncomputable def atom1053 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 2 * (g 8) ^ 1 * (z) ^ 2)
theorem atom1053_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1053 g t z = CoefficientMerge.eval (monomial g t z) coeff1053 := by
  norm_num [atom1053, coeff1053, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1053_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1053 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1053]
  positivity
theorem weighted1053_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1225907435344330162094799533820806755135423794454611466981439473439056087515614197410607487713051940230490753752782511643191309382526748800 : Int) coeff1053) := by
  rw [CoefficientMerge.eval_scale, ← atom1053_identity]
  exact mul_nonneg (by norm_num) (atom1053_nonneg g t z hg hA hB ht hz hw)

def coeff1054 : CoefficientMerge.Poly :=
  [(1085440, 1)]
noncomputable def atom1054 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 1 * (g 7) ^ 2 * (z) ^ 1)
theorem atom1054_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1054 g t z = CoefficientMerge.eval (monomial g t z) coeff1054 := by
  norm_num [atom1054, coeff1054, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1054_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1054 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1054]
  positivity
theorem weighted1054_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1295468493567210958459115617646897770008625549167715217029632259287996313007416566292452932374727776188544992274092360424481437839986688000 : Int) coeff1054) := by
  rw [CoefficientMerge.eval_scale, ← atom1054_identity]
  exact mul_nonneg (by norm_num) (atom1054_nonneg g t z hg hA hB ht hz hw)

def coeff1055 : CoefficientMerge.Poly :=
  [(2134016, 1)]
noncomputable def atom1055 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 1 * (g 7) ^ 2 * (z) ^ 2)
theorem atom1055_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1055 g t z = CoefficientMerge.eval (monomial g t z) coeff1055 := by
  norm_num [atom1055, coeff1055, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1055_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1055 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1055]
  positivity
theorem weighted1055_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1948296844977521995305405249365968555095952981733605012254279349354330829288044585077571055811363893673929917164435254673384826168179208800 : Int) coeff1055) := by
  rw [CoefficientMerge.eval_scale, ← atom1055_identity]
  exact mul_nonneg (by norm_num) (atom1055_nonneg g t z hg hA hB ht hz hw)

def coeff1056 : CoefficientMerge.Poly :=
  [(2183168, 1)]
noncomputable def atom1056 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (z) ^ 2)
theorem atom1056_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1056 g t z = CoefficientMerge.eval (monomial g t z) coeff1056 := by
  norm_num [atom1056, coeff1056, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1056_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1056 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1056]
  positivity
theorem weighted1056_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3174814711371103425713201285087820882422937338999308612527915507005332915397964208218060263502536200721676178206705200727164382062898165600 : Int) coeff1056) := by
  rw [CoefficientMerge.eval_scale, ← atom1056_identity]
  exact mul_nonneg (by norm_num) (atom1056_nonneg g t z hg hA hB ht hz hw)

def coeff1057 : CoefficientMerge.Poly :=
  [(2232320, 1)]
noncomputable def atom1057 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 1 * (g 8) ^ 2 * (z) ^ 2)
theorem atom1057_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1057 g t z = CoefficientMerge.eval (monomial g t z) coeff1057 := by
  norm_num [atom1057, coeff1057, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1057_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1057 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1057]
  positivity
theorem weighted1057_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1059027104337558892392250107900915605311477146704905882745765950339640733188950114643939844507533988383094164397156661659286241505091209600 : Int) coeff1057) := by
  rw [CoefficientMerge.eval_scale, ← atom1057_identity]
  exact mul_nonneg (by norm_num) (atom1057_nonneg g t z hg hA hB ht hz hw)

def coeff1058 : CoefficientMerge.Poly :=
  [(1146880, 1)]
noncomputable def atom1058 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 7) ^ 2 * (g 8) ^ 1 * (z) ^ 1)
theorem atom1058_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1058 g t z = CoefficientMerge.eval (monomial g t z) coeff1058 := by
  norm_num [atom1058, coeff1058, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1058_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1058 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1058]
  positivity
theorem weighted1058_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (644054769473776020839631065878498528268616436503264526874627316869313134748238357365840219068451776760355391538491426601846433012309708800 : Int) coeff1058) := by
  rw [CoefficientMerge.eval_scale, ← atom1058_identity]
  exact mul_nonneg (by norm_num) (atom1058_nonneg g t z hg hA hB ht hz hw)

def coeff1059 : CoefficientMerge.Poly :=
  [(1196032, 1)]
noncomputable def atom1059 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 7) ^ 1 * (g 8) ^ 2 * (z) ^ 1)
theorem atom1059_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1059 g t z = CoefficientMerge.eval (monomial g t z) coeff1059 := by
  norm_num [atom1059, coeff1059, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1059_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1059 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1059]
  positivity
theorem weighted1059_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3324191444967170694572712479182928347153929602748067300136852537428413224368484865532519788657587590179404627355071810203374225059599718400 : Int) coeff1059) := by
  rw [CoefficientMerge.eval_scale, ← atom1059_identity]
  exact mul_nonneg (by norm_num) (atom1059_nonneg g t z hg hA hB ht hz hw)

def coeff1060 : CoefficientMerge.Poly :=
  [(573440, 1)]
noncomputable def atom1060 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 7) ^ 3 * (t) ^ 2)
theorem atom1060_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1060 g t z = CoefficientMerge.eval (monomial g t z) coeff1060 := by
  norm_num [atom1060, coeff1060, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1060_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1060 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1060]
  positivity
theorem weighted1060_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (765898647641642666720614429123840984048453314080292000851111625675867785579047309254554999606260277449822767765162804923772480295876608000 : Int) coeff1060) := by
  rw [CoefficientMerge.eval_scale, ← atom1060_identity]
  exact mul_nonneg (by norm_num) (atom1060_nonneg g t z hg hA hB ht hz hw)

def coeff1061 : CoefficientMerge.Poly :=
  [(622592, 1)]
noncomputable def atom1061 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 7) ^ 2 * (g 8) ^ 1 * (t) ^ 2)
theorem atom1061_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1061 g t z = CoefficientMerge.eval (monomial g t z) coeff1061 := by
  norm_num [atom1061, coeff1061, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1061_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1061 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1061]
  positivity
theorem weighted1061_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2404199566310961881249127400359054810046889551144711516958442009617594108959245347356181406832563417659782611404893598516199422269146931200 : Int) coeff1061) := by
  rw [CoefficientMerge.eval_scale, ← atom1061_identity]
  exact mul_nonneg (by norm_num) (atom1061_nonneg g t z hg hA hB ht hz hw)

def coeff1062 : CoefficientMerge.Poly :=
  [(1359872, 1)]
noncomputable def atom1062 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 7) ^ 3 * (t) ^ 1 * (z) ^ 1)
theorem atom1062_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1062 g t z = CoefficientMerge.eval (monomial g t z) coeff1062 := by
  norm_num [atom1062, coeff1062, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1062_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1062 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1062]
  positivity
theorem weighted1062_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1420841558829765420073111473796143952629442138149230796005157000424110543369688591569778169895824241497915132712289317046991926045777305600 : Int) coeff1062) := by
  rw [CoefficientMerge.eval_scale, ← atom1062_identity]
  exact mul_nonneg (by norm_num) (atom1062_nonneg g t z hg hA hB ht hz hw)

def coeff1063 : CoefficientMerge.Poly :=
  [(1409024, 1)]
noncomputable def atom1063 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 7) ^ 2 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom1063_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1063 g t z = CoefficientMerge.eval (monomial g t z) coeff1063 := by
  norm_num [atom1063, coeff1063, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1063_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1063 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1063]
  positivity
theorem weighted1063_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3837344983488956746927918000768051844720348277962492999192848023964363153621256486223637328068243207684721976644349133880704884151728230400 : Int) coeff1063) := by
  rw [CoefficientMerge.eval_scale, ← atom1063_identity]
  exact mul_nonneg (by norm_num) (atom1063_nonneg g t z hg hA hB ht hz hw)

def coeff1064 : CoefficientMerge.Poly :=
  [(671744, 1)]
noncomputable def atom1064 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 7) ^ 1 * (g 8) ^ 2 * (t) ^ 2)
theorem atom1064_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1064 g t z = CoefficientMerge.eval (monomial g t z) coeff1064 := by
  norm_num [atom1064, coeff1064, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1064_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1064 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1064]
  positivity
theorem weighted1064_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1660917868354733478785184423600260389783414040194989476167721795384012709281857752911017656739696403579657584769175330637509961090238707200 : Int) coeff1064) := by
  rw [CoefficientMerge.eval_scale, ← atom1064_identity]
  exact mul_nonneg (by norm_num) (atom1064_nonneg g t z hg hA hB ht hz hw)

def sparseBlock084 : CoefficientMerge.Poly :=
  [(561152, 1733732591080601713856633380846960540875274162643690777830094002779942163385728591868647647394068750648763681491065556613223214656827084800), (573440, 765898647641642666720614429123840984048453314080292000851111625675867785579047309254554999606260277449822767765162804923772480295876608000), (610304, 2872443756960626520436266143879262373596782258085528502343856638641272650072056781439201200069894432956587102904630411162839118633279718400), (622592, 2404199566310961881249127400359054810046889551144711516958442009617594108959245347356181406832563417659782611404893598516199422269146931200), (659456, 974860217496150502294379492557711204486379199103552124518053103784688569006193054733548077901697747552864501785135500473186768881395097600), (671744, 1660917868354733478785184423600260389783414040194989476167721795384012709281857752911017656739696403579657584769175330637509961090238707200), (1085440, 1295468493567210958459115617646897770008625549167715217029632259287996313007416566292452932374727776188544992274092360424481437839986688000), (1146880, 644054769473776020839631065878498528268616436503264526874627316869313134748238357365840219068451776760355391538491426601846433012309708800), (1196032, 3324191444967170694572712479182928347153929602748067300136852537428413224368484865532519788657587590179404627355071810203374225059599718400), (1347584, 3400650050794848066838573629827387990248649751663203294941893171493684892243312966721025094511983213395674851728415626347134668952250163200), (1359872, 1420841558829765420073111473796143952629442138149230796005157000424110543369688591569778169895824241497915132712289317046991926045777305600), (1396736, 5093584859723694692941584788884427761843432479549144856254774939012158352802097566526492139927676320067464250947414811865538333635547494400), (1409024, 3837344983488956746927918000768051844720348277962492999192848023964363153621256486223637328068243207684721976644349133880704884151728230400), (1445888, 1598139203265084282612026926262410386694817044401530460081650933733003498623702258971683230484016217180046527292384116727706336375734681600), (2109440, 411470457701146173556205367284300899333144094344895561734688044161718365414498435462387511512842880445945482570465727331120769453250425600), (2121728, 1735941994431665575780137383096030885584936992969510738200066364406900910054918550669904355932549855774215160169918279654056757139578258400), (2134016, 1948296844977521995305405249365968555095952981733605012254279349354330829288044585077571055811363893673929917164435254673384826168179208800), (2170880, 1225907435344330162094799533820806755135423794454611466981439473439056087515614197410607487713051940230490753752782511643191309382526748800), (2183168, 3174814711371103425713201285087820882422937338999308612527915507005332915397964208218060263502536200721676178206705200727164382062898165600), (2232320, 1059027104337558892392250107900915605311477146704905882745765950339640733188950114643939844507533988383094164397156661659286241505091209600)]
theorem sparseBlock084_data : sparseBlock084 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1733732591080601713856633380846960540875274162643690777830094002779942163385728591868647647394068750648763681491065556613223214656827084800 : Int) coeff1045) (CoefficientMerge.scale (2872443756960626520436266143879262373596782258085528502343856638641272650072056781439201200069894432956587102904630411162839118633279718400 : Int) coeff1046)) (CoefficientMerge.merge (CoefficientMerge.scale (3400650050794848066838573629827387990248649751663203294941893171493684892243312966721025094511983213395674851728415626347134668952250163200 : Int) coeff1047) (CoefficientMerge.merge (CoefficientMerge.scale (5093584859723694692941584788884427761843432479549144856254774939012158352802097566526492139927676320067464250947414811865538333635547494400 : Int) coeff1048) (CoefficientMerge.scale (974860217496150502294379492557711204486379199103552124518053103784688569006193054733548077901697747552864501785135500473186768881395097600 : Int) coeff1049)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1598139203265084282612026926262410386694817044401530460081650933733003498623702258971683230484016217180046527292384116727706336375734681600 : Int) coeff1050) (CoefficientMerge.scale (411470457701146173556205367284300899333144094344895561734688044161718365414498435462387511512842880445945482570465727331120769453250425600 : Int) coeff1051)) (CoefficientMerge.merge (CoefficientMerge.scale (1735941994431665575780137383096030885584936992969510738200066364406900910054918550669904355932549855774215160169918279654056757139578258400 : Int) coeff1052) (CoefficientMerge.merge (CoefficientMerge.scale (1225907435344330162094799533820806755135423794454611466981439473439056087515614197410607487713051940230490753752782511643191309382526748800 : Int) coeff1053) (CoefficientMerge.scale (1295468493567210958459115617646897770008625549167715217029632259287996313007416566292452932374727776188544992274092360424481437839986688000 : Int) coeff1054))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1948296844977521995305405249365968555095952981733605012254279349354330829288044585077571055811363893673929917164435254673384826168179208800 : Int) coeff1055) (CoefficientMerge.scale (3174814711371103425713201285087820882422937338999308612527915507005332915397964208218060263502536200721676178206705200727164382062898165600 : Int) coeff1056)) (CoefficientMerge.merge (CoefficientMerge.scale (1059027104337558892392250107900915605311477146704905882745765950339640733188950114643939844507533988383094164397156661659286241505091209600 : Int) coeff1057) (CoefficientMerge.merge (CoefficientMerge.scale (644054769473776020839631065878498528268616436503264526874627316869313134748238357365840219068451776760355391538491426601846433012309708800 : Int) coeff1058) (CoefficientMerge.scale (3324191444967170694572712479182928347153929602748067300136852537428413224368484865532519788657587590179404627355071810203374225059599718400 : Int) coeff1059)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (765898647641642666720614429123840984048453314080292000851111625675867785579047309254554999606260277449822767765162804923772480295876608000 : Int) coeff1060) (CoefficientMerge.scale (2404199566310961881249127400359054810046889551144711516958442009617594108959245347356181406832563417659782611404893598516199422269146931200 : Int) coeff1061)) (CoefficientMerge.merge (CoefficientMerge.scale (1420841558829765420073111473796143952629442138149230796005157000424110543369688591569778169895824241497915132712289317046991926045777305600 : Int) coeff1062) (CoefficientMerge.merge (CoefficientMerge.scale (3837344983488956746927918000768051844720348277962492999192848023964363153621256486223637328068243207684721976644349133880704884151728230400 : Int) coeff1063) (CoefficientMerge.scale (1660917868354733478785184423600260389783414040194989476167721795384012709281857752911017656739696403579657584769175330637509961090238707200 : Int) coeff1064)))))) := by decide +kernel
theorem sparseBlock084_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock084 := by
  rw [sparseBlock084_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted1045_nonneg g t z hg hA hB ht hz hw) (weighted1046_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1047_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1048_nonneg g t z hg hA hB ht hz hw) (weighted1049_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1050_nonneg g t z hg hA hB ht hz hw) (weighted1051_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1052_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1053_nonneg g t z hg hA hB ht hz hw) (weighted1054_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted1055_nonneg g t z hg hA hB ht hz hw) (weighted1056_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1057_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1058_nonneg g t z hg hA hB ht hz hw) (weighted1059_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1060_nonneg g t z hg hA hB ht hz hw) (weighted1061_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1062_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1063_nonneg g t z hg hA hB ht hz hw) (weighted1064_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
