import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff1185 : CoefficientMerge.Poly :=
  [(2441280, 1)]
noncomputable def atom1185 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1185_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1185 g t z = CoefficientMerge.eval (monomial g t z) coeff1185 := by
  norm_num [atom1185, coeff1185, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1185_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1185 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1185]
  positivity
theorem weighted1185_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (412580221968726935227800262629780221120636862626012182573452969613250718303670688972318966715765963048964674557177441803495331171129030400 : Int) coeff1185) := by
  rw [CoefficientMerge.eval_scale, ← atom1185_identity]
  exact mul_nonneg (by norm_num) (atom1185_nonneg g t z hg hA hB ht hz hw)

def coeff1186 : CoefficientMerge.Poly :=
  [(2490432, 1)]
noncomputable def atom1186 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 8) ^ 2 * (t) ^ 1 * (z) ^ 2)
theorem atom1186_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1186 g t z = CoefficientMerge.eval (monomial g t z) coeff1186 := by
  norm_num [atom1186, coeff1186, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1186_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1186 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1186]
  positivity
theorem weighted1186_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (149043945160591064045767928957903435793325218700482397440403027070276499688136824590624470552827910329028531669654054934127106768091745920 : Int) coeff1186) := by
  rw [CoefficientMerge.eval_scale, ← atom1186_identity]
  exact mul_nonneg (by norm_num) (atom1186_nonneg g t z hg hA hB ht hz hw)

def coeff1187 : CoefficientMerge.Poly :=
  [(787200, 1)]
noncomputable def atom1187 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 3 * (t) ^ 3)
theorem atom1187_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1187 g t z = CoefficientMerge.eval (monomial g t z) coeff1187 := by
  norm_num [atom1187, coeff1187, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1187_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1187 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1187]
  positivity
theorem weighted1187_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (863060596296160767423236354859153985078033006855176850315523561170413635541701160742168733310139246574672710762125748050865851259392000 : Int) coeff1187) := by
  rw [CoefficientMerge.eval_scale, ← atom1187_identity]
  exact mul_nonneg (by norm_num) (atom1187_nonneg g t z hg hA hB ht hz hw)

def coeff1188 : CoefficientMerge.Poly :=
  [(787968, 1)]
noncomputable def atom1188 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 2 * (g 5) ^ 1 * (t) ^ 3)
theorem atom1188_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1188 g t z = CoefficientMerge.eval (monomial g t z) coeff1188 := by
  norm_num [atom1188, coeff1188, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1188_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1188 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1188]
  positivity
theorem weighted1188_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (79472392736821449163069873148118949504883298980187336623801433156362282760112689418924471710423150102935521857934641331021936825334169600 : Int) coeff1188) := by
  rw [CoefficientMerge.eval_scale, ← atom1188_identity]
  exact mul_nonneg (by norm_num) (atom1188_nonneg g t z hg hA hB ht hz hw)

def coeff1189 : CoefficientMerge.Poly :=
  [(791040, 1)]
noncomputable def atom1189 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 2 * (g 6) ^ 1 * (t) ^ 3)
theorem atom1189_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1189 g t z = CoefficientMerge.eval (monomial g t z) coeff1189 := by
  norm_num [atom1189, coeff1189, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1189_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1189 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1189]
  positivity
theorem weighted1189_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (64084967913955272092314217783306521742102781578162473895585676984526936645017373416400943598752336444780124719204135137450397256545049600 : Int) coeff1189) := by
  rw [CoefficientMerge.eval_scale, ← atom1189_identity]
  exact mul_nonneg (by norm_num) (atom1189_nonneg g t z hg hA hB ht hz hw)

def coeff1190 : CoefficientMerge.Poly :=
  [(803328, 1)]
noncomputable def atom1190 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 2 * (g 7) ^ 1 * (t) ^ 3)
theorem atom1190_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1190 g t z = CoefficientMerge.eval (monomial g t z) coeff1190 := by
  norm_num [atom1190, coeff1190, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1190_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1190 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1190]
  positivity
theorem weighted1190_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (47349201655922100898397973301067853365638564487653002909469745093410049164679199869646279252335294609340167794273977325703948268402508800 : Int) coeff1190) := by
  rw [CoefficientMerge.eval_scale, ← atom1190_identity]
  exact mul_nonneg (by norm_num) (atom1190_nonneg g t z hg hA hB ht hz hw)

def coeff1191 : CoefficientMerge.Poly :=
  [(852480, 1)]
noncomputable def atom1191 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 2 * (g 8) ^ 1 * (t) ^ 3)
theorem atom1191_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1191 g t z = CoefficientMerge.eval (monomial g t z) coeff1191 := by
  norm_num [atom1191, coeff1191, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1191_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1191 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1191]
  positivity
theorem weighted1191_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (19818253406028685140115833485194721090582770767819242963744621928284346019805359539256873931112665821619718928694892381171786487866854400 : Int) coeff1191) := by
  rw [CoefficientMerge.eval_scale, ← atom1191_identity]
  exact mul_nonneg (by norm_num) (atom1191_nonneg g t z hg hA hB ht hz hw)

def coeff1192 : CoefficientMerge.Poly :=
  [(1573632, 1)]
noncomputable def atom1192 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 3 * (t) ^ 2 * (z) ^ 1)
theorem atom1192_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1192 g t z = CoefficientMerge.eval (monomial g t z) coeff1192 := by
  norm_num [atom1192, coeff1192, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1192_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1192 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1192]
  positivity
theorem weighted1192_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2589181788888482302269709064577461955234099020565530550946570683511240906625103482226506199930417739724018132286377244152597553778176000 : Int) coeff1192) := by
  rw [CoefficientMerge.eval_scale, ← atom1192_identity]
  exact mul_nonneg (by norm_num) (atom1192_nonneg g t z hg hA hB ht hz hw)

def coeff1193 : CoefficientMerge.Poly :=
  [(1574400, 1)]
noncomputable def atom1193 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 2 * (g 5) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1193_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1193 g t z = CoefficientMerge.eval (monomial g t z) coeff1193 := by
  norm_num [atom1193, coeff1193, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1193_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1193 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1193]
  positivity
theorem weighted1193_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (238584557993510366451792204317530610503893141576954302428675775446095669449444961250636206040927071391007561127550000505985988410820608000 : Int) coeff1193) := by
  rw [CoefficientMerge.eval_scale, ← atom1193_identity]
  exact mul_nonneg (by norm_num) (atom1193_nonneg g t z hg hA hB ht hz hw)

def coeff1194 : CoefficientMerge.Poly :=
  [(1577472, 1)]
noncomputable def atom1194 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 2 * (g 6) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1194_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1194 g t z = CoefficientMerge.eval (monomial g t z) coeff1194 := by
  norm_num [atom1194, coeff1194, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1194_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1194 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1194]
  positivity
theorem weighted1194_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (185498978477890753042624960962679720132070788988551257012763243426537024741638748565112220950002105348342045259539802362246655605237816640 : Int) coeff1194) := by
  rw [CoefficientMerge.eval_scale, ← atom1194_identity]
  exact mul_nonneg (by norm_num) (atom1194_nonneg g t z hg hA hB ht hz hw)

def coeff1195 : CoefficientMerge.Poly :=
  [(1589760, 1)]
noncomputable def atom1195 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 2 * (g 7) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1195_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1195 g t z = CoefficientMerge.eval (monomial g t z) coeff1195 := by
  norm_num [atom1195, coeff1195, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1195_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1195 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1195]
  positivity
theorem weighted1195_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (150006760041254276966179593259102969464077491858816359001015063557395716073794844842921786756091720422966530748741169400147731924885808960 : Int) coeff1195) := by
  rw [CoefficientMerge.eval_scale, ← atom1195_identity]
  exact mul_nonneg (by norm_num) (atom1195_nonneg g t z hg hA hB ht hz hw)

def coeff1196 : CoefficientMerge.Poly :=
  [(1638912, 1)]
noncomputable def atom1196 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 2 * (g 8) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1196_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1196 g t z = CoefficientMerge.eval (monomial g t z) coeff1196 := by
  norm_num [atom1196, coeff1196, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1196_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1196 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1196]
  positivity
theorem weighted1196_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (67149223250689526895250667140639275876521204266761184019770946015161302326891173331334666863527622173247959343353570863608413648190466240 : Int) coeff1196) := by
  rw [CoefficientMerge.eval_scale, ← atom1196_identity]
  exact mul_nonneg (by norm_num) (atom1196_nonneg g t z hg hA hB ht hz hw)

def coeff1197 : CoefficientMerge.Poly :=
  [(788736, 1)]
noncomputable def atom1197 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 5) ^ 2 * (t) ^ 3)
theorem atom1197_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1197 g t z = CoefficientMerge.eval (monomial g t z) coeff1197 := by
  norm_num [atom1197, coeff1197, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1197_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1197 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1197]
  positivity
theorem weighted1197_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (132853011914530543419526903676315367605520655830833948208505970594240162019472814263219141319121980570716612510722968557783159762736025600 : Int) coeff1197) := by
  rw [CoefficientMerge.eval_scale, ← atom1197_identity]
  exact mul_nonneg (by norm_num) (atom1197_nonneg g t z hg hA hB ht hz hw)

def coeff1198 : CoefficientMerge.Poly :=
  [(791808, 1)]
noncomputable def atom1198 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (t) ^ 3)
theorem atom1198_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1198 g t z = CoefficientMerge.eval (monomial g t z) coeff1198 := by
  norm_num [atom1198, coeff1198, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1198_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1198 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1198]
  positivity
theorem weighted1198_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (240238964255619122507350817000116897241905328946568116721779771899255067483534256324225757068613342909669925631237381295019970158688972800 : Int) coeff1198) := by
  rw [CoefficientMerge.eval_scale, ← atom1198_identity]
  exact mul_nonneg (by norm_num) (atom1198_nonneg g t z hg hA hB ht hz hw)

def coeff1199 : CoefficientMerge.Poly :=
  [(804096, 1)]
noncomputable def atom1199 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (t) ^ 3)
theorem atom1199_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1199 g t z = CoefficientMerge.eval (monomial g t z) coeff1199 := by
  norm_num [atom1199, coeff1199, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1199_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1199 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1199]
  positivity
theorem weighted1199_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (202335784875808778323533244474631600704943109410064045883483370628097340729579117232603262363767816258478910876337423147469958859711744000 : Int) coeff1199) := by
  rw [CoefficientMerge.eval_scale, ← atom1199_identity]
  exact mul_nonneg (by norm_num) (atom1199_nonneg g t z hg hA hB ht hz hw)

def coeff1200 : CoefficientMerge.Poly :=
  [(853248, 1)]
noncomputable def atom1200 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (t) ^ 3)
theorem atom1200_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1200 g t z = CoefficientMerge.eval (monomial g t z) coeff1200 := by
  norm_num [atom1200, coeff1200, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1200_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1200 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1200]
  positivity
theorem weighted1200_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (157307944030445347266249751229750914940056022531385089548546867842484426219142089985047140946184334868737014335926049397163295275867340800 : Int) coeff1200) := by
  rw [CoefficientMerge.eval_scale, ← atom1200_identity]
  exact mul_nonneg (by norm_num) (atom1200_nonneg g t z hg hA hB ht hz hw)

def coeff1201 : CoefficientMerge.Poly :=
  [(1575168, 1)]
noncomputable def atom1201 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 5) ^ 2 * (t) ^ 2 * (z) ^ 1)
theorem atom1201_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1201 g t z = CoefficientMerge.eval (monomial g t z) coeff1201 := by
  norm_num [atom1201, coeff1201, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1201_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1201 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1201]
  positivity
theorem weighted1201_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (398958398032964587783339159147395780545282691537227314586727047447162585689971731336417767180408686750383791835843754897159026641458278400 : Int) coeff1201) := by
  rw [CoefficientMerge.eval_scale, ← atom1201_identity]
  exact mul_nonneg (by norm_num) (atom1201_nonneg g t z hg hA hB ht hz hw)

def coeff1202 : CoefficientMerge.Poly :=
  [(1578240, 1)]
noncomputable def atom1202 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1202_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1202 g t z = CoefficientMerge.eval (monomial g t z) coeff1202 := by
  norm_num [atom1202, coeff1202, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1202_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1202 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1202]
  positivity
theorem weighted1202_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (718006049598887989928141885495005337213226705705203938696248380852380074109154565097387742812959897126134382026004813338651766638751663360 : Int) coeff1202) := by
  rw [CoefficientMerge.eval_scale, ← atom1202_identity]
  exact mul_nonneg (by norm_num) (atom1202_nonneg g t z hg hA hB ht hz hw)

def coeff1203 : CoefficientMerge.Poly :=
  [(1590528, 1)]
noncomputable def atom1203 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1203_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1203 g t z = CoefficientMerge.eval (monomial g t z) coeff1203 := by
  norm_num [atom1203, coeff1203, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1203_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1203 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1203]
  positivity
theorem weighted1203_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (631580321535530030290816080057155643712230540692941010701910083742921282665815408919099937901708051792710389128385617973014339843018620160 : Int) coeff1203) := by
  rw [CoefficientMerge.eval_scale, ← atom1203_identity]
  exact mul_nonneg (by norm_num) (atom1203_nonneg g t z hg hA hB ht hz hw)

def coeff1204 : CoefficientMerge.Poly :=
  [(1639680, 1)]
noncomputable def atom1204 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1204_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1204 g t z = CoefficientMerge.eval (monomial g t z) coeff1204 := by
  norm_num [atom1204, coeff1204, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1204_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1204 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1204]
  positivity
theorem weighted1204_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (498359146590065906609344251509694233233205326646443569223208171433768910901578262707691900297729260645173183877532450151849394271286754560 : Int) coeff1204) := by
  rw [CoefficientMerge.eval_scale, ← atom1204_identity]
  exact mul_nonneg (by norm_num) (atom1204_nonneg g t z hg hA hB ht hz hw)

def sparseBlock091 : CoefficientMerge.Poly :=
  [(787200, 863060596296160767423236354859153985078033006855176850315523561170413635541701160742168733310139246574672710762125748050865851259392000), (787968, 79472392736821449163069873148118949504883298980187336623801433156362282760112689418924471710423150102935521857934641331021936825334169600), (788736, 132853011914530543419526903676315367605520655830833948208505970594240162019472814263219141319121980570716612510722968557783159762736025600), (791040, 64084967913955272092314217783306521742102781578162473895585676984526936645017373416400943598752336444780124719204135137450397256545049600), (791808, 240238964255619122507350817000116897241905328946568116721779771899255067483534256324225757068613342909669925631237381295019970158688972800), (803328, 47349201655922100898397973301067853365638564487653002909469745093410049164679199869646279252335294609340167794273977325703948268402508800), (804096, 202335784875808778323533244474631600704943109410064045883483370628097340729579117232603262363767816258478910876337423147469958859711744000), (852480, 19818253406028685140115833485194721090582770767819242963744621928284346019805359539256873931112665821619718928694892381171786487866854400), (853248, 157307944030445347266249751229750914940056022531385089548546867842484426219142089985047140946184334868737014335926049397163295275867340800), (1573632, 2589181788888482302269709064577461955234099020565530550946570683511240906625103482226506199930417739724018132286377244152597553778176000), (1574400, 238584557993510366451792204317530610503893141576954302428675775446095669449444961250636206040927071391007561127550000505985988410820608000), (1575168, 398958398032964587783339159147395780545282691537227314586727047447162585689971731336417767180408686750383791835843754897159026641458278400), (1577472, 185498978477890753042624960962679720132070788988551257012763243426537024741638748565112220950002105348342045259539802362246655605237816640), (1578240, 718006049598887989928141885495005337213226705705203938696248380852380074109154565097387742812959897126134382026004813338651766638751663360), (1589760, 150006760041254276966179593259102969464077491858816359001015063557395716073794844842921786756091720422966530748741169400147731924885808960), (1590528, 631580321535530030290816080057155643712230540692941010701910083742921282665815408919099937901708051792710389128385617973014339843018620160), (1638912, 67149223250689526895250667140639275876521204266761184019770946015161302326891173331334666863527622173247959343353570863608413648190466240), (1639680, 498359146590065906609344251509694233233205326646443569223208171433768910901578262707691900297729260645173183877532450151849394271286754560), (2441280, 412580221968726935227800262629780221120636862626012182573452969613250718303670688972318966715765963048964674557177441803495331171129030400), (2490432, 149043945160591064045767928957903435793325218700482397440403027070276499688136824590624470552827910329028531669654054934127106768091745920)]
theorem sparseBlock091_data : sparseBlock091 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (412580221968726935227800262629780221120636862626012182573452969613250718303670688972318966715765963048964674557177441803495331171129030400 : Int) coeff1185) (CoefficientMerge.scale (149043945160591064045767928957903435793325218700482397440403027070276499688136824590624470552827910329028531669654054934127106768091745920 : Int) coeff1186)) (CoefficientMerge.merge (CoefficientMerge.scale (863060596296160767423236354859153985078033006855176850315523561170413635541701160742168733310139246574672710762125748050865851259392000 : Int) coeff1187) (CoefficientMerge.merge (CoefficientMerge.scale (79472392736821449163069873148118949504883298980187336623801433156362282760112689418924471710423150102935521857934641331021936825334169600 : Int) coeff1188) (CoefficientMerge.scale (64084967913955272092314217783306521742102781578162473895585676984526936645017373416400943598752336444780124719204135137450397256545049600 : Int) coeff1189)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (47349201655922100898397973301067853365638564487653002909469745093410049164679199869646279252335294609340167794273977325703948268402508800 : Int) coeff1190) (CoefficientMerge.scale (19818253406028685140115833485194721090582770767819242963744621928284346019805359539256873931112665821619718928694892381171786487866854400 : Int) coeff1191)) (CoefficientMerge.merge (CoefficientMerge.scale (2589181788888482302269709064577461955234099020565530550946570683511240906625103482226506199930417739724018132286377244152597553778176000 : Int) coeff1192) (CoefficientMerge.merge (CoefficientMerge.scale (238584557993510366451792204317530610503893141576954302428675775446095669449444961250636206040927071391007561127550000505985988410820608000 : Int) coeff1193) (CoefficientMerge.scale (185498978477890753042624960962679720132070788988551257012763243426537024741638748565112220950002105348342045259539802362246655605237816640 : Int) coeff1194))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (150006760041254276966179593259102969464077491858816359001015063557395716073794844842921786756091720422966530748741169400147731924885808960 : Int) coeff1195) (CoefficientMerge.scale (67149223250689526895250667140639275876521204266761184019770946015161302326891173331334666863527622173247959343353570863608413648190466240 : Int) coeff1196)) (CoefficientMerge.merge (CoefficientMerge.scale (132853011914530543419526903676315367605520655830833948208505970594240162019472814263219141319121980570716612510722968557783159762736025600 : Int) coeff1197) (CoefficientMerge.merge (CoefficientMerge.scale (240238964255619122507350817000116897241905328946568116721779771899255067483534256324225757068613342909669925631237381295019970158688972800 : Int) coeff1198) (CoefficientMerge.scale (202335784875808778323533244474631600704943109410064045883483370628097340729579117232603262363767816258478910876337423147469958859711744000 : Int) coeff1199)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (157307944030445347266249751229750914940056022531385089548546867842484426219142089985047140946184334868737014335926049397163295275867340800 : Int) coeff1200) (CoefficientMerge.scale (398958398032964587783339159147395780545282691537227314586727047447162585689971731336417767180408686750383791835843754897159026641458278400 : Int) coeff1201)) (CoefficientMerge.merge (CoefficientMerge.scale (718006049598887989928141885495005337213226705705203938696248380852380074109154565097387742812959897126134382026004813338651766638751663360 : Int) coeff1202) (CoefficientMerge.merge (CoefficientMerge.scale (631580321535530030290816080057155643712230540692941010701910083742921282665815408919099937901708051792710389128385617973014339843018620160 : Int) coeff1203) (CoefficientMerge.scale (498359146590065906609344251509694233233205326646443569223208171433768910901578262707691900297729260645173183877532450151849394271286754560 : Int) coeff1204)))))) := by decide +kernel
theorem sparseBlock091_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock091 := by
  rw [sparseBlock091_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted1185_nonneg g t z hg hA hB ht hz hw) (weighted1186_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1187_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1188_nonneg g t z hg hA hB ht hz hw) (weighted1189_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1190_nonneg g t z hg hA hB ht hz hw) (weighted1191_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1192_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1193_nonneg g t z hg hA hB ht hz hw) (weighted1194_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted1195_nonneg g t z hg hA hB ht hz hw) (weighted1196_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1197_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1198_nonneg g t z hg hA hB ht hz hw) (weighted1199_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1200_nonneg g t z hg hA hB ht hz hw) (weighted1201_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1202_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1203_nonneg g t z hg hA hB ht hz hw) (weighted1204_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
