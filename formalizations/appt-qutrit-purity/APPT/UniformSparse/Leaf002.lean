import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff0040 : CoefficientMerge.Poly :=
  [(1048648, 324), (1310792, -36), (1572936, 1), (2097224, -36), (2359368, 2), (3145800, 1)]
noncomputable def atom0040 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 1) * (g 1) * (g 3)) * z * (t+z-18) * (t+z-18))
theorem atom0040_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0040 g t z = CoefficientMerge.eval (monomial g t z) coeff0040 := by
  norm_num [atom0040, coeff0040, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0040_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0040 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0040]
  positivity
theorem weighted0040_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1394929875276519356023129876724654187107846731809496292223504344829906878497161081064638846547893463105021952450781163005644778084556800 : Int) coeff0040) := by
  rw [CoefficientMerge.eval_scale, ← atom0040_identity]
  exact mul_nonneg (by norm_num) (atom0040_nonneg g t z hg hA hB ht hz hw)

def coeff0041 : CoefficientMerge.Poly :=
  [(72, -5832), (262216, 972), (524360, -54), (786504, 1), (1048648, 972), (1310792, -108), (1572936, 3), (2097224, -54), (2359368, 3), (3145800, 1)]
noncomputable def atom0041 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 1) * (g 1) * (g 3)) * (t+z-18) * (t+z-18) * (t+z-18))
theorem atom0041_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0041 g t z = CoefficientMerge.eval (monomial g t z) coeff0041 := by
  norm_num [atom0041, coeff0041, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0041_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0041 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0041]
  positivity
theorem weighted0041_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1270003622262140800726784492498512804145027805149603420485181973800637899390439816943064719548865966364313336905604969154588729254604800 : Int) coeff0041) := by
  rw [CoefficientMerge.eval_scale, ← atom0041_identity]
  exact mul_nonneg (by norm_num) (atom0041_nonneg g t z hg hA hB ht hz hw)

def coeff0042 : CoefficientMerge.Poly :=
  [(524552, -18), (786696, 1), (1573128, 1)]
noncomputable def atom0042 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 1) * (g 1) * (g 4)) * t * t * (t+z-18))
theorem atom0042_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0042 g t z = CoefficientMerge.eval (monomial g t z) coeff0042 := by
  norm_num [atom0042, coeff0042, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0042_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0042 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0042]
  positivity
theorem weighted0042_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (19511864826118309264896395423997313577294902492104631098656186798251819696384962140202940771758478541735462896646725890222554791164211200 : Int) coeff0042) := by
  rw [CoefficientMerge.eval_scale, ← atom0042_identity]
  exact mul_nonneg (by norm_num) (atom0042_nonneg g t z hg hA hB ht hz hw)

def coeff0043 : CoefficientMerge.Poly :=
  [(1310984, -18), (1573128, 1), (2359560, 1)]
noncomputable def atom0043 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 1) * (g 1) * (g 4)) * t * z * (t+z-18))
theorem atom0043_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0043 g t z = CoefficientMerge.eval (monomial g t z) coeff0043 := by
  norm_num [atom0043, coeff0043, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0043_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0043 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0043]
  positivity
theorem weighted0043_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (39343658953806959811817917116923377829605557879788254391737366354277005886487446589399913184733883468769120631113730630183928942319104000 : Int) coeff0043) := by
  rw [CoefficientMerge.eval_scale, ← atom0043_identity]
  exact mul_nonneg (by norm_num) (atom0043_nonneg g t z hg hA hB ht hz hw)

def coeff0044 : CoefficientMerge.Poly :=
  [(262408, 324), (524552, -36), (786696, 1), (1310984, -36), (1573128, 2), (2359560, 1)]
noncomputable def atom0044 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 1) * (g 1) * (g 4)) * t * (t+z-18) * (t+z-18))
theorem atom0044_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0044 g t z = CoefficientMerge.eval (monomial g t z) coeff0044 := by
  norm_num [atom0044, coeff0044, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0044_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0044 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0044]
  positivity
theorem weighted0044_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1108182892567701341214636432215304305658174790595362935690911993901930552202085581229785808889089710809668266505940999428360962455859200 : Int) coeff0044) := by
  rw [CoefficientMerge.eval_scale, ← atom0044_identity]
  exact mul_nonneg (by norm_num) (atom0044_nonneg g t z hg hA hB ht hz hw)

def coeff0045 : CoefficientMerge.Poly :=
  [(2097416, -18), (2359560, 1), (3145992, 1)]
noncomputable def atom0045 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 1) * (g 1) * (g 4)) * z * z * (t+z-18))
theorem atom0045_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0045 g t z = CoefficientMerge.eval (monomial g t z) coeff0045 := by
  norm_num [atom0045, coeff0045, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0045_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0045 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0045]
  positivity
theorem weighted0045_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (21142470325109109621119226465538456907953886072386324110169277215239330081696981985658853908502125640264654841185470793983779278915993600 : Int) coeff0045) := by
  rw [CoefficientMerge.eval_scale, ← atom0045_identity]
  exact mul_nonneg (by norm_num) (atom0045_nonneg g t z hg hA hB ht hz hw)

def coeff0046 : CoefficientMerge.Poly :=
  [(266248, 324), (528392, -36), (790536, 1), (1314824, -36), (1576968, 2), (2363400, 1)]
noncomputable def atom0046 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 1) * (g 1) * (g 6)) * t * (t+z-18) * (t+z-18))
theorem atom0046_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0046 g t z = CoefficientMerge.eval (monomial g t z) coeff0046 := by
  norm_num [atom0046, coeff0046, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0046_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0046 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0046]
  positivity
theorem weighted0046_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1776277405903864644012493078445414149624544418275021817568743546787831954184643693172211927430775097908198367290506393813024661855641600 : Int) coeff0046) := by
  rw [CoefficientMerge.eval_scale, ← atom0046_identity]
  exact mul_nonneg (by norm_num) (atom0046_nonneg g t z hg hA hB ht hz hw)

def coeff0047 : CoefficientMerge.Poly :=
  [(1052680, 324), (1314824, -36), (1576968, 1), (2101256, -36), (2363400, 2), (3149832, 1)]
noncomputable def atom0047 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 1) * (g 1) * (g 6)) * z * (t+z-18) * (t+z-18))
theorem atom0047_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0047 g t z = CoefficientMerge.eval (monomial g t z) coeff0047 := by
  norm_num [atom0047, coeff0047, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0047_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0047 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0047]
  positivity
theorem weighted0047_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1271609411900275053079349960648737362505094271985551796968688135144419137394076483404264841592705873872791724704585123333044297234227200 : Int) coeff0047) := by
  rw [CoefficientMerge.eval_scale, ← atom0047_identity]
  exact mul_nonneg (by norm_num) (atom0047_nonneg g t z hg hA hB ht hz hw)

def coeff0048 : CoefficientMerge.Poly :=
  [(262240, 324), (524384, -36), (786528, 1), (1310816, -36), (1572960, 2), (2359392, 1)]
noncomputable def atom0048 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 2) * (g 2) * (g 3)) * t * (t+z-18) * (t+z-18))
theorem atom0048_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0048 g t z = CoefficientMerge.eval (monomial g t z) coeff0048 := by
  norm_num [atom0048, coeff0048, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0048_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0048 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0048]
  positivity
theorem weighted0048_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (17394432993900187067134569103144152997798880335574804275527221975360531021504447423666981789454190973814358694543413610707669456990003200 : Int) coeff0048) := by
  rw [CoefficientMerge.eval_scale, ← atom0048_identity]
  exact mul_nonneg (by norm_num) (atom0048_nonneg g t z hg hA hB ht hz hw)

def coeff0049 : CoefficientMerge.Poly :=
  [(2097248, -18), (2359392, 1), (3145824, 1)]
noncomputable def atom0049 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 2) * (g 2) * (g 3)) * z * z * (t+z-18))
theorem atom0049_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0049 g t z = CoefficientMerge.eval (monomial g t z) coeff0049 := by
  norm_num [atom0049, coeff0049, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0049_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0049 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0049]
  positivity
theorem weighted0049_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (15162569004287593081451759468426919839841749803669558059691043396321193825726373903396217689213543598047482225030781150819431762216437760 : Int) coeff0049) := by
  rw [CoefficientMerge.eval_scale, ← atom0049_identity]
  exact mul_nonneg (by norm_num) (atom0049_nonneg g t z hg hA hB ht hz hw)

def coeff0050 : CoefficientMerge.Poly :=
  [(2097440, -18), (2359584, 1), (3146016, 1)]
noncomputable def atom0050 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 2) * (g 2) * (g 4)) * z * z * (t+z-18))
theorem atom0050_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0050 g t z = CoefficientMerge.eval (monomial g t z) coeff0050 := by
  norm_num [atom0050, coeff0050, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0050_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0050 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0050]
  positivity
theorem weighted0050_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (30181483878517410519260271260300079894957413291800022945425627664503111229492242675588733313495106281161235060572026114277251860083097792 : Int) coeff0050) := by
  rw [CoefficientMerge.eval_scale, ← atom0050_identity]
  exact mul_nonneg (by norm_num) (atom0050_nonneg g t z hg hA hB ht hz hw)

def coeff0051 : CoefficientMerge.Poly :=
  [(525344, -18), (787488, 1), (1573920, 1)]
noncomputable def atom0051 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 2) * (g 2) * (g 5)) * t * t * (t+z-18))
theorem atom0051_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0051 g t z = CoefficientMerge.eval (monomial g t z) coeff0051 := by
  norm_num [atom0051, coeff0051, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0051_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0051 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0051]
  positivity
theorem weighted0051_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (69188666916186021031424956744117835178157015220528625520378710150761320081282948615708904697555277622220155590023439889388164729233152000 : Int) coeff0051) := by
  rw [CoefficientMerge.eval_scale, ← atom0051_identity]
  exact mul_nonneg (by norm_num) (atom0051_nonneg g t z hg hA hB ht hz hw)

def coeff0052 : CoefficientMerge.Poly :=
  [(2098208, -18), (2360352, 1), (3146784, 1)]
noncomputable def atom0052 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 2) * (g 2) * (g 5)) * z * z * (t+z-18))
theorem atom0052_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0052 g t z = CoefficientMerge.eval (monomial g t z) coeff0052 := by
  norm_num [atom0052, coeff0052, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0052_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0052 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0052]
  positivity
theorem weighted0052_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (22545046087934274964387345968681676962453872271859182779192630457221646692520492684932993961556979348287199107453196062735733353934421120 : Int) coeff0052) := by
  rw [CoefficientMerge.eval_scale, ← atom0052_identity]
  exact mul_nonneg (by norm_num) (atom0052_nonneg g t z hg hA hB ht hz hw)

def coeff0053 : CoefficientMerge.Poly :=
  [(528416, -18), (790560, 1), (1576992, 1)]
noncomputable def atom0053 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 2) * (g 2) * (g 6)) * t * t * (t+z-18))
theorem atom0053_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0053 g t z = CoefficientMerge.eval (monomial g t z) coeff0053 := by
  norm_num [atom0053, coeff0053, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0053_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0053 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0053]
  positivity
theorem weighted0053_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (80007328949911992346377551112690804235198158545470939364749337835953029711680694831433758970950529715124513345564087300020144165181992960 : Int) coeff0053) := by
  rw [CoefficientMerge.eval_scale, ← atom0053_identity]
  exact mul_nonneg (by norm_num) (atom0053_nonneg g t z hg hA hB ht hz hw)

def coeff0054 : CoefficientMerge.Poly :=
  [(1314848, -18), (1576992, 1), (2363424, 1)]
noncomputable def atom0054 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 2) * (g 2) * (g 6)) * t * z * (t+z-18))
theorem atom0054_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0054 g t z = CoefficientMerge.eval (monomial g t z) coeff0054 := by
  norm_num [atom0054, coeff0054, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0054_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0054 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0054]
  positivity
theorem weighted0054_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (28224666089839999168517884356151872372394571432203214655686386541444968504883382927564523835554464447021157497329946669155718628842762240 : Int) coeff0054) := by
  rw [CoefficientMerge.eval_scale, ← atom0054_identity]
  exact mul_nonneg (by norm_num) (atom0054_nonneg g t z hg hA hB ht hz hw)

def coeff0055 : CoefficientMerge.Poly :=
  [(2101280, -18), (2363424, 1), (3149856, 1)]
noncomputable def atom0055 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 2) * (g 2) * (g 6)) * z * z * (t+z-18))
theorem atom0055_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0055 g t z = CoefficientMerge.eval (monomial g t z) coeff0055 := by
  norm_num [atom0055, coeff0055, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0055_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0055 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0055]
  positivity
theorem weighted0055_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2889671934653233004786139022204279587180902206126525225888721667733427948203912659312590266499616437885556091228461074872412570172764160 : Int) coeff0055) := by
  rw [CoefficientMerge.eval_scale, ← atom0055_identity]
  exact mul_nonneg (by norm_num) (atom0055_nonneg g t z hg hA hB ht hz hw)

def coeff0056 : CoefficientMerge.Poly :=
  [(540704, -18), (802848, 1), (1589280, 1)]
noncomputable def atom0056 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 2) * (g 2) * (g 7)) * t * t * (t+z-18))
theorem atom0056_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0056 g t z = CoefficientMerge.eval (monomial g t z) coeff0056 := by
  norm_num [atom0056, coeff0056, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0056_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0056 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0056]
  positivity
theorem weighted0056_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (55825103292999508913855256296168938927862761425657004577556220496743943522953771631577983429419890833361432146477170907521423705505126400 : Int) coeff0056) := by
  rw [CoefficientMerge.eval_scale, ← atom0056_identity]
  exact mul_nonneg (by norm_num) (atom0056_nonneg g t z hg hA hB ht hz hw)

def coeff0057 : CoefficientMerge.Poly :=
  [(1327136, -18), (1589280, 1), (2375712, 1)]
noncomputable def atom0057 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 2) * (g 2) * (g 7)) * t * z * (t+z-18))
theorem atom0057_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0057 g t z = CoefficientMerge.eval (monomial g t z) coeff0057 := by
  norm_num [atom0057, coeff0057, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0057_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0057 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0057]
  positivity
theorem weighted0057_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (46634691782604861437858679012884043294082949473498213933891725842013076088264381391650024007829663461656229644593530363054864757005772800 : Int) coeff0057) := by
  rw [CoefficientMerge.eval_scale, ← atom0057_identity]
  exact mul_nonneg (by norm_num) (atom0057_nonneg g t z hg hA hB ht hz hw)

def coeff0058 : CoefficientMerge.Poly :=
  [(2113568, -18), (2375712, 1), (3162144, 1)]
noncomputable def atom0058 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 2) * (g 2) * (g 7)) * z * z * (t+z-18))
theorem atom0058_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0058 g t z = CoefficientMerge.eval (monomial g t z) coeff0058 := by
  norm_num [atom0058, coeff0058, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0058_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0058 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0058]
  positivity
theorem weighted0058_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (22776414420289402905828735547619296637180579277765230538313137856446305395606872803985935741012978407271568626310457148196917019404697600 : Int) coeff0058) := by
  rw [CoefficientMerge.eval_scale, ← atom0058_identity]
  exact mul_nonneg (by norm_num) (atom0058_nonneg g t z hg hA hB ht hz hw)

def coeff0059 : CoefficientMerge.Poly :=
  [(144, -5832), (262288, 972), (524432, -54), (786576, 1), (1048720, 972), (1310864, -108), (1573008, 3), (2097296, -54), (2359440, 3), (3145872, 1)]
noncomputable def atom0059 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 2) * (g 3) * (g 3)) * (t+z-18) * (t+z-18) * (t+z-18))
theorem atom0059_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0059 g t z = CoefficientMerge.eval (monomial g t z) coeff0059 := by
  norm_num [atom0059, coeff0059, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0059_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0059 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0059]
  positivity
theorem weighted0059_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (757457044479864800133835935636855828065184329771892971456755674871135645194823461962263482741548531244881166949964516610184891489228800 : Int) coeff0059) := by
  rw [CoefficientMerge.eval_scale, ← atom0059_identity]
  exact mul_nonneg (by norm_num) (atom0059_nonneg g t z hg hA hB ht hz hw)

def sparseBlock002 : CoefficientMerge.Poly :=
  [(72, -7406661125032805149838607160251326673773802159632487148269581271205320229245045012411953444408986315836675380833488180109561469012855193600), (144, -4417489483406571514380531176634143189276155011229679809535799095848463082776210430163920631348711034220146965652193060870598287165182361600), (262216, 1234443520838800858306434526708554445628967026605414524711596878534220038207507502068658907401497719306112563472248030018260244835475865600), (262240, 5635796290023660609751600389418705571286837228726236585270819920016812050967440965268102099783157875515852217032066009869284904064761036800), (262288, 736248247234428585730088529439023864879359168538279968255966515974743847129368405027320105224785172370024494275365510145099714527530393600), (262408, 359051257191935234553542204037758595033248632152897591163855486024225498913475728318450602080065066302332518347924883814788951835698380800), (266248, 575513879512852144660047757416314184478352391521107068892272909159257553155824556587796664487571131722256271002124071595419990441227878400), (524360, -68580195602155603239246362594919691423831501478078584706199826585234446567083750114925494855638762183672920192902668334347791379748659200), (524384, -626199587780406734416844487713189507920759692080692953918979991112979116774160107252011344420350875057316913003562889985476100451640115200), (524432, -40902680401912699207227140524390214715519953807682220458664806443041324840520466945962228068043620687223583015298083896949984140418355200), (524552, -391108151002566815051862029191702599395002537319316425460684194149002254414204399447925223011659843340386389733854942003426980889366732800), (525344, -1245396004491348378565649221394121033206826273969515259366816782713703761463093075082760284555994997199962800620421918008986965126196736000), (528392, -63945986612539127184449750824034909386483599057900785432474767684361950350647172954199629387507903524695141222458230177268887826803097600), (528416, -1440131921098415862234795920028434476233566853818476908565488081047154534810252506965807661477109534872241240220153571400362594973275873280), (540704, -1004851859273991160449394613331040900701529705661826082396011968941390983413167889368403701729558035000505778636589076335385626699092275200), (786504, 1270003622262140800726784492498512804145027805149603420485181973800637899390439816943064719548865966364313336905604969154588729254604800), (786528, 17394432993900187067134569103144152997798880335574804275527221975360531021504447423666981789454190973814358694543413610707669456990003200), (786576, 757457044479864800133835935636855828065184329771892971456755674871135645194823461962263482741548531244881166949964516610184891489228800), (786696, 20620047718686010606111031856212617882953077282699994034347098792153750248587047721432726580647568252545131163152666889650915753620070400), (787488, 69188666916186021031424956744117835178157015220528625520378710150761320081282948615708904697555277622220155590023439889388164729233152000), (790536, 1776277405903864644012493078445414149624544418275021817568743546787831954184643693172211927430775097908198367290506393813024661855641600), (790560, 80007328949911992346377551112690804235198158545470939364749337835953029711680694831433758970950529715124513345564087300020144165181992960), (802848, 55825103292999508913855256296168938927862761425657004577556220496743943522953771631577983429419890833361432146477170907521423705505126400), (1048648, 1686400800428393129657928606767342402251909367711691323392012286259109866840587692333601893683015201352139676066301126832089152934872268800), (1048720, 736248247234428585730088529439023864879359168538279968255966515974743847129368405027320105224785172370024494275365510145099714527530393600), (1052680, 412001449455689117197709387250190905451650544123318782217854955786791800515680780622981808676036703134784518804285579959906352303889612800), (1310792, -187377866714265903295325400751926933583545485301299035932445809584345540760065299148177988187001689039126630674033458536898794770541363200), (1310816, -626199587780406734416844487713189507920759692080692953918979991112979116774160107252011344420350875057316913003562889985476100451640115200), (1310864, -81805360803825398414454281048780429431039907615364440917329612886082649681040933891924456136087241374447166030596167793899968280836710400), (1310984, -748080445300962524896449419664371755936594334297621644736145426157455605836049119533470726445217132026992228954261027322731715610154803200), (1314824, -109723925440949029095306349407389454436666992849380650123347540549561039296833926356753163684845314984115643311823294617258482527235276800), (1314848, -508043989617119985033321918410733702703102285779657863802354957746009433087900892696161429039980360046380834951939040044802935319169720320), (1327136, -839424452086887505881456222231912779293493090522967850810051065156235369588758865049700432140933942309812133602683546534987565626103910400), (1572936, 5204940742062941758203483354220192599542930147258306553679050266231820576668480531893833005194491362197961963167596070469410965848371200), (1572960, 34788865987800374134269138206288305995597760671149608551054443950721062043008894847333963578908381947628717389086827221415338913980006400), (1573008, 2272371133439594400401507806910567484195552989315678914370267024613406935584470385886790448224645593734643500849893549830554674467686400), (1573128, 61071889565060671759143585405351300018216809953083611361775377140332686687276579892062425574270541432123920060772338519263205658395033600), (1573920, 69188666916186021031424956744117835178157015220528625520378710150761320081282948615708904697555277622220155590023439889388164729233152000), (1576968, 4824164223708004341104336117539565661754183108535595432106175228720083045763363869748688696454256069689188459285597910959093620945510400), (1576992, 108231995039751991514895435468842676607592729977674154020435724377397998216564077758998282806504994162145670842894033969175862794024755200), (1589280, 102459795075604370351713935309052982221945710899155218511447946338757019611218153023228007437249554295017661791070701270576288462510899200), (2097224, -118797671112110300056079038157007242159713983823220451226245982999111094192981549033252493331362926855453710481130790202551003390792704000), (2097248, -272926242077176675466131670431684557117151496466052045074438781133781488863074730261131918405843784764854680050554060714749771719895879680), (2097296, -40902680401912699207227140524390214715519953807682220458664806443041324840520466945962228068043620687223583015298083896949984140418355200), (2097416, -380564465851963973180146076379692224343169949302953833983046989874307941470545675741859370353038261524763787141338474291708027020487884800), (2097440, -543266709813313389346684882685401438109233439252400413017661297961056002130860368160597199642911913060902231090296470056990533481495760256), (2098208, -405810829582816949358972227436270185324169700893465290025467348229989640465368868328793891308025628269169583934157529129243200370819580160), (2101256, -45777938828409901910856598583354545050183393791479864690872772865199088946186753402553534297337411459420502089365064439989594700432179200), (2101280, -52014094823758194086150502399677032569256239710277454065996990019201703067670427867626624796993095881940009642112299347703426263109754880), (2113568, -409975459565209252304917239857147339469250426999774149689636481416033497120923710471746843338233611330888235273588228667544506349284556800), (2359368, 6599870617339461114226613230944846786650776879067802845902554611061727455165641612958471851742384825302983915618377233475055743932928000), (2359392, 32557001998187780148586328571571072837640630139244362335218265371681724847230821327063199478667734571861840919574194761527101219206440960), (2359440, 2272371133439594400401507806910567484195552989315678914370267024613406935584470385886790448224645593734643500849893549830554674467686400), (2359560, 61594312171483770774151780014677139043217618742769941437597555563418266520386514156288552902125098819843443738805142423596069183690956800), (2359584, 30181483878517410519260271260300079894957413291800022945425627664503111229492242675588733313495106281161235060572026114277251860083097792), (2360352, 22545046087934274964387345968681676962453872271859182779192630457221646692520492684932993961556979348287199107453196062735733353934421120), (2363400, 4319496229704414750171192999742888874634732962246125411506119817076670228972796659980741610616186845653781816699676640479113256324096000), (2363424, 31114338024493232173304023378356151959575473638329739881575108209178396453087295586877114102054080884906713588558407744028131199015526400), (2375712, 69411106202894264343687414560503339931263528751263444472204863698459381483871254195635959748842641868927798270903987511251781776410470400), (3145800, 2664933497538660156749914369223166991252874536959099712708686318630544777887600898007703566096759429469335289356386132160233507339161600), (3145824, 15162569004287593081451759468426919839841749803669558059691043396321193825726373903396217689213543598047482225030781150819431762216437760), (3145872, 757457044479864800133835935636855828065184329771892971456755674871135645194823461962263482741548531244881166949964516610184891489228800), (3145992, 21142470325109109621119226465538456907953886072386324110169277215239330081696981985658853908502125640264654841185470793983779278915993600), (3146016, 30181483878517410519260271260300079894957413291800022945425627664503111229492242675588733313495106281161235060572026114277251860083097792), (3146784, 22545046087934274964387345968681676962453872271859182779192630457221646692520492684932993961556979348287199107453196062735733353934421120), (3149832, 1271609411900275053079349960648737362505094271985551796968688135144419137394076483404264841592705873872791724704585123333044297234227200), (3149856, 2889671934653233004786139022204279587180902206126525225888721667733427948203912659312590266499616437885556091228461074872412570172764160), (3162144, 22776414420289402905828735547619296637180579277765230538313137856446305395606872803985935741012978407271568626310457148196917019404697600)]
theorem sparseBlock002_data : sparseBlock002 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1394929875276519356023129876724654187107846731809496292223504344829906878497161081064638846547893463105021952450781163005644778084556800 : Int) coeff0040) (CoefficientMerge.scale (1270003622262140800726784492498512804145027805149603420485181973800637899390439816943064719548865966364313336905604969154588729254604800 : Int) coeff0041)) (CoefficientMerge.merge (CoefficientMerge.scale (19511864826118309264896395423997313577294902492104631098656186798251819696384962140202940771758478541735462896646725890222554791164211200 : Int) coeff0042) (CoefficientMerge.merge (CoefficientMerge.scale (39343658953806959811817917116923377829605557879788254391737366354277005886487446589399913184733883468769120631113730630183928942319104000 : Int) coeff0043) (CoefficientMerge.scale (1108182892567701341214636432215304305658174790595362935690911993901930552202085581229785808889089710809668266505940999428360962455859200 : Int) coeff0044)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (21142470325109109621119226465538456907953886072386324110169277215239330081696981985658853908502125640264654841185470793983779278915993600 : Int) coeff0045) (CoefficientMerge.scale (1776277405903864644012493078445414149624544418275021817568743546787831954184643693172211927430775097908198367290506393813024661855641600 : Int) coeff0046)) (CoefficientMerge.merge (CoefficientMerge.scale (1271609411900275053079349960648737362505094271985551796968688135144419137394076483404264841592705873872791724704585123333044297234227200 : Int) coeff0047) (CoefficientMerge.merge (CoefficientMerge.scale (17394432993900187067134569103144152997798880335574804275527221975360531021504447423666981789454190973814358694543413610707669456990003200 : Int) coeff0048) (CoefficientMerge.scale (15162569004287593081451759468426919839841749803669558059691043396321193825726373903396217689213543598047482225030781150819431762216437760 : Int) coeff0049))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (30181483878517410519260271260300079894957413291800022945425627664503111229492242675588733313495106281161235060572026114277251860083097792 : Int) coeff0050) (CoefficientMerge.scale (69188666916186021031424956744117835178157015220528625520378710150761320081282948615708904697555277622220155590023439889388164729233152000 : Int) coeff0051)) (CoefficientMerge.merge (CoefficientMerge.scale (22545046087934274964387345968681676962453872271859182779192630457221646692520492684932993961556979348287199107453196062735733353934421120 : Int) coeff0052) (CoefficientMerge.merge (CoefficientMerge.scale (80007328949911992346377551112690804235198158545470939364749337835953029711680694831433758970950529715124513345564087300020144165181992960 : Int) coeff0053) (CoefficientMerge.scale (28224666089839999168517884356151872372394571432203214655686386541444968504883382927564523835554464447021157497329946669155718628842762240 : Int) coeff0054)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (2889671934653233004786139022204279587180902206126525225888721667733427948203912659312590266499616437885556091228461074872412570172764160 : Int) coeff0055) (CoefficientMerge.scale (55825103292999508913855256296168938927862761425657004577556220496743943522953771631577983429419890833361432146477170907521423705505126400 : Int) coeff0056)) (CoefficientMerge.merge (CoefficientMerge.scale (46634691782604861437858679012884043294082949473498213933891725842013076088264381391650024007829663461656229644593530363054864757005772800 : Int) coeff0057) (CoefficientMerge.merge (CoefficientMerge.scale (22776414420289402905828735547619296637180579277765230538313137856446305395606872803985935741012978407271568626310457148196917019404697600 : Int) coeff0058) (CoefficientMerge.scale (757457044479864800133835935636855828065184329771892971456755674871135645194823461962263482741548531244881166949964516610184891489228800 : Int) coeff0059)))))) := by decide +kernel
theorem sparseBlock002_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock002 := by
  rw [sparseBlock002_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted0040_nonneg g t z hg hA hB ht hz hw) (weighted0041_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0042_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0043_nonneg g t z hg hA hB ht hz hw) (weighted0044_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0045_nonneg g t z hg hA hB ht hz hw) (weighted0046_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0047_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0048_nonneg g t z hg hA hB ht hz hw) (weighted0049_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted0050_nonneg g t z hg hA hB ht hz hw) (weighted0051_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0052_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0053_nonneg g t z hg hA hB ht hz hw) (weighted0054_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0055_nonneg g t z hg hA hB ht hz hw) (weighted0056_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0057_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0058_nonneg g t z hg hA hB ht hz hw) (weighted0059_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
