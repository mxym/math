import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff0000 : CoefficientMerge.Poly :=
  [(1048579, -18), (1310723, 1), (2097155, 1)]
noncomputable def atom0000 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 0) * (g 0) * (g 0)) * z * (t+z-18))
theorem atom0000_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0000 g t z = CoefficientMerge.eval (monomial g t z) coeff0000 := by
  norm_num [atom0000, coeff0000, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0000_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0000 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0000]
  positivity
theorem weighted0000_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (478186436282738944115913317155502065391427534965141579620576011817642512343712382417597782709957443185178542387831446433202514816000000 : Int) coeff0000) := by
  rw [CoefficientMerge.eval_scale, ← atom0000_identity]
  exact mul_nonneg (by norm_num) (atom0000_nonneg g t z hg hA hB ht hz hw)

def coeff0001 : CoefficientMerge.Poly :=
  [(524291, -18), (786435, 1), (1572867, 1)]
noncomputable def atom0001 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 0) * (g 0) * (g 0)) * t * t * (t+z-18))
theorem atom0001_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0001 g t z = CoefficientMerge.eval (monomial g t z) coeff0001 := by
  norm_num [atom0001, coeff0001, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0001_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0001 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0001]
  positivity
theorem weighted0001_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1458693965570975944940681163142232087455830434121425662505110244231685017816959708296623211228404360407897539316268869945125382410240000 : Int) coeff0001) := by
  rw [CoefficientMerge.eval_scale, ← atom0001_identity]
  exact mul_nonneg (by norm_num) (atom0001_nonneg g t z hg hA hB ht hz hw)

def coeff0002 : CoefficientMerge.Poly :=
  [(1310723, -18), (1572867, 1), (2359299, 1)]
noncomputable def atom0002 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 0) * (g 0) * (g 0)) * t * z * (t+z-18))
theorem atom0002_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0002 g t z = CoefficientMerge.eval (monomial g t z) coeff0002 := by
  norm_num [atom0002, coeff0002, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0002_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0002 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0002]
  positivity
theorem weighted0002_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2890822018015133059652700475331380726834359338522565681697966265584612118281490950903379878972922196194396270722102659532850625108480000 : Int) coeff0002) := by
  rw [CoefficientMerge.eval_scale, ← atom0002_identity]
  exact mul_nonneg (by norm_num) (atom0002_nonneg g t z hg hA hB ht hz hw)

def coeff0003 : CoefficientMerge.Poly :=
  [(2097155, -18), (2359299, 1), (3145731, 1)]
noncomputable def atom0003 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 0) * (g 0) * (g 0)) * z * z * (t+z-18))
theorem atom0003_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0003 g t z = CoefficientMerge.eval (monomial g t z) coeff0003 := by
  norm_num [atom0003, coeff0003, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0003_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0003 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0003]
  positivity
theorem weighted0003_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1432128052444157114712019312189148639378528904401140019192856021352927100464531242606756667744517835786498731405833789587725242698240000 : Int) coeff0003) := by
  rw [CoefficientMerge.eval_scale, ← atom0003_identity]
  exact mul_nonneg (by norm_num) (atom0003_nonneg g t z hg hA hB ht hz hw)

def coeff0004 : CoefficientMerge.Poly :=
  [(3, -5832), (262147, 972), (524291, -54), (786435, 1), (1048579, 972), (1310723, -108), (1572867, 3), (2097155, -54), (2359299, 3), (3145731, 1)]
noncomputable def atom0004 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 0) * (g 0) * (g 0)) * (t+z-18) * (t+z-18) * (t+z-18))
theorem atom0004_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0004 g t z = CoefficientMerge.eval (monomial g t z) coeff0004 := by
  norm_num [atom0004, coeff0004, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0004_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0004 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0004]
  positivity
theorem weighted0004_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (47735710482238087425238989893041029928933969320572664993151927495887899925391127797769314466026851624093668177543880350864631598694400 : Int) coeff0004) := by
  rw [CoefficientMerge.eval_scale, ← atom0004_identity]
  exact mul_nonneg (by norm_num) (atom0004_nonneg g t z hg hA hB ht hz hw)

def coeff0005 : CoefficientMerge.Poly :=
  [(524294, -18), (786438, 1), (1572870, 1)]
noncomputable def atom0005 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 0) * (g 0) * (g 1)) * t * t * (t+z-18))
theorem atom0005_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0005 g t z = CoefficientMerge.eval (monomial g t z) coeff0005 := by
  norm_num [atom0005, coeff0005, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0005_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0005 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0005]
  positivity
theorem weighted0005_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4280265207417277417085250816272798075002030962668903075283243821662352440262024403392810947787543884577032113272221848170515033962700800 : Int) coeff0005) := by
  rw [CoefficientMerge.eval_scale, ← atom0005_identity]
  exact mul_nonneg (by norm_num) (atom0005_nonneg g t z hg hA hB ht hz hw)

def coeff0006 : CoefficientMerge.Poly :=
  [(1310726, -18), (1572870, 1), (2359302, 1)]
noncomputable def atom0006 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 0) * (g 0) * (g 1)) * t * z * (t+z-18))
theorem atom0006_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0006 g t z = CoefficientMerge.eval (monomial g t z) coeff0006 := by
  norm_num [atom0006, coeff0006, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0006_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0006 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0006]
  positivity
theorem weighted0006_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (8612933689008836899958760272040945919509027462232769083513802191173714187089042433852576719391493715436433882725705432600878009367326720 : Int) coeff0006) := by
  rw [CoefficientMerge.eval_scale, ← atom0006_identity]
  exact mul_nonneg (by norm_num) (atom0006_nonneg g t z hg hA hB ht hz hw)

def coeff0007 : CoefficientMerge.Poly :=
  [(2097158, -18), (2359302, 1), (3145734, 1)]
noncomputable def atom0007 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 0) * (g 0) * (g 1)) * z * z * (t+z-18))
theorem atom0007_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0007 g t z = CoefficientMerge.eval (monomial g t z) coeff0007 := by
  norm_num [atom0007, coeff0007, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0007_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0007 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0007]
  positivity
theorem weighted0007_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4315989040744648457997115870722836379457224866695071207498839598418279968214302350241153199222180987627732523922788778109745918839971840 : Int) coeff0007) := by
  rw [CoefficientMerge.eval_scale, ← atom0007_identity]
  exact mul_nonneg (by norm_num) (atom0007_nonneg g t z hg hA hB ht hz hw)

def coeff0008 : CoefficientMerge.Poly :=
  [(524306, -18), (786450, 1), (1572882, 1)]
noncomputable def atom0008 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 0) * (g 0) * (g 2)) * t * t * (t+z-18))
theorem atom0008_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0008 g t z = CoefficientMerge.eval (monomial g t z) coeff0008 := by
  norm_num [atom0008, coeff0008, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0008_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0008 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0008]
  positivity
theorem weighted0008_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (18289181114263150683465391899742157861215514661216294558776083534531686542731568598228356837812824514490577648178758181125157117797949440 : Int) coeff0008) := by
  rw [CoefficientMerge.eval_scale, ← atom0008_identity]
  exact mul_nonneg (by norm_num) (atom0008_nonneg g t z hg hA hB ht hz hw)

def coeff0009 : CoefficientMerge.Poly :=
  [(1310738, -18), (1572882, 1), (2359314, 1)]
noncomputable def atom0009 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 0) * (g 0) * (g 2)) * t * z * (t+z-18))
theorem atom0009_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0009 g t z = CoefficientMerge.eval (monomial g t z) coeff0009 := by
  norm_num [atom0009, coeff0009, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0009_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0009 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0009]
  positivity
theorem weighted0009_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (38562253786508324226379010447229856042114780733025950278690800652252493314756586402749972203375057724642275200240988559600981050573066240 : Int) coeff0009) := by
  rw [CoefficientMerge.eval_scale, ← atom0009_identity]
  exact mul_nonneg (by norm_num) (atom0009_nonneg g t z hg hA hB ht hz hw)

def coeff0010 : CoefficientMerge.Poly :=
  [(2097170, -18), (2359314, 1), (3145746, 1)]
noncomputable def atom0010 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 0) * (g 0) * (g 2)) * z * z * (t+z-18))
theorem atom0010_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0010 g t z = CoefficientMerge.eval (monomial g t z) coeff0010 := by
  norm_num [atom0010, coeff0010, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0010_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0010 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0010]
  positivity
theorem weighted0010_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (11947557382826586573503440640093077865367475005219846267714696240299605160731054289101880756597298364559111728476914443931864894300160000 : Int) coeff0010) := by
  rw [CoefficientMerge.eval_scale, ← atom0010_identity]
  exact mul_nonneg (by norm_num) (atom0010_nonneg g t z hg hA hB ht hz hw)

def coeff0011 : CoefficientMerge.Poly :=
  [(18, -5832), (262162, 972), (524306, -54), (786450, 1), (1048594, 972), (1310738, -108), (1572882, 3), (2097170, -54), (2359314, 3), (3145746, 1)]
noncomputable def atom0011 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 0) * (g 0) * (g 2)) * (t+z-18) * (t+z-18) * (t+z-18))
theorem atom0011_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0011 g t z = CoefficientMerge.eval (monomial g t z) coeff0011 := by
  norm_num [atom0011, coeff0011, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0011_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0011 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0011]
  positivity
theorem weighted0011_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1362082924598573322045228007294820208056278818304259484698035121685699158413741001303671866398805821119221214226477716970201571287193600 : Int) coeff0011) := by
  rw [CoefficientMerge.eval_scale, ← atom0011_identity]
  exact mul_nonneg (by norm_num) (atom0011_nonneg g t z hg hA hB ht hz hw)

def coeff0012 : CoefficientMerge.Poly :=
  [(524354, -18), (786498, 1), (1572930, 1)]
noncomputable def atom0012 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 0) * (g 0) * (g 3)) * t * t * (t+z-18))
theorem atom0012_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0012 g t z = CoefficientMerge.eval (monomial g t z) coeff0012 := by
  norm_num [atom0012, coeff0012, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0012_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0012 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0012]
  positivity
theorem weighted0012_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (487530578865564664953982097218037745488710861068376806259604800624225958392001540013341669705898752766571773929419900404900555942297600 : Int) coeff0012) := by
  rw [CoefficientMerge.eval_scale, ← atom0012_identity]
  exact mul_nonneg (by norm_num) (atom0012_nonneg g t z hg hA hB ht hz hw)

def coeff0013 : CoefficientMerge.Poly :=
  [(262210, 324), (524354, -36), (786498, 1), (1310786, -36), (1572930, 2), (2359362, 1)]
noncomputable def atom0013 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 0) * (g 0) * (g 3)) * t * (t+z-18) * (t+z-18))
theorem atom0013_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0013 g t z = CoefficientMerge.eval (monomial g t z) coeff0013 := by
  norm_num [atom0013, coeff0013, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0013_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0013 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0013]
  positivity
theorem weighted0013_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2187395550845093077364412817346154610018239762983944421923551464509823453766568484813387615731392769450902745602606513911431851102720000 : Int) coeff0013) := by
  rw [CoefficientMerge.eval_scale, ← atom0013_identity]
  exact mul_nonneg (by norm_num) (atom0013_nonneg g t z hg hA hB ht hz hw)

def coeff0014 : CoefficientMerge.Poly :=
  [(1048642, 324), (1310786, -36), (1572930, 1), (2097218, -36), (2359362, 2), (3145794, 1)]
noncomputable def atom0014 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 0) * (g 0) * (g 3)) * z * (t+z-18) * (t+z-18))
theorem atom0014_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0014 g t z = CoefficientMerge.eval (monomial g t z) coeff0014 := by
  norm_num [atom0014, coeff0014, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0014_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0014 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0014]
  positivity
theorem weighted0014_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3380056189527226677045941068019761849422817233244418492195142601435831779794390087014618324994803919400273833919141116611769974515302400 : Int) coeff0014) := by
  rw [CoefficientMerge.eval_scale, ← atom0014_identity]
  exact mul_nonneg (by norm_num) (atom0014_nonneg g t z hg hA hB ht hz hw)

def coeff0015 : CoefficientMerge.Poly :=
  [(262402, 324), (524546, -36), (786690, 1), (1310978, -36), (1573122, 2), (2359554, 1)]
noncomputable def atom0015 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 0) * (g 0) * (g 4)) * t * (t+z-18) * (t+z-18))
theorem atom0015_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0015 g t z = CoefficientMerge.eval (monomial g t z) coeff0015 := by
  norm_num [atom0015, coeff0015, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0015_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0015 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0015]
  positivity
theorem weighted0015_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2434051020462176551759856499377119930077725181644204387044026021957020180949758467489256456184055210317499633970284997851191421492039680 : Int) coeff0015) := by
  rw [CoefficientMerge.eval_scale, ← atom0015_identity]
  exact mul_nonneg (by norm_num) (atom0015_nonneg g t z hg hA hB ht hz hw)

def coeff0016 : CoefficientMerge.Poly :=
  [(1048834, 324), (1310978, -36), (1573122, 1), (2097410, -36), (2359554, 2), (3145986, 1)]
noncomputable def atom0016 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 0) * (g 0) * (g 4)) * z * (t+z-18) * (t+z-18))
theorem atom0016_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0016 g t z = CoefficientMerge.eval (monomial g t z) coeff0016 := by
  norm_num [atom0016, coeff0016, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0016_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0016 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0016]
  positivity
theorem weighted0016_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2470962742919062933505665781002465480522083110293246367596502686956091924398896029917387823651867491099735331497183566547399915163238400 : Int) coeff0016) := by
  rw [CoefficientMerge.eval_scale, ← atom0016_identity]
  exact mul_nonneg (by norm_num) (atom0016_nonneg g t z hg hA hB ht hz hw)

def coeff0017 : CoefficientMerge.Poly :=
  [(258, -5832), (262402, 972), (524546, -54), (786690, 1), (1048834, 972), (1310978, -108), (1573122, 3), (2097410, -54), (2359554, 3), (3145986, 1)]
noncomputable def atom0017 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 0) * (g 0) * (g 4)) * (t+z-18) * (t+z-18) * (t+z-18))
theorem atom0017_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0017 g t z = CoefficientMerge.eval (monomial g t z) coeff0017 := by
  norm_num [atom0017, coeff0017, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0017_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0017 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0017]
  positivity
theorem weighted0017_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (448126274995213310209025267278083705773888124516245588809850346414853857979112986927649424629621860695559065910927508678358323829350400 : Int) coeff0017) := by
  rw [CoefficientMerge.eval_scale, ← atom0017_identity]
  exact mul_nonneg (by norm_num) (atom0017_nonneg g t z hg hA hB ht hz hw)

def coeff0018 : CoefficientMerge.Poly :=
  [(263170, 324), (525314, -36), (787458, 1), (1311746, -36), (1573890, 2), (2360322, 1)]
noncomputable def atom0018 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 0) * (g 0) * (g 5)) * t * (t+z-18) * (t+z-18))
theorem atom0018_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0018 g t z = CoefficientMerge.eval (monomial g t z) coeff0018 := by
  norm_num [atom0018, coeff0018, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0018_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0018 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0018]
  positivity
theorem weighted0018_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1251474801057033078634221229267452256696448128961640460884681996324064206359610388856962098604847715285576245272894805624400653554022400 : Int) coeff0018) := by
  rw [CoefficientMerge.eval_scale, ← atom0018_identity]
  exact mul_nonneg (by norm_num) (atom0018_nonneg g t z hg hA hB ht hz hw)

def coeff0019 : CoefficientMerge.Poly :=
  [(2098178, -18), (2360322, 1), (3146754, 1)]
noncomputable def atom0019 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 0) * (g 0) * (g 5)) * z * z * (t+z-18))
theorem atom0019_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0019 g t z = CoefficientMerge.eval (monomial g t z) coeff0019 := by
  norm_num [atom0019, coeff0019, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0019_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0019 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0019]
  positivity
theorem weighted0019_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (370450133491454319314781490696607949871103926194121925233689705583299807848049365334843327678014152218926800624027224822958383502786560 : Int) coeff0019) := by
  rw [CoefficientMerge.eval_scale, ← atom0019_identity]
  exact mul_nonneg (by norm_num) (atom0019_nonneg g t z hg hA hB ht hz hw)

def sparseBlock000 : CoefficientMerge.Poly :=
  [(3, -278394663532412525863993789056215286545542909077579782240062041156018232364881057316590641965868598671714272811435910206242531483585740800), (18, -7943667616258879614167769738543391453384218068350441314758940829670997491868937519603014324837835548767298121368818045370215563746913075200), (258, -2613472435772084025139035358765784172073315542178744273939047220291427699734186939762051444439954691576500472392529230612185744572771532800), (262147, 46399110588735420977332298176035881090923818179596630373343673526003038727480176219431773660978099778619045468572651701040421913930956800), (262162, 1323944602709813269027961623090565242230703011391740219126490138278499581978156253267169054139639258127883020228136340895035927291152179200), (262210, 708716158473810157066069752820154093645909683206797992703230674501182799020368189079537587496971257302092489575244510507303919757281280000), (262402, 1224211269925092540293366065592484219357402215882512933725438967829312488583419566760194332543626336738953293471793877739150311325549445120), (263170, 405477835542478717477487678282654531169649193783571509326636966808996802860513765989655719947970659752526703468417917022305811751503257600), (524291, -28834219746318423729895166390784393190367382157496585834722188480948276916676395650418760783276728475043213789280209197958946989713817600), (524294, -77044773733510993507534514692910365350036557328040255355098388789922343924716439261070597060175789922386578038899993267069270611328614400), (524306, -402757737985059671692819366589279132736918320090323314231663400192598112323510248838508703866166355601268343235447443976643712969871544320), (524354, -87521790250003514754290539174386245379453426966652781701920739133589711586652493173522104221036317250030790772423392708099756646659276800), (524546, -111824655586379874614642198410592837594588065263068619729316855496854834845063406123706301352625568048990176382120345391274240660498350080), (525314, -45053092838053190830831964253628281241072132642619056591848551867666311428945973998850635549774517750280744829824213002478423527944806400), (786435, 1506429676053214032365920153035273117384764403441998327498262171727572917742350836094392525694431212031991207493812750295990014008934400), (786438, 4280265207417277417085250816272798075002030962668903075283243821662352440262024403392810947787543884577032113272221848170515033962700800), (786450, 19651264038861724005510619907036978069271793479520554043474118656217385701145309599532028704211630335609798862405235898095358689085143040), (786498, 2674926129710657742318394914564192355506950624052321228183156265134049412158570024826729285437291522217474519532026414316332407045017600), (786690, 2882177295457389861968881766655203635851613306160449975853876368371874038928871454416905880813677071013058699881212506529549745321390080), (787458, 1251474801057033078634221229267452256696448128961640460884681996324064206359610388856962098604847715285576245272894805624400653554022400), (1048579, 37791754735646119983245858467236843913878122550224081940173305313285473505293353335915013572198865801285831705591685665242776647242956800), (1048594, 1323944602709813269027961623090565242230703011391740219126490138278499581978156253267169054139639258127883020228136340895035927291152179200), (1048642, 1095138205406821443362884906038402839212992783571191591471226202865209496653382388192736337298316469885688722189801721782213471742957977600), (1048834, 1236170668001123727979008272839096177701374184764802535424441407289011733460940136986908895603197515712397659470509013996721863275017830400), (1310723, -56712066620071369571558506147257782249951909245062888510203224938261268808665366536002326001133542063716070493784755503051488949795635200), (1310726, -155032806402159064199257684896737026551162494320189843503248439441126855367602763809346380949046886877855809889062697786815804168611880960), (1310738, -841225524013795754855706812837977991228144165571327129363822204882600388774302583390296061231822067724436844740797387505599428609332101120), (1310786, -200428262653403511158772739873172992539878051864221064908272986374043588408194508585808213866143080798642356862782914698835265722248806400), (1310978, -224978133181207658972133530959698115005173015957502750758522870933676252454295764494825331934092378206140837875209039255611987093159854080), (1311746, -45053092838053190830831964253628281241072132642619056591848551867666311428945973998850635549774517750280744829824213002478423527944806400), (1572867, 4492723115032823266869098608152735904076991680605709339182532292303960835874624042593311033599407111474574814571003170530569902314803200), (1572870, 12893198896426114317044011088313743994511058424901672158797046012836066627351066837245387667179037600013465995997927280771393043330027520), (1572882, 60937683674567194875980086368856474527499131849155023291560989551841277332729378004889344640384299702490516491099179891636742882232596480), (1572930, 8242377870082977496728748799930108814948007620280684142301850331079704645719528596654735226163488211068651099053774044839534232663040000), (1573122, 8683443608829055967652454581590956457999197847130391908114105770114693860235751925678849009908843493821411797170536088284857729635368960), (1573890, 2502949602114066157268442458534904513392896257923280921769363992648128412719220777713924197209695430571152490545789611248801307108044800), (2097155, -27877846873752945841663339756473389059584527087566302675481036457312991891988970885583565217856813588672856704504546305092541960081817600), (2097158, -77687802733403672243948085673011054830230047600511281734979112771529039427857442304340757585999257777299185430610198005975426539119493120), (2097170, -288608510819201517713504243915595692811653606282387244992558428896420647447500991274232134404286884902501956680814256707164452946911334400), (2097218, -121682022822980160373653878448711426579221420396799065719025133651689944072598043132526259699812941098409858021089080198023719082550886400), (2097410, -113153477594827784357491332549105277410584950694434131029206015436821417609232358371119030581466810157150661493088693864337746432661504000), (2098178, -6668102402846177747666066832538943097679870671494194654206414700499396541264888576027179898204254739940682411232490046813250903050158080), (2359299, 4466157201906004436640436757199652455999690150885423695870278069425202918522195576903444490115520586853176006660568090173169762602803200), (2359302, 12928922729753485357955876142763782298966252328927840291012641789591994155303344784093729918613674703064166406648494210710623928207298560), (2359314, 54596059943130630766018135109207394531651092193158575000499602257609195950728863695762868559168773552559050571397336154443450658734807040), (2359362, 8947507929899546431456294953385678308863874229472781406313836667381487013355348658842624265721000608251450413440888747134971800133324800), (2359554, 8720355331285942349398263863216302008443555775779433888666582435113765603684889488106980377376655774603647494697434656981066223306567680), (2360322, 1621924934548487397949002719964060206567552055155762386118371701907364014207659754191805426282861867504503045896922030447359037056808960), (3145731, 1479863762926395202137258302082189669307462873721712684186007948848815000389922370404525982210544687410592399583377669938589874296934400), (3145734, 4315989040744648457997115870722836379457224866695071207498839598418279968214302350241153199222180987627732523922788778109745918839971840), (3145746, 13309640307425159895548668647387898073423753823524105752412731361985304319144795290405552622996104185678332942703392160902066465587353600), (3145794, 3380056189527226677045941068019761849422817233244418492195142601435831779794390087014618324994803919400273833919141116611769974515302400), (3145986, 2919089017914276243714691048280549186295971234809491956406353033370945782378009016845037248281489351795294397408111075225758238992588800), (3146754, 370450133491454319314781490696607949871103926194121925233689705583299807848049365334843327678014152218926800624027224822958383502786560)]
theorem sparseBlock000_data : sparseBlock000 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (478186436282738944115913317155502065391427534965141579620576011817642512343712382417597782709957443185178542387831446433202514816000000 : Int) coeff0000) (CoefficientMerge.scale (1458693965570975944940681163142232087455830434121425662505110244231685017816959708296623211228404360407897539316268869945125382410240000 : Int) coeff0001)) (CoefficientMerge.merge (CoefficientMerge.scale (2890822018015133059652700475331380726834359338522565681697966265584612118281490950903379878972922196194396270722102659532850625108480000 : Int) coeff0002) (CoefficientMerge.merge (CoefficientMerge.scale (1432128052444157114712019312189148639378528904401140019192856021352927100464531242606756667744517835786498731405833789587725242698240000 : Int) coeff0003) (CoefficientMerge.scale (47735710482238087425238989893041029928933969320572664993151927495887899925391127797769314466026851624093668177543880350864631598694400 : Int) coeff0004)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (4280265207417277417085250816272798075002030962668903075283243821662352440262024403392810947787543884577032113272221848170515033962700800 : Int) coeff0005) (CoefficientMerge.scale (8612933689008836899958760272040945919509027462232769083513802191173714187089042433852576719391493715436433882725705432600878009367326720 : Int) coeff0006)) (CoefficientMerge.merge (CoefficientMerge.scale (4315989040744648457997115870722836379457224866695071207498839598418279968214302350241153199222180987627732523922788778109745918839971840 : Int) coeff0007) (CoefficientMerge.merge (CoefficientMerge.scale (18289181114263150683465391899742157861215514661216294558776083534531686542731568598228356837812824514490577648178758181125157117797949440 : Int) coeff0008) (CoefficientMerge.scale (38562253786508324226379010447229856042114780733025950278690800652252493314756586402749972203375057724642275200240988559600981050573066240 : Int) coeff0009))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (11947557382826586573503440640093077865367475005219846267714696240299605160731054289101880756597298364559111728476914443931864894300160000 : Int) coeff0010) (CoefficientMerge.scale (1362082924598573322045228007294820208056278818304259484698035121685699158413741001303671866398805821119221214226477716970201571287193600 : Int) coeff0011)) (CoefficientMerge.merge (CoefficientMerge.scale (487530578865564664953982097218037745488710861068376806259604800624225958392001540013341669705898752766571773929419900404900555942297600 : Int) coeff0012) (CoefficientMerge.merge (CoefficientMerge.scale (2187395550845093077364412817346154610018239762983944421923551464509823453766568484813387615731392769450902745602606513911431851102720000 : Int) coeff0013) (CoefficientMerge.scale (3380056189527226677045941068019761849422817233244418492195142601435831779794390087014618324994803919400273833919141116611769974515302400 : Int) coeff0014)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (2434051020462176551759856499377119930077725181644204387044026021957020180949758467489256456184055210317499633970284997851191421492039680 : Int) coeff0015) (CoefficientMerge.scale (2470962742919062933505665781002465480522083110293246367596502686956091924398896029917387823651867491099735331497183566547399915163238400 : Int) coeff0016)) (CoefficientMerge.merge (CoefficientMerge.scale (448126274995213310209025267278083705773888124516245588809850346414853857979112986927649424629621860695559065910927508678358323829350400 : Int) coeff0017) (CoefficientMerge.merge (CoefficientMerge.scale (1251474801057033078634221229267452256696448128961640460884681996324064206359610388856962098604847715285576245272894805624400653554022400 : Int) coeff0018) (CoefficientMerge.scale (370450133491454319314781490696607949871103926194121925233689705583299807848049365334843327678014152218926800624027224822958383502786560 : Int) coeff0019)))))) := by decide +kernel
theorem sparseBlock000_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock000 := by
  rw [sparseBlock000_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted0000_nonneg g t z hg hA hB ht hz hw) (weighted0001_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0002_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0003_nonneg g t z hg hA hB ht hz hw) (weighted0004_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0005_nonneg g t z hg hA hB ht hz hw) (weighted0006_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0007_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0008_nonneg g t z hg hA hB ht hz hw) (weighted0009_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted0010_nonneg g t z hg hA hB ht hz hw) (weighted0011_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0012_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0013_nonneg g t z hg hA hB ht hz hw) (weighted0014_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0015_nonneg g t z hg hA hB ht hz hw) (weighted0016_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0017_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0018_nonneg g t z hg hA hB ht hz hw) (weighted0019_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
