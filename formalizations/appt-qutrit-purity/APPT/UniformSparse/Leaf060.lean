import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff0565 : CoefficientMerge.Poly :=
  [(263233, 1)]
noncomputable def atom0565 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 5) ^ 1 * (t) ^ 1)
theorem atom0565_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0565 g t z = CoefficientMerge.eval (monomial g t z) coeff0565 := by
  norm_num [atom0565, coeff0565, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0565_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0565 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0565]
  positivity
theorem weighted0565_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1196588720727980410746003737432391733289909211227733898234723031091190942501089166927494436596994879947174282853835777315570695006908733440 : Int) coeff0565) := by
  rw [CoefficientMerge.eval_scale, ← atom0565_identity]
  exact mul_nonneg (by norm_num) (atom0565_nonneg g t z hg hA hB ht hz hw)

def coeff0566 : CoefficientMerge.Poly :=
  [(266305, 1)]
noncomputable def atom0566 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 6) ^ 1 * (t) ^ 1)
theorem atom0566_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0566 g t z = CoefficientMerge.eval (monomial g t z) coeff0566 := by
  norm_num [atom0566, coeff0566, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0566_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0566 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0566]
  positivity
theorem weighted0566_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (117149616328893520775043278857262176605407399538773584699474919626290147036099800492939902728960185922581033670413448604769524534682449920 : Int) coeff0566) := by
  rw [CoefficientMerge.eval_scale, ← atom0566_identity]
  exact mul_nonneg (by norm_num) (atom0566_nonneg g t z hg hA hB ht hz hw)

def coeff0567 : CoefficientMerge.Poly :=
  [(278593, 1)]
noncomputable def atom0567 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 7) ^ 1 * (t) ^ 1)
theorem atom0567_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0567 g t z = CoefficientMerge.eval (monomial g t z) coeff0567 := by
  norm_num [atom0567, coeff0567, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0567_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0567 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0567]
  positivity
theorem weighted0567_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (148920317793190381977391263008993557734110414782984740573473347543083088517839366018212491179560695383414671702910747516161347063533578240 : Int) coeff0567) := by
  rw [CoefficientMerge.eval_scale, ← atom0567_identity]
  exact mul_nonneg (by norm_num) (atom0567_nonneg g t z hg hA hB ht hz hw)

def coeff0568 : CoefficientMerge.Poly :=
  [(327745, 1)]
noncomputable def atom0568 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 8) ^ 1 * (t) ^ 1)
theorem atom0568_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0568 g t z = CoefficientMerge.eval (monomial g t z) coeff0568 := by
  norm_num [atom0568, coeff0568, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0568_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0568 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0568]
  positivity
theorem weighted0568_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (678000501879380171830554545575835445614302676158631031711817453076600011182911663108618654478576329491617865745279072505754721984406988800 : Int) coeff0568) := by
  rw [CoefficientMerge.eval_scale, ← atom0568_identity]
  exact mul_nonneg (by norm_num) (atom0568_nonneg g t z hg hA hB ht hz hw)

def coeff0569 : CoefficientMerge.Poly :=
  [(1048705, 1)]
noncomputable def atom0569 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 2 * (z) ^ 1)
theorem atom0569_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0569 g t z = CoefficientMerge.eval (monomial g t z) coeff0569 := by
  norm_num [atom0569, coeff0569, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0569_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0569 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0569]
  positivity
theorem weighted0569_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5080674701369869619885060026127917062961606154349012265375142676047936602614444642804881319747655668300728859596911298497738585075855157760 : Int) coeff0569) := by
  rw [CoefficientMerge.eval_scale, ← atom0569_identity]
  exact mul_nonneg (by norm_num) (atom0569_nonneg g t z hg hA hB ht hz hw)

def coeff0570 : CoefficientMerge.Poly :=
  [(1048897, 1)]
noncomputable def atom0570 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 4) ^ 1 * (z) ^ 1)
theorem atom0570_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0570 g t z = CoefficientMerge.eval (monomial g t z) coeff0570 := by
  norm_num [atom0570, coeff0570, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0570_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0570 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0570]
  positivity
theorem weighted0570_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (6985624249355430410794793966215792815210955733058298832275177478028134679478522007782941091809975246472301187764829314787725420893013061312 : Int) coeff0570) := by
  rw [CoefficientMerge.eval_scale, ← atom0570_identity]
  exact mul_nonneg (by norm_num) (atom0570_nonneg g t z hg hA hB ht hz hw)

def coeff0571 : CoefficientMerge.Poly :=
  [(1049665, 1)]
noncomputable def atom0571 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 5) ^ 1 * (z) ^ 1)
theorem atom0571_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0571 g t z = CoefficientMerge.eval (monomial g t z) coeff0571 := by
  norm_num [atom0571, coeff0571, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0571_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0571 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0571]
  positivity
theorem weighted0571_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2128214897886178584118761413206422417049663857918312194219623613427927000568859196940221374953673590561569977035137134823490065640958674944 : Int) coeff0571) := by
  rw [CoefficientMerge.eval_scale, ← atom0571_identity]
  exact mul_nonneg (by norm_num) (atom0571_nonneg g t z hg hA hB ht hz hw)

def coeff0572 : CoefficientMerge.Poly :=
  [(1052737, 1)]
noncomputable def atom0572 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 6) ^ 1 * (z) ^ 1)
theorem atom0572_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0572 g t z = CoefficientMerge.eval (monomial g t z) coeff0572 := by
  norm_num [atom0572, coeff0572, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0572_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0572 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0572]
  positivity
theorem weighted0572_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1883794301594911992149541652940804816404105327745794310011812559731823151427744766522687174771347170883655107739540628195854431433583001600 : Int) coeff0572) := by
  rw [CoefficientMerge.eval_scale, ← atom0572_identity]
  exact mul_nonneg (by norm_num) (atom0572_nonneg g t z hg hA hB ht hz hw)

def coeff0573 : CoefficientMerge.Poly :=
  [(1065025, 1)]
noncomputable def atom0573 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 7) ^ 1 * (z) ^ 1)
theorem atom0573_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0573 g t z = CoefficientMerge.eval (monomial g t z) coeff0573 := by
  norm_num [atom0573, coeff0573, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0573_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0573 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0573]
  positivity
theorem weighted0573_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (472071035661668367184822157469948824941799472547029191202528972891069330421925797942822159471391473210538480402585368257885266861329428480 : Int) coeff0573) := by
  rw [CoefficientMerge.eval_scale, ← atom0573_identity]
  exact mul_nonneg (by norm_num) (atom0573_nonneg g t z hg hA hB ht hz hw)

def coeff0574 : CoefficientMerge.Poly :=
  [(1114177, 1)]
noncomputable def atom0574 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 8) ^ 1 * (z) ^ 1)
theorem atom0574_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0574 g t z = CoefficientMerge.eval (monomial g t z) coeff0574 := by
  norm_num [atom0574, coeff0574, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0574_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0574 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0574]
  positivity
theorem weighted0574_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (767559709363086267056202025333241031225360802584736106484763042449059138061575437899823633502120790619263615515145505975711077283377868800 : Int) coeff0574) := by
  rw [CoefficientMerge.eval_scale, ← atom0574_identity]
  exact mul_nonneg (by norm_num) (atom0574_nonneg g t z hg hA hB ht hz hw)

def coeff0575 : CoefficientMerge.Poly :=
  [(1281, 1)]
noncomputable def atom0575 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 5) ^ 1)
theorem atom0575_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0575 g t z = CoefficientMerge.eval (monomial g t z) coeff0575 := by
  norm_num [atom0575, coeff0575, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0575_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0575 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0575]
  positivity
theorem weighted0575_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1560865278101077287943255949462547790671169306048121512100994672491322315322631549873246120831346801630064174540348999973506673765257405440 : Int) coeff0575) := by
  rw [CoefficientMerge.eval_scale, ← atom0575_identity]
  exact mul_nonneg (by norm_num) (atom0575_nonneg g t z hg hA hB ht hz hw)

def coeff0576 : CoefficientMerge.Poly :=
  [(4353, 1)]
noncomputable def atom0576 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1)
theorem atom0576_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0576 g t z = CoefficientMerge.eval (monomial g t z) coeff0576 := by
  norm_num [atom0576, coeff0576, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0576_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0576 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0576]
  positivity
theorem weighted0576_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2218518085662810448644070053168176920201382729111862531700615910753731458536676335844511756858878120751219854578149192871387535241798579200 : Int) coeff0576) := by
  rw [CoefficientMerge.eval_scale, ← atom0576_identity]
  exact mul_nonneg (by norm_num) (atom0576_nonneg g t z hg hA hB ht hz hw)

def coeff0577 : CoefficientMerge.Poly :=
  [(16641, 1)]
noncomputable def atom0577 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1)
theorem atom0577_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0577 g t z = CoefficientMerge.eval (monomial g t z) coeff0577 := by
  norm_num [atom0577, coeff0577, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0577_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0577 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0577]
  positivity
theorem weighted0577_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4635311144794107960555066033132239592115792067347469512079275899134573323161639995063629477674426693992762173028959825664911863380028134400 : Int) coeff0577) := by
  rw [CoefficientMerge.eval_scale, ← atom0577_identity]
  exact mul_nonneg (by norm_num) (atom0577_nonneg g t z hg hA hB ht hz hw)

def coeff0578 : CoefficientMerge.Poly :=
  [(65793, 1)]
noncomputable def atom0578 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1)
theorem atom0578_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0578 g t z = CoefficientMerge.eval (monomial g t z) coeff0578 := by
  norm_num [atom0578, coeff0578, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0578_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0578 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0578]
  positivity
theorem weighted0578_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (16074912214834274465868928531477777699294994045152003550711528380480207796679814755893627772476674292194301530651096137339038894104748160000 : Int) coeff0578) := by
  rw [CoefficientMerge.eval_scale, ← atom0578_identity]
  exact mul_nonneg (by norm_num) (atom0578_nonneg g t z hg hA hB ht hz hw)

def coeff0579 : CoefficientMerge.Poly :=
  [(263425, 1)]
noncomputable def atom0579 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 5) ^ 1 * (t) ^ 1)
theorem atom0579_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0579 g t z = CoefficientMerge.eval (monomial g t z) coeff0579 := by
  norm_num [atom0579, coeff0579, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0579_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0579 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0579]
  positivity
theorem weighted0579_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (774592224679108824723903910230170404271300356611269152332797643349905009532736129694185915252111658777255494873407615179732768057901079040 : Int) coeff0579) := by
  rw [CoefficientMerge.eval_scale, ← atom0579_identity]
  exact mul_nonneg (by norm_num) (atom0579_nonneg g t z hg hA hB ht hz hw)

def coeff0580 : CoefficientMerge.Poly :=
  [(266497, 1)]
noncomputable def atom0580 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (t) ^ 1)
theorem atom0580_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0580 g t z = CoefficientMerge.eval (monomial g t z) coeff0580 := by
  norm_num [atom0580, coeff0580, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0580_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0580 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0580]
  positivity
theorem weighted0580_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (303402950671199209476064737460473225755293802395867049436696742116501125587028302250647575548024110463737543780692366095871834720535626240 : Int) coeff0580) := by
  rw [CoefficientMerge.eval_scale, ← atom0580_identity]
  exact mul_nonneg (by norm_num) (atom0580_nonneg g t z hg hA hB ht hz hw)

def coeff0581 : CoefficientMerge.Poly :=
  [(278785, 1)]
noncomputable def atom0581 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (t) ^ 1)
theorem atom0581_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0581 g t z = CoefficientMerge.eval (monomial g t z) coeff0581 := by
  norm_num [atom0581, coeff0581, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0581_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0581 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0581]
  positivity
theorem weighted0581_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1058854994125577560062220998223442447726158684308658658365512832294963911848195211672550202441926966351917006237898693213555556175538414080 : Int) coeff0581) := by
  rw [CoefficientMerge.eval_scale, ← atom0581_identity]
  exact mul_nonneg (by norm_num) (atom0581_nonneg g t z hg hA hB ht hz hw)

def coeff0582 : CoefficientMerge.Poly :=
  [(327937, 1)]
noncomputable def atom0582 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (t) ^ 1)
theorem atom0582_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0582 g t z = CoefficientMerge.eval (monomial g t z) coeff0582 := by
  norm_num [atom0582, coeff0582, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0582_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0582 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0582]
  positivity
theorem weighted0582_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2009023071262035353012353455745775751554198275337027689819170613416299937717672508964582246316237936351042299429107676623246895809944076800 : Int) coeff0582) := by
  rw [CoefficientMerge.eval_scale, ← atom0582_identity]
  exact mul_nonneg (by norm_num) (atom0582_nonneg g t z hg hA hB ht hz hw)

def coeff0583 : CoefficientMerge.Poly :=
  [(1049089, 1)]
noncomputable def atom0583 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 2 * (z) ^ 1)
theorem atom0583_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0583 g t z = CoefficientMerge.eval (monomial g t z) coeff0583 := by
  norm_num [atom0583, coeff0583, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0583_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0583 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0583]
  positivity
theorem weighted0583_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4323921170452650331701013495958535434636818438167172077636760178436382793142559547559356825922367455271502090855548795779710118321336468864 : Int) coeff0583) := by
  rw [CoefficientMerge.eval_scale, ← atom0583_identity]
  exact mul_nonneg (by norm_num) (atom0583_nonneg g t z hg hA hB ht hz hw)

def coeff0584 : CoefficientMerge.Poly :=
  [(1049857, 1)]
noncomputable def atom0584 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 5) ^ 1 * (z) ^ 1)
theorem atom0584_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0584 g t z = CoefficientMerge.eval (monomial g t z) coeff0584 := by
  norm_num [atom0584, coeff0584, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0584_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0584 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0584]
  positivity
theorem weighted0584_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4970730080679324124437509856427961054018014289330432775634464873550346699308274827749578686789099648194600465984013743687524739095966762208 : Int) coeff0584) := by
  rw [CoefficientMerge.eval_scale, ← atom0584_identity]
  exact mul_nonneg (by norm_num) (atom0584_nonneg g t z hg hA hB ht hz hw)

def sparseBlock060 : CoefficientMerge.Poly :=
  [(1281, 1560865278101077287943255949462547790671169306048121512100994672491322315322631549873246120831346801630064174540348999973506673765257405440), (4353, 2218518085662810448644070053168176920201382729111862531700615910753731458536676335844511756858878120751219854578149192871387535241798579200), (16641, 4635311144794107960555066033132239592115792067347469512079275899134573323161639995063629477674426693992762173028959825664911863380028134400), (65793, 16074912214834274465868928531477777699294994045152003550711528380480207796679814755893627772476674292194301530651096137339038894104748160000), (263233, 1196588720727980410746003737432391733289909211227733898234723031091190942501089166927494436596994879947174282853835777315570695006908733440), (263425, 774592224679108824723903910230170404271300356611269152332797643349905009532736129694185915252111658777255494873407615179732768057901079040), (266305, 117149616328893520775043278857262176605407399538773584699474919626290147036099800492939902728960185922581033670413448604769524534682449920), (266497, 303402950671199209476064737460473225755293802395867049436696742116501125587028302250647575548024110463737543780692366095871834720535626240), (278593, 148920317793190381977391263008993557734110414782984740573473347543083088517839366018212491179560695383414671702910747516161347063533578240), (278785, 1058854994125577560062220998223442447726158684308658658365512832294963911848195211672550202441926966351917006237898693213555556175538414080), (327745, 678000501879380171830554545575835445614302676158631031711817453076600011182911663108618654478576329491617865745279072505754721984406988800), (327937, 2009023071262035353012353455745775751554198275337027689819170613416299937717672508964582246316237936351042299429107676623246895809944076800), (1048705, 5080674701369869619885060026127917062961606154349012265375142676047936602614444642804881319747655668300728859596911298497738585075855157760), (1048897, 6985624249355430410794793966215792815210955733058298832275177478028134679478522007782941091809975246472301187764829314787725420893013061312), (1049089, 4323921170452650331701013495958535434636818438167172077636760178436382793142559547559356825922367455271502090855548795779710118321336468864), (1049665, 2128214897886178584118761413206422417049663857918312194219623613427927000568859196940221374953673590561569977035137134823490065640958674944), (1049857, 4970730080679324124437509856427961054018014289330432775634464873550346699308274827749578686789099648194600465984013743687524739095966762208), (1052737, 1883794301594911992149541652940804816404105327745794310011812559731823151427744766522687174771347170883655107739540628195854431433583001600), (1065025, 472071035661668367184822157469948824941799472547029191202528972891069330421925797942822159471391473210538480402585368257885266861329428480), (1114177, 767559709363086267056202025333241031225360802584736106484763042449059138061575437899823633502120790619263615515145505975711077283377868800)]
theorem sparseBlock060_data : sparseBlock060 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1196588720727980410746003737432391733289909211227733898234723031091190942501089166927494436596994879947174282853835777315570695006908733440 : Int) coeff0565) (CoefficientMerge.scale (117149616328893520775043278857262176605407399538773584699474919626290147036099800492939902728960185922581033670413448604769524534682449920 : Int) coeff0566)) (CoefficientMerge.merge (CoefficientMerge.scale (148920317793190381977391263008993557734110414782984740573473347543083088517839366018212491179560695383414671702910747516161347063533578240 : Int) coeff0567) (CoefficientMerge.merge (CoefficientMerge.scale (678000501879380171830554545575835445614302676158631031711817453076600011182911663108618654478576329491617865745279072505754721984406988800 : Int) coeff0568) (CoefficientMerge.scale (5080674701369869619885060026127917062961606154349012265375142676047936602614444642804881319747655668300728859596911298497738585075855157760 : Int) coeff0569)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (6985624249355430410794793966215792815210955733058298832275177478028134679478522007782941091809975246472301187764829314787725420893013061312 : Int) coeff0570) (CoefficientMerge.scale (2128214897886178584118761413206422417049663857918312194219623613427927000568859196940221374953673590561569977035137134823490065640958674944 : Int) coeff0571)) (CoefficientMerge.merge (CoefficientMerge.scale (1883794301594911992149541652940804816404105327745794310011812559731823151427744766522687174771347170883655107739540628195854431433583001600 : Int) coeff0572) (CoefficientMerge.merge (CoefficientMerge.scale (472071035661668367184822157469948824941799472547029191202528972891069330421925797942822159471391473210538480402585368257885266861329428480 : Int) coeff0573) (CoefficientMerge.scale (767559709363086267056202025333241031225360802584736106484763042449059138061575437899823633502120790619263615515145505975711077283377868800 : Int) coeff0574))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1560865278101077287943255949462547790671169306048121512100994672491322315322631549873246120831346801630064174540348999973506673765257405440 : Int) coeff0575) (CoefficientMerge.scale (2218518085662810448644070053168176920201382729111862531700615910753731458536676335844511756858878120751219854578149192871387535241798579200 : Int) coeff0576)) (CoefficientMerge.merge (CoefficientMerge.scale (4635311144794107960555066033132239592115792067347469512079275899134573323161639995063629477674426693992762173028959825664911863380028134400 : Int) coeff0577) (CoefficientMerge.merge (CoefficientMerge.scale (16074912214834274465868928531477777699294994045152003550711528380480207796679814755893627772476674292194301530651096137339038894104748160000 : Int) coeff0578) (CoefficientMerge.scale (774592224679108824723903910230170404271300356611269152332797643349905009532736129694185915252111658777255494873407615179732768057901079040 : Int) coeff0579)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (303402950671199209476064737460473225755293802395867049436696742116501125587028302250647575548024110463737543780692366095871834720535626240 : Int) coeff0580) (CoefficientMerge.scale (1058854994125577560062220998223442447726158684308658658365512832294963911848195211672550202441926966351917006237898693213555556175538414080 : Int) coeff0581)) (CoefficientMerge.merge (CoefficientMerge.scale (2009023071262035353012353455745775751554198275337027689819170613416299937717672508964582246316237936351042299429107676623246895809944076800 : Int) coeff0582) (CoefficientMerge.merge (CoefficientMerge.scale (4323921170452650331701013495958535434636818438167172077636760178436382793142559547559356825922367455271502090855548795779710118321336468864 : Int) coeff0583) (CoefficientMerge.scale (4970730080679324124437509856427961054018014289330432775634464873550346699308274827749578686789099648194600465984013743687524739095966762208 : Int) coeff0584)))))) := by decide +kernel
theorem sparseBlock060_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock060 := by
  rw [sparseBlock060_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted0565_nonneg g t z hg hA hB ht hz hw) (weighted0566_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0567_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0568_nonneg g t z hg hA hB ht hz hw) (weighted0569_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0570_nonneg g t z hg hA hB ht hz hw) (weighted0571_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0572_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0573_nonneg g t z hg hA hB ht hz hw) (weighted0574_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted0575_nonneg g t z hg hA hB ht hz hw) (weighted0576_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0577_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0578_nonneg g t z hg hA hB ht hz hw) (weighted0579_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0580_nonneg g t z hg hA hB ht hz hw) (weighted0581_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0582_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0583_nonneg g t z hg hA hB ht hz hw) (weighted0584_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
