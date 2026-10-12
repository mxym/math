import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff1585 : CoefficientMerge.Poly :=
  [(3150849, 1)]
noncomputable def atom1585 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (z) ^ 3)
theorem atom1585_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1585 g t z = CoefficientMerge.eval (monomial g t z) coeff1585 := by
  norm_num [atom1585, coeff1585, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1585_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1585 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1585]
  positivity
theorem weighted1585_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (11694976302943476921050338000361711812793694529776081806115073033153027221697175403759195506213892368390111273129881206581686926405216000 : Int) coeff1585) := by
  rw [CoefficientMerge.eval_scale, ← atom1585_identity]
  exact mul_nonneg (by norm_num) (atom1585_nonneg g t z hg hA hB ht hz hw)

def coeff1586 : CoefficientMerge.Poly :=
  [(3212289, 1)]
noncomputable def atom1586 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (z) ^ 3)
theorem atom1586_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1586 g t z = CoefficientMerge.eval (monomial g t z) coeff1586 := by
  norm_num [atom1586, coeff1586, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1586_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1586 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1586]
  positivity
theorem weighted1586_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5120640452920602728164532539291274884239369533225034009060799429823878019081095483133789263183267263690337314454473686159905914022147080 : Int) coeff1586) := by
  rw [CoefficientMerge.eval_scale, ← atom1586_identity]
  exact mul_nonneg (by norm_num) (atom1586_nonneg g t z hg hA hB ht hz hw)

def coeff1587 : CoefficientMerge.Poly :=
  [(3153921, 1)]
noncomputable def atom1587 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 6) ^ 2 * (z) ^ 3)
theorem atom1587_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1587 g t z = CoefficientMerge.eval (monomial g t z) coeff1587 := by
  norm_num [atom1587, coeff1587, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1587_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1587 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1587]
  positivity
theorem weighted1587_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (10856464357785204872724904851505006823393544668068889780789149827308377394606357610317746052223616009680495274102572991976712829769433600 : Int) coeff1587) := by
  rw [CoefficientMerge.eval_scale, ← atom1587_identity]
  exact mul_nonneg (by norm_num) (atom1587_nonneg g t z hg hA hB ht hz hw)

def coeff1588 : CoefficientMerge.Poly :=
  [(3166209, 1)]
noncomputable def atom1588 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (z) ^ 3)
theorem atom1588_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1588 g t z = CoefficientMerge.eval (monomial g t z) coeff1588 := by
  norm_num [atom1588, coeff1588, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1588_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1588 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1588]
  positivity
theorem weighted1588_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (12711982956068836043838518659251334297611183397149246315742434473295029235214854464852881920071828975885415447218368278762799608149080000 : Int) coeff1588) := by
  rw [CoefficientMerge.eval_scale, ← atom1588_identity]
  exact mul_nonneg (by norm_num) (atom1588_nonneg g t z hg hA hB ht hz hw)

def coeff1589 : CoefficientMerge.Poly :=
  [(3215361, 1)]
noncomputable def atom1589 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (z) ^ 3)
theorem atom1589_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1589 g t z = CoefficientMerge.eval (monomial g t z) coeff1589 := by
  norm_num [atom1589, coeff1589, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1589_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1589 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1589]
  positivity
theorem weighted1589_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (18874689987035263801167199764776794787440292087153258427171162350773415520879141370037966511025852572677291651563239226547877670796486400 : Int) coeff1589) := by
  rw [CoefficientMerge.eval_scale, ← atom1589_identity]
  exact mul_nonneg (by norm_num) (atom1589_nonneg g t z hg hA hB ht hz hw)

def coeff1590 : CoefficientMerge.Poly :=
  [(3146760, 1)]
noncomputable def atom1590 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 2 * (g 5) ^ 1 * (z) ^ 3)
theorem atom1590_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1590 g t z = CoefficientMerge.eval (monomial g t z) coeff1590 := by
  norm_num [atom1590, coeff1590, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1590_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1590 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1590]
  positivity
theorem weighted1590_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (436892065806819691399234924204130885214410228234233605696032553071381297198165845487293831842240237743665702239488684674135042587033600 : Int) coeff1590) := by
  rw [CoefficientMerge.eval_scale, ← atom1590_identity]
  exact mul_nonneg (by norm_num) (atom1590_nonneg g t z hg hA hB ht hz hw)

def coeff1591 : CoefficientMerge.Poly :=
  [(3145812, 1)]
noncomputable def atom1591 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 3) ^ 1 * (z) ^ 3)
theorem atom1591_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1591 g t z = CoefficientMerge.eval (monomial g t z) coeff1591 := by
  norm_num [atom1591, coeff1591, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1591_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1591 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1591]
  positivity
theorem weighted1591_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (57474487973296337994962849379630468630452277079840966886618532152700614462458993422070906094131815556215235526225801775593949275992867584 : Int) coeff1591) := by
  rw [CoefficientMerge.eval_scale, ← atom1591_identity]
  exact mul_nonneg (by norm_num) (atom1591_nonneg g t z hg hA hB ht hz hw)

def coeff1592 : CoefficientMerge.Poly :=
  [(3146004, 1)]
noncomputable def atom1592 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 4) ^ 1 * (z) ^ 3)
theorem atom1592_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1592 g t z = CoefficientMerge.eval (monomial g t z) coeff1592 := by
  norm_num [atom1592, coeff1592, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1592_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1592 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1592]
  positivity
theorem weighted1592_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (54862140372443657974306966349421262900650724225342645531609911160915499209469147938130930669556063402380870780212007428066588799103926496 : Int) coeff1592) := by
  rw [CoefficientMerge.eval_scale, ← atom1592_identity]
  exact mul_nonneg (by norm_num) (atom1592_nonneg g t z hg hA hB ht hz hw)

def coeff1593 : CoefficientMerge.Poly :=
  [(3146772, 1)]
noncomputable def atom1593 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 5) ^ 1 * (z) ^ 3)
theorem atom1593_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1593 g t z = CoefficientMerge.eval (monomial g t z) coeff1593 := by
  norm_num [atom1593, coeff1593, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1593_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1593 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1593]
  positivity
theorem weighted1593_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (26528404430340204525058069674505718775838497770129398760596764777272411480768678168654749223262096942676823868471543009933148145186529600 : Int) coeff1593) := by
  rw [CoefficientMerge.eval_scale, ← atom1593_identity]
  exact mul_nonneg (by norm_num) (atom1593_nonneg g t z hg hA hB ht hz hw)

def coeff1594 : CoefficientMerge.Poly :=
  [(3149844, 1)]
noncomputable def atom1594 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 6) ^ 1 * (z) ^ 3)
theorem atom1594_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1594 g t z = CoefficientMerge.eval (monomial g t z) coeff1594 := by
  norm_num [atom1594, coeff1594, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1594_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1594 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1594]
  positivity
theorem weighted1594_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (34982601852375435960781527646880217430884921894214975548957152568695245914946150459510809805181033686595051034571598096040968059915952640 : Int) coeff1594) := by
  rw [CoefficientMerge.eval_scale, ← atom1594_identity]
  exact mul_nonneg (by norm_num) (atom1594_nonneg g t z hg hA hB ht hz hw)

def coeff1595 : CoefficientMerge.Poly :=
  [(3162132, 1)]
noncomputable def atom1595 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 7) ^ 1 * (z) ^ 3)
theorem atom1595_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1595 g t z = CoefficientMerge.eval (monomial g t z) coeff1595 := by
  norm_num [atom1595, coeff1595, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1595_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1595 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1595]
  positivity
theorem weighted1595_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (33596290007505705678015730750520366033205387450744855714787418233883235540189228274722273982394651069165476037708525848386429604261031680 : Int) coeff1595) := by
  rw [CoefficientMerge.eval_scale, ← atom1595_identity]
  exact mul_nonneg (by norm_num) (atom1595_nonneg g t z hg hA hB ht hz hw)

def coeff1596 : CoefficientMerge.Poly :=
  [(3211284, 1)]
noncomputable def atom1596 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 8) ^ 1 * (z) ^ 3)
theorem atom1596_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1596 g t z = CoefficientMerge.eval (monomial g t z) coeff1596 := by
  norm_num [atom1596, coeff1596, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1596_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1596 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1596]
  positivity
theorem weighted1596_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (11526486492886198298388820843816212848308339067124655555366171576797693492616181906236772929210283489205665499803208248903809015388574720 : Int) coeff1596) := by
  rw [CoefficientMerge.eval_scale, ← atom1596_identity]
  exact mul_nonneg (by norm_num) (atom1596_nonneg g t z hg hA hB ht hz hw)

def coeff1597 : CoefficientMerge.Poly :=
  [(3145860, 1)]
noncomputable def atom1597 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 2 * (z) ^ 3)
theorem atom1597_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1597 g t z = CoefficientMerge.eval (monomial g t z) coeff1597 := by
  norm_num [atom1597, coeff1597, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1597_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1597 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1597]
  positivity
theorem weighted1597_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (44477188846217163227965403400548050926775213359713100730087462534471166633338843026042419291240933679913628495631270302102244600338004864 : Int) coeff1597) := by
  rw [CoefficientMerge.eval_scale, ← atom1597_identity]
  exact mul_nonneg (by norm_num) (atom1597_nonneg g t z hg hA hB ht hz hw)

def coeff1598 : CoefficientMerge.Poly :=
  [(3146052, 1)]
noncomputable def atom1598 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 4) ^ 1 * (z) ^ 3)
theorem atom1598_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1598 g t z = CoefficientMerge.eval (monomial g t z) coeff1598 := by
  norm_num [atom1598, coeff1598, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1598_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1598 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1598]
  positivity
theorem weighted1598_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (48627276849397223502380223174331757218706754807421477707426862875017588174842572484229754660321528858969469514762812523399922178742274048 : Int) coeff1598) := by
  rw [CoefficientMerge.eval_scale, ← atom1598_identity]
  exact mul_nonneg (by norm_num) (atom1598_nonneg g t z hg hA hB ht hz hw)

def coeff1599 : CoefficientMerge.Poly :=
  [(3146820, 1)]
noncomputable def atom1599 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 5) ^ 1 * (z) ^ 3)
theorem atom1599_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1599 g t z = CoefficientMerge.eval (monomial g t z) coeff1599 := by
  norm_num [atom1599, coeff1599, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1599_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1599 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1599]
  positivity
theorem weighted1599_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (9406581566117442188963393098422994772614680339025476980555032873500470097086442126819397986515533905248332381592503839587896169484430656 : Int) coeff1599) := by
  rw [CoefficientMerge.eval_scale, ← atom1599_identity]
  exact mul_nonneg (by norm_num) (atom1599_nonneg g t z hg hA hB ht hz hw)

def coeff1600 : CoefficientMerge.Poly :=
  [(3149892, 1)]
noncomputable def atom1600 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 6) ^ 1 * (z) ^ 3)
theorem atom1600_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1600 g t z = CoefficientMerge.eval (monomial g t z) coeff1600 := by
  norm_num [atom1600, coeff1600, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1600_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1600 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1600]
  positivity
theorem weighted1600_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (10961799972652299288544306606541646365004265239901929431539360652264498441027242964383887791412812655644041569991557096072165005729432640 : Int) coeff1600) := by
  rw [CoefficientMerge.eval_scale, ← atom1600_identity]
  exact mul_nonneg (by norm_num) (atom1600_nonneg g t z hg hA hB ht hz hw)

def coeff1601 : CoefficientMerge.Poly :=
  [(3162180, 1)]
noncomputable def atom1601 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 7) ^ 1 * (z) ^ 3)
theorem atom1601_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1601 g t z = CoefficientMerge.eval (monomial g t z) coeff1601 := by
  norm_num [atom1601, coeff1601, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1601_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1601 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1601]
  positivity
theorem weighted1601_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (17657852840340496172688566524042887408234752808949991247468941510552170929085830561728252230894701346146953501558412083744355465208499520 : Int) coeff1601) := by
  rw [CoefficientMerge.eval_scale, ← atom1601_identity]
  exact mul_nonneg (by norm_num) (atom1601_nonneg g t z hg hA hB ht hz hw)

def coeff1602 : CoefficientMerge.Poly :=
  [(3211332, 1)]
noncomputable def atom1602 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 8) ^ 1 * (z) ^ 3)
theorem atom1602_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1602 g t z = CoefficientMerge.eval (monomial g t z) coeff1602 := by
  norm_num [atom1602, coeff1602, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1602_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1602 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1602]
  positivity
theorem weighted1602_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (36068473439833583135274839845839783745303903980530063513933133696344478049114913167114008456570582284863512434218997964647741764493762880 : Int) coeff1602) := by
  rw [CoefficientMerge.eval_scale, ← atom1602_identity]
  exact mul_nonneg (by norm_num) (atom1602_nonneg g t z hg hA hB ht hz hw)

def coeff1603 : CoefficientMerge.Poly :=
  [(3146244, 1)]
noncomputable def atom1603 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 2 * (z) ^ 3)
theorem atom1603_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1603 g t z = CoefficientMerge.eval (monomial g t z) coeff1603 := by
  norm_num [atom1603, coeff1603, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1603_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1603 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1603]
  positivity
theorem weighted1603_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (33333162094924361549753942459284489807540382306026377101924316586216640231753459691187822169075499964942314546954802561036162459088739840 : Int) coeff1603) := by
  rw [CoefficientMerge.eval_scale, ← atom1603_identity]
  exact mul_nonneg (by norm_num) (atom1603_nonneg g t z hg hA hB ht hz hw)

def coeff1604 : CoefficientMerge.Poly :=
  [(3147012, 1)]
noncomputable def atom1604 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 5) ^ 1 * (z) ^ 3)
theorem atom1604_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1604 g t z = CoefficientMerge.eval (monomial g t z) coeff1604 := by
  norm_num [atom1604, coeff1604, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1604_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1604 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1604]
  positivity
theorem weighted1604_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (22047653984052548143203446447700376797474266101250844355839160289930902367357462459178014913010911288686814652842937274869345428737421312 : Int) coeff1604) := by
  rw [CoefficientMerge.eval_scale, ← atom1604_identity]
  exact mul_nonneg (by norm_num) (atom1604_nonneg g t z hg hA hB ht hz hw)

def sparseBlock111 : CoefficientMerge.Poly :=
  [(3145812, 57474487973296337994962849379630468630452277079840966886618532152700614462458993422070906094131815556215235526225801775593949275992867584), (3145860, 44477188846217163227965403400548050926775213359713100730087462534471166633338843026042419291240933679913628495631270302102244600338004864), (3146004, 54862140372443657974306966349421262900650724225342645531609911160915499209469147938130930669556063402380870780212007428066588799103926496), (3146052, 48627276849397223502380223174331757218706754807421477707426862875017588174842572484229754660321528858969469514762812523399922178742274048), (3146244, 33333162094924361549753942459284489807540382306026377101924316586216640231753459691187822169075499964942314546954802561036162459088739840), (3146760, 436892065806819691399234924204130885214410228234233605696032553071381297198165845487293831842240237743665702239488684674135042587033600), (3146772, 26528404430340204525058069674505718775838497770129398760596764777272411480768678168654749223262096942676823868471543009933148145186529600), (3146820, 9406581566117442188963393098422994772614680339025476980555032873500470097086442126819397986515533905248332381592503839587896169484430656), (3147012, 22047653984052548143203446447700376797474266101250844355839160289930902367357462459178014913010911288686814652842937274869345428737421312), (3149844, 34982601852375435960781527646880217430884921894214975548957152568695245914946150459510809805181033686595051034571598096040968059915952640), (3149892, 10961799972652299288544306606541646365004265239901929431539360652264498441027242964383887791412812655644041569991557096072165005729432640), (3150849, 11694976302943476921050338000361711812793694529776081806115073033153027221697175403759195506213892368390111273129881206581686926405216000), (3153921, 10856464357785204872724904851505006823393544668068889780789149827308377394606357610317746052223616009680495274102572991976712829769433600), (3162132, 33596290007505705678015730750520366033205387450744855714787418233883235540189228274722273982394651069165476037708525848386429604261031680), (3162180, 17657852840340496172688566524042887408234752808949991247468941510552170929085830561728252230894701346146953501558412083744355465208499520), (3166209, 12711982956068836043838518659251334297611183397149246315742434473295029235214854464852881920071828975885415447218368278762799608149080000), (3211284, 11526486492886198298388820843816212848308339067124655555366171576797693492616181906236772929210283489205665499803208248903809015388574720), (3211332, 36068473439833583135274839845839783745303903980530063513933133696344478049114913167114008456570582284863512434218997964647741764493762880), (3212289, 5120640452920602728164532539291274884239369533225034009060799429823878019081095483133789263183267263690337314454473686159905914022147080), (3215361, 18874689987035263801167199764776794787440292087153258427171162350773415520879141370037966511025852572677291651563239226547877670796486400)]
theorem sparseBlock111_data : sparseBlock111 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (11694976302943476921050338000361711812793694529776081806115073033153027221697175403759195506213892368390111273129881206581686926405216000 : Int) coeff1585) (CoefficientMerge.scale (5120640452920602728164532539291274884239369533225034009060799429823878019081095483133789263183267263690337314454473686159905914022147080 : Int) coeff1586)) (CoefficientMerge.merge (CoefficientMerge.scale (10856464357785204872724904851505006823393544668068889780789149827308377394606357610317746052223616009680495274102572991976712829769433600 : Int) coeff1587) (CoefficientMerge.merge (CoefficientMerge.scale (12711982956068836043838518659251334297611183397149246315742434473295029235214854464852881920071828975885415447218368278762799608149080000 : Int) coeff1588) (CoefficientMerge.scale (18874689987035263801167199764776794787440292087153258427171162350773415520879141370037966511025852572677291651563239226547877670796486400 : Int) coeff1589)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (436892065806819691399234924204130885214410228234233605696032553071381297198165845487293831842240237743665702239488684674135042587033600 : Int) coeff1590) (CoefficientMerge.scale (57474487973296337994962849379630468630452277079840966886618532152700614462458993422070906094131815556215235526225801775593949275992867584 : Int) coeff1591)) (CoefficientMerge.merge (CoefficientMerge.scale (54862140372443657974306966349421262900650724225342645531609911160915499209469147938130930669556063402380870780212007428066588799103926496 : Int) coeff1592) (CoefficientMerge.merge (CoefficientMerge.scale (26528404430340204525058069674505718775838497770129398760596764777272411480768678168654749223262096942676823868471543009933148145186529600 : Int) coeff1593) (CoefficientMerge.scale (34982601852375435960781527646880217430884921894214975548957152568695245914946150459510809805181033686595051034571598096040968059915952640 : Int) coeff1594))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (33596290007505705678015730750520366033205387450744855714787418233883235540189228274722273982394651069165476037708525848386429604261031680 : Int) coeff1595) (CoefficientMerge.scale (11526486492886198298388820843816212848308339067124655555366171576797693492616181906236772929210283489205665499803208248903809015388574720 : Int) coeff1596)) (CoefficientMerge.merge (CoefficientMerge.scale (44477188846217163227965403400548050926775213359713100730087462534471166633338843026042419291240933679913628495631270302102244600338004864 : Int) coeff1597) (CoefficientMerge.merge (CoefficientMerge.scale (48627276849397223502380223174331757218706754807421477707426862875017588174842572484229754660321528858969469514762812523399922178742274048 : Int) coeff1598) (CoefficientMerge.scale (9406581566117442188963393098422994772614680339025476980555032873500470097086442126819397986515533905248332381592503839587896169484430656 : Int) coeff1599)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (10961799972652299288544306606541646365004265239901929431539360652264498441027242964383887791412812655644041569991557096072165005729432640 : Int) coeff1600) (CoefficientMerge.scale (17657852840340496172688566524042887408234752808949991247468941510552170929085830561728252230894701346146953501558412083744355465208499520 : Int) coeff1601)) (CoefficientMerge.merge (CoefficientMerge.scale (36068473439833583135274839845839783745303903980530063513933133696344478049114913167114008456570582284863512434218997964647741764493762880 : Int) coeff1602) (CoefficientMerge.merge (CoefficientMerge.scale (33333162094924361549753942459284489807540382306026377101924316586216640231753459691187822169075499964942314546954802561036162459088739840 : Int) coeff1603) (CoefficientMerge.scale (22047653984052548143203446447700376797474266101250844355839160289930902367357462459178014913010911288686814652842937274869345428737421312 : Int) coeff1604)))))) := by decide +kernel
theorem sparseBlock111_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock111 := by
  rw [sparseBlock111_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted1585_nonneg g t z hg hA hB ht hz hw) (weighted1586_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1587_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1588_nonneg g t z hg hA hB ht hz hw) (weighted1589_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1590_nonneg g t z hg hA hB ht hz hw) (weighted1591_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1592_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1593_nonneg g t z hg hA hB ht hz hw) (weighted1594_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted1595_nonneg g t z hg hA hB ht hz hw) (weighted1596_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1597_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1598_nonneg g t z hg hA hB ht hz hw) (weighted1599_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1600_nonneg g t z hg hA hB ht hz hw) (weighted1601_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1602_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1603_nonneg g t z hg hA hB ht hz hw) (weighted1604_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
