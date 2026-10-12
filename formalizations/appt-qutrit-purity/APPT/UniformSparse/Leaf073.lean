import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff0825 : CoefficientMerge.Poly :=
  [(65616, 1)]
noncomputable def atom0825 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 8) ^ 1)
theorem atom0825_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0825 g t z = CoefficientMerge.eval (monomial g t z) coeff0825 := by
  norm_num [atom0825, coeff0825, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0825_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0825 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0825]
  positivity
theorem weighted0825_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2978465330465111071646686216630453143946752335047517542029044169050592990405460176147589214371777957090598958133296519808937841382953369600 : Int) coeff0825) := by
  rw [CoefficientMerge.eval_scale, ← atom0825_identity]
  exact mul_nonneg (by norm_num) (atom0825_nonneg g t z hg hA hB ht hz hw)

def coeff0826 : CoefficientMerge.Poly :=
  [(266320, 1)]
noncomputable def atom0826 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 6) ^ 1 * (t) ^ 1)
theorem atom0826_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0826 g t z = CoefficientMerge.eval (monomial g t z) coeff0826 := by
  norm_num [atom0826, coeff0826, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0826_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0826 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0826]
  positivity
theorem weighted0826_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1509387038507717668226518510844013193983339035451174159195060118987234851467043393812029155004783697026869124638112515496450543696114790400 : Int) coeff0826) := by
  rw [CoefficientMerge.eval_scale, ← atom0826_identity]
  exact mul_nonneg (by norm_num) (atom0826_nonneg g t z hg hA hB ht hz hw)

def coeff0827 : CoefficientMerge.Poly :=
  [(278608, 1)]
noncomputable def atom0827 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 7) ^ 1 * (t) ^ 1)
theorem atom0827_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0827 g t z = CoefficientMerge.eval (monomial g t z) coeff0827 := by
  norm_num [atom0827, coeff0827, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0827_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0827 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0827]
  positivity
theorem weighted0827_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1473386806706529090011284064196828464713294610786878563616769026990442253697012182524126896145168980137853555628976096008682570247806566400 : Int) coeff0827) := by
  rw [CoefficientMerge.eval_scale, ← atom0827_identity]
  exact mul_nonneg (by norm_num) (atom0827_nonneg g t z hg hA hB ht hz hw)

def coeff0828 : CoefficientMerge.Poly :=
  [(1048912, 1)]
noncomputable def atom0828 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 4) ^ 1 * (z) ^ 1)
theorem atom0828_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0828 g t z = CoefficientMerge.eval (monomial g t z) coeff0828 := by
  norm_num [atom0828, coeff0828, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0828_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0828 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0828]
  positivity
theorem weighted0828_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (6227622118773046978153260161480348749547274942508628801736564576045926477378744960479615039983814662833467516483565700179312135515829765760 : Int) coeff0828) := by
  rw [CoefficientMerge.eval_scale, ← atom0828_identity]
  exact mul_nonneg (by norm_num) (atom0828_nonneg g t z hg hA hB ht hz hw)

def coeff0829 : CoefficientMerge.Poly :=
  [(1049680, 1)]
noncomputable def atom0829 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 5) ^ 1 * (z) ^ 1)
theorem atom0829_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0829 g t z = CoefficientMerge.eval (monomial g t z) coeff0829 := by
  norm_num [atom0829, coeff0829, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0829_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0829 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0829]
  positivity
theorem weighted0829_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5901785990407208015958035187157155536656940608909450571437046370533257961167447864543912412915340003400575790351487830935410025578027635200 : Int) coeff0829) := by
  rw [CoefficientMerge.eval_scale, ← atom0829_identity]
  exact mul_nonneg (by norm_num) (atom0829_nonneg g t z hg hA hB ht hz hw)

def coeff0830 : CoefficientMerge.Poly :=
  [(1052752, 1)]
noncomputable def atom0830 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 6) ^ 1 * (z) ^ 1)
theorem atom0830_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0830 g t z = CoefficientMerge.eval (monomial g t z) coeff0830 := by
  norm_num [atom0830, coeff0830, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0830_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0830 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0830]
  positivity
theorem weighted0830_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (7671853613154813588152537362702540674680790768591443002813503261900652606555913588525969250124899814248365466159189645372447654165655315200 : Int) coeff0830) := by
  rw [CoefficientMerge.eval_scale, ← atom0830_identity]
  exact mul_nonneg (by norm_num) (atom0830_nonneg g t z hg hA hB ht hz hw)

def coeff0831 : CoefficientMerge.Poly :=
  [(1065040, 1)]
noncomputable def atom0831 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 7) ^ 1 * (z) ^ 1)
theorem atom0831_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0831 g t z = CoefficientMerge.eval (monomial g t z) coeff0831 := by
  norm_num [atom0831, coeff0831, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0831_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0831 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0831]
  positivity
theorem weighted0831_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (11716384220059408473508759074595952904108641093096766336604152832074808715548953858877934163819874525475514030282699893660033049348968851200 : Int) coeff0831) := by
  rw [CoefficientMerge.eval_scale, ← atom0831_identity]
  exact mul_nonneg (by norm_num) (atom0831_nonneg g t z hg hA hB ht hz hw)

def coeff0832 : CoefficientMerge.Poly :=
  [(1114192, 1)]
noncomputable def atom0832 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 8) ^ 1 * (z) ^ 1)
theorem atom0832_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0832 g t z = CoefficientMerge.eval (monomial g t z) coeff0832 := by
  norm_num [atom0832, coeff0832, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0832_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0832 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0832]
  positivity
theorem weighted0832_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (15850368928878342618648110225697348024864350166145526247791555608461266980641534011208660991234335676260830971740759988922219358410723884800 : Int) coeff0832) := by
  rw [CoefficientMerge.eval_scale, ← atom0832_identity]
  exact mul_nonneg (by norm_num) (atom0832_nonneg g t z hg hA hB ht hz hw)

def coeff0833 : CoefficientMerge.Poly :=
  [(4368, 1)]
noncomputable def atom0833 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1)
theorem atom0833_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0833 g t z = CoefficientMerge.eval (monomial g t z) coeff0833 := by
  norm_num [atom0833, coeff0833, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0833_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0833 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0833]
  positivity
theorem weighted0833_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1189438952564238681868397922150922001804923745976383044623641587178342784695039121956046773482075227567549007660681579282296935959415193600 : Int) coeff0833) := by
  rw [CoefficientMerge.eval_scale, ← atom0833_identity]
  exact mul_nonneg (by norm_num) (atom0833_nonneg g t z hg hA hB ht hz hw)

def coeff0834 : CoefficientMerge.Poly :=
  [(16656, 1)]
noncomputable def atom0834 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1)
theorem atom0834_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0834 g t z = CoefficientMerge.eval (monomial g t z) coeff0834 := by
  norm_num [atom0834, coeff0834, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0834_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0834 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0834]
  positivity
theorem weighted0834_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3325135973686637154555838887202185337523386881746191093912792540516766580318680503542632481697048908374044763574337137674833292218122854400 : Int) coeff0834) := by
  rw [CoefficientMerge.eval_scale, ← atom0834_identity]
  exact mul_nonneg (by norm_num) (atom0834_nonneg g t z hg hA hB ht hz hw)

def coeff0835 : CoefficientMerge.Poly :=
  [(266512, 1)]
noncomputable def atom0835 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (t) ^ 1)
theorem atom0835_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0835 g t z = CoefficientMerge.eval (monomial g t z) coeff0835 := by
  norm_num [atom0835, coeff0835, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0835_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0835 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0835]
  positivity
theorem weighted0835_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1057957210731140709386294905564884339099211904195743925752405311493362770430856472338926766567149404450945639574697238994180894649239859200 : Int) coeff0835) := by
  rw [CoefficientMerge.eval_scale, ← atom0835_identity]
  exact mul_nonneg (by norm_num) (atom0835_nonneg g t z hg hA hB ht hz hw)

def coeff0836 : CoefficientMerge.Poly :=
  [(278800, 1)]
noncomputable def atom0836 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (t) ^ 1)
theorem atom0836_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0836 g t z = CoefficientMerge.eval (monomial g t z) coeff0836 := by
  norm_num [atom0836, coeff0836, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0836_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0836 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0836]
  positivity
theorem weighted0836_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (611914621157608271327930546292182869563231358428232895074445417503193770274813655375216025702883775660961632778054167664247562728272281600 : Int) coeff0836) := by
  rw [CoefficientMerge.eval_scale, ← atom0836_identity]
  exact mul_nonneg (by norm_num) (atom0836_nonneg g t z hg hA hB ht hz hw)

def coeff0837 : CoefficientMerge.Poly :=
  [(1052944, 1)]
noncomputable def atom0837 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (z) ^ 1)
theorem atom0837_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0837 g t z = CoefficientMerge.eval (monomial g t z) coeff0837 := by
  norm_num [atom0837, coeff0837, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0837_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0837 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0837]
  positivity
theorem weighted0837_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3222719806429586377544214855218573744984543341251064401892032682554012433283166842433181320167488210060372843687028664158971423823097078720 : Int) coeff0837) := by
  rw [CoefficientMerge.eval_scale, ← atom0837_identity]
  exact mul_nonneg (by norm_num) (atom0837_nonneg g t z hg hA hB ht hz hw)

def coeff0838 : CoefficientMerge.Poly :=
  [(1065232, 1)]
noncomputable def atom0838 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (z) ^ 1)
theorem atom0838_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0838 g t z = CoefficientMerge.eval (monomial g t z) coeff0838 := by
  norm_num [atom0838, coeff0838, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0838_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0838 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0838]
  positivity
theorem weighted0838_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (8529510337463854846492928089753967096896254376298975692538828010298345980622202925086174789298029762233370101022670966401216915710189843200 : Int) coeff0838) := by
  rw [CoefficientMerge.eval_scale, ← atom0838_identity]
  exact mul_nonneg (by norm_num) (atom0838_nonneg g t z hg hA hB ht hz hw)

def coeff0839 : CoefficientMerge.Poly :=
  [(1114384, 1)]
noncomputable def atom0839 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (z) ^ 1)
theorem atom0839_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0839 g t z = CoefficientMerge.eval (monomial g t z) coeff0839 := by
  norm_num [atom0839, coeff0839, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0839_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0839 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0839]
  positivity
theorem weighted0839_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (10938997730558826654274352534479278941281786161593352255239624992246937305973538315823952169607474670423399071790523167718555020555608119840 : Int) coeff0839) := by
  rw [CoefficientMerge.eval_scale, ← atom0839_identity]
  exact mul_nonneg (by norm_num) (atom0839_nonneg g t z hg hA hB ht hz hw)

def coeff0840 : CoefficientMerge.Poly :=
  [(66576, 1)]
noncomputable def atom0840 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1)
theorem atom0840_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0840 g t z = CoefficientMerge.eval (monomial g t z) coeff0840 := by
  norm_num [atom0840, coeff0840, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0840_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0840 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0840]
  positivity
theorem weighted0840_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1547821185045656865076645298460303935834699403162703095625771507240851156374053351732030012854202022481679985191232700560923677432267571200 : Int) coeff0840) := by
  rw [CoefficientMerge.eval_scale, ← atom0840_identity]
  exact mul_nonneg (by norm_num) (atom0840_nonneg g t z hg hA hB ht hz hw)

def coeff0841 : CoefficientMerge.Poly :=
  [(1050640, 1)]
noncomputable def atom0841 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 5) ^ 2 * (z) ^ 1)
theorem atom0841_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0841 g t z = CoefficientMerge.eval (monomial g t z) coeff0841 := by
  norm_num [atom0841, coeff0841, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0841_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0841 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0841]
  positivity
theorem weighted0841_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1165489574873236174202144572902184109182633473844109465553986539406654771625739264562122415373767753072828056155472207462012406083914393600 : Int) coeff0841) := by
  rw [CoefficientMerge.eval_scale, ← atom0841_identity]
  exact mul_nonneg (by norm_num) (atom0841_nonneg g t z hg hA hB ht hz hw)

def coeff0842 : CoefficientMerge.Poly :=
  [(1053712, 1)]
noncomputable def atom0842 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (z) ^ 1)
theorem atom0842_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0842 g t z = CoefficientMerge.eval (monomial g t z) coeff0842 := by
  norm_num [atom0842, coeff0842, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0842_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0842 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0842]
  positivity
theorem weighted0842_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4281664939339112765534882014741725321410725831756988523235745948176439362260675315651764379561627425866291777339912875302194019645204889600 : Int) coeff0842) := by
  rw [CoefficientMerge.eval_scale, ← atom0842_identity]
  exact mul_nonneg (by norm_num) (atom0842_nonneg g t z hg hA hB ht hz hw)

def coeff0843 : CoefficientMerge.Poly :=
  [(1066000, 1)]
noncomputable def atom0843 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (z) ^ 1)
theorem atom0843_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0843 g t z = CoefficientMerge.eval (monomial g t z) coeff0843 := by
  norm_num [atom0843, coeff0843, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0843_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0843 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0843]
  positivity
theorem weighted0843_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4837365964224299937269152546214671943648089439924199616986811631002512477205008422908964830006353007154304293651466504018701943838467018240 : Int) coeff0843) := by
  rw [CoefficientMerge.eval_scale, ← atom0843_identity]
  exact mul_nonneg (by norm_num) (atom0843_nonneg g t z hg hA hB ht hz hw)

def coeff0844 : CoefficientMerge.Poly :=
  [(1115152, 1)]
noncomputable def atom0844 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (z) ^ 1)
theorem atom0844_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0844 g t z = CoefficientMerge.eval (monomial g t z) coeff0844 := by
  norm_num [atom0844, coeff0844, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0844_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0844 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0844]
  positivity
theorem weighted0844_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (7812606302749971409689664636673793181373129373735094696733988643572226948673730178598234458441740823639510470867815915051208392706633708480 : Int) coeff0844) := by
  rw [CoefficientMerge.eval_scale, ← atom0844_identity]
  exact mul_nonneg (by norm_num) (atom0844_nonneg g t z hg hA hB ht hz hw)

def sparseBlock073 : CoefficientMerge.Poly :=
  [(4368, 1189438952564238681868397922150922001804923745976383044623641587178342784695039121956046773482075227567549007660681579282296935959415193600), (16656, 3325135973686637154555838887202185337523386881746191093912792540516766580318680503542632481697048908374044763574337137674833292218122854400), (65616, 2978465330465111071646686216630453143946752335047517542029044169050592990405460176147589214371777957090598958133296519808937841382953369600), (66576, 1547821185045656865076645298460303935834699403162703095625771507240851156374053351732030012854202022481679985191232700560923677432267571200), (266320, 1509387038507717668226518510844013193983339035451174159195060118987234851467043393812029155004783697026869124638112515496450543696114790400), (266512, 1057957210731140709386294905564884339099211904195743925752405311493362770430856472338926766567149404450945639574697238994180894649239859200), (278608, 1473386806706529090011284064196828464713294610786878563616769026990442253697012182524126896145168980137853555628976096008682570247806566400), (278800, 611914621157608271327930546292182869563231358428232895074445417503193770274813655375216025702883775660961632778054167664247562728272281600), (1048912, 6227622118773046978153260161480348749547274942508628801736564576045926477378744960479615039983814662833467516483565700179312135515829765760), (1049680, 5901785990407208015958035187157155536656940608909450571437046370533257961167447864543912412915340003400575790351487830935410025578027635200), (1050640, 1165489574873236174202144572902184109182633473844109465553986539406654771625739264562122415373767753072828056155472207462012406083914393600), (1052752, 7671853613154813588152537362702540674680790768591443002813503261900652606555913588525969250124899814248365466159189645372447654165655315200), (1052944, 3222719806429586377544214855218573744984543341251064401892032682554012433283166842433181320167488210060372843687028664158971423823097078720), (1053712, 4281664939339112765534882014741725321410725831756988523235745948176439362260675315651764379561627425866291777339912875302194019645204889600), (1065040, 11716384220059408473508759074595952904108641093096766336604152832074808715548953858877934163819874525475514030282699893660033049348968851200), (1065232, 8529510337463854846492928089753967096896254376298975692538828010298345980622202925086174789298029762233370101022670966401216915710189843200), (1066000, 4837365964224299937269152546214671943648089439924199616986811631002512477205008422908964830006353007154304293651466504018701943838467018240), (1114192, 15850368928878342618648110225697348024864350166145526247791555608461266980641534011208660991234335676260830971740759988922219358410723884800), (1114384, 10938997730558826654274352534479278941281786161593352255239624992246937305973538315823952169607474670423399071790523167718555020555608119840), (1115152, 7812606302749971409689664636673793181373129373735094696733988643572226948673730178598234458441740823639510470867815915051208392706633708480)]
theorem sparseBlock073_data : sparseBlock073 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (2978465330465111071646686216630453143946752335047517542029044169050592990405460176147589214371777957090598958133296519808937841382953369600 : Int) coeff0825) (CoefficientMerge.scale (1509387038507717668226518510844013193983339035451174159195060118987234851467043393812029155004783697026869124638112515496450543696114790400 : Int) coeff0826)) (CoefficientMerge.merge (CoefficientMerge.scale (1473386806706529090011284064196828464713294610786878563616769026990442253697012182524126896145168980137853555628976096008682570247806566400 : Int) coeff0827) (CoefficientMerge.merge (CoefficientMerge.scale (6227622118773046978153260161480348749547274942508628801736564576045926477378744960479615039983814662833467516483565700179312135515829765760 : Int) coeff0828) (CoefficientMerge.scale (5901785990407208015958035187157155536656940608909450571437046370533257961167447864543912412915340003400575790351487830935410025578027635200 : Int) coeff0829)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (7671853613154813588152537362702540674680790768591443002813503261900652606555913588525969250124899814248365466159189645372447654165655315200 : Int) coeff0830) (CoefficientMerge.scale (11716384220059408473508759074595952904108641093096766336604152832074808715548953858877934163819874525475514030282699893660033049348968851200 : Int) coeff0831)) (CoefficientMerge.merge (CoefficientMerge.scale (15850368928878342618648110225697348024864350166145526247791555608461266980641534011208660991234335676260830971740759988922219358410723884800 : Int) coeff0832) (CoefficientMerge.merge (CoefficientMerge.scale (1189438952564238681868397922150922001804923745976383044623641587178342784695039121956046773482075227567549007660681579282296935959415193600 : Int) coeff0833) (CoefficientMerge.scale (3325135973686637154555838887202185337523386881746191093912792540516766580318680503542632481697048908374044763574337137674833292218122854400 : Int) coeff0834))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1057957210731140709386294905564884339099211904195743925752405311493362770430856472338926766567149404450945639574697238994180894649239859200 : Int) coeff0835) (CoefficientMerge.scale (611914621157608271327930546292182869563231358428232895074445417503193770274813655375216025702883775660961632778054167664247562728272281600 : Int) coeff0836)) (CoefficientMerge.merge (CoefficientMerge.scale (3222719806429586377544214855218573744984543341251064401892032682554012433283166842433181320167488210060372843687028664158971423823097078720 : Int) coeff0837) (CoefficientMerge.merge (CoefficientMerge.scale (8529510337463854846492928089753967096896254376298975692538828010298345980622202925086174789298029762233370101022670966401216915710189843200 : Int) coeff0838) (CoefficientMerge.scale (10938997730558826654274352534479278941281786161593352255239624992246937305973538315823952169607474670423399071790523167718555020555608119840 : Int) coeff0839)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1547821185045656865076645298460303935834699403162703095625771507240851156374053351732030012854202022481679985191232700560923677432267571200 : Int) coeff0840) (CoefficientMerge.scale (1165489574873236174202144572902184109182633473844109465553986539406654771625739264562122415373767753072828056155472207462012406083914393600 : Int) coeff0841)) (CoefficientMerge.merge (CoefficientMerge.scale (4281664939339112765534882014741725321410725831756988523235745948176439362260675315651764379561627425866291777339912875302194019645204889600 : Int) coeff0842) (CoefficientMerge.merge (CoefficientMerge.scale (4837365964224299937269152546214671943648089439924199616986811631002512477205008422908964830006353007154304293651466504018701943838467018240 : Int) coeff0843) (CoefficientMerge.scale (7812606302749971409689664636673793181373129373735094696733988643572226948673730178598234458441740823639510470867815915051208392706633708480 : Int) coeff0844)))))) := by decide +kernel
theorem sparseBlock073_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock073 := by
  rw [sparseBlock073_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted0825_nonneg g t z hg hA hB ht hz hw) (weighted0826_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0827_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0828_nonneg g t z hg hA hB ht hz hw) (weighted0829_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0830_nonneg g t z hg hA hB ht hz hw) (weighted0831_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0832_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0833_nonneg g t z hg hA hB ht hz hw) (weighted0834_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted0835_nonneg g t z hg hA hB ht hz hw) (weighted0836_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0837_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0838_nonneg g t z hg hA hB ht hz hw) (weighted0839_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0840_nonneg g t z hg hA hB ht hz hw) (weighted0841_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0842_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0843_nonneg g t z hg hA hB ht hz hw) (weighted0844_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
