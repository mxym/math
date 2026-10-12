import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff1105 : CoefficientMerge.Poly :=
  [(1593360, 1)]
noncomputable def atom1105 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1105_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1105 g t z = CoefficientMerge.eval (monomial g t z) coeff1105 := by
  norm_num [atom1105, coeff1105, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1105_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1105 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1105]
  positivity
theorem weighted1105_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (83010680142511082347250943832494770683080506237345552749078505237545757093951148968135046889404103224901004753051256161396298012046579200 : Int) coeff1105) := by
  rw [CoefficientMerge.eval_scale, ← atom1105_identity]
  exact mul_nonneg (by norm_num) (atom1105_nonneg g t z hg hA hB ht hz hw)

def coeff1106 : CoefficientMerge.Poly :=
  [(2359440, 1)]
noncomputable def atom1106 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 2 * (t) ^ 1 * (z) ^ 2)
theorem atom1106_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1106 g t z = CoefficientMerge.eval (monomial g t z) coeff1106 := by
  norm_num [atom1106, coeff1106, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1106_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1106 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1106]
  positivity
theorem weighted1106_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (369885456153967621904444994375300699287655137176794187133506717964784313236223145570801639924543076784513182306226297204473096935551107840 : Int) coeff1106) := by
  rw [CoefficientMerge.eval_scale, ← atom1106_identity]
  exact mul_nonneg (by norm_num) (atom1106_nonneg g t z hg hA hB ht hz hw)

def coeff1107 : CoefficientMerge.Poly :=
  [(2359632, 1)]
noncomputable def atom1107 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 4) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1107_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1107 g t z = CoefficientMerge.eval (monomial g t z) coeff1107 := by
  norm_num [atom1107, coeff1107, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1107_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1107 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1107]
  positivity
theorem weighted1107_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (673366719604190772571908750803614478107418926345877856537406973788151257976376257110069666516526494785941875887454247241540559760128399296 : Int) coeff1107) := by
  rw [CoefficientMerge.eval_scale, ← atom1107_identity]
  exact mul_nonneg (by norm_num) (atom1107_nonneg g t z hg hA hB ht hz hw)

def coeff1108 : CoefficientMerge.Poly :=
  [(2360400, 1)]
noncomputable def atom1108 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 5) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1108_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1108 g t z = CoefficientMerge.eval (monomial g t z) coeff1108 := by
  norm_num [atom1108, coeff1108, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1108_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1108 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1108]
  positivity
theorem weighted1108_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (416597280537508185242680571359218902565313312098116035999402025279199371469834015682363000671087693366810863469194234601796880490877717920 : Int) coeff1108) := by
  rw [CoefficientMerge.eval_scale, ← atom1108_identity]
  exact mul_nonneg (by norm_num) (atom1108_nonneg g t z hg hA hB ht hz hw)

def coeff1109 : CoefficientMerge.Poly :=
  [(2363472, 1)]
noncomputable def atom1109 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1109_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1109 g t z = CoefficientMerge.eval (monomial g t z) coeff1109 := by
  norm_num [atom1109, coeff1109, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1109_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1109 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1109]
  positivity
theorem weighted1109_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (371086522568272615190704384619560916419779832215050791623215813834041801026854412048225317716208743731732071972732147227195430505874596960 : Int) coeff1109) := by
  rw [CoefficientMerge.eval_scale, ← atom1109_identity]
  exact mul_nonneg (by norm_num) (atom1109_nonneg g t z hg hA hB ht hz hw)

def coeff1110 : CoefficientMerge.Poly :=
  [(2375760, 1)]
noncomputable def atom1110 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1110_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1110 g t z = CoefficientMerge.eval (monomial g t z) coeff1110 := by
  norm_num [atom1110, coeff1110, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1110_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1110 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1110]
  positivity
theorem weighted1110_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (371661038649635183145406406579552620347353539750473914384668680628785251165198009902430107347263677404645077900978730882110658530976436320 : Int) coeff1110) := by
  rw [CoefficientMerge.eval_scale, ← atom1110_identity]
  exact mul_nonneg (by norm_num) (atom1110_nonneg g t z hg hA hB ht hz hw)

def coeff1111 : CoefficientMerge.Poly :=
  [(2424912, 1)]
noncomputable def atom1111 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1111_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1111 g t z = CoefficientMerge.eval (monomial g t z) coeff1111 := by
  norm_num [atom1111, coeff1111, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1111_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1111 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1111]
  positivity
theorem weighted1111_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (306513165901500928227101668579042719943215152325891270154369675949873645532899259615908499815197846870492524612679774389070144608211217760 : Int) coeff1111) := by
  rw [CoefficientMerge.eval_scale, ← atom1111_identity]
  exact mul_nonneg (by norm_num) (atom1111_nonneg g t z hg hA hB ht hz hw)

def coeff1112 : CoefficientMerge.Poly :=
  [(2359824, 1)]
noncomputable def atom1112 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 2 * (t) ^ 1 * (z) ^ 2)
theorem atom1112_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1112 g t z = CoefficientMerge.eval (monomial g t z) coeff1112 := by
  norm_num [atom1112, coeff1112, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1112_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1112 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1112]
  positivity
theorem weighted1112_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (290225809014605980097206523347133682904827296020976207991584529325785325701315832133089306827896132419440395583376889922518610194060112000 : Int) coeff1112) := by
  rw [CoefficientMerge.eval_scale, ← atom1112_identity]
  exact mul_nonneg (by norm_num) (atom1112_nonneg g t z hg hA hB ht hz hw)

def coeff1113 : CoefficientMerge.Poly :=
  [(2360592, 1)]
noncomputable def atom1113 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 5) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1113_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1113 g t z = CoefficientMerge.eval (monomial g t z) coeff1113 := by
  norm_num [atom1113, coeff1113, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1113_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1113 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1113]
  positivity
theorem weighted1113_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (318161081914817220678323845989393144553892300269748961861654318561197291974560629862392182278325149072415019061379059657544636836486598656 : Int) coeff1113) := by
  rw [CoefficientMerge.eval_scale, ← atom1113_identity]
  exact mul_nonneg (by norm_num) (atom1113_nonneg g t z hg hA hB ht hz hw)

def coeff1114 : CoefficientMerge.Poly :=
  [(2363664, 1)]
noncomputable def atom1114 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1114_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1114 g t z = CoefficientMerge.eval (monomial g t z) coeff1114 := by
  norm_num [atom1114, coeff1114, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1114_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1114 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1114]
  positivity
theorem weighted1114_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (254186796401344478006460244401072467738034251626239756225022471392760338009332900369992819352104143648110655684973592080024659459690771456 : Int) coeff1114) := by
  rw [CoefficientMerge.eval_scale, ← atom1114_identity]
  exact mul_nonneg (by norm_num) (atom1114_nonneg g t z hg hA hB ht hz hw)

def coeff1115 : CoefficientMerge.Poly :=
  [(2375952, 1)]
noncomputable def atom1115 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1115_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1115 g t z = CoefficientMerge.eval (monomial g t z) coeff1115 := by
  norm_num [atom1115, coeff1115, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1115_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1115 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1115]
  positivity
theorem weighted1115_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (259483790583685111483588809957475757277798007565611076280403111390765464677223006185026836497694761827215711007828514030242476761423816928 : Int) coeff1115) := by
  rw [CoefficientMerge.eval_scale, ← atom1115_identity]
  exact mul_nonneg (by norm_num) (atom1115_nonneg g t z hg hA hB ht hz hw)

def coeff1116 : CoefficientMerge.Poly :=
  [(2425104, 1)]
noncomputable def atom1116 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1116_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1116 g t z = CoefficientMerge.eval (monomial g t z) coeff1116 := by
  norm_num [atom1116, coeff1116, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1116_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1116 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1116]
  positivity
theorem weighted1116_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (182824195161860720229389713841213554649239234672047886766370152521883620681499117936663151112250136218219815755958201100908095315285594384 : Int) coeff1116) := by
  rw [CoefficientMerge.eval_scale, ← atom1116_identity]
  exact mul_nonneg (by norm_num) (atom1116_nonneg g t z hg hA hB ht hz hw)

def coeff1117 : CoefficientMerge.Poly :=
  [(2361360, 1)]
noncomputable def atom1117 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 5) ^ 2 * (t) ^ 1 * (z) ^ 2)
theorem atom1117_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1117 g t z = CoefficientMerge.eval (monomial g t z) coeff1117 := by
  norm_num [atom1117, coeff1117, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1117_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1117 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1117]
  positivity
theorem weighted1117_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (135223250470733598178857787946667981330030927617583855574802557564659086520723091827499273816766114307313190558183969396074762583323767360 : Int) coeff1117) := by
  rw [CoefficientMerge.eval_scale, ← atom1117_identity]
  exact mul_nonneg (by norm_num) (atom1117_nonneg g t z hg hA hB ht hz hw)

def coeff1118 : CoefficientMerge.Poly :=
  [(2364432, 1)]
noncomputable def atom1118 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1118_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1118 g t z = CoefficientMerge.eval (monomial g t z) coeff1118 := by
  norm_num [atom1118, coeff1118, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1118_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1118 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1118]
  positivity
theorem weighted1118_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (196556014168859949065767610414233490204930045158822439885754917675896850182414536630799903839364206043339707895387619160021714810861107040 : Int) coeff1118) := by
  rw [CoefficientMerge.eval_scale, ← atom1118_identity]
  exact mul_nonneg (by norm_num) (atom1118_nonneg g t z hg hA hB ht hz hw)

def coeff1119 : CoefficientMerge.Poly :=
  [(2376720, 1)]
noncomputable def atom1119 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1119_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1119 g t z = CoefficientMerge.eval (monomial g t z) coeff1119 := by
  norm_num [atom1119, coeff1119, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1119_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1119 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1119]
  positivity
theorem weighted1119_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (146329640717957025752121475031694601762327901351657240572501665241308361541491476332042615365261706542422851504585288082998551740883616640 : Int) coeff1119) := by
  rw [CoefficientMerge.eval_scale, ← atom1119_identity]
  exact mul_nonneg (by norm_num) (atom1119_nonneg g t z hg hA hB ht hz hw)

def coeff1120 : CoefficientMerge.Poly :=
  [(2425872, 1)]
noncomputable def atom1120 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1120_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1120 g t z = CoefficientMerge.eval (monomial g t z) coeff1120 := by
  norm_num [atom1120, coeff1120, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1120_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1120 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1120]
  positivity
theorem weighted1120_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (115222860758765082672502955201248165999800680682152178969895903028404721646586693665567859200787897290705515495894855394620685134494260480 : Int) coeff1120) := by
  rw [CoefficientMerge.eval_scale, ← atom1120_identity]
  exact mul_nonneg (by norm_num) (atom1120_nonneg g t z hg hA hB ht hz hw)

def coeff1121 : CoefficientMerge.Poly :=
  [(2367504, 1)]
noncomputable def atom1121 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 6) ^ 2 * (t) ^ 1 * (z) ^ 2)
theorem atom1121_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1121 g t z = CoefficientMerge.eval (monomial g t z) coeff1121 := by
  norm_num [atom1121, coeff1121, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1121_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1121 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1121]
  positivity
theorem weighted1121_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (71139270787503143790564652033250251960077166116144530801108154341959703481409035872374275113465923126904046142449225765939144810301363200 : Int) coeff1121) := by
  rw [CoefficientMerge.eval_scale, ← atom1121_identity]
  exact mul_nonneg (by norm_num) (atom1121_nonneg g t z hg hA hB ht hz hw)

def coeff1122 : CoefficientMerge.Poly :=
  [(2379792, 1)]
noncomputable def atom1122 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1122_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1122 g t z = CoefficientMerge.eval (monomial g t z) coeff1122 := by
  norm_num [atom1122, coeff1122, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1122_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1122 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1122]
  positivity
theorem weighted1122_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (86260414008643957786730818160525241965161375778888628164044687734838161300577609160608470327121066558361698616230263237356726943615382400 : Int) coeff1122) := by
  rw [CoefficientMerge.eval_scale, ← atom1122_identity]
  exact mul_nonneg (by norm_num) (atom1122_nonneg g t z hg hA hB ht hz hw)

def coeff1123 : CoefficientMerge.Poly :=
  [(2428944, 1)]
noncomputable def atom1123 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1123_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1123 g t z = CoefficientMerge.eval (monomial g t z) coeff1123 := by
  norm_num [atom1123, coeff1123, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1123_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1123 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1123]
  positivity
theorem weighted1123_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (42828039179535935177066334509715382936765741253688027747030373461003273006372791904950051128129658166014802294043216451563914811419763200 : Int) coeff1123) := by
  rw [CoefficientMerge.eval_scale, ← atom1123_identity]
  exact mul_nonneg (by norm_num) (atom1123_nonneg g t z hg hA hB ht hz hw)

def coeff1124 : CoefficientMerge.Poly :=
  [(786624, 1)]
noncomputable def atom1124 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 3 * (t) ^ 3)
theorem atom1124_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1124 g t z = CoefficientMerge.eval (monomial g t z) coeff1124 := by
  norm_num [atom1124, coeff1124, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1124_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1124 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1124]
  positivity
theorem weighted1124_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5540746141005892951045932926179880416908786184968181291325827939802396354874423784336830006761284810814942333426249407101244661948620800 : Int) coeff1124) := by
  rw [CoefficientMerge.eval_scale, ← atom1124_identity]
  exact mul_nonneg (by norm_num) (atom1124_nonneg g t z hg hA hB ht hz hw)

def sparseBlock087 : CoefficientMerge.Poly :=
  [(786624, 5540746141005892951045932926179880416908786184968181291325827939802396354874423784336830006761284810814942333426249407101244661948620800), (1593360, 83010680142511082347250943832494770683080506237345552749078505237545757093951148968135046889404103224901004753051256161396298012046579200), (2359440, 369885456153967621904444994375300699287655137176794187133506717964784313236223145570801639924543076784513182306226297204473096935551107840), (2359632, 673366719604190772571908750803614478107418926345877856537406973788151257976376257110069666516526494785941875887454247241540559760128399296), (2359824, 290225809014605980097206523347133682904827296020976207991584529325785325701315832133089306827896132419440395583376889922518610194060112000), (2360400, 416597280537508185242680571359218902565313312098116035999402025279199371469834015682363000671087693366810863469194234601796880490877717920), (2360592, 318161081914817220678323845989393144553892300269748961861654318561197291974560629862392182278325149072415019061379059657544636836486598656), (2361360, 135223250470733598178857787946667981330030927617583855574802557564659086520723091827499273816766114307313190558183969396074762583323767360), (2363472, 371086522568272615190704384619560916419779832215050791623215813834041801026854412048225317716208743731732071972732147227195430505874596960), (2363664, 254186796401344478006460244401072467738034251626239756225022471392760338009332900369992819352104143648110655684973592080024659459690771456), (2364432, 196556014168859949065767610414233490204930045158822439885754917675896850182414536630799903839364206043339707895387619160021714810861107040), (2367504, 71139270787503143790564652033250251960077166116144530801108154341959703481409035872374275113465923126904046142449225765939144810301363200), (2375760, 371661038649635183145406406579552620347353539750473914384668680628785251165198009902430107347263677404645077900978730882110658530976436320), (2375952, 259483790583685111483588809957475757277798007565611076280403111390765464677223006185026836497694761827215711007828514030242476761423816928), (2376720, 146329640717957025752121475031694601762327901351657240572501665241308361541491476332042615365261706542422851504585288082998551740883616640), (2379792, 86260414008643957786730818160525241965161375778888628164044687734838161300577609160608470327121066558361698616230263237356726943615382400), (2424912, 306513165901500928227101668579042719943215152325891270154369675949873645532899259615908499815197846870492524612679774389070144608211217760), (2425104, 182824195161860720229389713841213554649239234672047886766370152521883620681499117936663151112250136218219815755958201100908095315285594384), (2425872, 115222860758765082672502955201248165999800680682152178969895903028404721646586693665567859200787897290705515495894855394620685134494260480), (2428944, 42828039179535935177066334509715382936765741253688027747030373461003273006372791904950051128129658166014802294043216451563914811419763200)]
theorem sparseBlock087_data : sparseBlock087 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (83010680142511082347250943832494770683080506237345552749078505237545757093951148968135046889404103224901004753051256161396298012046579200 : Int) coeff1105) (CoefficientMerge.scale (369885456153967621904444994375300699287655137176794187133506717964784313236223145570801639924543076784513182306226297204473096935551107840 : Int) coeff1106)) (CoefficientMerge.merge (CoefficientMerge.scale (673366719604190772571908750803614478107418926345877856537406973788151257976376257110069666516526494785941875887454247241540559760128399296 : Int) coeff1107) (CoefficientMerge.merge (CoefficientMerge.scale (416597280537508185242680571359218902565313312098116035999402025279199371469834015682363000671087693366810863469194234601796880490877717920 : Int) coeff1108) (CoefficientMerge.scale (371086522568272615190704384619560916419779832215050791623215813834041801026854412048225317716208743731732071972732147227195430505874596960 : Int) coeff1109)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (371661038649635183145406406579552620347353539750473914384668680628785251165198009902430107347263677404645077900978730882110658530976436320 : Int) coeff1110) (CoefficientMerge.scale (306513165901500928227101668579042719943215152325891270154369675949873645532899259615908499815197846870492524612679774389070144608211217760 : Int) coeff1111)) (CoefficientMerge.merge (CoefficientMerge.scale (290225809014605980097206523347133682904827296020976207991584529325785325701315832133089306827896132419440395583376889922518610194060112000 : Int) coeff1112) (CoefficientMerge.merge (CoefficientMerge.scale (318161081914817220678323845989393144553892300269748961861654318561197291974560629862392182278325149072415019061379059657544636836486598656 : Int) coeff1113) (CoefficientMerge.scale (254186796401344478006460244401072467738034251626239756225022471392760338009332900369992819352104143648110655684973592080024659459690771456 : Int) coeff1114))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (259483790583685111483588809957475757277798007565611076280403111390765464677223006185026836497694761827215711007828514030242476761423816928 : Int) coeff1115) (CoefficientMerge.scale (182824195161860720229389713841213554649239234672047886766370152521883620681499117936663151112250136218219815755958201100908095315285594384 : Int) coeff1116)) (CoefficientMerge.merge (CoefficientMerge.scale (135223250470733598178857787946667981330030927617583855574802557564659086520723091827499273816766114307313190558183969396074762583323767360 : Int) coeff1117) (CoefficientMerge.merge (CoefficientMerge.scale (196556014168859949065767610414233490204930045158822439885754917675896850182414536630799903839364206043339707895387619160021714810861107040 : Int) coeff1118) (CoefficientMerge.scale (146329640717957025752121475031694601762327901351657240572501665241308361541491476332042615365261706542422851504585288082998551740883616640 : Int) coeff1119)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (115222860758765082672502955201248165999800680682152178969895903028404721646586693665567859200787897290705515495894855394620685134494260480 : Int) coeff1120) (CoefficientMerge.scale (71139270787503143790564652033250251960077166116144530801108154341959703481409035872374275113465923126904046142449225765939144810301363200 : Int) coeff1121)) (CoefficientMerge.merge (CoefficientMerge.scale (86260414008643957786730818160525241965161375778888628164044687734838161300577609160608470327121066558361698616230263237356726943615382400 : Int) coeff1122) (CoefficientMerge.merge (CoefficientMerge.scale (42828039179535935177066334509715382936765741253688027747030373461003273006372791904950051128129658166014802294043216451563914811419763200 : Int) coeff1123) (CoefficientMerge.scale (5540746141005892951045932926179880416908786184968181291325827939802396354874423784336830006761284810814942333426249407101244661948620800 : Int) coeff1124)))))) := by decide +kernel
theorem sparseBlock087_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock087 := by
  rw [sparseBlock087_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted1105_nonneg g t z hg hA hB ht hz hw) (weighted1106_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1107_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1108_nonneg g t z hg hA hB ht hz hw) (weighted1109_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1110_nonneg g t z hg hA hB ht hz hw) (weighted1111_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1112_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1113_nonneg g t z hg hA hB ht hz hw) (weighted1114_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted1115_nonneg g t z hg hA hB ht hz hw) (weighted1116_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1117_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1118_nonneg g t z hg hA hB ht hz hw) (weighted1119_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1120_nonneg g t z hg hA hB ht hz hw) (weighted1121_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1122_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1123_nonneg g t z hg hA hB ht hz hw) (weighted1124_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
