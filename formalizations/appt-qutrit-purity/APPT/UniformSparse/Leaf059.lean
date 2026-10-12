import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff0545 : CoefficientMerge.Poly :=
  [(273, 1)]
noncomputable def atom0545 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 4) ^ 1)
theorem atom0545_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0545 g t z = CoefficientMerge.eval (monomial g t z) coeff0545 := by
  norm_num [atom0545, coeff0545, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0545_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0545 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0545]
  positivity
theorem weighted0545_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (9229305922009214132227333810712285106984622825352697741438323555665293376330287213775078269029748598578004115801462034884176139320385341440 : Int) coeff0545) := by
  rw [CoefficientMerge.eval_scale, ← atom0545_identity]
  exact mul_nonneg (by norm_num) (atom0545_nonneg g t z hg hA hB ht hz hw)

def coeff0546 : CoefficientMerge.Poly :=
  [(1041, 1)]
noncomputable def atom0546 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 5) ^ 1)
theorem atom0546_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0546 g t z = CoefficientMerge.eval (monomial g t z) coeff0546 := by
  norm_num [atom0546, coeff0546, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0546_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0546 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0546]
  positivity
theorem weighted0546_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2693885329493025081554090180156270151466661126369079751217103701535707626297192168959900068100163447579071893675927913381740377950482534400 : Int) coeff0546) := by
  rw [CoefficientMerge.eval_scale, ← atom0546_identity]
  exact mul_nonneg (by norm_num) (atom0546_nonneg g t z hg hA hB ht hz hw)

def coeff0547 : CoefficientMerge.Poly :=
  [(4113, 1)]
noncomputable def atom0547 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 6) ^ 1)
theorem atom0547_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0547 g t z = CoefficientMerge.eval (monomial g t z) coeff0547 := by
  norm_num [atom0547, coeff0547, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0547_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0547 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0547]
  positivity
theorem weighted0547_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5373566792177359693101805283718853938375262569712665127300096245783900953688806458353761224816090003311321861341375887257040376768579420160 : Int) coeff0547) := by
  rw [CoefficientMerge.eval_scale, ← atom0547_identity]
  exact mul_nonneg (by norm_num) (atom0547_nonneg g t z hg hA hB ht hz hw)

def coeff0548 : CoefficientMerge.Poly :=
  [(16401, 1)]
noncomputable def atom0548 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 7) ^ 1)
theorem atom0548_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0548 g t z = CoefficientMerge.eval (monomial g t z) coeff0548 := by
  norm_num [atom0548, coeff0548, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0548_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0548 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0548]
  positivity
theorem weighted0548_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1076297714185172201482608273079871928081792874512843632393314537519615643706729485510335342588753764193900052436388515013946182735753666560 : Int) coeff0548) := by
  rw [CoefficientMerge.eval_scale, ← atom0548_identity]
  exact mul_nonneg (by norm_num) (atom0548_nonneg g t z hg hA hB ht hz hw)

def coeff0549 : CoefficientMerge.Poly :=
  [(262177, 1)]
noncomputable def atom0549 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 2 * (t) ^ 1)
theorem atom0549_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0549 g t z = CoefficientMerge.eval (monomial g t z) coeff0549 := by
  norm_num [atom0549, coeff0549, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0549_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0549 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0549]
  positivity
theorem weighted0549_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1935368248938574311149762889587675526359157956452938368243187555642801300871724305084750061930408041604929875051291996029666666621968416768 : Int) coeff0549) := by
  rw [CoefficientMerge.eval_scale, ← atom0549_identity]
  exact mul_nonneg (by norm_num) (atom0549_nonneg g t z hg hA hB ht hz hw)

def coeff0550 : CoefficientMerge.Poly :=
  [(262225, 1)]
noncomputable def atom0550 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 3) ^ 1 * (t) ^ 1)
theorem atom0550_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0550 g t z = CoefficientMerge.eval (monomial g t z) coeff0550 := by
  norm_num [atom0550, coeff0550, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0550_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0550 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0550]
  positivity
theorem weighted0550_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (16220083618451074519174080448957572008066671114563810081806731667481661682529211018389766099086118897005519047576034056253567403985927890944 : Int) coeff0550) := by
  rw [CoefficientMerge.eval_scale, ← atom0550_identity]
  exact mul_nonneg (by norm_num) (atom0550_nonneg g t z hg hA hB ht hz hw)

def coeff0551 : CoefficientMerge.Poly :=
  [(262417, 1)]
noncomputable def atom0551 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 4) ^ 1 * (t) ^ 1)
theorem atom0551_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0551 g t z = CoefficientMerge.eval (monomial g t z) coeff0551 := by
  norm_num [atom0551, coeff0551, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0551_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0551 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0551]
  positivity
theorem weighted0551_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (18222442130754833267480193335675648769920825858881771819696716425386305948667085845402780212380598782199395797975684370279739707687367914496 : Int) coeff0551) := by
  rw [CoefficientMerge.eval_scale, ← atom0551_identity]
  exact mul_nonneg (by norm_num) (atom0551_nonneg g t z hg hA hB ht hz hw)

def coeff0552 : CoefficientMerge.Poly :=
  [(263185, 1)]
noncomputable def atom0552 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 5) ^ 1 * (t) ^ 1)
theorem atom0552_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0552 g t z = CoefficientMerge.eval (monomial g t z) coeff0552 := by
  norm_num [atom0552, coeff0552, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0552_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0552 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0552]
  positivity
theorem weighted0552_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (10874702779084168278876896522756070416220869037616398590043527560624380940717171672286919366655497416521789707391556385626290692645196793856 : Int) coeff0552) := by
  rw [CoefficientMerge.eval_scale, ← atom0552_identity]
  exact mul_nonneg (by norm_num) (atom0552_nonneg g t z hg hA hB ht hz hw)

def coeff0553 : CoefficientMerge.Poly :=
  [(266257, 1)]
noncomputable def atom0553 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 6) ^ 1 * (t) ^ 1)
theorem atom0553_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0553 g t z = CoefficientMerge.eval (monomial g t z) coeff0553 := by
  norm_num [atom0553, coeff0553, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0553_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0553 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0553]
  positivity
theorem weighted0553_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (8287527431066263622092681708180505472348627357378921804200617878152812430149221286135722147009676690484576506011710383462032141577914777600 : Int) coeff0553) := by
  rw [CoefficientMerge.eval_scale, ← atom0553_identity]
  exact mul_nonneg (by norm_num) (atom0553_nonneg g t z hg hA hB ht hz hw)

def coeff0554 : CoefficientMerge.Poly :=
  [(278545, 1)]
noncomputable def atom0554 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 7) ^ 1 * (t) ^ 1)
theorem atom0554_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0554 g t z = CoefficientMerge.eval (monomial g t z) coeff0554 := by
  norm_num [atom0554, coeff0554, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0554_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0554 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0554]
  positivity
theorem weighted0554_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5784608686564947213035613310329815970236172477835515484860648437833942912008962801079592730582658958036898503496074724907035325798117027840 : Int) coeff0554) := by
  rw [CoefficientMerge.eval_scale, ← atom0554_identity]
  exact mul_nonneg (by norm_num) (atom0554_nonneg g t z hg hA hB ht hz hw)

def coeff0555 : CoefficientMerge.Poly :=
  [(1048657, 1)]
noncomputable def atom0555 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 3) ^ 1 * (z) ^ 1)
theorem atom0555_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0555 g t z = CoefficientMerge.eval (monomial g t z) coeff0555 := by
  norm_num [atom0555, coeff0555, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0555_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0555 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0555]
  positivity
theorem weighted0555_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (13334915560740832651247828394350717139772513646254025565134256660380864413334935871848916171546633173430720623436002968500368359137910727680 : Int) coeff0555) := by
  rw [CoefficientMerge.eval_scale, ← atom0555_identity]
  exact mul_nonneg (by norm_num) (atom0555_nonneg g t z hg hA hB ht hz hw)

def coeff0556 : CoefficientMerge.Poly :=
  [(1048849, 1)]
noncomputable def atom0556 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 4) ^ 1 * (z) ^ 1)
theorem atom0556_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0556 g t z = CoefficientMerge.eval (monomial g t z) coeff0556 := by
  norm_num [atom0556, coeff0556, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0556_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0556 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0556]
  positivity
theorem weighted0556_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (8716816580561601373023530915577468185114190832422381578255960708743970272984745454862849978908532935451235765016202912425116823281400407808 : Int) coeff0556) := by
  rw [CoefficientMerge.eval_scale, ← atom0556_identity]
  exact mul_nonneg (by norm_num) (atom0556_nonneg g t z hg hA hB ht hz hw)

def coeff0557 : CoefficientMerge.Poly :=
  [(1049617, 1)]
noncomputable def atom0557 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 5) ^ 1 * (z) ^ 1)
theorem atom0557_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0557 g t z = CoefficientMerge.eval (monomial g t z) coeff0557 := by
  norm_num [atom0557, coeff0557, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0557_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0557 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0557]
  positivity
theorem weighted0557_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5325552212678163582809256848013200735636193116548697426006706797970981603578817490605510947542417460785430204465407333465412214979999003776 : Int) coeff0557) := by
  rw [CoefficientMerge.eval_scale, ← atom0557_identity]
  exact mul_nonneg (by norm_num) (atom0557_nonneg g t z hg hA hB ht hz hw)

def coeff0558 : CoefficientMerge.Poly :=
  [(1052689, 1)]
noncomputable def atom0558 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 6) ^ 1 * (z) ^ 1)
theorem atom0558_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0558 g t z = CoefficientMerge.eval (monomial g t z) coeff0558 := by
  norm_num [atom0558, coeff0558, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0558_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0558 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0558]
  positivity
theorem weighted0558_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5040823268469535327959185642830129670452353784817405816870331585915234566851467086502619088038280912940413914236424882073477632072945889280 : Int) coeff0558) := by
  rw [CoefficientMerge.eval_scale, ← atom0558_identity]
  exact mul_nonneg (by norm_num) (atom0558_nonneg g t z hg hA hB ht hz hw)

def coeff0559 : CoefficientMerge.Poly :=
  [(1064977, 1)]
noncomputable def atom0559 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 1 * (g 7) ^ 1 * (z) ^ 1)
theorem atom0559_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0559 g t z = CoefficientMerge.eval (monomial g t z) coeff0559 := by
  norm_num [atom0559, coeff0559, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0559_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0559 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0559]
  positivity
theorem weighted0559_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4266071787981979062830968469567708855895099282375254643241736621886347644063382671166731604621561454739300785214776724576372036123207680000 : Int) coeff0559) := by
  rw [CoefficientMerge.eval_scale, ← atom0559_identity]
  exact mul_nonneg (by norm_num) (atom0559_nonneg g t z hg hA hB ht hz hw)

def coeff0560 : CoefficientMerge.Poly :=
  [(129, 1)]
noncomputable def atom0560 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 2)
theorem atom0560_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0560 g t z = CoefficientMerge.eval (monomial g t z) coeff0560 := by
  norm_num [atom0560, coeff0560, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0560_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0560 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0560]
  positivity
theorem weighted0560_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4066455932619687921410673035212839516851090830989413414510019615933192899685752065332763713565920986781167294518315905665079479023000535040 : Int) coeff0560) := by
  rw [CoefficientMerge.eval_scale, ← atom0560_identity]
  exact mul_nonneg (by norm_num) (atom0560_nonneg g t z hg hA hB ht hz hw)

def coeff0561 : CoefficientMerge.Poly :=
  [(321, 1)]
noncomputable def atom0561 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 4) ^ 1)
theorem atom0561_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0561 g t z = CoefficientMerge.eval (monomial g t z) coeff0561 := by
  norm_num [atom0561, coeff0561, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0561_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0561 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0561]
  positivity
theorem weighted0561_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2853444064045600606232543366824574508982886630556505592889166242410338090044911979280718202259220071479305496537128951708212021550580295680 : Int) coeff0561) := by
  rw [CoefficientMerge.eval_scale, ← atom0561_identity]
  exact mul_nonneg (by norm_num) (atom0561_nonneg g t z hg hA hB ht hz hw)

def coeff0562 : CoefficientMerge.Poly :=
  [(16449, 1)]
noncomputable def atom0562 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 7) ^ 1)
theorem atom0562_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0562 g t z = CoefficientMerge.eval (monomial g t z) coeff0562 := by
  norm_num [atom0562, coeff0562, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0562_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0562 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0562]
  positivity
theorem weighted0562_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1938685664091271320029969258282814248222809624970156473336429056410091425885441038862182201163785727463669741740546683436024096905849036800 : Int) coeff0562) := by
  rw [CoefficientMerge.eval_scale, ← atom0562_identity]
  exact mul_nonneg (by norm_num) (atom0562_nonneg g t z hg hA hB ht hz hw)

def coeff0563 : CoefficientMerge.Poly :=
  [(262273, 1)]
noncomputable def atom0563 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 2 * (t) ^ 1)
theorem atom0563_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0563 g t z = CoefficientMerge.eval (monomial g t z) coeff0563 := by
  norm_num [atom0563, coeff0563, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0563_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0563 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0563]
  positivity
theorem weighted0563_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2661617767552955332118203256259861715514050709009907771764165866189072297310293660662578341242124523777173173102349200291747118679057756160 : Int) coeff0563) := by
  rw [CoefficientMerge.eval_scale, ← atom0563_identity]
  exact mul_nonneg (by norm_num) (atom0563_nonneg g t z hg hA hB ht hz hw)

def coeff0564 : CoefficientMerge.Poly :=
  [(262465, 1)]
noncomputable def atom0564 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 4) ^ 1 * (t) ^ 1)
theorem atom0564_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0564 g t z = CoefficientMerge.eval (monomial g t z) coeff0564 := by
  norm_num [atom0564, coeff0564, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0564_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0564 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0564]
  positivity
theorem weighted0564_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2521232171391671068549106363613652480646869733573765005078150066797961908559806022323084285726132743191733224948843088837293886473779102720 : Int) coeff0564) := by
  rw [CoefficientMerge.eval_scale, ← atom0564_identity]
  exact mul_nonneg (by norm_num) (atom0564_nonneg g t z hg hA hB ht hz hw)

def sparseBlock059 : CoefficientMerge.Poly :=
  [(129, 4066455932619687921410673035212839516851090830989413414510019615933192899685752065332763713565920986781167294518315905665079479023000535040), (273, 9229305922009214132227333810712285106984622825352697741438323555665293376330287213775078269029748598578004115801462034884176139320385341440), (321, 2853444064045600606232543366824574508982886630556505592889166242410338090044911979280718202259220071479305496537128951708212021550580295680), (1041, 2693885329493025081554090180156270151466661126369079751217103701535707626297192168959900068100163447579071893675927913381740377950482534400), (4113, 5373566792177359693101805283718853938375262569712665127300096245783900953688806458353761224816090003311321861341375887257040376768579420160), (16401, 1076297714185172201482608273079871928081792874512843632393314537519615643706729485510335342588753764193900052436388515013946182735753666560), (16449, 1938685664091271320029969258282814248222809624970156473336429056410091425885441038862182201163785727463669741740546683436024096905849036800), (262177, 1935368248938574311149762889587675526359157956452938368243187555642801300871724305084750061930408041604929875051291996029666666621968416768), (262225, 16220083618451074519174080448957572008066671114563810081806731667481661682529211018389766099086118897005519047576034056253567403985927890944), (262273, 2661617767552955332118203256259861715514050709009907771764165866189072297310293660662578341242124523777173173102349200291747118679057756160), (262417, 18222442130754833267480193335675648769920825858881771819696716425386305948667085845402780212380598782199395797975684370279739707687367914496), (262465, 2521232171391671068549106363613652480646869733573765005078150066797961908559806022323084285726132743191733224948843088837293886473779102720), (263185, 10874702779084168278876896522756070416220869037616398590043527560624380940717171672286919366655497416521789707391556385626290692645196793856), (266257, 8287527431066263622092681708180505472348627357378921804200617878152812430149221286135722147009676690484576506011710383462032141577914777600), (278545, 5784608686564947213035613310329815970236172477835515484860648437833942912008962801079592730582658958036898503496074724907035325798117027840), (1048657, 13334915560740832651247828394350717139772513646254025565134256660380864413334935871848916171546633173430720623436002968500368359137910727680), (1048849, 8716816580561601373023530915577468185114190832422381578255960708743970272984745454862849978908532935451235765016202912425116823281400407808), (1049617, 5325552212678163582809256848013200735636193116548697426006706797970981603578817490605510947542417460785430204465407333465412214979999003776), (1052689, 5040823268469535327959185642830129670452353784817405816870331585915234566851467086502619088038280912940413914236424882073477632072945889280), (1064977, 4266071787981979062830968469567708855895099282375254643241736621886347644063382671166731604621561454739300785214776724576372036123207680000)]
theorem sparseBlock059_data : sparseBlock059 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (9229305922009214132227333810712285106984622825352697741438323555665293376330287213775078269029748598578004115801462034884176139320385341440 : Int) coeff0545) (CoefficientMerge.scale (2693885329493025081554090180156270151466661126369079751217103701535707626297192168959900068100163447579071893675927913381740377950482534400 : Int) coeff0546)) (CoefficientMerge.merge (CoefficientMerge.scale (5373566792177359693101805283718853938375262569712665127300096245783900953688806458353761224816090003311321861341375887257040376768579420160 : Int) coeff0547) (CoefficientMerge.merge (CoefficientMerge.scale (1076297714185172201482608273079871928081792874512843632393314537519615643706729485510335342588753764193900052436388515013946182735753666560 : Int) coeff0548) (CoefficientMerge.scale (1935368248938574311149762889587675526359157956452938368243187555642801300871724305084750061930408041604929875051291996029666666621968416768 : Int) coeff0549)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (16220083618451074519174080448957572008066671114563810081806731667481661682529211018389766099086118897005519047576034056253567403985927890944 : Int) coeff0550) (CoefficientMerge.scale (18222442130754833267480193335675648769920825858881771819696716425386305948667085845402780212380598782199395797975684370279739707687367914496 : Int) coeff0551)) (CoefficientMerge.merge (CoefficientMerge.scale (10874702779084168278876896522756070416220869037616398590043527560624380940717171672286919366655497416521789707391556385626290692645196793856 : Int) coeff0552) (CoefficientMerge.merge (CoefficientMerge.scale (8287527431066263622092681708180505472348627357378921804200617878152812430149221286135722147009676690484576506011710383462032141577914777600 : Int) coeff0553) (CoefficientMerge.scale (5784608686564947213035613310329815970236172477835515484860648437833942912008962801079592730582658958036898503496074724907035325798117027840 : Int) coeff0554))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (13334915560740832651247828394350717139772513646254025565134256660380864413334935871848916171546633173430720623436002968500368359137910727680 : Int) coeff0555) (CoefficientMerge.scale (8716816580561601373023530915577468185114190832422381578255960708743970272984745454862849978908532935451235765016202912425116823281400407808 : Int) coeff0556)) (CoefficientMerge.merge (CoefficientMerge.scale (5325552212678163582809256848013200735636193116548697426006706797970981603578817490605510947542417460785430204465407333465412214979999003776 : Int) coeff0557) (CoefficientMerge.merge (CoefficientMerge.scale (5040823268469535327959185642830129670452353784817405816870331585915234566851467086502619088038280912940413914236424882073477632072945889280 : Int) coeff0558) (CoefficientMerge.scale (4266071787981979062830968469567708855895099282375254643241736621886347644063382671166731604621561454739300785214776724576372036123207680000 : Int) coeff0559)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (4066455932619687921410673035212839516851090830989413414510019615933192899685752065332763713565920986781167294518315905665079479023000535040 : Int) coeff0560) (CoefficientMerge.scale (2853444064045600606232543366824574508982886630556505592889166242410338090044911979280718202259220071479305496537128951708212021550580295680 : Int) coeff0561)) (CoefficientMerge.merge (CoefficientMerge.scale (1938685664091271320029969258282814248222809624970156473336429056410091425885441038862182201163785727463669741740546683436024096905849036800 : Int) coeff0562) (CoefficientMerge.merge (CoefficientMerge.scale (2661617767552955332118203256259861715514050709009907771764165866189072297310293660662578341242124523777173173102349200291747118679057756160 : Int) coeff0563) (CoefficientMerge.scale (2521232171391671068549106363613652480646869733573765005078150066797961908559806022323084285726132743191733224948843088837293886473779102720 : Int) coeff0564)))))) := by decide +kernel
theorem sparseBlock059_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock059 := by
  rw [sparseBlock059_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted0545_nonneg g t z hg hA hB ht hz hw) (weighted0546_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0547_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0548_nonneg g t z hg hA hB ht hz hw) (weighted0549_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0550_nonneg g t z hg hA hB ht hz hw) (weighted0551_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0552_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0553_nonneg g t z hg hA hB ht hz hw) (weighted0554_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted0555_nonneg g t z hg hA hB ht hz hw) (weighted0556_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0557_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0558_nonneg g t z hg hA hB ht hz hw) (weighted0559_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0560_nonneg g t z hg hA hB ht hz hw) (weighted0561_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0562_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0563_nonneg g t z hg hA hB ht hz hw) (weighted0564_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
