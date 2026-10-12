import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff1545 : CoefficientMerge.Poly :=
  [(803844, 1)]
noncomputable def atom1545 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (t) ^ 3)
theorem atom1545_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1545 g t z = CoefficientMerge.eval (monomial g t z) coeff1545 := by
  norm_num [atom1545, coeff1545, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1545_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1545 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1545]
  positivity
theorem weighted1545_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4122799525164451203686037574047220817050292940752437973189918514920776211189235966329289568576225857181057962984918625908342759520012800 : Int) coeff1545) := by
  rw [CoefficientMerge.eval_scale, ← atom1545_identity]
  exact mul_nonneg (by norm_num) (atom1545_nonneg g t z hg hA hB ht hz hw)

def coeff1546 : CoefficientMerge.Poly :=
  [(1590276, 1)]
noncomputable def atom1546 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1546_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1546 g t z = CoefficientMerge.eval (monomial g t z) coeff1546 := by
  norm_num [atom1546, coeff1546, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1546_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1546 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1546]
  positivity
theorem weighted1546_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (9436151095432208088119253535583838996617425688061593346041502048828230867393638247779973501970535865298189977843271967855373388753638400 : Int) coeff1546) := by
  rw [CoefficientMerge.eval_scale, ← atom1546_identity]
  exact mul_nonneg (by norm_num) (atom1546_nonneg g t z hg hA hB ht hz hw)

def coeff1547 : CoefficientMerge.Poly :=
  [(2376708, 1)]
noncomputable def atom1547 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1547_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1547 g t z = CoefficientMerge.eval (monomial g t z) coeff1547 := by
  norm_num [atom1547, coeff1547, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1547_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1547 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1547]
  positivity
theorem weighted1547_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3288698005195661694391161714250537474588602816176255952376369493383285752363460624863844141168594818340699233177346741924106800922806800 : Int) coeff1547) := by
  rw [CoefficientMerge.eval_scale, ← atom1547_identity]
  exact mul_nonneg (by norm_num) (atom1547_nonneg g t z hg hA hB ht hz hw)

def coeff1548 : CoefficientMerge.Poly :=
  [(852996, 1)]
noncomputable def atom1548 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (t) ^ 3)
theorem atom1548_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1548 g t z = CoefficientMerge.eval (monomial g t z) coeff1548 := by
  norm_num [atom1548, coeff1548, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1548_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1548 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1548]
  positivity
theorem weighted1548_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (9034062556777350684178757746653040718913567968993947923811120349080378503093632551321431663290380647158672076879966196566519436348070400 : Int) coeff1548) := by
  rw [CoefficientMerge.eval_scale, ← atom1548_identity]
  exact mul_nonneg (by norm_num) (atom1548_nonneg g t z hg hA hB ht hz hw)

def coeff1549 : CoefficientMerge.Poly :=
  [(1639428, 1)]
noncomputable def atom1549 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1549_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1549 g t z = CoefficientMerge.eval (monomial g t z) coeff1549 := by
  norm_num [atom1549, coeff1549, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1549_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1549 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1549]
  positivity
theorem weighted1549_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (16790749098999189438876384216322978271686797473217075264867501172615763329996901318316504778572055783100434241775936665251921185412459200 : Int) coeff1549) := by
  rw [CoefficientMerge.eval_scale, ← atom1549_identity]
  exact mul_nonneg (by norm_num) (atom1549_nonneg g t z hg hA hB ht hz hw)

def coeff1550 : CoefficientMerge.Poly :=
  [(2425860, 1)]
noncomputable def atom1550 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1550_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1550 g t z = CoefficientMerge.eval (monomial g t z) coeff1550 := by
  norm_num [atom1550, coeff1550, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1550_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1550 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1550]
  positivity
theorem weighted1550_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (14792445981117277294830275953327801522118105191035680486342503990542749614180807107857426340240748992966826718381883575715985537108059660 : Int) coeff1550) := by
  rw [CoefficientMerge.eval_scale, ← atom1550_identity]
  exact mul_nonneg (by norm_num) (atom1550_nonneg g t z hg hA hB ht hz hw)

def coeff1551 : CoefficientMerge.Poly :=
  [(794628, 1)]
noncomputable def atom1551 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 6) ^ 2 * (t) ^ 3)
theorem atom1551_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1551 g t z = CoefficientMerge.eval (monomial g t z) coeff1551 := by
  norm_num [atom1551, coeff1551, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1551_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1551 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1551]
  positivity
theorem weighted1551_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (14131002411967512565632522683064115755270554446595617181788789980529299937340013815337546112479851201707944716036859345250782568071648000 : Int) coeff1551) := by
  rw [CoefficientMerge.eval_scale, ← atom1551_identity]
  exact mul_nonneg (by norm_num) (atom1551_nonneg g t z hg hA hB ht hz hw)

def coeff1552 : CoefficientMerge.Poly :=
  [(1581060, 1)]
noncomputable def atom1552 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 6) ^ 2 * (t) ^ 2 * (z) ^ 1)
theorem atom1552_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1552 g t z = CoefficientMerge.eval (monomial g t z) coeff1552 := by
  norm_num [atom1552, coeff1552, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1552_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1552 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1552]
  positivity
theorem weighted1552_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (26506762618097867380006979885923575718787057748937361935755468073182707968777235120546189969328179274049192139398438143009531311468601600 : Int) coeff1552) := by
  rw [CoefficientMerge.eval_scale, ← atom1552_identity]
  exact mul_nonneg (by norm_num) (atom1552_nonneg g t z hg hA hB ht hz hw)

def coeff1553 : CoefficientMerge.Poly :=
  [(2367492, 1)]
noncomputable def atom1553 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 6) ^ 2 * (t) ^ 1 * (z) ^ 2)
theorem atom1553_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1553 g t z = CoefficientMerge.eval (monomial g t z) coeff1553 := by
  norm_num [atom1553, coeff1553, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1553_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1553 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1553]
  positivity
theorem weighted1553_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (11870193113293819354533649762712344545977879910592767895530559616982070748455634177117253690986194197257113145075607713058202566534336000 : Int) coeff1553) := by
  rw [CoefficientMerge.eval_scale, ← atom1553_identity]
  exact mul_nonneg (by norm_num) (atom1553_nonneg g t z hg hA hB ht hz hw)

def coeff1554 : CoefficientMerge.Poly :=
  [(806916, 1)]
noncomputable def atom1554 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (t) ^ 3)
theorem atom1554_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1554 g t z = CoefficientMerge.eval (monomial g t z) coeff1554 := by
  norm_num [atom1554, coeff1554, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1554_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1554 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1554]
  positivity
theorem weighted1554_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1119476115509426698518215138680791980532645736281897007771358512323028649146604042604409129733852575058767903864386954151046981190892800 : Int) coeff1554) := by
  rw [CoefficientMerge.eval_scale, ← atom1554_identity]
  exact mul_nonneg (by norm_num) (atom1554_nonneg g t z hg hA hB ht hz hw)

def coeff1555 : CoefficientMerge.Poly :=
  [(856068, 1)]
noncomputable def atom1555 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (t) ^ 3)
theorem atom1555_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1555 g t z = CoefficientMerge.eval (monomial g t z) coeff1555 := by
  norm_num [atom1555, coeff1555, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1555_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1555 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1555]
  positivity
theorem weighted1555_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (17163017853221353605259007255359811457656277915386536762962221891006365753802645361952902345952445991627931802200756025037672111706694400 : Int) coeff1555) := by
  rw [CoefficientMerge.eval_scale, ← atom1555_identity]
  exact mul_nonneg (by norm_num) (atom1555_nonneg g t z hg hA hB ht hz hw)

def coeff1556 : CoefficientMerge.Poly :=
  [(1642500, 1)]
noncomputable def atom1556 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1556_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1556 g t z = CoefficientMerge.eval (monomial g t z) coeff1556 := by
  norm_num [atom1556, coeff1556, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1556_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1556 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1556]
  positivity
theorem weighted1556_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (30886975259593217972802199330834439921894723993265180292804751593963615235094764011944581603197314518666155407014783333407561932480441600 : Int) coeff1556) := by
  rw [CoefficientMerge.eval_scale, ← atom1556_identity]
  exact mul_nonneg (by norm_num) (atom1556_nonneg g t z hg hA hB ht hz hw)

def coeff1557 : CoefficientMerge.Poly :=
  [(2428932, 1)]
noncomputable def atom1557 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1557_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1557 g t z = CoefficientMerge.eval (monomial g t z) coeff1557 := by
  norm_num [atom1557, coeff1557, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1557_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1557 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1557]
  positivity
theorem weighted1557_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (23801666618346881008232586777491164138649943271139752421352601776434698336470877128840712311401211951816643048813668134417686037253129600 : Int) coeff1557) := by
  rw [CoefficientMerge.eval_scale, ← atom1557_identity]
  exact mul_nonneg (by norm_num) (atom1557_nonneg g t z hg hA hB ht hz hw)

def coeff1558 : CoefficientMerge.Poly :=
  [(786465, 1)]
noncomputable def atom1558 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 2 * (t) ^ 3)
theorem atom1558_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1558 g t z = CoefficientMerge.eval (monomial g t z) coeff1558 := by
  norm_num [atom1558, coeff1558, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1558_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1558 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1558]
  positivity
theorem weighted1558_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (61544167597240452212354526238443950353490567286056237893568246929532537464138022013146649120444287364621024232006717090945763921939742720 : Int) coeff1558) := by
  rw [CoefficientMerge.eval_scale, ← atom1558_identity]
  exact mul_nonneg (by norm_num) (atom1558_nonneg g t z hg hA hB ht hz hw)

def coeff1559 : CoefficientMerge.Poly :=
  [(1572897, 1)]
noncomputable def atom1559 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 2 * (t) ^ 2 * (z) ^ 1)
theorem atom1559_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1559 g t z = CoefficientMerge.eval (monomial g t z) coeff1559 := by
  norm_num [atom1559, coeff1559, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1559_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1559 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1559]
  positivity
theorem weighted1559_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (84059059686071192289162549693628382843571473116610087446893437863907899185589560366253302739260664801900004925298984389540225238372638720 : Int) coeff1559) := by
  rw [CoefficientMerge.eval_scale, ← atom1559_identity]
  exact mul_nonneg (by norm_num) (atom1559_nonneg g t z hg hA hB ht hz hw)

def coeff1560 : CoefficientMerge.Poly :=
  [(2359329, 1)]
noncomputable def atom1560 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 2) ^ 2 * (t) ^ 1 * (z) ^ 2)
theorem atom1560_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1560 g t z = CoefficientMerge.eval (monomial g t z) coeff1560 := by
  norm_num [atom1560, coeff1560, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1560_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1560 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1560]
  positivity
theorem weighted1560_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (73092586887959226993797153191419483016003385270021781576895927999623726258701537190026902300373434683595551824327985396944973442008268800 : Int) coeff1560) := by
  rw [CoefficientMerge.eval_scale, ← atom1560_identity]
  exact mul_nonneg (by norm_num) (atom1560_nonneg g t z hg hA hB ht hz hw)

def coeff1561 : CoefficientMerge.Poly :=
  [(786468, 1)]
noncomputable def atom1561 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 2 * (t) ^ 3)
theorem atom1561_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1561 g t z = CoefficientMerge.eval (monomial g t z) coeff1561 := by
  norm_num [atom1561, coeff1561, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1561_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1561 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1561]
  positivity
theorem weighted1561_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (124321857339914507802694053498059721983114467027626296464647837266233701439714653828196004387220061618665192615491318587346480673416601600 : Int) coeff1561) := by
  rw [CoefficientMerge.eval_scale, ← atom1561_identity]
  exact mul_nonneg (by norm_num) (atom1561_nonneg g t z hg hA hB ht hz hw)

def coeff1562 : CoefficientMerge.Poly :=
  [(1572900, 1)]
noncomputable def atom1562 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 2 * (t) ^ 2 * (z) ^ 1)
theorem atom1562_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1562 g t z = CoefficientMerge.eval (monomial g t z) coeff1562 := by
  norm_num [atom1562, coeff1562, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1562_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1562 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1562]
  positivity
theorem weighted1562_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (140843935852634710864683146182592738904020206669958749723655975764108409084908866097454006477771478875080903364080821732115004018945433600 : Int) coeff1562) := by
  rw [CoefficientMerge.eval_scale, ← atom1562_identity]
  exact mul_nonneg (by norm_num) (atom1562_nonneg g t z hg hA hB ht hz hw)

def coeff1563 : CoefficientMerge.Poly :=
  [(2359332, 1)]
noncomputable def atom1563 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 2 * (t) ^ 1 * (z) ^ 2)
theorem atom1563_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1563 g t z = CoefficientMerge.eval (monomial g t z) coeff1563 := by
  norm_num [atom1563, coeff1563, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1563_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1563 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1563]
  positivity
theorem weighted1563_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (118283198097198409873279687256291682537729655763481407978580509354050917155291482403861829720079539224031811977546032274410613687626360832 : Int) coeff1563) := by
  rw [CoefficientMerge.eval_scale, ← atom1563_identity]
  exact mul_nonneg (by norm_num) (atom1563_nonneg g t z hg hA hB ht hz hw)

def coeff1564 : CoefficientMerge.Poly :=
  [(3211344, 1)]
noncomputable def atom1564 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 8) ^ 1 * (z) ^ 3)
theorem atom1564_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1564 g t z = CoefficientMerge.eval (monomial g t z) coeff1564 := by
  norm_num [atom1564, coeff1564, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1564_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1564 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1564]
  positivity
theorem weighted1564_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (66391135464033672631375715175457989255797774743704733222986713528558620605163426309299692895027483804336030894707395888362136972714484160 : Int) coeff1564) := by
  rw [CoefficientMerge.eval_scale, ← atom1564_identity]
  exact mul_nonneg (by norm_num) (atom1564_nonneg g t z hg hA hB ht hz hw)

def sparseBlock109 : CoefficientMerge.Poly :=
  [(786465, 61544167597240452212354526238443950353490567286056237893568246929532537464138022013146649120444287364621024232006717090945763921939742720), (786468, 124321857339914507802694053498059721983114467027626296464647837266233701439714653828196004387220061618665192615491318587346480673416601600), (794628, 14131002411967512565632522683064115755270554446595617181788789980529299937340013815337546112479851201707944716036859345250782568071648000), (803844, 4122799525164451203686037574047220817050292940752437973189918514920776211189235966329289568576225857181057962984918625908342759520012800), (806916, 1119476115509426698518215138680791980532645736281897007771358512323028649146604042604409129733852575058767903864386954151046981190892800), (852996, 9034062556777350684178757746653040718913567968993947923811120349080378503093632551321431663290380647158672076879966196566519436348070400), (856068, 17163017853221353605259007255359811457656277915386536762962221891006365753802645361952902345952445991627931802200756025037672111706694400), (1572897, 84059059686071192289162549693628382843571473116610087446893437863907899185589560366253302739260664801900004925298984389540225238372638720), (1572900, 140843935852634710864683146182592738904020206669958749723655975764108409084908866097454006477771478875080903364080821732115004018945433600), (1581060, 26506762618097867380006979885923575718787057748937361935755468073182707968777235120546189969328179274049192139398438143009531311468601600), (1590276, 9436151095432208088119253535583838996617425688061593346041502048828230867393638247779973501970535865298189977843271967855373388753638400), (1639428, 16790749098999189438876384216322978271686797473217075264867501172615763329996901318316504778572055783100434241775936665251921185412459200), (1642500, 30886975259593217972802199330834439921894723993265180292804751593963615235094764011944581603197314518666155407014783333407561932480441600), (2359329, 73092586887959226993797153191419483016003385270021781576895927999623726258701537190026902300373434683595551824327985396944973442008268800), (2359332, 118283198097198409873279687256291682537729655763481407978580509354050917155291482403861829720079539224031811977546032274410613687626360832), (2367492, 11870193113293819354533649762712344545977879910592767895530559616982070748455634177117253690986194197257113145075607713058202566534336000), (2376708, 3288698005195661694391161714250537474588602816176255952376369493383285752363460624863844141168594818340699233177346741924106800922806800), (2425860, 14792445981117277294830275953327801522118105191035680486342503990542749614180807107857426340240748992966826718381883575715985537108059660), (2428932, 23801666618346881008232586777491164138649943271139752421352601776434698336470877128840712311401211951816643048813668134417686037253129600), (3211344, 66391135464033672631375715175457989255797774743704733222986713528558620605163426309299692895027483804336030894707395888362136972714484160)]
theorem sparseBlock109_data : sparseBlock109 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (4122799525164451203686037574047220817050292940752437973189918514920776211189235966329289568576225857181057962984918625908342759520012800 : Int) coeff1545) (CoefficientMerge.scale (9436151095432208088119253535583838996617425688061593346041502048828230867393638247779973501970535865298189977843271967855373388753638400 : Int) coeff1546)) (CoefficientMerge.merge (CoefficientMerge.scale (3288698005195661694391161714250537474588602816176255952376369493383285752363460624863844141168594818340699233177346741924106800922806800 : Int) coeff1547) (CoefficientMerge.merge (CoefficientMerge.scale (9034062556777350684178757746653040718913567968993947923811120349080378503093632551321431663290380647158672076879966196566519436348070400 : Int) coeff1548) (CoefficientMerge.scale (16790749098999189438876384216322978271686797473217075264867501172615763329996901318316504778572055783100434241775936665251921185412459200 : Int) coeff1549)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (14792445981117277294830275953327801522118105191035680486342503990542749614180807107857426340240748992966826718381883575715985537108059660 : Int) coeff1550) (CoefficientMerge.scale (14131002411967512565632522683064115755270554446595617181788789980529299937340013815337546112479851201707944716036859345250782568071648000 : Int) coeff1551)) (CoefficientMerge.merge (CoefficientMerge.scale (26506762618097867380006979885923575718787057748937361935755468073182707968777235120546189969328179274049192139398438143009531311468601600 : Int) coeff1552) (CoefficientMerge.merge (CoefficientMerge.scale (11870193113293819354533649762712344545977879910592767895530559616982070748455634177117253690986194197257113145075607713058202566534336000 : Int) coeff1553) (CoefficientMerge.scale (1119476115509426698518215138680791980532645736281897007771358512323028649146604042604409129733852575058767903864386954151046981190892800 : Int) coeff1554))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (17163017853221353605259007255359811457656277915386536762962221891006365753802645361952902345952445991627931802200756025037672111706694400 : Int) coeff1555) (CoefficientMerge.scale (30886975259593217972802199330834439921894723993265180292804751593963615235094764011944581603197314518666155407014783333407561932480441600 : Int) coeff1556)) (CoefficientMerge.merge (CoefficientMerge.scale (23801666618346881008232586777491164138649943271139752421352601776434698336470877128840712311401211951816643048813668134417686037253129600 : Int) coeff1557) (CoefficientMerge.merge (CoefficientMerge.scale (61544167597240452212354526238443950353490567286056237893568246929532537464138022013146649120444287364621024232006717090945763921939742720 : Int) coeff1558) (CoefficientMerge.scale (84059059686071192289162549693628382843571473116610087446893437863907899185589560366253302739260664801900004925298984389540225238372638720 : Int) coeff1559)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (73092586887959226993797153191419483016003385270021781576895927999623726258701537190026902300373434683595551824327985396944973442008268800 : Int) coeff1560) (CoefficientMerge.scale (124321857339914507802694053498059721983114467027626296464647837266233701439714653828196004387220061618665192615491318587346480673416601600 : Int) coeff1561)) (CoefficientMerge.merge (CoefficientMerge.scale (140843935852634710864683146182592738904020206669958749723655975764108409084908866097454006477771478875080903364080821732115004018945433600 : Int) coeff1562) (CoefficientMerge.merge (CoefficientMerge.scale (118283198097198409873279687256291682537729655763481407978580509354050917155291482403861829720079539224031811977546032274410613687626360832 : Int) coeff1563) (CoefficientMerge.scale (66391135464033672631375715175457989255797774743704733222986713528558620605163426309299692895027483804336030894707395888362136972714484160 : Int) coeff1564)))))) := by decide +kernel
theorem sparseBlock109_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock109 := by
  rw [sparseBlock109_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted1545_nonneg g t z hg hA hB ht hz hw) (weighted1546_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1547_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1548_nonneg g t z hg hA hB ht hz hw) (weighted1549_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1550_nonneg g t z hg hA hB ht hz hw) (weighted1551_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1552_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1553_nonneg g t z hg hA hB ht hz hw) (weighted1554_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted1555_nonneg g t z hg hA hB ht hz hw) (weighted1556_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1557_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1558_nonneg g t z hg hA hB ht hz hw) (weighted1559_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1560_nonneg g t z hg hA hB ht hz hw) (weighted1561_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1562_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1563_nonneg g t z hg hA hB ht hz hw) (weighted1564_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
