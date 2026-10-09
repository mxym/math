import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff1505 : CoefficientMerge.Poly :=
  [(2424852, 1)]
noncomputable def atom1505 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1505_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1505 g t z = CoefficientMerge.eval (monomial g t z) coeff1505 := by
  norm_num [atom1505, coeff1505, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1505_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1505 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1505]
  positivity
theorem weighted1505_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (85114126150042666058525237596207669345715752017414872018674531009455799461812612848304827284360516998374519659561344947647125425405701120 : Int) coeff1505) := by
  rw [CoefficientMerge.eval_scale, ← atom1505_identity]
  exact mul_nonneg (by norm_num) (atom1505_nonneg g t z hg hA hB ht hz hw)

def coeff1506 : CoefficientMerge.Poly :=
  [(786564, 1)]
noncomputable def atom1506 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 2 * (t) ^ 3)
theorem atom1506_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1506 g t z = CoefficientMerge.eval (monomial g t z) coeff1506 := by
  norm_num [atom1506, coeff1506, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1506_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1506 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1506]
  positivity
theorem weighted1506_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (26172491812027816327175655714003309244980288302371170603430410897664945537097231862641940249292728969326577658461863688376340113466388480 : Int) coeff1506) := by
  rw [CoefficientMerge.eval_scale, ← atom1506_identity]
  exact mul_nonneg (by norm_num) (atom1506_nonneg g t z hg hA hB ht hz hw)

def coeff1507 : CoefficientMerge.Poly :=
  [(1572996, 1)]
noncomputable def atom1507 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 2 * (t) ^ 2 * (z) ^ 1)
theorem atom1507_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1507 g t z = CoefficientMerge.eval (monomial g t z) coeff1507 := by
  norm_num [atom1507, coeff1507, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1507_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1507 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1507]
  positivity
theorem weighted1507_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (76393095252594673391127619474534786724937906271830031427596799666819764756300581035734540742802807671964996377943768448183970071703401344 : Int) coeff1507) := by
  rw [CoefficientMerge.eval_scale, ← atom1507_identity]
  exact mul_nonneg (by norm_num) (atom1507_nonneg g t z hg hA hB ht hz hw)

def coeff1508 : CoefficientMerge.Poly :=
  [(2359428, 1)]
noncomputable def atom1508 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 2 * (t) ^ 1 * (z) ^ 2)
theorem atom1508_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1508 g t z = CoefficientMerge.eval (monomial g t z) coeff1508 := by
  norm_num [atom1508, coeff1508, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1508_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1508 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1508]
  positivity
theorem weighted1508_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (94697792286784020291917367161079528406732831329171961554253851303625985852542192199135019784751012382552047215113175061909874558575017728 : Int) coeff1508) := by
  rw [CoefficientMerge.eval_scale, ← atom1508_identity]
  exact mul_nonneg (by norm_num) (atom1508_nonneg g t z hg hA hB ht hz hw)

def coeff1509 : CoefficientMerge.Poly :=
  [(786756, 1)]
noncomputable def atom1509 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 4) ^ 1 * (t) ^ 3)
theorem atom1509_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1509 g t z = CoefficientMerge.eval (monomial g t z) coeff1509 := by
  norm_num [atom1509, coeff1509, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1509_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1509 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1509]
  positivity
theorem weighted1509_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (88158565491290531876033390263756024097136253552742912672854176812877089013432985899686613119951484311418292418405766065300859237613704960 : Int) coeff1509) := by
  rw [CoefficientMerge.eval_scale, ← atom1509_identity]
  exact mul_nonneg (by norm_num) (atom1509_nonneg g t z hg hA hB ht hz hw)

def coeff1510 : CoefficientMerge.Poly :=
  [(1573188, 1)]
noncomputable def atom1510 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 4) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1510_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1510 g t z = CoefficientMerge.eval (monomial g t z) coeff1510 := by
  norm_num [atom1510, coeff1510, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1510_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1510 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1510]
  positivity
theorem weighted1510_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (213679799091517321759255492491264110816004362848517282145639160471301936255700535892884442756855388918795180988577472519931539031661412288 : Int) coeff1510) := by
  rw [CoefficientMerge.eval_scale, ← atom1510_identity]
  exact mul_nonneg (by norm_num) (atom1510_nonneg g t z hg hA hB ht hz hw)

def coeff1511 : CoefficientMerge.Poly :=
  [(2359620, 1)]
noncomputable def atom1511 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 4) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1511_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1511 g t z = CoefficientMerge.eval (monomial g t z) coeff1511 := by
  norm_num [atom1511, coeff1511, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1511_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1511 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1511]
  positivity
theorem weighted1511_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (174148510449624013385602325401839843937574864103195847180211846533442435417110122477427584297225433466346358084934518978030601972789981376 : Int) coeff1511) := by
  rw [CoefficientMerge.eval_scale, ← atom1511_identity]
  exact mul_nonneg (by norm_num) (atom1511_nonneg g t z hg hA hB ht hz hw)

def coeff1512 : CoefficientMerge.Poly :=
  [(787524, 1)]
noncomputable def atom1512 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 5) ^ 1 * (t) ^ 3)
theorem atom1512_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1512 g t z = CoefficientMerge.eval (monomial g t z) coeff1512 := by
  norm_num [atom1512, coeff1512, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1512_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1512 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1512]
  positivity
theorem weighted1512_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (20598236805369384931718238818438851478719313557591508651796007651354615026478549040472771848038075675169653098630126723232886247985152000 : Int) coeff1512) := by
  rw [CoefficientMerge.eval_scale, ← atom1512_identity]
  exact mul_nonneg (by norm_num) (atom1512_nonneg g t z hg hA hB ht hz hw)

def coeff1513 : CoefficientMerge.Poly :=
  [(1573956, 1)]
noncomputable def atom1513 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 5) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1513_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1513 g t z = CoefficientMerge.eval (monomial g t z) coeff1513 := by
  norm_num [atom1513, coeff1513, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1513_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1513 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1513]
  positivity
theorem weighted1513_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (50634839138193071955361128275393573733073312619769582285334502748858324157691020497043852811524657373148055707572796244881679601199656256 : Int) coeff1513) := by
  rw [CoefficientMerge.eval_scale, ← atom1513_identity]
  exact mul_nonneg (by norm_num) (atom1513_nonneg g t z hg hA hB ht hz hw)

def coeff1514 : CoefficientMerge.Poly :=
  [(2360388, 1)]
noncomputable def atom1514 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 5) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1514_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1514 g t z = CoefficientMerge.eval (monomial g t z) coeff1514 := by
  norm_num [atom1514, coeff1514, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1514_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1514 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1514]
  positivity
theorem weighted1514_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (39443183898941129212606282555377717026968679401203550614093527971004179228298913583390478950002115603226734990535173361236689522698934912 : Int) coeff1514) := by
  rw [CoefficientMerge.eval_scale, ← atom1514_identity]
  exact mul_nonneg (by norm_num) (atom1514_nonneg g t z hg hA hB ht hz hw)

def coeff1515 : CoefficientMerge.Poly :=
  [(790596, 1)]
noncomputable def atom1515 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 6) ^ 1 * (t) ^ 3)
theorem atom1515_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1515 g t z = CoefficientMerge.eval (monomial g t z) coeff1515 := by
  norm_num [atom1515, coeff1515, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1515_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1515 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1515]
  positivity
theorem weighted1515_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (26012217520875161899971738949684517467237117916732180390325561249462341794235363431459804919931988340594948431034147387318371629136104960 : Int) coeff1515) := by
  rw [CoefficientMerge.eval_scale, ← atom1515_identity]
  exact mul_nonneg (by norm_num) (atom1515_nonneg g t z hg hA hB ht hz hw)

def coeff1516 : CoefficientMerge.Poly :=
  [(1577028, 1)]
noncomputable def atom1516 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 6) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1516_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1516 g t z = CoefficientMerge.eval (monomial g t z) coeff1516 := by
  norm_num [atom1516, coeff1516, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1516_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1516 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1516]
  positivity
theorem weighted1516_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (63788790566808548721585153120497342274441006950123730545659873946080634652866649883650851922864401473870984101189144598845572583507255360 : Int) coeff1516) := by
  rw [CoefficientMerge.eval_scale, ← atom1516_identity]
  exact mul_nonneg (by norm_num) (atom1516_nonneg g t z hg hA hB ht hz hw)

def coeff1517 : CoefficientMerge.Poly :=
  [(2363460, 1)]
noncomputable def atom1517 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1517_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1517 g t z = CoefficientMerge.eval (monomial g t z) coeff1517 := by
  norm_num [atom1517, coeff1517, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1517_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1517 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1517]
  positivity
theorem weighted1517_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (47980022379330882920396509617133798045900219185670014299219495635375785375186148724437849545552024976293875822717597680548546694806656640 : Int) coeff1517) := by
  rw [CoefficientMerge.eval_scale, ← atom1517_identity]
  exact mul_nonneg (by norm_num) (atom1517_nonneg g t z hg hA hB ht hz hw)

def coeff1518 : CoefficientMerge.Poly :=
  [(802884, 1)]
noncomputable def atom1518 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 7) ^ 1 * (t) ^ 3)
theorem atom1518_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1518 g t z = CoefficientMerge.eval (monomial g t z) coeff1518 := by
  norm_num [atom1518, coeff1518, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1518_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1518 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1518]
  positivity
theorem weighted1518_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (20082167053472978063931476659625982704206507408076654299558460478025273634546759444579227830968864940150740056398153150656376103262223360 : Int) coeff1518) := by
  rw [CoefficientMerge.eval_scale, ← atom1518_identity]
  exact mul_nonneg (by norm_num) (atom1518_nonneg g t z hg hA hB ht hz hw)

def coeff1519 : CoefficientMerge.Poly :=
  [(1589316, 1)]
noncomputable def atom1519 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 7) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1519_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1519 g t z = CoefficientMerge.eval (monomial g t z) coeff1519 := by
  norm_num [atom1519, coeff1519, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1519_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1519 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1519]
  positivity
theorem weighted1519_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (57683651547455087561279204514776075822474135943531140087375809100701030758074544358591925900115533630654882465656892870293167642106674240 : Int) coeff1519) := by
  rw [CoefficientMerge.eval_scale, ← atom1519_identity]
  exact mul_nonneg (by norm_num) (atom1519_nonneg g t z hg hA hB ht hz hw)

def coeff1520 : CoefficientMerge.Poly :=
  [(2375748, 1)]
noncomputable def atom1520 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1520_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1520 g t z = CoefficientMerge.eval (monomial g t z) coeff1520 := by
  norm_num [atom1520, coeff1520, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1520_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1520 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1520]
  positivity
theorem weighted1520_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (53790465414800683227594452036374448292113781547162185184367340735988992446938722576484420453349855425110409098300974260163822733934054800 : Int) coeff1520) := by
  rw [CoefficientMerge.eval_scale, ← atom1520_identity]
  exact mul_nonneg (by norm_num) (atom1520_nonneg g t z hg hA hB ht hz hw)

def coeff1521 : CoefficientMerge.Poly :=
  [(852036, 1)]
noncomputable def atom1521 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 8) ^ 1 * (t) ^ 3)
theorem atom1521_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1521 g t z = CoefficientMerge.eval (monomial g t z) coeff1521 := by
  norm_num [atom1521, coeff1521, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1521_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1521 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1521]
  positivity
theorem weighted1521_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (14386496813169987438991853913208635799607712898319468180890399262399592266146416247279471366628603411187699597483412542901061183927961600 : Int) coeff1521) := by
  rw [CoefficientMerge.eval_scale, ← atom1521_identity]
  exact mul_nonneg (by norm_num) (atom1521_nonneg g t z hg hA hB ht hz hw)

def coeff1522 : CoefficientMerge.Poly :=
  [(1638468, 1)]
noncomputable def atom1522 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 8) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1522_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1522 g t z = CoefficientMerge.eval (monomial g t z) coeff1522 := by
  norm_num [atom1522, coeff1522, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1522_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1522 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1522]
  positivity
theorem weighted1522_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (38171120988763710882100530061852588242788179952970756499737729918431999059440424930556107180409903027509326613556118414923565121541098560 : Int) coeff1522) := by
  rw [CoefficientMerge.eval_scale, ← atom1522_identity]
  exact mul_nonneg (by norm_num) (atom1522_nonneg g t z hg hA hB ht hz hw)

def coeff1523 : CoefficientMerge.Poly :=
  [(2424900, 1)]
noncomputable def atom1523 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1523_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1523 g t z = CoefficientMerge.eval (monomial g t z) coeff1523 := by
  norm_num [atom1523, coeff1523, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1523_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1523 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1523]
  positivity
theorem weighted1523_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (59853097615427306578383515994483736188484371035181351832780464352376884842408921850390644270351881901185139450291703836670245702106899840 : Int) coeff1523) := by
  rw [CoefficientMerge.eval_scale, ← atom1523_identity]
  exact mul_nonneg (by norm_num) (atom1523_nonneg g t z hg hA hB ht hz hw)

def coeff1524 : CoefficientMerge.Poly :=
  [(786948, 1)]
noncomputable def atom1524 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 2 * (t) ^ 3)
theorem atom1524_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1524 g t z = CoefficientMerge.eval (monomial g t z) coeff1524 := by
  norm_num [atom1524, coeff1524, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1524_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1524 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1524]
  positivity
theorem weighted1524_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (23214837101385609711944297773513847130639108326621650510367273492030942570860940755287294557865388595977736092184790958575221118868377600 : Int) coeff1524) := by
  rw [CoefficientMerge.eval_scale, ← atom1524_identity]
  exact mul_nonneg (by norm_num) (atom1524_nonneg g t z hg hA hB ht hz hw)

def sparseBlock107 : CoefficientMerge.Poly :=
  [(786564, 26172491812027816327175655714003309244980288302371170603430410897664945537097231862641940249292728969326577658461863688376340113466388480), (786756, 88158565491290531876033390263756024097136253552742912672854176812877089013432985899686613119951484311418292418405766065300859237613704960), (786948, 23214837101385609711944297773513847130639108326621650510367273492030942570860940755287294557865388595977736092184790958575221118868377600), (787524, 20598236805369384931718238818438851478719313557591508651796007651354615026478549040472771848038075675169653098630126723232886247985152000), (790596, 26012217520875161899971738949684517467237117916732180390325561249462341794235363431459804919931988340594948431034147387318371629136104960), (802884, 20082167053472978063931476659625982704206507408076654299558460478025273634546759444579227830968864940150740056398153150656376103262223360), (852036, 14386496813169987438991853913208635799607712898319468180890399262399592266146416247279471366628603411187699597483412542901061183927961600), (1572996, 76393095252594673391127619474534786724937906271830031427596799666819764756300581035734540742802807671964996377943768448183970071703401344), (1573188, 213679799091517321759255492491264110816004362848517282145639160471301936255700535892884442756855388918795180988577472519931539031661412288), (1573956, 50634839138193071955361128275393573733073312619769582285334502748858324157691020497043852811524657373148055707572796244881679601199656256), (1577028, 63788790566808548721585153120497342274441006950123730545659873946080634652866649883650851922864401473870984101189144598845572583507255360), (1589316, 57683651547455087561279204514776075822474135943531140087375809100701030758074544358591925900115533630654882465656892870293167642106674240), (1638468, 38171120988763710882100530061852588242788179952970756499737729918431999059440424930556107180409903027509326613556118414923565121541098560), (2359428, 94697792286784020291917367161079528406732831329171961554253851303625985852542192199135019784751012382552047215113175061909874558575017728), (2359620, 174148510449624013385602325401839843937574864103195847180211846533442435417110122477427584297225433466346358084934518978030601972789981376), (2360388, 39443183898941129212606282555377717026968679401203550614093527971004179228298913583390478950002115603226734990535173361236689522698934912), (2363460, 47980022379330882920396509617133798045900219185670014299219495635375785375186148724437849545552024976293875822717597680548546694806656640), (2375748, 53790465414800683227594452036374448292113781547162185184367340735988992446938722576484420453349855425110409098300974260163822733934054800), (2424852, 85114126150042666058525237596207669345715752017414872018674531009455799461812612848304827284360516998374519659561344947647125425405701120), (2424900, 59853097615427306578383515994483736188484371035181351832780464352376884842408921850390644270351881901185139450291703836670245702106899840)]
theorem sparseBlock107_data : sparseBlock107 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (85114126150042666058525237596207669345715752017414872018674531009455799461812612848304827284360516998374519659561344947647125425405701120 : Int) coeff1505) (CoefficientMerge.scale (26172491812027816327175655714003309244980288302371170603430410897664945537097231862641940249292728969326577658461863688376340113466388480 : Int) coeff1506)) (CoefficientMerge.merge (CoefficientMerge.scale (76393095252594673391127619474534786724937906271830031427596799666819764756300581035734540742802807671964996377943768448183970071703401344 : Int) coeff1507) (CoefficientMerge.merge (CoefficientMerge.scale (94697792286784020291917367161079528406732831329171961554253851303625985852542192199135019784751012382552047215113175061909874558575017728 : Int) coeff1508) (CoefficientMerge.scale (88158565491290531876033390263756024097136253552742912672854176812877089013432985899686613119951484311418292418405766065300859237613704960 : Int) coeff1509)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (213679799091517321759255492491264110816004362848517282145639160471301936255700535892884442756855388918795180988577472519931539031661412288 : Int) coeff1510) (CoefficientMerge.scale (174148510449624013385602325401839843937574864103195847180211846533442435417110122477427584297225433466346358084934518978030601972789981376 : Int) coeff1511)) (CoefficientMerge.merge (CoefficientMerge.scale (20598236805369384931718238818438851478719313557591508651796007651354615026478549040472771848038075675169653098630126723232886247985152000 : Int) coeff1512) (CoefficientMerge.merge (CoefficientMerge.scale (50634839138193071955361128275393573733073312619769582285334502748858324157691020497043852811524657373148055707572796244881679601199656256 : Int) coeff1513) (CoefficientMerge.scale (39443183898941129212606282555377717026968679401203550614093527971004179228298913583390478950002115603226734990535173361236689522698934912 : Int) coeff1514))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (26012217520875161899971738949684517467237117916732180390325561249462341794235363431459804919931988340594948431034147387318371629136104960 : Int) coeff1515) (CoefficientMerge.scale (63788790566808548721585153120497342274441006950123730545659873946080634652866649883650851922864401473870984101189144598845572583507255360 : Int) coeff1516)) (CoefficientMerge.merge (CoefficientMerge.scale (47980022379330882920396509617133798045900219185670014299219495635375785375186148724437849545552024976293875822717597680548546694806656640 : Int) coeff1517) (CoefficientMerge.merge (CoefficientMerge.scale (20082167053472978063931476659625982704206507408076654299558460478025273634546759444579227830968864940150740056398153150656376103262223360 : Int) coeff1518) (CoefficientMerge.scale (57683651547455087561279204514776075822474135943531140087375809100701030758074544358591925900115533630654882465656892870293167642106674240 : Int) coeff1519)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (53790465414800683227594452036374448292113781547162185184367340735988992446938722576484420453349855425110409098300974260163822733934054800 : Int) coeff1520) (CoefficientMerge.scale (14386496813169987438991853913208635799607712898319468180890399262399592266146416247279471366628603411187699597483412542901061183927961600 : Int) coeff1521)) (CoefficientMerge.merge (CoefficientMerge.scale (38171120988763710882100530061852588242788179952970756499737729918431999059440424930556107180409903027509326613556118414923565121541098560 : Int) coeff1522) (CoefficientMerge.merge (CoefficientMerge.scale (59853097615427306578383515994483736188484371035181351832780464352376884842408921850390644270351881901185139450291703836670245702106899840 : Int) coeff1523) (CoefficientMerge.scale (23214837101385609711944297773513847130639108326621650510367273492030942570860940755287294557865388595977736092184790958575221118868377600 : Int) coeff1524)))))) := by decide +kernel
theorem sparseBlock107_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock107 := by
  rw [sparseBlock107_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted1505_nonneg g t z hg hA hB ht hz hw) (weighted1506_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1507_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1508_nonneg g t z hg hA hB ht hz hw) (weighted1509_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1510_nonneg g t z hg hA hB ht hz hw) (weighted1511_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1512_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1513_nonneg g t z hg hA hB ht hz hw) (weighted1514_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted1515_nonneg g t z hg hA hB ht hz hw) (weighted1516_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1517_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1518_nonneg g t z hg hA hB ht hz hw) (weighted1519_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1520_nonneg g t z hg hA hB ht hz hw) (weighted1521_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1522_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1523_nonneg g t z hg hA hB ht hz hw) (weighted1524_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
