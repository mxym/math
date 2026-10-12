import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff0585 : CoefficientMerge.Poly :=
  [(1052929, 1)]
noncomputable def atom0585 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (z) ^ 1)
theorem atom0585_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0585 g t z = CoefficientMerge.eval (monomial g t z) coeff0585 := by
  norm_num [atom0585, coeff0585, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0585_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0585 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0585]
  positivity
theorem weighted0585_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (7818757403030491013836611586971595043272371137363516115626647141205005367447056716476826820004705053103176415005127519204396038063548442080 : Int) coeff0585) := by
  rw [CoefficientMerge.eval_scale, ← atom0585_identity]
  exact mul_nonneg (by norm_num) (atom0585_nonneg g t z hg hA hB ht hz hw)

def coeff0586 : CoefficientMerge.Poly :=
  [(1065217, 1)]
noncomputable def atom0586 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (z) ^ 1)
theorem atom0586_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0586 g t z = CoefficientMerge.eval (monomial g t z) coeff0586 := by
  norm_num [atom0586, coeff0586, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0586_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0586 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0586]
  positivity
theorem weighted0586_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (6105982752177053254460357814416374986849577379736640842756742052148772238839533211005375531309391719019917605081357752118019971488351492320 : Int) coeff0586) := by
  rw [CoefficientMerge.eval_scale, ← atom0586_identity]
  exact mul_nonneg (by norm_num) (atom0586_nonneg g t z hg hA hB ht hz hw)

def coeff0587 : CoefficientMerge.Poly :=
  [(1114369, 1)]
noncomputable def atom0587 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (z) ^ 1)
theorem atom0587_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0587 g t z = CoefficientMerge.eval (monomial g t z) coeff0587 := by
  norm_num [atom0587, coeff0587, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0587_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0587 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0587]
  positivity
theorem weighted0587_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5634047446058960334377274124267974256613269101854432750608367313847935911212530516622591299007346214379814426168886955724656537438649353440 : Int) coeff0587) := by
  rw [CoefficientMerge.eval_scale, ← atom0587_identity]
  exact mul_nonneg (by norm_num) (atom0587_nonneg g t z hg hA hB ht hz hw)

def coeff0588 : CoefficientMerge.Poly :=
  [(5121, 1)]
noncomputable def atom0588 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1)
theorem atom0588_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0588 g t z = CoefficientMerge.eval (monomial g t z) coeff0588 := by
  norm_num [atom0588, coeff0588, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0588_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0588 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0588]
  positivity
theorem weighted0588_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3373394464075776909763398952107717200445554582483153074604280702629759254864018822347774346195217395374992955856617980158944824050363637760 : Int) coeff0588) := by
  rw [CoefficientMerge.eval_scale, ← atom0588_identity]
  exact mul_nonneg (by norm_num) (atom0588_nonneg g t z hg hA hB ht hz hw)

def coeff0589 : CoefficientMerge.Poly :=
  [(17409, 1)]
noncomputable def atom0589 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1)
theorem atom0589_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0589 g t z = CoefficientMerge.eval (monomial g t z) coeff0589 := by
  norm_num [atom0589, coeff0589, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0589_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0589 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0589]
  positivity
theorem weighted0589_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (8435051750075114189339369383343774223082056505195863703394701332183254539923759216551564225108782862006833925297812516011459716979865681920 : Int) coeff0589) := by
  rw [CoefficientMerge.eval_scale, ← atom0589_identity]
  exact mul_nonneg (by norm_num) (atom0589_nonneg g t z hg hA hB ht hz hw)

def coeff0590 : CoefficientMerge.Poly :=
  [(66561, 1)]
noncomputable def atom0590 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1)
theorem atom0590_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0590 g t z = CoefficientMerge.eval (monomial g t z) coeff0590 := by
  norm_num [atom0590, coeff0590, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0590_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0590 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0590]
  positivity
theorem weighted0590_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (15871555607717052488129997118509029900668790304471811577756204188387209115108318643713541403125829253356012517227338933939660353797508300800 : Int) coeff0590) := by
  rw [CoefficientMerge.eval_scale, ← atom0590_identity]
  exact mul_nonneg (by norm_num) (atom0590_nonneg g t z hg hA hB ht hz hw)

def coeff0591 : CoefficientMerge.Poly :=
  [(267265, 1)]
noncomputable def atom0591 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (t) ^ 1)
theorem atom0591_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0591 g t z = CoefficientMerge.eval (monomial g t z) coeff0591 := by
  norm_num [atom0591, coeff0591, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0591_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0591 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0591]
  positivity
theorem weighted0591_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2687256850533400213293708924926309005789305548251255297257556064783003626274253104039730402038350087088314408832461358837732608460753264640 : Int) coeff0591) := by
  rw [CoefficientMerge.eval_scale, ← atom0591_identity]
  exact mul_nonneg (by norm_num) (atom0591_nonneg g t z hg hA hB ht hz hw)

def coeff0592 : CoefficientMerge.Poly :=
  [(279553, 1)]
noncomputable def atom0592 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (t) ^ 1)
theorem atom0592_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0592 g t z = CoefficientMerge.eval (monomial g t z) coeff0592 := by
  norm_num [atom0592, coeff0592, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0592_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0592 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0592]
  positivity
theorem weighted0592_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1252702612795546126733010941883052627779007705417950934917345287921269344013191583063467810859633533311907989847438886005760237865796833280 : Int) coeff0592) := by
  rw [CoefficientMerge.eval_scale, ← atom0592_identity]
  exact mul_nonneg (by norm_num) (atom0592_nonneg g t z hg hA hB ht hz hw)

def coeff0593 : CoefficientMerge.Poly :=
  [(328705, 1)]
noncomputable def atom0593 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (t) ^ 1)
theorem atom0593_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0593 g t z = CoefficientMerge.eval (monomial g t z) coeff0593 := by
  norm_num [atom0593, coeff0593, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0593_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0593 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0593]
  positivity
theorem weighted0593_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2014126570154167125498484209246783856750682984223246775024391294970128196380200252319676243373476194598430275687790032688339737780059750400 : Int) coeff0593) := by
  rw [CoefficientMerge.eval_scale, ← atom0593_identity]
  exact mul_nonneg (by norm_num) (atom0593_nonneg g t z hg hA hB ht hz hw)

def coeff0594 : CoefficientMerge.Poly :=
  [(1050625, 1)]
noncomputable def atom0594 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 2 * (z) ^ 1)
theorem atom0594_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0594 g t z = CoefficientMerge.eval (monomial g t z) coeff0594 := by
  norm_num [atom0594, coeff0594, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0594_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0594 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0594]
  positivity
theorem weighted0594_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (671198206537487606233737513671011292688071194169836954212520776965276279978272939068064885030288211500286376773925336100045956798522163200 : Int) coeff0594) := by
  rw [CoefficientMerge.eval_scale, ← atom0594_identity]
  exact mul_nonneg (by norm_num) (atom0594_nonneg g t z hg hA hB ht hz hw)

def coeff0595 : CoefficientMerge.Poly :=
  [(1053697, 1)]
noncomputable def atom0595 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (z) ^ 1)
theorem atom0595_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0595 g t z = CoefficientMerge.eval (monomial g t z) coeff0595 := by
  norm_num [atom0595, coeff0595, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0595_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0595 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0595]
  positivity
theorem weighted0595_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (6753713822377785541352331725876171336188600215074227577643212136934205944956911908541258986910390810062283878001676806924932744284729768960 : Int) coeff0595) := by
  rw [CoefficientMerge.eval_scale, ← atom0595_identity]
  exact mul_nonneg (by norm_num) (atom0595_nonneg g t z hg hA hB ht hz hw)

def coeff0596 : CoefficientMerge.Poly :=
  [(1065985, 1)]
noncomputable def atom0596 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (z) ^ 1)
theorem atom0596_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0596 g t z = CoefficientMerge.eval (monomial g t z) coeff0596 := by
  norm_num [atom0596, coeff0596, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0596_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0596 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0596]
  positivity
theorem weighted0596_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1328779564854165977235902090780097175886117930348534257451678057084284045270737422014950991035956821383581117965020412034439271020980920320 : Int) coeff0596) := by
  rw [CoefficientMerge.eval_scale, ← atom0596_identity]
  exact mul_nonneg (by norm_num) (atom0596_nonneg g t z hg hA hB ht hz hw)

def coeff0597 : CoefficientMerge.Poly :=
  [(1115137, 1)]
noncomputable def atom0597 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (z) ^ 1)
theorem atom0597_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0597 g t z = CoefficientMerge.eval (monomial g t z) coeff0597 := by
  norm_num [atom0597, coeff0597, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0597_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0597 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0597]
  positivity
theorem weighted0597_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2395884058811822438542613331016883452047549269639391583353229545609715188925874978614567375638736908102921224311112009218811441397574210560 : Int) coeff0597) := by
  rw [CoefficientMerge.eval_scale, ← atom0597_identity]
  exact mul_nonneg (by norm_num) (atom0597_nonneg g t z hg hA hB ht hz hw)

def coeff0598 : CoefficientMerge.Poly :=
  [(20481, 1)]
noncomputable def atom0598 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1)
theorem atom0598_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0598 g t z = CoefficientMerge.eval (monomial g t z) coeff0598 := by
  norm_num [atom0598, coeff0598, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0598_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0598 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0598]
  positivity
theorem weighted0598_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2491973167472336646089436175681995261379984237082841022655964941385838490354297532897327616891221060912318842785442888947572902825597337600 : Int) coeff0598) := by
  rw [CoefficientMerge.eval_scale, ← atom0598_identity]
  exact mul_nonneg (by norm_num) (atom0598_nonneg g t z hg hA hB ht hz hw)

def coeff0599 : CoefficientMerge.Poly :=
  [(69633, 1)]
noncomputable def atom0599 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1)
theorem atom0599_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0599 g t z = CoefficientMerge.eval (monomial g t z) coeff0599 := by
  norm_num [atom0599, coeff0599, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0599_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0599 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0599]
  positivity
theorem weighted0599_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3271058218405868413070178012833874752751031649474414573601373107202623846714332346555400911449875778338997176238335128294238579674975436800 : Int) coeff0599) := by
  rw [CoefficientMerge.eval_scale, ← atom0599_identity]
  exact mul_nonneg (by norm_num) (atom0599_nonneg g t z hg hA hB ht hz hw)

def coeff0600 : CoefficientMerge.Poly :=
  [(270337, 1)]
noncomputable def atom0600 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 6) ^ 2 * (t) ^ 1)
theorem atom0600_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0600 g t z = CoefficientMerge.eval (monomial g t z) coeff0600 := by
  norm_num [atom0600, coeff0600, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0600_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0600 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0600]
  positivity
theorem weighted0600_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1938569520032839592909873028406754264975897431060601265433170488206203994623398875891977238871086989202452753689013507545102067560743833600 : Int) coeff0600) := by
  rw [CoefficientMerge.eval_scale, ← atom0600_identity]
  exact mul_nonneg (by norm_num) (atom0600_nonneg g t z hg hA hB ht hz hw)

def coeff0601 : CoefficientMerge.Poly :=
  [(282625, 1)]
noncomputable def atom0601 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (t) ^ 1)
theorem atom0601_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0601 g t z = CoefficientMerge.eval (monomial g t z) coeff0601 := by
  norm_num [atom0601, coeff0601, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0601_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0601 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0601]
  positivity
theorem weighted0601_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1486050396643847841784780361696982072597373498444436115202683879116814363741223287913344378459595676473820651838857626575090875009405952000 : Int) coeff0601) := by
  rw [CoefficientMerge.eval_scale, ← atom0601_identity]
  exact mul_nonneg (by norm_num) (atom0601_nonneg g t z hg hA hB ht hz hw)

def coeff0602 : CoefficientMerge.Poly :=
  [(331777, 1)]
noncomputable def atom0602 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (t) ^ 1)
theorem atom0602_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0602 g t z = CoefficientMerge.eval (monomial g t z) coeff0602 := by
  norm_num [atom0602, coeff0602, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0602_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0602 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0602]
  positivity
theorem weighted0602_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5121984858235970884889407888941135644294236206147065579426037390552444928032200975469572554818664302359939425036672433898704833720760832000 : Int) coeff0602) := by
  rw [CoefficientMerge.eval_scale, ← atom0602_identity]
  exact mul_nonneg (by norm_num) (atom0602_nonneg g t z hg hA hB ht hz hw)

def coeff0603 : CoefficientMerge.Poly :=
  [(1056769, 1)]
noncomputable def atom0603 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 6) ^ 2 * (z) ^ 1)
theorem atom0603_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0603 g t z = CoefficientMerge.eval (monomial g t z) coeff0603 := by
  norm_num [atom0603, coeff0603, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0603_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0603 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0603]
  positivity
theorem weighted0603_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5557653580936864669307302166074549586015512738072103631504228707443867435453830917916935432893560531152661126986322213759900435179482828800 : Int) coeff0603) := by
  rw [CoefficientMerge.eval_scale, ← atom0603_identity]
  exact mul_nonneg (by norm_num) (atom0603_nonneg g t z hg hA hB ht hz hw)

def coeff0604 : CoefficientMerge.Poly :=
  [(1069057, 1)]
noncomputable def atom0604 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (z) ^ 1)
theorem atom0604_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0604 g t z = CoefficientMerge.eval (monomial g t z) coeff0604 := by
  norm_num [atom0604, coeff0604, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0604_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0604 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0604]
  positivity
theorem weighted0604_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (6674722384524421735362204888660665600580493894865391433865488432132216215664467365841219435185136000744056559920484551916109747832933683200 : Int) coeff0604) := by
  rw [CoefficientMerge.eval_scale, ← atom0604_identity]
  exact mul_nonneg (by norm_num) (atom0604_nonneg g t z hg hA hB ht hz hw)

def sparseBlock061 : CoefficientMerge.Poly :=
  [(5121, 3373394464075776909763398952107717200445554582483153074604280702629759254864018822347774346195217395374992955856617980158944824050363637760), (17409, 8435051750075114189339369383343774223082056505195863703394701332183254539923759216551564225108782862006833925297812516011459716979865681920), (20481, 2491973167472336646089436175681995261379984237082841022655964941385838490354297532897327616891221060912318842785442888947572902825597337600), (66561, 15871555607717052488129997118509029900668790304471811577756204188387209115108318643713541403125829253356012517227338933939660353797508300800), (69633, 3271058218405868413070178012833874752751031649474414573601373107202623846714332346555400911449875778338997176238335128294238579674975436800), (267265, 2687256850533400213293708924926309005789305548251255297257556064783003626274253104039730402038350087088314408832461358837732608460753264640), (270337, 1938569520032839592909873028406754264975897431060601265433170488206203994623398875891977238871086989202452753689013507545102067560743833600), (279553, 1252702612795546126733010941883052627779007705417950934917345287921269344013191583063467810859633533311907989847438886005760237865796833280), (282625, 1486050396643847841784780361696982072597373498444436115202683879116814363741223287913344378459595676473820651838857626575090875009405952000), (328705, 2014126570154167125498484209246783856750682984223246775024391294970128196380200252319676243373476194598430275687790032688339737780059750400), (331777, 5121984858235970884889407888941135644294236206147065579426037390552444928032200975469572554818664302359939425036672433898704833720760832000), (1050625, 671198206537487606233737513671011292688071194169836954212520776965276279978272939068064885030288211500286376773925336100045956798522163200), (1052929, 7818757403030491013836611586971595043272371137363516115626647141205005367447056716476826820004705053103176415005127519204396038063548442080), (1053697, 6753713822377785541352331725876171336188600215074227577643212136934205944956911908541258986910390810062283878001676806924932744284729768960), (1056769, 5557653580936864669307302166074549586015512738072103631504228707443867435453830917916935432893560531152661126986322213759900435179482828800), (1065217, 6105982752177053254460357814416374986849577379736640842756742052148772238839533211005375531309391719019917605081357752118019971488351492320), (1065985, 1328779564854165977235902090780097175886117930348534257451678057084284045270737422014950991035956821383581117965020412034439271020980920320), (1069057, 6674722384524421735362204888660665600580493894865391433865488432132216215664467365841219435185136000744056559920484551916109747832933683200), (1114369, 5634047446058960334377274124267974256613269101854432750608367313847935911212530516622591299007346214379814426168886955724656537438649353440), (1115137, 2395884058811822438542613331016883452047549269639391583353229545609715188925874978614567375638736908102921224311112009218811441397574210560)]
theorem sparseBlock061_data : sparseBlock061 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (7818757403030491013836611586971595043272371137363516115626647141205005367447056716476826820004705053103176415005127519204396038063548442080 : Int) coeff0585) (CoefficientMerge.scale (6105982752177053254460357814416374986849577379736640842756742052148772238839533211005375531309391719019917605081357752118019971488351492320 : Int) coeff0586)) (CoefficientMerge.merge (CoefficientMerge.scale (5634047446058960334377274124267974256613269101854432750608367313847935911212530516622591299007346214379814426168886955724656537438649353440 : Int) coeff0587) (CoefficientMerge.merge (CoefficientMerge.scale (3373394464075776909763398952107717200445554582483153074604280702629759254864018822347774346195217395374992955856617980158944824050363637760 : Int) coeff0588) (CoefficientMerge.scale (8435051750075114189339369383343774223082056505195863703394701332183254539923759216551564225108782862006833925297812516011459716979865681920 : Int) coeff0589)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (15871555607717052488129997118509029900668790304471811577756204188387209115108318643713541403125829253356012517227338933939660353797508300800 : Int) coeff0590) (CoefficientMerge.scale (2687256850533400213293708924926309005789305548251255297257556064783003626274253104039730402038350087088314408832461358837732608460753264640 : Int) coeff0591)) (CoefficientMerge.merge (CoefficientMerge.scale (1252702612795546126733010941883052627779007705417950934917345287921269344013191583063467810859633533311907989847438886005760237865796833280 : Int) coeff0592) (CoefficientMerge.merge (CoefficientMerge.scale (2014126570154167125498484209246783856750682984223246775024391294970128196380200252319676243373476194598430275687790032688339737780059750400 : Int) coeff0593) (CoefficientMerge.scale (671198206537487606233737513671011292688071194169836954212520776965276279978272939068064885030288211500286376773925336100045956798522163200 : Int) coeff0594))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (6753713822377785541352331725876171336188600215074227577643212136934205944956911908541258986910390810062283878001676806924932744284729768960 : Int) coeff0595) (CoefficientMerge.scale (1328779564854165977235902090780097175886117930348534257451678057084284045270737422014950991035956821383581117965020412034439271020980920320 : Int) coeff0596)) (CoefficientMerge.merge (CoefficientMerge.scale (2395884058811822438542613331016883452047549269639391583353229545609715188925874978614567375638736908102921224311112009218811441397574210560 : Int) coeff0597) (CoefficientMerge.merge (CoefficientMerge.scale (2491973167472336646089436175681995261379984237082841022655964941385838490354297532897327616891221060912318842785442888947572902825597337600 : Int) coeff0598) (CoefficientMerge.scale (3271058218405868413070178012833874752751031649474414573601373107202623846714332346555400911449875778338997176238335128294238579674975436800 : Int) coeff0599)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1938569520032839592909873028406754264975897431060601265433170488206203994623398875891977238871086989202452753689013507545102067560743833600 : Int) coeff0600) (CoefficientMerge.scale (1486050396643847841784780361696982072597373498444436115202683879116814363741223287913344378459595676473820651838857626575090875009405952000 : Int) coeff0601)) (CoefficientMerge.merge (CoefficientMerge.scale (5121984858235970884889407888941135644294236206147065579426037390552444928032200975469572554818664302359939425036672433898704833720760832000 : Int) coeff0602) (CoefficientMerge.merge (CoefficientMerge.scale (5557653580936864669307302166074549586015512738072103631504228707443867435453830917916935432893560531152661126986322213759900435179482828800 : Int) coeff0603) (CoefficientMerge.scale (6674722384524421735362204888660665600580493894865391433865488432132216215664467365841219435185136000744056559920484551916109747832933683200 : Int) coeff0604)))))) := by decide +kernel
theorem sparseBlock061_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock061 := by
  rw [sparseBlock061_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted0585_nonneg g t z hg hA hB ht hz hw) (weighted0586_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0587_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0588_nonneg g t z hg hA hB ht hz hw) (weighted0589_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0590_nonneg g t z hg hA hB ht hz hw) (weighted0591_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0592_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0593_nonneg g t z hg hA hB ht hz hw) (weighted0594_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted0595_nonneg g t z hg hA hB ht hz hw) (weighted0596_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0597_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0598_nonneg g t z hg hA hB ht hz hw) (weighted0599_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0600_nonneg g t z hg hA hB ht hz hw) (weighted0601_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0602_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0603_nonneg g t z hg hA hB ht hz hw) (weighted0604_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
