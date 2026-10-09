import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff0645 : CoefficientMerge.Poly :=
  [(541697, 1)]
noncomputable def atom0645 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (t) ^ 2)
theorem atom0645_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0645 g t z = CoefficientMerge.eval (monomial g t z) coeff0645 := by
  norm_num [atom0645, coeff0645, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0645_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0645 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0645]
  positivity
theorem weighted0645_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (952922105938254468095497149239679336707890215739789378855710911358103606359465151357763633310758564366607861385193144195359067182088355840 : Int) coeff0645) := by
  rw [CoefficientMerge.eval_scale, ← atom0645_identity]
  exact mul_nonneg (by norm_num) (atom0645_nonneg g t z hg hA hB ht hz hw)

def coeff0646 : CoefficientMerge.Poly :=
  [(590849, 1)]
noncomputable def atom0646 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (t) ^ 2)
theorem atom0646_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0646 g t z = CoefficientMerge.eval (monomial g t z) coeff0646 := by
  norm_num [atom0646, coeff0646, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0646_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0646 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0646]
  positivity
theorem weighted0646_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (912284870754010357287731724039877300478870364429950859393041062539698253651474489900594501565638393043800426058762731255572068577970585600 : Int) coeff0646) := by
  rw [CoefficientMerge.eval_scale, ← atom0646_identity]
  exact mul_nonneg (by norm_num) (atom0646_nonneg g t z hg hA hB ht hz hw)

def coeff0647 : CoefficientMerge.Poly :=
  [(1312769, 1)]
noncomputable def atom0647 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 2 * (t) ^ 1 * (z) ^ 1)
theorem atom0647_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0647 g t z = CoefficientMerge.eval (monomial g t z) coeff0647 := by
  norm_num [atom0647, coeff0647, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0647_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0647 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0647]
  positivity
theorem weighted0647_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1882204448855019290563934962635145722896748973564780275632485039585513113758731183388268220373633778097359173049209858308442935378483200000 : Int) coeff0647) := by
  rw [CoefficientMerge.eval_scale, ← atom0647_identity]
  exact mul_nonneg (by norm_num) (atom0647_nonneg g t z hg hA hB ht hz hw)

def coeff0648 : CoefficientMerge.Poly :=
  [(1315841, 1)]
noncomputable def atom0648 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0648_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0648 g t z = CoefficientMerge.eval (monomial g t z) coeff0648 := by
  norm_num [atom0648, coeff0648, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0648_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0648 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0648]
  positivity
theorem weighted0648_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3174051974767597656061564065550192857838645057768991317236078362354957840323684805028872056310775776785059451590267283735372345707387048960 : Int) coeff0648) := by
  rw [CoefficientMerge.eval_scale, ← atom0648_identity]
  exact mul_nonneg (by norm_num) (atom0648_nonneg g t z hg hA hB ht hz hw)

def coeff0649 : CoefficientMerge.Poly :=
  [(1328129, 1)]
noncomputable def atom0649 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0649_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0649 g t z = CoefficientMerge.eval (monomial g t z) coeff0649 := by
  norm_num [atom0649, coeff0649, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0649_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0649 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0649]
  positivity
theorem weighted0649_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2004189237864544363614475343003237201893692426099121466357393870094078728806920603793927827039145350020718241485102092002573215190476779520 : Int) coeff0649) := by
  rw [CoefficientMerge.eval_scale, ← atom0649_identity]
  exact mul_nonneg (by norm_num) (atom0649_nonneg g t z hg hA hB ht hz hw)

def coeff0650 : CoefficientMerge.Poly :=
  [(1377281, 1)]
noncomputable def atom0650 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0650_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0650 g t z = CoefficientMerge.eval (monomial g t z) coeff0650 := by
  norm_num [atom0650, coeff0650, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0650_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0650 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0650]
  positivity
theorem weighted0650_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1882910642340103823454358818183428177506065503090658470424292964927778820656668843296913262692450490939693177558902540295641284645011164160 : Int) coeff0650) := by
  rw [CoefficientMerge.eval_scale, ← atom0650_identity]
  exact mul_nonneg (by norm_num) (atom0650_nonneg g t z hg hA hB ht hz hw)

def coeff0651 : CoefficientMerge.Poly :=
  [(532481, 1)]
noncomputable def atom0651 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 6) ^ 2 * (t) ^ 2)
theorem atom0651_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0651 g t z = CoefficientMerge.eval (monomial g t z) coeff0651 := by
  norm_num [atom0651, coeff0651, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0651_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0651 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0651]
  positivity
theorem weighted0651_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (863417226341643104097666685078834557072978295680215843427891769761758457476070327239064242475293093860621637918650190944428455920150425600 : Int) coeff0651) := by
  rw [CoefficientMerge.eval_scale, ← atom0651_identity]
  exact mul_nonneg (by norm_num) (atom0651_nonneg g t z hg hA hB ht hz hw)

def coeff0652 : CoefficientMerge.Poly :=
  [(544769, 1)]
noncomputable def atom0652 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (t) ^ 2)
theorem atom0652_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0652 g t z = CoefficientMerge.eval (monomial g t z) coeff0652 := by
  norm_num [atom0652, coeff0652, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0652_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0652 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0652]
  positivity
theorem weighted0652_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1064164699797090315226609656521324935198638036590368398968385457542644516669254302118152286377524553746684888357206317831811167511599820800 : Int) coeff0652) := by
  rw [CoefficientMerge.eval_scale, ← atom0652_identity]
  exact mul_nonneg (by norm_num) (atom0652_nonneg g t z hg hA hB ht hz hw)

def coeff0653 : CoefficientMerge.Poly :=
  [(593921, 1)]
noncomputable def atom0653 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (t) ^ 2)
theorem atom0653_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0653 g t z = CoefficientMerge.eval (monomial g t z) coeff0653 := by
  norm_num [atom0653, coeff0653, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0653_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0653 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0653]
  positivity
theorem weighted0653_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (772892187384981956226666953841198331584231316444485919974886257268824728849979635365541475006938569437957953612965479242926635196051968000 : Int) coeff0653) := by
  rw [CoefficientMerge.eval_scale, ← atom0653_identity]
  exact mul_nonneg (by norm_num) (atom0653_nonneg g t z hg hA hB ht hz hw)

def coeff0654 : CoefficientMerge.Poly :=
  [(1318913, 1)]
noncomputable def atom0654 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 6) ^ 2 * (t) ^ 1 * (z) ^ 1)
theorem atom0654_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0654 g t z = CoefficientMerge.eval (monomial g t z) coeff0654 := by
  norm_num [atom0654, coeff0654, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0654_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0654 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0654]
  positivity
theorem weighted0654_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1414628104343117568787129362009563020659513441769508260509491466899586982267482352633081960941477982430455431518763828868822177158768844800 : Int) coeff0654) := by
  rw [CoefficientMerge.eval_scale, ← atom0654_identity]
  exact mul_nonneg (by norm_num) (atom0654_nonneg g t z hg hA hB ht hz hw)

def coeff0655 : CoefficientMerge.Poly :=
  [(1331201, 1)]
noncomputable def atom0655 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0655_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0655 g t z = CoefficientMerge.eval (monomial g t z) coeff0655 := by
  norm_num [atom0655, coeff0655, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0655_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0655 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0655]
  positivity
theorem weighted0655_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1682590471200704192782319075652273409711915788425000798219496385066733893371210607682951449939092116746942301802140271378856428272169676800 : Int) coeff0655) := by
  rw [CoefficientMerge.eval_scale, ← atom0655_identity]
  exact mul_nonneg (by norm_num) (atom0655_nonneg g t z hg hA hB ht hz hw)

def coeff0656 : CoefficientMerge.Poly :=
  [(1380353, 1)]
noncomputable def atom0656 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0656_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0656 g t z = CoefficientMerge.eval (monomial g t z) coeff0656 := by
  norm_num [atom0656, coeff0656, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0656_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0656 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0656]
  positivity
theorem weighted0656_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1234990152688011182519552604527868791313654560179084217814870951872520456064207110340070292109968391538537966536015397848289111330554060800 : Int) coeff0656) := by
  rw [CoefficientMerge.eval_scale, ← atom0656_identity]
  exact mul_nonneg (by norm_num) (atom0656_nonneg g t z hg hA hB ht hz hw)

def coeff0657 : CoefficientMerge.Poly :=
  [(294913, 1)]
noncomputable def atom0657 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 7) ^ 2 * (t) ^ 1)
theorem atom0657_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0657 g t z = CoefficientMerge.eval (monomial g t z) coeff0657 := by
  norm_num [atom0657, coeff0657, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0657_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0657 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0657]
  positivity
theorem weighted0657_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (535768342149983075699686565405635387513138319198370814614749436174910813785643505431109964434662204553968747799160361589874708593384755200 : Int) coeff0657) := by
  rw [CoefficientMerge.eval_scale, ← atom0657_identity]
  exact mul_nonneg (by norm_num) (atom0657_nonneg g t z hg hA hB ht hz hw)

def coeff0658 : CoefficientMerge.Poly :=
  [(557057, 1)]
noncomputable def atom0658 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 7) ^ 2 * (t) ^ 2)
theorem atom0658_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0658 g t z = CoefficientMerge.eval (monomial g t z) coeff0658 := by
  norm_num [atom0658, coeff0658, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0658_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0658 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0658]
  positivity
theorem weighted0658_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (30930388376103764514055662460058554187463911231373477335869200543200329031931018780912136022418876793832138397933920096308415907240345600 : Int) coeff0658) := by
  rw [CoefficientMerge.eval_scale, ← atom0658_identity]
  exact mul_nonneg (by norm_num) (atom0658_nonneg g t z hg hA hB ht hz hw)

def coeff0659 : CoefficientMerge.Poly :=
  [(1343489, 1)]
noncomputable def atom0659 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 7) ^ 2 * (t) ^ 1 * (z) ^ 1)
theorem atom0659_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0659 g t z = CoefficientMerge.eval (monomial g t z) coeff0659 := by
  norm_num [atom0659, coeff0659, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0659_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0659 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0659]
  positivity
theorem weighted0659_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (11871311470652345045465085262110894585661092996236581005133407026914153732737063741793595656744348894033334404726109908598129340638515200 : Int) coeff0659) := by
  rw [CoefficientMerge.eval_scale, ← atom0659_identity]
  exact mul_nonneg (by norm_num) (atom0659_nonneg g t z hg hA hB ht hz hw)

def coeff0660 : CoefficientMerge.Poly :=
  [(1392641, 1)]
noncomputable def atom0660 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0660_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0660 g t z = CoefficientMerge.eval (monomial g t z) coeff0660 := by
  norm_num [atom0660, coeff0660, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0660_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0660 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0660]
  positivity
theorem weighted0660_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (167175881184957312154616490960711986297830569608114180844150999465631946763426022837657773355727091472693826055027661053454653582481612800 : Int) coeff0660) := by
  rw [CoefficientMerge.eval_scale, ← atom0660_identity]
  exact mul_nonneg (by norm_num) (atom0660_nonneg g t z hg hA hB ht hz hw)

def coeff0661 : CoefficientMerge.Poly :=
  [(2097281, 1)]
noncomputable def atom0661 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 2 * (z) ^ 2)
theorem atom0661_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0661 g t z = CoefficientMerge.eval (monomial g t z) coeff0661 := by
  norm_num [atom0661, coeff0661, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0661_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0661 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0661]
  positivity
theorem weighted0661_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (821281225368576665184237414792880645505081166000358448527059766339039846280196195743921210033952453116783860507810353520885834577721300480 : Int) coeff0661) := by
  rw [CoefficientMerge.eval_scale, ← atom0661_identity]
  exact mul_nonneg (by norm_num) (atom0661_nonneg g t z hg hA hB ht hz hw)

def coeff0662 : CoefficientMerge.Poly :=
  [(2097473, 1)]
noncomputable def atom0662 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 4) ^ 1 * (z) ^ 2)
theorem atom0662_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0662 g t z = CoefficientMerge.eval (monomial g t z) coeff0662 := by
  norm_num [atom0662, coeff0662, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0662_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0662 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0662]
  positivity
theorem weighted0662_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1538248363738103395176131868497092555285150770030829586797989475690273111694505304336976271983764633545948399615380338341131034623370545472 : Int) coeff0662) := by
  rw [CoefficientMerge.eval_scale, ← atom0662_identity]
  exact mul_nonneg (by norm_num) (atom0662_nonneg g t z hg hA hB ht hz hw)

def coeff0663 : CoefficientMerge.Poly :=
  [(2098241, 1)]
noncomputable def atom0663 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 5) ^ 1 * (z) ^ 2)
theorem atom0663_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0663 g t z = CoefficientMerge.eval (monomial g t z) coeff0663 := by
  norm_num [atom0663, coeff0663, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0663_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0663 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0663]
  positivity
theorem weighted0663_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2240325279697249585901301507186269672002780855572120290294013752200663319405312544839590454655731234938144217266826119038739474602650793984 : Int) coeff0663) := by
  rw [CoefficientMerge.eval_scale, ← atom0663_identity]
  exact mul_nonneg (by norm_num) (atom0663_nonneg g t z hg hA hB ht hz hw)

def coeff0664 : CoefficientMerge.Poly :=
  [(2101313, 1)]
noncomputable def atom0664 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 6) ^ 1 * (z) ^ 2)
theorem atom0664_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0664 g t z = CoefficientMerge.eval (monomial g t z) coeff0664 := by
  norm_num [atom0664, coeff0664, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0664_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0664 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0664]
  positivity
theorem weighted0664_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1854359677146470056855786930098907666298343716619764065456697394744901845288821954899828874210257057135429783415038140502117144479755059200 : Int) coeff0664) := by
  rw [CoefficientMerge.eval_scale, ← atom0664_identity]
  exact mul_nonneg (by norm_num) (atom0664_nonneg g t z hg hA hB ht hz hw)

def sparseBlock064 : CoefficientMerge.Poly :=
  [(294913, 535768342149983075699686565405635387513138319198370814614749436174910813785643505431109964434662204553968747799160361589874708593384755200), (532481, 863417226341643104097666685078834557072978295680215843427891769761758457476070327239064242475293093860621637918650190944428455920150425600), (541697, 952922105938254468095497149239679336707890215739789378855710911358103606359465151357763633310758564366607861385193144195359067182088355840), (544769, 1064164699797090315226609656521324935198638036590368398968385457542644516669254302118152286377524553746684888357206317831811167511599820800), (557057, 30930388376103764514055662460058554187463911231373477335869200543200329031931018780912136022418876793832138397933920096308415907240345600), (590849, 912284870754010357287731724039877300478870364429950859393041062539698253651474489900594501565638393043800426058762731255572068577970585600), (593921, 772892187384981956226666953841198331584231316444485919974886257268824728849979635365541475006938569437957953612965479242926635196051968000), (1312769, 1882204448855019290563934962635145722896748973564780275632485039585513113758731183388268220373633778097359173049209858308442935378483200000), (1315841, 3174051974767597656061564065550192857838645057768991317236078362354957840323684805028872056310775776785059451590267283735372345707387048960), (1318913, 1414628104343117568787129362009563020659513441769508260509491466899586982267482352633081960941477982430455431518763828868822177158768844800), (1328129, 2004189237864544363614475343003237201893692426099121466357393870094078728806920603793927827039145350020718241485102092002573215190476779520), (1331201, 1682590471200704192782319075652273409711915788425000798219496385066733893371210607682951449939092116746942301802140271378856428272169676800), (1343489, 11871311470652345045465085262110894585661092996236581005133407026914153732737063741793595656744348894033334404726109908598129340638515200), (1377281, 1882910642340103823454358818183428177506065503090658470424292964927778820656668843296913262692450490939693177558902540295641284645011164160), (1380353, 1234990152688011182519552604527868791313654560179084217814870951872520456064207110340070292109968391538537966536015397848289111330554060800), (1392641, 167175881184957312154616490960711986297830569608114180844150999465631946763426022837657773355727091472693826055027661053454653582481612800), (2097281, 821281225368576665184237414792880645505081166000358448527059766339039846280196195743921210033952453116783860507810353520885834577721300480), (2097473, 1538248363738103395176131868497092555285150770030829586797989475690273111694505304336976271983764633545948399615380338341131034623370545472), (2098241, 2240325279697249585901301507186269672002780855572120290294013752200663319405312544839590454655731234938144217266826119038739474602650793984), (2101313, 1854359677146470056855786930098907666298343716619764065456697394744901845288821954899828874210257057135429783415038140502117144479755059200)]
theorem sparseBlock064_data : sparseBlock064 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (952922105938254468095497149239679336707890215739789378855710911358103606359465151357763633310758564366607861385193144195359067182088355840 : Int) coeff0645) (CoefficientMerge.scale (912284870754010357287731724039877300478870364429950859393041062539698253651474489900594501565638393043800426058762731255572068577970585600 : Int) coeff0646)) (CoefficientMerge.merge (CoefficientMerge.scale (1882204448855019290563934962635145722896748973564780275632485039585513113758731183388268220373633778097359173049209858308442935378483200000 : Int) coeff0647) (CoefficientMerge.merge (CoefficientMerge.scale (3174051974767597656061564065550192857838645057768991317236078362354957840323684805028872056310775776785059451590267283735372345707387048960 : Int) coeff0648) (CoefficientMerge.scale (2004189237864544363614475343003237201893692426099121466357393870094078728806920603793927827039145350020718241485102092002573215190476779520 : Int) coeff0649)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1882910642340103823454358818183428177506065503090658470424292964927778820656668843296913262692450490939693177558902540295641284645011164160 : Int) coeff0650) (CoefficientMerge.scale (863417226341643104097666685078834557072978295680215843427891769761758457476070327239064242475293093860621637918650190944428455920150425600 : Int) coeff0651)) (CoefficientMerge.merge (CoefficientMerge.scale (1064164699797090315226609656521324935198638036590368398968385457542644516669254302118152286377524553746684888357206317831811167511599820800 : Int) coeff0652) (CoefficientMerge.merge (CoefficientMerge.scale (772892187384981956226666953841198331584231316444485919974886257268824728849979635365541475006938569437957953612965479242926635196051968000 : Int) coeff0653) (CoefficientMerge.scale (1414628104343117568787129362009563020659513441769508260509491466899586982267482352633081960941477982430455431518763828868822177158768844800 : Int) coeff0654))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1682590471200704192782319075652273409711915788425000798219496385066733893371210607682951449939092116746942301802140271378856428272169676800 : Int) coeff0655) (CoefficientMerge.scale (1234990152688011182519552604527868791313654560179084217814870951872520456064207110340070292109968391538537966536015397848289111330554060800 : Int) coeff0656)) (CoefficientMerge.merge (CoefficientMerge.scale (535768342149983075699686565405635387513138319198370814614749436174910813785643505431109964434662204553968747799160361589874708593384755200 : Int) coeff0657) (CoefficientMerge.merge (CoefficientMerge.scale (30930388376103764514055662460058554187463911231373477335869200543200329031931018780912136022418876793832138397933920096308415907240345600 : Int) coeff0658) (CoefficientMerge.scale (11871311470652345045465085262110894585661092996236581005133407026914153732737063741793595656744348894033334404726109908598129340638515200 : Int) coeff0659)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (167175881184957312154616490960711986297830569608114180844150999465631946763426022837657773355727091472693826055027661053454653582481612800 : Int) coeff0660) (CoefficientMerge.scale (821281225368576665184237414792880645505081166000358448527059766339039846280196195743921210033952453116783860507810353520885834577721300480 : Int) coeff0661)) (CoefficientMerge.merge (CoefficientMerge.scale (1538248363738103395176131868497092555285150770030829586797989475690273111694505304336976271983764633545948399615380338341131034623370545472 : Int) coeff0662) (CoefficientMerge.merge (CoefficientMerge.scale (2240325279697249585901301507186269672002780855572120290294013752200663319405312544839590454655731234938144217266826119038739474602650793984 : Int) coeff0663) (CoefficientMerge.scale (1854359677146470056855786930098907666298343716619764065456697394744901845288821954899828874210257057135429783415038140502117144479755059200 : Int) coeff0664)))))) := by decide +kernel
theorem sparseBlock064_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock064 := by
  rw [sparseBlock064_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted0645_nonneg g t z hg hA hB ht hz hw) (weighted0646_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0647_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0648_nonneg g t z hg hA hB ht hz hw) (weighted0649_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0650_nonneg g t z hg hA hB ht hz hw) (weighted0651_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0652_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0653_nonneg g t z hg hA hB ht hz hw) (weighted0654_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted0655_nonneg g t z hg hA hB ht hz hw) (weighted0656_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0657_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0658_nonneg g t z hg hA hB ht hz hw) (weighted0659_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0660_nonneg g t z hg hA hB ht hz hw) (weighted0661_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0662_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0663_nonneg g t z hg hA hB ht hz hw) (weighted0664_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
