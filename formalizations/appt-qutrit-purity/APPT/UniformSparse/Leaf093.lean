import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff1225 : CoefficientMerge.Poly :=
  [(2426112, 1)]
noncomputable def atom1225 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1225_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1225 g t z = CoefficientMerge.eval (monomial g t z) coeff1225 := by
  norm_num [atom1225, coeff1225, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1225_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1225 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1225]
  positivity
theorem weighted1225_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (516884607483792700108148028544517920701121963154906712162432384843279214753984594325311603213277888021759663812178235722889397423591855050 : Int) coeff1225) := by
  rw [CoefficientMerge.eval_scale, ← atom1225_identity]
  exact mul_nonneg (by norm_num) (atom1225_nonneg g t z hg hA hB ht hz hw)

def coeff1226 : CoefficientMerge.Poly :=
  [(2367744, 1)]
noncomputable def atom1226 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 6) ^ 2 * (t) ^ 1 * (z) ^ 2)
theorem atom1226_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1226 g t z = CoefficientMerge.eval (monomial g t z) coeff1226 := by
  norm_num [atom1226, coeff1226, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1226_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1226 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1226]
  positivity
theorem weighted1226_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (324433887857014867064491037741854564982468491498413306437250791084564368073674961471955724442964874696680144710730514227719777538801477120 : Int) coeff1226) := by
  rw [CoefficientMerge.eval_scale, ← atom1226_identity]
  exact mul_nonneg (by norm_num) (atom1226_nonneg g t z hg hA hB ht hz hw)

def coeff1227 : CoefficientMerge.Poly :=
  [(2380032, 1)]
noncomputable def atom1227 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1227_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1227 g t z = CoefficientMerge.eval (monomial g t z) coeff1227 := by
  norm_num [atom1227, coeff1227, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1227_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1227 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1227]
  positivity
theorem weighted1227_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (558666378854109341526290272785813436052435597474572579809767203515222637692390683395789989415628021600329009602393251749612959577437848240 : Int) coeff1227) := by
  rw [CoefficientMerge.eval_scale, ← atom1227_identity]
  exact mul_nonneg (by norm_num) (atom1227_nonneg g t z hg hA hB ht hz hw)

def coeff1228 : CoefficientMerge.Poly :=
  [(2429184, 1)]
noncomputable def atom1228 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1228_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1228 g t z = CoefficientMerge.eval (monomial g t z) coeff1228 := by
  norm_num [atom1228, coeff1228, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1228_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1228 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1228]
  positivity
theorem weighted1228_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (465778908169359392161537380068769644557244615229672411684982336593947753426815317345532212377069070420973238582452027548046846057395229440 : Int) coeff1228) := by
  rw [CoefficientMerge.eval_scale, ← atom1228_identity]
  exact mul_nonneg (by norm_num) (atom1228_nonneg g t z hg hA hB ht hz hw)

def coeff1229 : CoefficientMerge.Poly :=
  [(2392320, 1)]
noncomputable def atom1229 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 7) ^ 2 * (t) ^ 1 * (z) ^ 2)
theorem atom1229_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1229 g t z = CoefficientMerge.eval (monomial g t z) coeff1229 := by
  norm_num [atom1229, coeff1229, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1229_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1229 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1229]
  positivity
theorem weighted1229_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (240777879899688550733945895911848419749942990690759760500569780122582739939544176534089020591347851042304694603721706988183759840072440320 : Int) coeff1229) := by
  rw [CoefficientMerge.eval_scale, ← atom1229_identity]
  exact mul_nonneg (by norm_num) (atom1229_nonneg g t z hg hA hB ht hz hw)

def coeff1230 : CoefficientMerge.Poly :=
  [(2441472, 1)]
noncomputable def atom1230 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 2)
theorem atom1230_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1230 g t z = CoefficientMerge.eval (monomial g t z) coeff1230 := by
  norm_num [atom1230, coeff1230, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1230_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1230 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1230]
  positivity
theorem weighted1230_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (325929777294400216549972551664755296958664730728583466340966140407208977136030289537542696257865564804662850065155219909443064912050263040 : Int) coeff1230) := by
  rw [CoefficientMerge.eval_scale, ← atom1230_identity]
  exact mul_nonneg (by norm_num) (atom1230_nonneg g t z hg hA hB ht hz hw)

def coeff1231 : CoefficientMerge.Poly :=
  [(2490624, 1)]
noncomputable def atom1231 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 8) ^ 2 * (t) ^ 1 * (z) ^ 2)
theorem atom1231_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1231 g t z = CoefficientMerge.eval (monomial g t z) coeff1231 := by
  norm_num [atom1231, coeff1231, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1231_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1231 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1231]
  positivity
theorem weighted1231_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (130478671048305608565003914182910470905433458646647098432688535434384987304061434118782973644818390312120643574894427991159633156228293120 : Int) coeff1231) := by
  rw [CoefficientMerge.eval_scale, ← atom1231_identity]
  exact mul_nonneg (by norm_num) (atom1231_nonneg g t z hg hA hB ht hz hw)

def coeff1232 : CoefficientMerge.Poly :=
  [(789504, 1)]
noncomputable def atom1232 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 3 * (t) ^ 3)
theorem atom1232_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1232 g t z = CoefficientMerge.eval (monomial g t z) coeff1232 := by
  norm_num [atom1232, coeff1232, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1232_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1232 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1232]
  positivity
theorem weighted1232_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (41632715529573085803721055112739049437492311527745962083595911551927215744228333978079984125522165205938158276013517648669928792128230400 : Int) coeff1232) := by
  rw [CoefficientMerge.eval_scale, ← atom1232_identity]
  exact mul_nonneg (by norm_num) (atom1232_nonneg g t z hg hA hB ht hz hw)

def coeff1233 : CoefficientMerge.Poly :=
  [(792576, 1)]
noncomputable def atom1233 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 2 * (g 6) ^ 1 * (t) ^ 3)
theorem atom1233_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1233 g t z = CoefficientMerge.eval (monomial g t z) coeff1233 := by
  norm_num [atom1233, coeff1233, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1233_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1233 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1233]
  positivity
theorem weighted1233_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (116772652836171883872026320092274374555317266595038318973236102112132382636882093583587456594827270179321027913659693980192229780398412800 : Int) coeff1233) := by
  rw [CoefficientMerge.eval_scale, ← atom1233_identity]
  exact mul_nonneg (by norm_num) (atom1233_nonneg g t z hg hA hB ht hz hw)

def coeff1234 : CoefficientMerge.Poly :=
  [(804864, 1)]
noncomputable def atom1234 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 2 * (g 7) ^ 1 * (t) ^ 3)
theorem atom1234_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1234 g t z = CoefficientMerge.eval (monomial g t z) coeff1234 := by
  norm_num [atom1234, coeff1234, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1234_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1234 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1234]
  positivity
theorem weighted1234_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (96788984300785908035051753110791489647795580675188755395637681174250996495268489964116854012176852195820195108815299380780462246238950400 : Int) coeff1234) := by
  rw [CoefficientMerge.eval_scale, ← atom1234_identity]
  exact mul_nonneg (by norm_num) (atom1234_nonneg g t z hg hA hB ht hz hw)

def coeff1235 : CoefficientMerge.Poly :=
  [(854016, 1)]
noncomputable def atom1235 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 2 * (g 8) ^ 1 * (t) ^ 3)
theorem atom1235_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1235 g t z = CoefficientMerge.eval (monomial g t z) coeff1235 := by
  norm_num [atom1235, coeff1235, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1235_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1235 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1235]
  positivity
theorem weighted1235_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (83110762132009095681702539933160108168249336054276387821295159523651887222504976754607055907901950601050011031929868803848402766062720000 : Int) coeff1235) := by
  rw [CoefficientMerge.eval_scale, ← atom1235_identity]
  exact mul_nonneg (by norm_num) (atom1235_nonneg g t z hg hA hB ht hz hw)

def coeff1236 : CoefficientMerge.Poly :=
  [(1575936, 1)]
noncomputable def atom1236 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 3 * (t) ^ 2 * (z) ^ 1)
theorem atom1236_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1236 g t z = CoefficientMerge.eval (monomial g t z) coeff1236 := by
  norm_num [atom1236, coeff1236, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1236_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1236 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1236]
  positivity
theorem weighted1236_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (123876079961794552161243461088132965163549285024671983523507990207296463816644382389732571839670591038666370090018674953024777620239403520 : Int) coeff1236) := by
  rw [CoefficientMerge.eval_scale, ← atom1236_identity]
  exact mul_nonneg (by norm_num) (atom1236_nonneg g t z hg hA hB ht hz hw)

def coeff1237 : CoefficientMerge.Poly :=
  [(1579008, 1)]
noncomputable def atom1237 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 2 * (g 6) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1237_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1237 g t z = CoefficientMerge.eval (monomial g t z) coeff1237 := by
  norm_num [atom1237, coeff1237, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1237_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1237 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1237]
  positivity
theorem weighted1237_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (349878717249883192576352966316364250807470990590335063164848997236872898191722369281097476204111428153662642740569720943940764272951389440 : Int) coeff1237) := by
  rw [CoefficientMerge.eval_scale, ← atom1237_identity]
  exact mul_nonneg (by norm_num) (atom1237_nonneg g t z hg hA hB ht hz hw)

def coeff1238 : CoefficientMerge.Poly :=
  [(1591296, 1)]
noncomputable def atom1238 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 2 * (g 7) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1238_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1238 g t z = CoefficientMerge.eval (monomial g t z) coeff1238 := by
  norm_num [atom1238, coeff1238, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1238_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1238 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1238]
  positivity
theorem weighted1238_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (301721443225491719728024851087988005377328830064813784861313979247852592581463505693892820808544994907421045116185060947163579013380394240 : Int) coeff1238) := by
  rw [CoefficientMerge.eval_scale, ← atom1238_identity]
  exact mul_nonneg (by norm_num) (atom1238_nonneg g t z hg hA hB ht hz hw)

def coeff1239 : CoefficientMerge.Poly :=
  [(1640448, 1)]
noncomputable def atom1239 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 2 * (g 8) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1239_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1239 g t z = CoefficientMerge.eval (monomial g t z) coeff1239 := by
  norm_num [atom1239, coeff1239, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1239_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1239 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1239]
  positivity
theorem weighted1239_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (259857084787851336641931648392499204519801100467593943085893423804493799885701180913875022682838253233276664745506463444665514054088592640 : Int) coeff1239) := by
  rw [CoefficientMerge.eval_scale, ← atom1239_identity]
  exact mul_nonneg (by norm_num) (atom1239_nonneg g t z hg hA hB ht hz hw)

def coeff1240 : CoefficientMerge.Poly :=
  [(795648, 1)]
noncomputable def atom1240 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 6) ^ 2 * (t) ^ 3)
theorem atom1240_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1240 g t z = CoefficientMerge.eval (monomial g t z) coeff1240 := by
  norm_num [atom1240, coeff1240, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1240_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1240 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1240]
  positivity
theorem weighted1240_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (109680543589982054148255619843370230681498222969289190046681624452537803249977562972710761359562734810961745278675028331498885732349081600 : Int) coeff1240) := by
  rw [CoefficientMerge.eval_scale, ← atom1240_identity]
  exact mul_nonneg (by norm_num) (atom1240_nonneg g t z hg hA hB ht hz hw)

def coeff1241 : CoefficientMerge.Poly :=
  [(807936, 1)]
noncomputable def atom1241 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (t) ^ 3)
theorem atom1241_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1241 g t z = CoefficientMerge.eval (monomial g t z) coeff1241 := by
  norm_num [atom1241, coeff1241, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1241_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1241 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1241]
  positivity
theorem weighted1241_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (173793004609530492336757117196764087952501231249056690177768310334522185268861212837265074412808261973028246981875933742770251585210521600 : Int) coeff1241) := by
  rw [CoefficientMerge.eval_scale, ← atom1241_identity]
  exact mul_nonneg (by norm_num) (atom1241_nonneg g t z hg hA hB ht hz hw)

def coeff1242 : CoefficientMerge.Poly :=
  [(857088, 1)]
noncomputable def atom1242 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (t) ^ 3)
theorem atom1242_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1242 g t z = CoefficientMerge.eval (monomial g t z) coeff1242 := by
  norm_num [atom1242, coeff1242, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1242_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1242 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1242]
  positivity
theorem weighted1242_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (138484331241657164319794529281078876220540055800842240044835299940138785519116144182804722004680642684493918319716047744323173839295385600 : Int) coeff1242) := by
  rw [CoefficientMerge.eval_scale, ← atom1242_identity]
  exact mul_nonneg (by norm_num) (atom1242_nonneg g t z hg hA hB ht hz hw)

def coeff1243 : CoefficientMerge.Poly :=
  [(1582080, 1)]
noncomputable def atom1243 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 6) ^ 2 * (t) ^ 2 * (z) ^ 1)
theorem atom1243_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1243 g t z = CoefficientMerge.eval (monomial g t z) coeff1243 := by
  norm_num [atom1243, coeff1243, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1243_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1243 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1243]
  positivity
theorem weighted1243_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (331168579108664035296755567506442100325664739931078478453953703317542218089100408227837477692007968186216248736541645553526043785212421120 : Int) coeff1243) := by
  rw [CoefficientMerge.eval_scale, ← atom1243_identity]
  exact mul_nonneg (by norm_num) (atom1243_nonneg g t z hg hA hB ht hz hw)

def coeff1244 : CoefficientMerge.Poly :=
  [(1594368, 1)]
noncomputable def atom1244 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1244_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1244 g t z = CoefficientMerge.eval (monomial g t z) coeff1244 := by
  norm_num [atom1244, coeff1244, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1244_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1244 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1244]
  positivity
theorem weighted1244_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (553176602588595945608906497350986057889224610116638739853385761651052964109232203038406358387352954852598703420770746636248423109518218240 : Int) coeff1244) := by
  rw [CoefficientMerge.eval_scale, ← atom1244_identity]
  exact mul_nonneg (by norm_num) (atom1244_nonneg g t z hg hA hB ht hz hw)

def sparseBlock093 : CoefficientMerge.Poly :=
  [(789504, 41632715529573085803721055112739049437492311527745962083595911551927215744228333978079984125522165205938158276013517648669928792128230400), (792576, 116772652836171883872026320092274374555317266595038318973236102112132382636882093583587456594827270179321027913659693980192229780398412800), (795648, 109680543589982054148255619843370230681498222969289190046681624452537803249977562972710761359562734810961745278675028331498885732349081600), (804864, 96788984300785908035051753110791489647795580675188755395637681174250996495268489964116854012176852195820195108815299380780462246238950400), (807936, 173793004609530492336757117196764087952501231249056690177768310334522185268861212837265074412808261973028246981875933742770251585210521600), (854016, 83110762132009095681702539933160108168249336054276387821295159523651887222504976754607055907901950601050011031929868803848402766062720000), (857088, 138484331241657164319794529281078876220540055800842240044835299940138785519116144182804722004680642684493918319716047744323173839295385600), (1575936, 123876079961794552161243461088132965163549285024671983523507990207296463816644382389732571839670591038666370090018674953024777620239403520), (1579008, 349878717249883192576352966316364250807470990590335063164848997236872898191722369281097476204111428153662642740569720943940764272951389440), (1582080, 331168579108664035296755567506442100325664739931078478453953703317542218089100408227837477692007968186216248736541645553526043785212421120), (1591296, 301721443225491719728024851087988005377328830064813784861313979247852592581463505693892820808544994907421045116185060947163579013380394240), (1594368, 553176602588595945608906497350986057889224610116638739853385761651052964109232203038406358387352954852598703420770746636248423109518218240), (1640448, 259857084787851336641931648392499204519801100467593943085893423804493799885701180913875022682838253233276664745506463444665514054088592640), (2367744, 324433887857014867064491037741854564982468491498413306437250791084564368073674961471955724442964874696680144710730514227719777538801477120), (2380032, 558666378854109341526290272785813436052435597474572579809767203515222637692390683395789989415628021600329009602393251749612959577437848240), (2392320, 240777879899688550733945895911848419749942990690759760500569780122582739939544176534089020591347851042304694603721706988183759840072440320), (2426112, 516884607483792700108148028544517920701121963154906712162432384843279214753984594325311603213277888021759663812178235722889397423591855050), (2429184, 465778908169359392161537380068769644557244615229672411684982336593947753426815317345532212377069070420973238582452027548046846057395229440), (2441472, 325929777294400216549972551664755296958664730728583466340966140407208977136030289537542696257865564804662850065155219909443064912050263040), (2490624, 130478671048305608565003914182910470905433458646647098432688535434384987304061434118782973644818390312120643574894427991159633156228293120)]
theorem sparseBlock093_data : sparseBlock093 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (516884607483792700108148028544517920701121963154906712162432384843279214753984594325311603213277888021759663812178235722889397423591855050 : Int) coeff1225) (CoefficientMerge.scale (324433887857014867064491037741854564982468491498413306437250791084564368073674961471955724442964874696680144710730514227719777538801477120 : Int) coeff1226)) (CoefficientMerge.merge (CoefficientMerge.scale (558666378854109341526290272785813436052435597474572579809767203515222637692390683395789989415628021600329009602393251749612959577437848240 : Int) coeff1227) (CoefficientMerge.merge (CoefficientMerge.scale (465778908169359392161537380068769644557244615229672411684982336593947753426815317345532212377069070420973238582452027548046846057395229440 : Int) coeff1228) (CoefficientMerge.scale (240777879899688550733945895911848419749942990690759760500569780122582739939544176534089020591347851042304694603721706988183759840072440320 : Int) coeff1229)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (325929777294400216549972551664755296958664730728583466340966140407208977136030289537542696257865564804662850065155219909443064912050263040 : Int) coeff1230) (CoefficientMerge.scale (130478671048305608565003914182910470905433458646647098432688535434384987304061434118782973644818390312120643574894427991159633156228293120 : Int) coeff1231)) (CoefficientMerge.merge (CoefficientMerge.scale (41632715529573085803721055112739049437492311527745962083595911551927215744228333978079984125522165205938158276013517648669928792128230400 : Int) coeff1232) (CoefficientMerge.merge (CoefficientMerge.scale (116772652836171883872026320092274374555317266595038318973236102112132382636882093583587456594827270179321027913659693980192229780398412800 : Int) coeff1233) (CoefficientMerge.scale (96788984300785908035051753110791489647795580675188755395637681174250996495268489964116854012176852195820195108815299380780462246238950400 : Int) coeff1234))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (83110762132009095681702539933160108168249336054276387821295159523651887222504976754607055907901950601050011031929868803848402766062720000 : Int) coeff1235) (CoefficientMerge.scale (123876079961794552161243461088132965163549285024671983523507990207296463816644382389732571839670591038666370090018674953024777620239403520 : Int) coeff1236)) (CoefficientMerge.merge (CoefficientMerge.scale (349878717249883192576352966316364250807470990590335063164848997236872898191722369281097476204111428153662642740569720943940764272951389440 : Int) coeff1237) (CoefficientMerge.merge (CoefficientMerge.scale (301721443225491719728024851087988005377328830064813784861313979247852592581463505693892820808544994907421045116185060947163579013380394240 : Int) coeff1238) (CoefficientMerge.scale (259857084787851336641931648392499204519801100467593943085893423804493799885701180913875022682838253233276664745506463444665514054088592640 : Int) coeff1239)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (109680543589982054148255619843370230681498222969289190046681624452537803249977562972710761359562734810961745278675028331498885732349081600 : Int) coeff1240) (CoefficientMerge.scale (173793004609530492336757117196764087952501231249056690177768310334522185268861212837265074412808261973028246981875933742770251585210521600 : Int) coeff1241)) (CoefficientMerge.merge (CoefficientMerge.scale (138484331241657164319794529281078876220540055800842240044835299940138785519116144182804722004680642684493918319716047744323173839295385600 : Int) coeff1242) (CoefficientMerge.merge (CoefficientMerge.scale (331168579108664035296755567506442100325664739931078478453953703317542218089100408227837477692007968186216248736541645553526043785212421120 : Int) coeff1243) (CoefficientMerge.scale (553176602588595945608906497350986057889224610116638739853385761651052964109232203038406358387352954852598703420770746636248423109518218240 : Int) coeff1244)))))) := by decide +kernel
theorem sparseBlock093_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock093 := by
  rw [sparseBlock093_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted1225_nonneg g t z hg hA hB ht hz hw) (weighted1226_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1227_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1228_nonneg g t z hg hA hB ht hz hw) (weighted1229_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1230_nonneg g t z hg hA hB ht hz hw) (weighted1231_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1232_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1233_nonneg g t z hg hA hB ht hz hw) (weighted1234_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted1235_nonneg g t z hg hA hB ht hz hw) (weighted1236_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1237_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1238_nonneg g t z hg hA hB ht hz hw) (weighted1239_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1240_nonneg g t z hg hA hB ht hz hw) (weighted1241_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1242_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1243_nonneg g t z hg hA hB ht hz hw) (weighted1244_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
