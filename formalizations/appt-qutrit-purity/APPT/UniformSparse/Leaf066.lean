import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff0685 : CoefficientMerge.Poly :=
  [(1049608, 1)]
noncomputable def atom0685 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 2 * (g 5) ^ 1 * (z) ^ 1)
theorem atom0685_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0685 g t z = CoefficientMerge.eval (monomial g t z) coeff0685 := by
  norm_num [atom0685, coeff0685, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0685_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0685 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0685]
  positivity
theorem weighted0685_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (498030633629076330522792734871611138929437793911042738283998686106144886821683650665332006259837924049922939310252316344010277117811916800 : Int) coeff0685) := by
  rw [CoefficientMerge.eval_scale, ← atom0685_identity]
  exact mul_nonneg (by norm_num) (atom0685_nonneg g t z hg hA hB ht hz hw)

def coeff0686 : CoefficientMerge.Poly :=
  [(36, 1)]
noncomputable def atom0686 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 2)
theorem atom0686_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0686 g t z = CoefficientMerge.eval (monomial g t z) coeff0686 := by
  norm_num [atom0686, coeff0686, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0686_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0686 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0686]
  positivity
theorem weighted0686_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4204563572593124919096110457911219194830166420570913992501828249324512472413302047908328061980735337472528075364885308586661395737113395200 : Int) coeff0686) := by
  rw [CoefficientMerge.eval_scale, ← atom0686_identity]
  exact mul_nonneg (by norm_num) (atom0686_nonneg g t z hg hA hB ht hz hw)

def coeff0687 : CoefficientMerge.Poly :=
  [(84, 1)]
noncomputable def atom0687 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 3) ^ 1)
theorem atom0687_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0687 g t z = CoefficientMerge.eval (monomial g t z) coeff0687 := by
  norm_num [atom0687, coeff0687, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0687_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0687 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0687]
  positivity
theorem weighted0687_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (27830134652085706025220612759063305029735707305684386529464540204370810386788952734824096946590817317637943331238812400766019950199830118400 : Int) coeff0687) := by
  rw [CoefficientMerge.eval_scale, ← atom0687_identity]
  exact mul_nonneg (by norm_num) (atom0687_nonneg g t z hg hA hB ht hz hw)

def coeff0688 : CoefficientMerge.Poly :=
  [(276, 1)]
noncomputable def atom0688 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 4) ^ 1)
theorem atom0688_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0688 g t z = CoefficientMerge.eval (monomial g t z) coeff0688 := by
  norm_num [atom0688, coeff0688, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0688_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0688 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0688]
  positivity
theorem weighted0688_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (19108075977377698268738757380353069560687427777712557899167192917462754914765242825257919063637954862632858777543867693204640145727169740800 : Int) coeff0688) := by
  rw [CoefficientMerge.eval_scale, ← atom0688_identity]
  exact mul_nonneg (by norm_num) (atom0688_nonneg g t z hg hA hB ht hz hw)

def coeff0689 : CoefficientMerge.Poly :=
  [(1044, 1)]
noncomputable def atom0689 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 5) ^ 1)
theorem atom0689_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0689 g t z = CoefficientMerge.eval (monomial g t z) coeff0689 := by
  norm_num [atom0689, coeff0689, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0689_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0689 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0689]
  positivity
theorem weighted0689_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (11851802023543487706376578554085002976901463314748703565002898720305523502561918318177017102547282572146396475388195936641731189290680320000 : Int) coeff0689) := by
  rw [CoefficientMerge.eval_scale, ← atom0689_identity]
  exact mul_nonneg (by norm_num) (atom0689_nonneg g t z hg hA hB ht hz hw)

def coeff0690 : CoefficientMerge.Poly :=
  [(4116, 1)]
noncomputable def atom0690 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 6) ^ 1)
theorem atom0690_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0690 g t z = CoefficientMerge.eval (monomial g t z) coeff0690 := by
  norm_num [atom0690, coeff0690, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0690_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0690 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0690]
  positivity
theorem weighted0690_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (17344429249338335075209705727315195759419056858046503807943485118505162779599677268089098503744679803439791281721834591875704932082278236160 : Int) coeff0690) := by
  rw [CoefficientMerge.eval_scale, ← atom0690_identity]
  exact mul_nonneg (by norm_num) (atom0690_nonneg g t z hg hA hB ht hz hw)

def coeff0691 : CoefficientMerge.Poly :=
  [(16404, 1)]
noncomputable def atom0691 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 7) ^ 1)
theorem atom0691_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0691 g t z = CoefficientMerge.eval (monomial g t z) coeff0691 := by
  norm_num [atom0691, coeff0691, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0691_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0691 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0691]
  positivity
theorem weighted0691_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1250805628228984389610339005326570297877373897079539808144469956295712667414045115429305149393463551451735359956373323033174901051850342400 : Int) coeff0691) := by
  rw [CoefficientMerge.eval_scale, ← atom0691_identity]
  exact mul_nonneg (by norm_num) (atom0691_nonneg g t z hg hA hB ht hz hw)

def coeff0692 : CoefficientMerge.Poly :=
  [(262180, 1)]
noncomputable def atom0692 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 2 * (t) ^ 1)
theorem atom0692_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0692 g t z = CoefficientMerge.eval (monomial g t z) coeff0692 := by
  norm_num [atom0692, coeff0692, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0692_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0692 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0692]
  positivity
theorem weighted0692_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (6090345303573908289399597564239873977201561501277753598081545508962463158526251277986172658470916823801275863686721449943203644774060032000 : Int) coeff0692) := by
  rw [CoefficientMerge.eval_scale, ← atom0692_identity]
  exact mul_nonneg (by norm_num) (atom0692_nonneg g t z hg hA hB ht hz hw)

def coeff0693 : CoefficientMerge.Poly :=
  [(262228, 1)]
noncomputable def atom0693 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 3) ^ 1 * (t) ^ 1)
theorem atom0693_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0693 g t z = CoefficientMerge.eval (monomial g t z) coeff0693 := by
  norm_num [atom0693, coeff0693, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0693_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0693 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0693]
  positivity
theorem weighted0693_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (18312612527900328283209201506857538370171774697302016596315257902825779060981627079136174500256427334681780826963890037779571315488106004480 : Int) coeff0693) := by
  rw [CoefficientMerge.eval_scale, ← atom0693_identity]
  exact mul_nonneg (by norm_num) (atom0693_nonneg g t z hg hA hB ht hz hw)

def coeff0694 : CoefficientMerge.Poly :=
  [(262420, 1)]
noncomputable def atom0694 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 4) ^ 1 * (t) ^ 1)
theorem atom0694_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0694 g t z = CoefficientMerge.eval (monomial g t z) coeff0694 := by
  norm_num [atom0694, coeff0694, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0694_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0694 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0694]
  positivity
theorem weighted0694_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (12676212849078023215726682948800665693455403305926900727263155157228438796496927194338584167509018312018515300806066151488125593107360563200 : Int) coeff0694) := by
  rw [CoefficientMerge.eval_scale, ← atom0694_identity]
  exact mul_nonneg (by norm_num) (atom0694_nonneg g t z hg hA hB ht hz hw)

def coeff0695 : CoefficientMerge.Poly :=
  [(263188, 1)]
noncomputable def atom0695 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 5) ^ 1 * (t) ^ 1)
theorem atom0695_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0695 g t z = CoefficientMerge.eval (monomial g t z) coeff0695 := by
  norm_num [atom0695, coeff0695, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0695_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0695 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0695]
  positivity
theorem weighted0695_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (9454092362974308273327175944404355097000603777966338157685775385388133997676381706058172666003944838556750190098383134714960397259983462400 : Int) coeff0695) := by
  rw [CoefficientMerge.eval_scale, ← atom0695_identity]
  exact mul_nonneg (by norm_num) (atom0695_nonneg g t z hg hA hB ht hz hw)

def coeff0696 : CoefficientMerge.Poly :=
  [(266260, 1)]
noncomputable def atom0696 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 6) ^ 1 * (t) ^ 1)
theorem atom0696_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0696 g t z = CoefficientMerge.eval (monomial g t z) coeff0696 := by
  norm_num [atom0696, coeff0696, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0696_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0696 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0696]
  positivity
theorem weighted0696_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (6758716015614127791462807935449388443467675375490667191910172062224787206241949462893717036546678635132642940076263773109198756966661457920 : Int) coeff0696) := by
  rw [CoefficientMerge.eval_scale, ← atom0696_identity]
  exact mul_nonneg (by norm_num) (atom0696_nonneg g t z hg hA hB ht hz hw)

def coeff0697 : CoefficientMerge.Poly :=
  [(278548, 1)]
noncomputable def atom0697 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 7) ^ 1 * (t) ^ 1)
theorem atom0697_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0697 g t z = CoefficientMerge.eval (monomial g t z) coeff0697 := by
  norm_num [atom0697, coeff0697, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0697_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0697 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0697]
  positivity
theorem weighted0697_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (7593076147306028553273340403837290498013221076861062878139232197397242103385189182249125237217169446286734841252011643227333467764310364160 : Int) coeff0697) := by
  rw [CoefficientMerge.eval_scale, ← atom0697_identity]
  exact mul_nonneg (by norm_num) (atom0697_nonneg g t z hg hA hB ht hz hw)

def coeff0698 : CoefficientMerge.Poly :=
  [(1048660, 1)]
noncomputable def atom0698 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 3) ^ 1 * (z) ^ 1)
theorem atom0698_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0698 g t z = CoefficientMerge.eval (monomial g t z) coeff0698 := by
  norm_num [atom0698, coeff0698, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0698_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0698 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0698]
  positivity
theorem weighted0698_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (13397961643821826918537513030338968011287235868135514231285767595369664741280547455572233273945862248111443194788661081170582731776373935104 : Int) coeff0698) := by
  rw [CoefficientMerge.eval_scale, ← atom0698_identity]
  exact mul_nonneg (by norm_num) (atom0698_nonneg g t z hg hA hB ht hz hw)

def coeff0699 : CoefficientMerge.Poly :=
  [(1048852, 1)]
noncomputable def atom0699 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 4) ^ 1 * (z) ^ 1)
theorem atom0699_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0699 g t z = CoefficientMerge.eval (monomial g t z) coeff0699 := by
  norm_num [atom0699, coeff0699, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0699_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0699 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0699]
  positivity
theorem weighted0699_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3843252809398849230613045829456876280370074328389467066676017775174902832317786102338783742723082087395984323852609059746699000967581416320 : Int) coeff0699) := by
  rw [CoefficientMerge.eval_scale, ← atom0699_identity]
  exact mul_nonneg (by norm_num) (atom0699_nonneg g t z hg hA hB ht hz hw)

def coeff0700 : CoefficientMerge.Poly :=
  [(1049620, 1)]
noncomputable def atom0700 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 5) ^ 1 * (z) ^ 1)
theorem atom0700_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0700 g t z = CoefficientMerge.eval (monomial g t z) coeff0700 := by
  norm_num [atom0700, coeff0700, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0700_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0700 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0700]
  positivity
theorem weighted0700_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4751025503916623722586704985087505935804523844562891020494259089187053903762629433652366349377399463101034546592734813570265296703788610816 : Int) coeff0700) := by
  rw [CoefficientMerge.eval_scale, ← atom0700_identity]
  exact mul_nonneg (by norm_num) (atom0700_nonneg g t z hg hA hB ht hz hw)

def coeff0701 : CoefficientMerge.Poly :=
  [(1052692, 1)]
noncomputable def atom0701 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 6) ^ 1 * (z) ^ 1)
theorem atom0701_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0701 g t z = CoefficientMerge.eval (monomial g t z) coeff0701 := by
  norm_num [atom0701, coeff0701, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0701_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0701 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0701]
  positivity
theorem weighted0701_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (11919969537118997080335147656892393688670581765475886662238215571341499618811932340060153663850779251295576501318339221954443460502101719040 : Int) coeff0701) := by
  rw [CoefficientMerge.eval_scale, ← atom0701_identity]
  exact mul_nonneg (by norm_num) (atom0701_nonneg g t z hg hA hB ht hz hw)

def coeff0702 : CoefficientMerge.Poly :=
  [(1064980, 1)]
noncomputable def atom0702 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 2) ^ 1 * (g 7) ^ 1 * (z) ^ 1)
theorem atom0702_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0702 g t z = CoefficientMerge.eval (monomial g t z) coeff0702 := by
  norm_num [atom0702, coeff0702, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0702_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0702 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0702]
  positivity
theorem weighted0702_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (6911572896712532804476486972856143707337243895716982834258190211390971091922240056005110789822282623442611255487728776555049010805416847360 : Int) coeff0702) := by
  rw [CoefficientMerge.eval_scale, ← atom0702_identity]
  exact mul_nonneg (by norm_num) (atom0702_nonneg g t z hg hA hB ht hz hw)

def coeff0703 : CoefficientMerge.Poly :=
  [(132, 1)]
noncomputable def atom0703 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 2)
theorem atom0703_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0703 g t z = CoefficientMerge.eval (monomial g t z) coeff0703 := by
  norm_num [atom0703, coeff0703, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0703_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0703 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0703]
  positivity
theorem weighted0703_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (7104491216748488109296511953570578387050021488114653919343597318928788669934901957307981229226002415050412232972144797022012070950513868800 : Int) coeff0703) := by
  rw [CoefficientMerge.eval_scale, ← atom0703_identity]
  exact mul_nonneg (by norm_num) (atom0703_nonneg g t z hg hA hB ht hz hw)

def coeff0704 : CoefficientMerge.Poly :=
  [(324, 1)]
noncomputable def atom0704 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 4) ^ 1)
theorem atom0704_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0704 g t z = CoefficientMerge.eval (monomial g t z) coeff0704 := by
  norm_num [atom0704, coeff0704, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0704_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0704 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0704]
  positivity
theorem weighted0704_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5431739092774544569194052124480373687350335275348637142330681954404757148394484476804052396912675183100114002128805712962412486716051404800 : Int) coeff0704) := by
  rw [CoefficientMerge.eval_scale, ← atom0704_identity]
  exact mul_nonneg (by norm_num) (atom0704_nonneg g t z hg hA hB ht hz hw)

def sparseBlock066 : CoefficientMerge.Poly :=
  [(36, 4204563572593124919096110457911219194830166420570913992501828249324512472413302047908328061980735337472528075364885308586661395737113395200), (84, 27830134652085706025220612759063305029735707305684386529464540204370810386788952734824096946590817317637943331238812400766019950199830118400), (132, 7104491216748488109296511953570578387050021488114653919343597318928788669934901957307981229226002415050412232972144797022012070950513868800), (276, 19108075977377698268738757380353069560687427777712557899167192917462754914765242825257919063637954862632858777543867693204640145727169740800), (324, 5431739092774544569194052124480373687350335275348637142330681954404757148394484476804052396912675183100114002128805712962412486716051404800), (1044, 11851802023543487706376578554085002976901463314748703565002898720305523502561918318177017102547282572146396475388195936641731189290680320000), (4116, 17344429249338335075209705727315195759419056858046503807943485118505162779599677268089098503744679803439791281721834591875704932082278236160), (16404, 1250805628228984389610339005326570297877373897079539808144469956295712667414045115429305149393463551451735359956373323033174901051850342400), (262180, 6090345303573908289399597564239873977201561501277753598081545508962463158526251277986172658470916823801275863686721449943203644774060032000), (262228, 18312612527900328283209201506857538370171774697302016596315257902825779060981627079136174500256427334681780826963890037779571315488106004480), (262420, 12676212849078023215726682948800665693455403305926900727263155157228438796496927194338584167509018312018515300806066151488125593107360563200), (263188, 9454092362974308273327175944404355097000603777966338157685775385388133997676381706058172666003944838556750190098383134714960397259983462400), (266260, 6758716015614127791462807935449388443467675375490667191910172062224787206241949462893717036546678635132642940076263773109198756966661457920), (278548, 7593076147306028553273340403837290498013221076861062878139232197397242103385189182249125237217169446286734841252011643227333467764310364160), (1048660, 13397961643821826918537513030338968011287235868135514231285767595369664741280547455572233273945862248111443194788661081170582731776373935104), (1048852, 3843252809398849230613045829456876280370074328389467066676017775174902832317786102338783742723082087395984323852609059746699000967581416320), (1049608, 498030633629076330522792734871611138929437793911042738283998686106144886821683650665332006259837924049922939310252316344010277117811916800), (1049620, 4751025503916623722586704985087505935804523844562891020494259089187053903762629433652366349377399463101034546592734813570265296703788610816), (1052692, 11919969537118997080335147656892393688670581765475886662238215571341499618811932340060153663850779251295576501318339221954443460502101719040), (1064980, 6911572896712532804476486972856143707337243895716982834258190211390971091922240056005110789822282623442611255487728776555049010805416847360)]
theorem sparseBlock066_data : sparseBlock066 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (498030633629076330522792734871611138929437793911042738283998686106144886821683650665332006259837924049922939310252316344010277117811916800 : Int) coeff0685) (CoefficientMerge.scale (4204563572593124919096110457911219194830166420570913992501828249324512472413302047908328061980735337472528075364885308586661395737113395200 : Int) coeff0686)) (CoefficientMerge.merge (CoefficientMerge.scale (27830134652085706025220612759063305029735707305684386529464540204370810386788952734824096946590817317637943331238812400766019950199830118400 : Int) coeff0687) (CoefficientMerge.merge (CoefficientMerge.scale (19108075977377698268738757380353069560687427777712557899167192917462754914765242825257919063637954862632858777543867693204640145727169740800 : Int) coeff0688) (CoefficientMerge.scale (11851802023543487706376578554085002976901463314748703565002898720305523502561918318177017102547282572146396475388195936641731189290680320000 : Int) coeff0689)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (17344429249338335075209705727315195759419056858046503807943485118505162779599677268089098503744679803439791281721834591875704932082278236160 : Int) coeff0690) (CoefficientMerge.scale (1250805628228984389610339005326570297877373897079539808144469956295712667414045115429305149393463551451735359956373323033174901051850342400 : Int) coeff0691)) (CoefficientMerge.merge (CoefficientMerge.scale (6090345303573908289399597564239873977201561501277753598081545508962463158526251277986172658470916823801275863686721449943203644774060032000 : Int) coeff0692) (CoefficientMerge.merge (CoefficientMerge.scale (18312612527900328283209201506857538370171774697302016596315257902825779060981627079136174500256427334681780826963890037779571315488106004480 : Int) coeff0693) (CoefficientMerge.scale (12676212849078023215726682948800665693455403305926900727263155157228438796496927194338584167509018312018515300806066151488125593107360563200 : Int) coeff0694))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (9454092362974308273327175944404355097000603777966338157685775385388133997676381706058172666003944838556750190098383134714960397259983462400 : Int) coeff0695) (CoefficientMerge.scale (6758716015614127791462807935449388443467675375490667191910172062224787206241949462893717036546678635132642940076263773109198756966661457920 : Int) coeff0696)) (CoefficientMerge.merge (CoefficientMerge.scale (7593076147306028553273340403837290498013221076861062878139232197397242103385189182249125237217169446286734841252011643227333467764310364160 : Int) coeff0697) (CoefficientMerge.merge (CoefficientMerge.scale (13397961643821826918537513030338968011287235868135514231285767595369664741280547455572233273945862248111443194788661081170582731776373935104 : Int) coeff0698) (CoefficientMerge.scale (3843252809398849230613045829456876280370074328389467066676017775174902832317786102338783742723082087395984323852609059746699000967581416320 : Int) coeff0699)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (4751025503916623722586704985087505935804523844562891020494259089187053903762629433652366349377399463101034546592734813570265296703788610816 : Int) coeff0700) (CoefficientMerge.scale (11919969537118997080335147656892393688670581765475886662238215571341499618811932340060153663850779251295576501318339221954443460502101719040 : Int) coeff0701)) (CoefficientMerge.merge (CoefficientMerge.scale (6911572896712532804476486972856143707337243895716982834258190211390971091922240056005110789822282623442611255487728776555049010805416847360 : Int) coeff0702) (CoefficientMerge.merge (CoefficientMerge.scale (7104491216748488109296511953570578387050021488114653919343597318928788669934901957307981229226002415050412232972144797022012070950513868800 : Int) coeff0703) (CoefficientMerge.scale (5431739092774544569194052124480373687350335275348637142330681954404757148394484476804052396912675183100114002128805712962412486716051404800 : Int) coeff0704)))))) := by decide +kernel
theorem sparseBlock066_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock066 := by
  rw [sparseBlock066_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted0685_nonneg g t z hg hA hB ht hz hw) (weighted0686_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0687_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0688_nonneg g t z hg hA hB ht hz hw) (weighted0689_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0690_nonneg g t z hg hA hB ht hz hw) (weighted0691_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0692_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0693_nonneg g t z hg hA hB ht hz hw) (weighted0694_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted0695_nonneg g t z hg hA hB ht hz hw) (weighted0696_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0697_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0698_nonneg g t z hg hA hB ht hz hw) (weighted0699_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0700_nonneg g t z hg hA hB ht hz hw) (weighted0701_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0702_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0703_nonneg g t z hg hA hB ht hz hw) (weighted0704_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
