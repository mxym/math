import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff1065 : CoefficientMerge.Poly :=
  [(1458176, 1)]
noncomputable def atom1065 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 7) ^ 1 * (g 8) ^ 2 * (t) ^ 1 * (z) ^ 1)
theorem atom1065_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1065 g t z = CoefficientMerge.eval (monomial g t z) coeff1065 := by
  norm_num [atom1065, coeff1065, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1065_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1065 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1065]
  positivity
theorem weighted1065_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2049321876287330521398070569579103648795588202906893099062225729452321768047954743928037921234655443147502612954908250008393988861611059200 : Int) coeff1065) := by
  rw [CoefficientMerge.eval_scale, ← atom1065_identity]
  exact mul_nonneg (by norm_num) (atom1065_nonneg g t z hg hA hB ht hz hw)

def coeff1066 : CoefficientMerge.Poly :=
  [(2146304, 1)]
noncomputable def atom1066 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 7) ^ 3 * (z) ^ 2)
theorem atom1066_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1066 g t z = CoefficientMerge.eval (monomial g t z) coeff1066 := by
  norm_num [atom1066, coeff1066, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1066_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1066 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1066]
  positivity
theorem weighted1066_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (644383190120364162090626118934005552578422618831669692693569035419160483261581157108598974301428670820167529953668915551336441458324544000 : Int) coeff1066) := by
  rw [CoefficientMerge.eval_scale, ← atom1066_identity]
  exact mul_nonneg (by norm_num) (atom1066_nonneg g t z hg hA hB ht hz hw)

def coeff1067 : CoefficientMerge.Poly :=
  [(2195456, 1)]
noncomputable def atom1067 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 7) ^ 2 * (g 8) ^ 1 * (z) ^ 2)
theorem atom1067_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1067 g t z = CoefficientMerge.eval (monomial g t z) coeff1067 := by
  norm_num [atom1067, coeff1067, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1067_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1067 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1067]
  positivity
theorem weighted1067_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1840780067874548646071565906804202194461290855807832637201498162629595799541689041726008405221206461067695818606010819686426262110703462400 : Int) coeff1067) := by
  rw [CoefficientMerge.eval_scale, ← atom1067_identity]
  exact mul_nonneg (by norm_num) (atom1067_nonneg g t z hg hA hB ht hz hw)

def coeff1068 : CoefficientMerge.Poly :=
  [(2244608, 1)]
noncomputable def atom1068 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 7) ^ 1 * (g 8) ^ 2 * (z) ^ 2)
theorem atom1068_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1068 g t z = CoefficientMerge.eval (monomial g t z) coeff1068 := by
  norm_num [atom1068, coeff1068, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1068_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1068 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1068]
  positivity
theorem weighted1068_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (904881688703926093071622673185347464934751991759368210915586626080045148844358870292436365884298106449527943620140505992348366632336128000 : Int) coeff1068) := by
  rw [CoefficientMerge.eval_scale, ← atom1068_identity]
  exact mul_nonneg (by norm_num) (atom1068_nonneg g t z hg hA hB ht hz hw)

def coeff1069 : CoefficientMerge.Poly :=
  [(786528, 1)]
noncomputable def atom1069 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 2 * (g 3) ^ 1 * (t) ^ 3)
theorem atom1069_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1069 g t z = CoefficientMerge.eval (monomial g t z) coeff1069 := by
  norm_num [atom1069, coeff1069, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1069_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1069 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1069]
  positivity
theorem weighted1069_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (145987174897015885532952432333606747110962931169875254318606352274490706096557937928373008703815998417871749555454828546013943465362329600 : Int) coeff1069) := by
  rw [CoefficientMerge.eval_scale, ← atom1069_identity]
  exact mul_nonneg (by norm_num) (atom1069_nonneg g t z hg hA hB ht hz hw)

def coeff1070 : CoefficientMerge.Poly :=
  [(786720, 1)]
noncomputable def atom1070 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 2 * (g 4) ^ 1 * (t) ^ 3)
theorem atom1070_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1070 g t z = CoefficientMerge.eval (monomial g t z) coeff1070 := by
  norm_num [atom1070, coeff1070, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1070_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1070 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1070]
  positivity
theorem weighted1070_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (115103813132975008173584756600364093484966116673852499860106926012162141928848412011554303200304965162520592226685321975554310803558553600 : Int) coeff1070) := by
  rw [CoefficientMerge.eval_scale, ← atom1070_identity]
  exact mul_nonneg (by norm_num) (atom1070_nonneg g t z hg hA hB ht hz hw)

def coeff1071 : CoefficientMerge.Poly :=
  [(786576, 1)]
noncomputable def atom1071 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 2 * (t) ^ 3)
theorem atom1071_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1071 g t z = CoefficientMerge.eval (monomial g t z) coeff1071 := by
  norm_num [atom1071, coeff1071, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1071_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1071 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1071]
  positivity
theorem weighted1071_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (20971183332447146304690390221954155175868498072649307783998335547595052827486946762474459536154089699197743758923249272453705825247449600 : Int) coeff1071) := by
  rw [CoefficientMerge.eval_scale, ← atom1071_identity]
  exact mul_nonneg (by norm_num) (atom1071_nonneg g t z hg hA hB ht hz hw)

def coeff1072 : CoefficientMerge.Poly :=
  [(786768, 1)]
noncomputable def atom1072 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 4) ^ 1 * (t) ^ 3)
theorem atom1072_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1072 g t z = CoefficientMerge.eval (monomial g t z) coeff1072 := by
  norm_num [atom1072, coeff1072, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1072_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1072 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1072]
  positivity
theorem weighted1072_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (103342765335247353488817536817370815374932882978274009512924282909708482416983574001872030837444737618439458727001861461677563743670355200 : Int) coeff1072) := by
  rw [CoefficientMerge.eval_scale, ← atom1072_identity]
  exact mul_nonneg (by norm_num) (atom1072_nonneg g t z hg hA hB ht hz hw)

def coeff1073 : CoefficientMerge.Poly :=
  [(787536, 1)]
noncomputable def atom1073 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 5) ^ 1 * (t) ^ 3)
theorem atom1073_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1073 g t z = CoefficientMerge.eval (monomial g t z) coeff1073 := by
  norm_num [atom1073, coeff1073, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1073_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1073 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1073]
  positivity
theorem weighted1073_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (130465358798520783304316502417701840342054359981119900132811285412079840818575767913396233489323261444931716691794105163282895045739500800 : Int) coeff1073) := by
  rw [CoefficientMerge.eval_scale, ← atom1073_identity]
  exact mul_nonneg (by norm_num) (atom1073_nonneg g t z hg hA hB ht hz hw)

def coeff1074 : CoefficientMerge.Poly :=
  [(790608, 1)]
noncomputable def atom1074 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 6) ^ 1 * (t) ^ 3)
theorem atom1074_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1074 g t z = CoefficientMerge.eval (monomial g t z) coeff1074 := by
  norm_num [atom1074, coeff1074, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1074_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1074 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1074]
  positivity
theorem weighted1074_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (136534629726572206520212817119399538667394599404159520232207947804714377246198734139075929403411000038329564220487956765358514998920577280 : Int) coeff1074) := by
  rw [CoefficientMerge.eval_scale, ← atom1074_identity]
  exact mul_nonneg (by norm_num) (atom1074_nonneg g t z hg hA hB ht hz hw)

def coeff1075 : CoefficientMerge.Poly :=
  [(802896, 1)]
noncomputable def atom1075 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 7) ^ 1 * (t) ^ 3)
theorem atom1075_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1075 g t z = CoefficientMerge.eval (monomial g t z) coeff1075 := by
  norm_num [atom1075, coeff1075, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1075_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1075 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1075]
  positivity
theorem weighted1075_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (121556215226235158255910992473756386856839985868639390895611538498764585450414728576720790743818861923870037206848464989560245875682950400 : Int) coeff1075) := by
  rw [CoefficientMerge.eval_scale, ← atom1075_identity]
  exact mul_nonneg (by norm_num) (atom1075_nonneg g t z hg hA hB ht hz hw)

def coeff1076 : CoefficientMerge.Poly :=
  [(852048, 1)]
noncomputable def atom1076 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 8) ^ 1 * (t) ^ 3)
theorem atom1076_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1076 g t z = CoefficientMerge.eval (monomial g t z) coeff1076 := by
  norm_num [atom1076, coeff1076, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1076_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1076 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1076]
  positivity
theorem weighted1076_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (95896728677448678888472922499647307527555494610432787903835481925421545093172087096335428530233113180230564053940981537002205319055648000 : Int) coeff1076) := by
  rw [CoefficientMerge.eval_scale, ← atom1076_identity]
  exact mul_nonneg (by norm_num) (atom1076_nonneg g t z hg hA hB ht hz hw)

def coeff1077 : CoefficientMerge.Poly :=
  [(1573008, 1)]
noncomputable def atom1077 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 2 * (t) ^ 2 * (z) ^ 1)
theorem atom1077_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1077 g t z = CoefficientMerge.eval (monomial g t z) coeff1077 := by
  norm_num [atom1077, coeff1077, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1077_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1077 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1077]
  positivity
theorem weighted1077_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (268564395539239731839395121711388435148432628184780278254493904195985591647003478033093997928216528082302211560313259633156115051210048000 : Int) coeff1077) := by
  rw [CoefficientMerge.eval_scale, ← atom1077_identity]
  exact mul_nonneg (by norm_num) (atom1077_nonneg g t z hg hA hB ht hz hw)

def coeff1078 : CoefficientMerge.Poly :=
  [(1573200, 1)]
noncomputable def atom1078 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 4) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1078_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1078 g t z = CoefficientMerge.eval (monomial g t z) coeff1078 := by
  norm_num [atom1078, coeff1078, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1078_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1078 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1078]
  positivity
theorem weighted1078_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (588036996937273531011384053426394383571057512564904816055225634627271721350949210621260591444622241331045036103624318886852676319105453920 : Int) coeff1078) := by
  rw [CoefficientMerge.eval_scale, ← atom1078_identity]
  exact mul_nonneg (by norm_num) (atom1078_nonneg g t z hg hA hB ht hz hw)

def coeff1079 : CoefficientMerge.Poly :=
  [(1573968, 1)]
noncomputable def atom1079 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 5) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1079_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1079 g t z = CoefficientMerge.eval (monomial g t z) coeff1079 := by
  norm_num [atom1079, coeff1079, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1079_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1079 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1079]
  positivity
theorem weighted1079_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (479503695692481427918814005895706394985882028988790274109405874815793668739140990310228058720341784560484309626408052872985813381767196960 : Int) coeff1079) := by
  rw [CoefficientMerge.eval_scale, ← atom1079_identity]
  exact mul_nonneg (by norm_num) (atom1079_nonneg g t z hg hA hB ht hz hw)

def coeff1080 : CoefficientMerge.Poly :=
  [(1577040, 1)]
noncomputable def atom1080 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 6) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1080_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1080 g t z = CoefficientMerge.eval (monomial g t z) coeff1080 := by
  norm_num [atom1080, coeff1080, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1080_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1080 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1080]
  positivity
theorem weighted1080_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (433453468563340191649945442056939543459200747131102446956973206880602486111691082575685966667248274472095379459874966654373622618313438880 : Int) coeff1080) := by
  rw [CoefficientMerge.eval_scale, ← atom1080_identity]
  exact mul_nonneg (by norm_num) (atom1080_nonneg g t z hg hA hB ht hz hw)

def coeff1081 : CoefficientMerge.Poly :=
  [(1589328, 1)]
noncomputable def atom1081 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 7) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1081_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1081 g t z = CoefficientMerge.eval (monomial g t z) coeff1081 := by
  norm_num [atom1081, coeff1081, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1081_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1081 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1081]
  positivity
theorem weighted1081_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (378972349327551259563286454000980398713420694345752681576521019911297225693955845403956040252636282219074431230722969464180123902886859680 : Int) coeff1081) := by
  rw [CoefficientMerge.eval_scale, ← atom1081_identity]
  exact mul_nonneg (by norm_num) (atom1081_nonneg g t z hg hA hB ht hz hw)

def coeff1082 : CoefficientMerge.Poly :=
  [(1638480, 1)]
noncomputable def atom1082 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 8) ^ 1 * (t) ^ 2 * (z) ^ 1)
theorem atom1082_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1082 g t z = CoefficientMerge.eval (monomial g t z) coeff1082 := by
  norm_num [atom1082, coeff1082, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1082_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1082 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1082]
  positivity
theorem weighted1082_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (249279769926449625123355480011882453954373630360992091461273830674094848499277555017613604465110134428187895048862656414332087730607090080 : Int) coeff1082) := by
  rw [CoefficientMerge.eval_scale, ← atom1082_identity]
  exact mul_nonneg (by norm_num) (atom1082_nonneg g t z hg hA hB ht hz hw)

def coeff1083 : CoefficientMerge.Poly :=
  [(786960, 1)]
noncomputable def atom1083 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 2 * (t) ^ 3)
theorem atom1083_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1083 g t z = CoefficientMerge.eval (monomial g t z) coeff1083 := by
  norm_num [atom1083, coeff1083, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1083_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1083 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1083]
  positivity
theorem weighted1083_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (53853213221716445614346620543117563228866565951766939152387399371319091418670620818458114079932765940898869997384533793780838969209990400 : Int) coeff1083) := by
  rw [CoefficientMerge.eval_scale, ← atom1083_identity]
  exact mul_nonneg (by norm_num) (atom1083_nonneg g t z hg hA hB ht hz hw)

def coeff1084 : CoefficientMerge.Poly :=
  [(787728, 1)]
noncomputable def atom1084 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 5) ^ 1 * (t) ^ 3)
theorem atom1084_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1084 g t z = CoefficientMerge.eval (monomial g t z) coeff1084 := by
  norm_num [atom1084, coeff1084, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1084_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1084 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1084]
  positivity
theorem weighted1084_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (141790480052027722472976074934032949996345216993256729286101233052744869140603261434664870517126834476059120050472609111966225708223059200 : Int) coeff1084) := by
  rw [CoefficientMerge.eval_scale, ← atom1084_identity]
  exact mul_nonneg (by norm_num) (atom1084_nonneg g t z hg hA hB ht hz hw)

def sparseBlock085 : CoefficientMerge.Poly :=
  [(786528, 145987174897015885532952432333606747110962931169875254318606352274490706096557937928373008703815998417871749555454828546013943465362329600), (786576, 20971183332447146304690390221954155175868498072649307783998335547595052827486946762474459536154089699197743758923249272453705825247449600), (786720, 115103813132975008173584756600364093484966116673852499860106926012162141928848412011554303200304965162520592226685321975554310803558553600), (786768, 103342765335247353488817536817370815374932882978274009512924282909708482416983574001872030837444737618439458727001861461677563743670355200), (786960, 53853213221716445614346620543117563228866565951766939152387399371319091418670620818458114079932765940898869997384533793780838969209990400), (787536, 130465358798520783304316502417701840342054359981119900132811285412079840818575767913396233489323261444931716691794105163282895045739500800), (787728, 141790480052027722472976074934032949996345216993256729286101233052744869140603261434664870517126834476059120050472609111966225708223059200), (790608, 136534629726572206520212817119399538667394599404159520232207947804714377246198734139075929403411000038329564220487956765358514998920577280), (802896, 121556215226235158255910992473756386856839985868639390895611538498764585450414728576720790743818861923870037206848464989560245875682950400), (852048, 95896728677448678888472922499647307527555494610432787903835481925421545093172087096335428530233113180230564053940981537002205319055648000), (1458176, 2049321876287330521398070569579103648795588202906893099062225729452321768047954743928037921234655443147502612954908250008393988861611059200), (1573008, 268564395539239731839395121711388435148432628184780278254493904195985591647003478033093997928216528082302211560313259633156115051210048000), (1573200, 588036996937273531011384053426394383571057512564904816055225634627271721350949210621260591444622241331045036103624318886852676319105453920), (1573968, 479503695692481427918814005895706394985882028988790274109405874815793668739140990310228058720341784560484309626408052872985813381767196960), (1577040, 433453468563340191649945442056939543459200747131102446956973206880602486111691082575685966667248274472095379459874966654373622618313438880), (1589328, 378972349327551259563286454000980398713420694345752681576521019911297225693955845403956040252636282219074431230722969464180123902886859680), (1638480, 249279769926449625123355480011882453954373630360992091461273830674094848499277555017613604465110134428187895048862656414332087730607090080), (2146304, 644383190120364162090626118934005552578422618831669692693569035419160483261581157108598974301428670820167529953668915551336441458324544000), (2195456, 1840780067874548646071565906804202194461290855807832637201498162629595799541689041726008405221206461067695818606010819686426262110703462400), (2244608, 904881688703926093071622673185347464934751991759368210915586626080045148844358870292436365884298106449527943620140505992348366632336128000)]
theorem sparseBlock085_data : sparseBlock085 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (2049321876287330521398070569579103648795588202906893099062225729452321768047954743928037921234655443147502612954908250008393988861611059200 : Int) coeff1065) (CoefficientMerge.scale (644383190120364162090626118934005552578422618831669692693569035419160483261581157108598974301428670820167529953668915551336441458324544000 : Int) coeff1066)) (CoefficientMerge.merge (CoefficientMerge.scale (1840780067874548646071565906804202194461290855807832637201498162629595799541689041726008405221206461067695818606010819686426262110703462400 : Int) coeff1067) (CoefficientMerge.merge (CoefficientMerge.scale (904881688703926093071622673185347464934751991759368210915586626080045148844358870292436365884298106449527943620140505992348366632336128000 : Int) coeff1068) (CoefficientMerge.scale (145987174897015885532952432333606747110962931169875254318606352274490706096557937928373008703815998417871749555454828546013943465362329600 : Int) coeff1069)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (115103813132975008173584756600364093484966116673852499860106926012162141928848412011554303200304965162520592226685321975554310803558553600 : Int) coeff1070) (CoefficientMerge.scale (20971183332447146304690390221954155175868498072649307783998335547595052827486946762474459536154089699197743758923249272453705825247449600 : Int) coeff1071)) (CoefficientMerge.merge (CoefficientMerge.scale (103342765335247353488817536817370815374932882978274009512924282909708482416983574001872030837444737618439458727001861461677563743670355200 : Int) coeff1072) (CoefficientMerge.merge (CoefficientMerge.scale (130465358798520783304316502417701840342054359981119900132811285412079840818575767913396233489323261444931716691794105163282895045739500800 : Int) coeff1073) (CoefficientMerge.scale (136534629726572206520212817119399538667394599404159520232207947804714377246198734139075929403411000038329564220487956765358514998920577280 : Int) coeff1074))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (121556215226235158255910992473756386856839985868639390895611538498764585450414728576720790743818861923870037206848464989560245875682950400 : Int) coeff1075) (CoefficientMerge.scale (95896728677448678888472922499647307527555494610432787903835481925421545093172087096335428530233113180230564053940981537002205319055648000 : Int) coeff1076)) (CoefficientMerge.merge (CoefficientMerge.scale (268564395539239731839395121711388435148432628184780278254493904195985591647003478033093997928216528082302211560313259633156115051210048000 : Int) coeff1077) (CoefficientMerge.merge (CoefficientMerge.scale (588036996937273531011384053426394383571057512564904816055225634627271721350949210621260591444622241331045036103624318886852676319105453920 : Int) coeff1078) (CoefficientMerge.scale (479503695692481427918814005895706394985882028988790274109405874815793668739140990310228058720341784560484309626408052872985813381767196960 : Int) coeff1079)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (433453468563340191649945442056939543459200747131102446956973206880602486111691082575685966667248274472095379459874966654373622618313438880 : Int) coeff1080) (CoefficientMerge.scale (378972349327551259563286454000980398713420694345752681576521019911297225693955845403956040252636282219074431230722969464180123902886859680 : Int) coeff1081)) (CoefficientMerge.merge (CoefficientMerge.scale (249279769926449625123355480011882453954373630360992091461273830674094848499277555017613604465110134428187895048862656414332087730607090080 : Int) coeff1082) (CoefficientMerge.merge (CoefficientMerge.scale (53853213221716445614346620543117563228866565951766939152387399371319091418670620818458114079932765940898869997384533793780838969209990400 : Int) coeff1083) (CoefficientMerge.scale (141790480052027722472976074934032949996345216993256729286101233052744869140603261434664870517126834476059120050472609111966225708223059200 : Int) coeff1084)))))) := by decide +kernel
theorem sparseBlock085_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock085 := by
  rw [sparseBlock085_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted1065_nonneg g t z hg hA hB ht hz hw) (weighted1066_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1067_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1068_nonneg g t z hg hA hB ht hz hw) (weighted1069_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1070_nonneg g t z hg hA hB ht hz hw) (weighted1071_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1072_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1073_nonneg g t z hg hA hB ht hz hw) (weighted1074_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted1075_nonneg g t z hg hA hB ht hz hw) (weighted1076_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1077_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1078_nonneg g t z hg hA hB ht hz hw) (weighted1079_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1080_nonneg g t z hg hA hB ht hz hw) (weighted1081_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1082_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1083_nonneg g t z hg hA hB ht hz hw) (weighted1084_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
