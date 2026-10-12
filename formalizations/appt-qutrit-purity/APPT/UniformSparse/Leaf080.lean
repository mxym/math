import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff0965 : CoefficientMerge.Poly :=
  [(541184, 1)]
noncomputable def atom0965 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 2 * (g 7) ^ 1 * (t) ^ 2)
theorem atom0965_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0965 g t z = CoefficientMerge.eval (monomial g t z) coeff0965 := by
  norm_num [atom0965, coeff0965, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0965_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0965 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0965]
  positivity
theorem weighted0965_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1426406674616953354650267917950896135769292201440548365197605257776138205746847045608093648502022915055321085472741829155473509867158681600 : Int) coeff0965) := by
  rw [CoefficientMerge.eval_scale, ← atom0965_identity]
  exact mul_nonneg (by norm_num) (atom0965_nonneg g t z hg hA hB ht hz hw)

def coeff0966 : CoefficientMerge.Poly :=
  [(590336, 1)]
noncomputable def atom0966 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 2 * (g 8) ^ 1 * (t) ^ 2)
theorem atom0966_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0966 g t z = CoefficientMerge.eval (monomial g t z) coeff0966 := by
  norm_num [atom0966, coeff0966, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0966_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0966 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0966]
  positivity
theorem weighted0966_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2834747965964221937413631314105384604514121532993520833647527508645385422125229674075558193086597915347284085553556597691847667393760716800 : Int) coeff0966) := by
  rw [CoefficientMerge.eval_scale, ← atom0966_identity]
  exact mul_nonneg (by norm_num) (atom0966_nonneg g t z hg hA hB ht hz hw)

def coeff0967 : CoefficientMerge.Poly :=
  [(1315328, 1)]
noncomputable def atom0967 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 2 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0967_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0967 g t z = CoefficientMerge.eval (monomial g t z) coeff0967 := by
  norm_num [atom0967, coeff0967, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0967_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0967 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0967]
  positivity
theorem weighted0967_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2475129607843638669431048320128806136434972094604122907329335005851390596670109791959190351629316002199834930147897861282664618160842362240 : Int) coeff0967) := by
  rw [CoefficientMerge.eval_scale, ← atom0967_identity]
  exact mul_nonneg (by norm_num) (atom0967_nonneg g t z hg hA hB ht hz hw)

def coeff0968 : CoefficientMerge.Poly :=
  [(1327616, 1)]
noncomputable def atom0968 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 2 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0968_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0968 g t z = CoefficientMerge.eval (monomial g t z) coeff0968 := by
  norm_num [atom0968, coeff0968, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0968_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0968 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0968]
  positivity
theorem weighted0968_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2753471936031993075361565604159427325660116216797207627892550564014314547198099993570091701008781741966320486063863102922492810581382645120 : Int) coeff0968) := by
  rw [CoefficientMerge.eval_scale, ← atom0968_identity]
  exact mul_nonneg (by norm_num) (atom0968_nonneg g t z hg hA hB ht hz hw)

def coeff0969 : CoefficientMerge.Poly :=
  [(1376768, 1)]
noncomputable def atom0969 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 2 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0969_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0969 g t z = CoefficientMerge.eval (monomial g t z) coeff0969 := by
  norm_num [atom0969, coeff0969, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0969_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0969 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0969]
  positivity
theorem weighted0969_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5530995597341581388279005627879777182142331010647579474981387573145222087435907643306963574909782585943569725076273108422020359464903178880 : Int) coeff0969) := by
  rw [CoefficientMerge.eval_scale, ← atom0969_identity]
  exact mul_nonneg (by norm_num) (atom0969_nonneg g t z hg hA hB ht hz hw)

def coeff0970 : CoefficientMerge.Poly :=
  [(529664, 1)]
noncomputable def atom0970 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (t) ^ 2)
theorem atom0970_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0970 g t z = CoefficientMerge.eval (monomial g t z) coeff0970 := by
  norm_num [atom0970, coeff0970, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0970_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0970 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0970]
  positivity
theorem weighted0970_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1434787149023949606455588328891236853738702048628286406409520973077306215004423785174471160456681075391116658817415433017685906396683673600 : Int) coeff0970) := by
  rw [CoefficientMerge.eval_scale, ← atom0970_identity]
  exact mul_nonneg (by norm_num) (atom0970_nonneg g t z hg hA hB ht hz hw)

def coeff0971 : CoefficientMerge.Poly :=
  [(541952, 1)]
noncomputable def atom0971 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (t) ^ 2)
theorem atom0971_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0971 g t z = CoefficientMerge.eval (monomial g t z) coeff0971 := by
  norm_num [atom0971, coeff0971, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0971_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0971 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0971]
  positivity
theorem weighted0971_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2116612727239539787819865208334782693945107027584633426357171490573334816052313208500642972307803601449647575423406798999386243403819315200 : Int) coeff0971) := by
  rw [CoefficientMerge.eval_scale, ← atom0971_identity]
  exact mul_nonneg (by norm_num) (atom0971_nonneg g t z hg hA hB ht hz hw)

def coeff0972 : CoefficientMerge.Poly :=
  [(591104, 1)]
noncomputable def atom0972 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (t) ^ 2)
theorem atom0972_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0972 g t z = CoefficientMerge.eval (monomial g t z) coeff0972 := by
  norm_num [atom0972, coeff0972, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0972_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0972 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0972]
  positivity
theorem weighted0972_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2963670319726344398539178672233824001500849458735112134637392220551467003150591411530965316346761709067110623288541092758025697539637248000 : Int) coeff0972) := by
  rw [CoefficientMerge.eval_scale, ← atom0972_identity]
  exact mul_nonneg (by norm_num) (atom0972_nonneg g t z hg hA hB ht hz hw)

def coeff0973 : CoefficientMerge.Poly :=
  [(1316096, 1)]
noncomputable def atom0973 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0973_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0973 g t z = CoefficientMerge.eval (monomial g t z) coeff0973 := by
  norm_num [atom0973, coeff0973, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0973_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0973 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0973]
  positivity
theorem weighted0973_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2926720845299117797839897913708623055323400416377574605804434522119142764802985480008465715267068982051176940250998633462735700928597624320 : Int) coeff0973) := by
  rw [CoefficientMerge.eval_scale, ← atom0973_identity]
  exact mul_nonneg (by norm_num) (atom0973_nonneg g t z hg hA hB ht hz hw)

def coeff0974 : CoefficientMerge.Poly :=
  [(1328384, 1)]
noncomputable def atom0974 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0974_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0974 g t z = CoefficientMerge.eval (monomial g t z) coeff0974 := by
  norm_num [atom0974, coeff0974, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0974_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0974 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0974]
  positivity
theorem weighted0974_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3905225908405272853532687964066714280128018928867171408183447634688660117674261252860812364093182318818743920559973773230759792496052651520 : Int) coeff0974) := by
  rw [CoefficientMerge.eval_scale, ← atom0974_identity]
  exact mul_nonneg (by norm_num) (atom0974_nonneg g t z hg hA hB ht hz hw)

def coeff0975 : CoefficientMerge.Poly :=
  [(1377536, 1)]
noncomputable def atom0975 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0975_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0975 g t z = CoefficientMerge.eval (monomial g t z) coeff0975 := by
  norm_num [atom0975, coeff0975, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0975_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0975 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0975]
  positivity
theorem weighted0975_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5462182046741434124311336481925311713196649965018901099900306581112131113114739285545585332244405375308039900981517630948488435566609118720 : Int) coeff0975) := by
  rw [CoefficientMerge.eval_scale, ← atom0975_identity]
  exact mul_nonneg (by norm_num) (atom0975_nonneg g t z hg hA hB ht hz hw)

def coeff0976 : CoefficientMerge.Poly :=
  [(532736, 1)]
noncomputable def atom0976 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 6) ^ 2 * (t) ^ 2)
theorem atom0976_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0976 g t z = CoefficientMerge.eval (monomial g t z) coeff0976 := by
  norm_num [atom0976, coeff0976, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0976_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0976 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0976]
  positivity
theorem weighted0976_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (926779280644271539065510756972912364699329418900504500576543959047728809352751503415476184618583609144373784880949478754572713042905702400 : Int) coeff0976) := by
  rw [CoefficientMerge.eval_scale, ← atom0976_identity]
  exact mul_nonneg (by norm_num) (atom0976_nonneg g t z hg hA hB ht hz hw)

def coeff0977 : CoefficientMerge.Poly :=
  [(545024, 1)]
noncomputable def atom0977 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (t) ^ 2)
theorem atom0977_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0977 g t z = CoefficientMerge.eval (monomial g t z) coeff0977 := by
  norm_num [atom0977, coeff0977, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0977_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0977 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0977]
  positivity
theorem weighted0977_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2730556515903646896086538509810480761547613300738743352529586919358615365322880072015067034683515128169289955020492459594465042158269286400 : Int) coeff0977) := by
  rw [CoefficientMerge.eval_scale, ← atom0977_identity]
  exact mul_nonneg (by norm_num) (atom0977_nonneg g t z hg hA hB ht hz hw)

def coeff0978 : CoefficientMerge.Poly :=
  [(594176, 1)]
noncomputable def atom0978 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (t) ^ 2)
theorem atom0978_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0978 g t z = CoefficientMerge.eval (monomial g t z) coeff0978 := by
  norm_num [atom0978, coeff0978, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0978_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0978 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0978]
  positivity
theorem weighted0978_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3176508262636610531599405732520041783682380741407229016171803228354389735554139393041566397530776565914260851260370480763673737892921446400 : Int) coeff0978) := by
  rw [CoefficientMerge.eval_scale, ← atom0978_identity]
  exact mul_nonneg (by norm_num) (atom0978_nonneg g t z hg hA hB ht hz hw)

def coeff0979 : CoefficientMerge.Poly :=
  [(1319168, 1)]
noncomputable def atom0979 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 6) ^ 2 * (t) ^ 1 * (z) ^ 1)
theorem atom0979_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0979 g t z = CoefficientMerge.eval (monomial g t z) coeff0979 := by
  norm_num [atom0979, coeff0979, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0979_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0979 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0979]
  positivity
theorem weighted0979_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1919971807155932387433946907932023108994492549598839778202970143112920569435033126307275060129213880514936517312548769761248135574544421120 : Int) coeff0979) := by
  rw [CoefficientMerge.eval_scale, ← atom0979_identity]
  exact mul_nonneg (by norm_num) (atom0979_nonneg g t z hg hA hB ht hz hw)

def coeff0980 : CoefficientMerge.Poly :=
  [(1331456, 1)]
noncomputable def atom0980 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0980_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0980 g t z = CoefficientMerge.eval (monomial g t z) coeff0980 := by
  norm_num [atom0980, coeff0980, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0980_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0980 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0980]
  positivity
theorem weighted0980_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5177639630377967372236443925987677794244260301741844459972195219291539875514072233536495353882927576378038624356373610899469723835907312640 : Int) coeff0980) := by
  rw [CoefficientMerge.eval_scale, ← atom0980_identity]
  exact mul_nonneg (by norm_num) (atom0980_nonneg g t z hg hA hB ht hz hw)

def coeff0981 : CoefficientMerge.Poly :=
  [(1380608, 1)]
noncomputable def atom0981 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0981_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0981 g t z = CoefficientMerge.eval (monomial g t z) coeff0981 := by
  norm_num [atom0981, coeff0981, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0981_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0981 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0981]
  positivity
theorem weighted0981_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (6319904101087655530222995565780758116145045875521806882327732871327300097311348340367140697263726589019769607082466583736109628021411987840 : Int) coeff0981) := by
  rw [CoefficientMerge.eval_scale, ← atom0981_identity]
  exact mul_nonneg (by norm_num) (atom0981_nonneg g t z hg hA hB ht hz hw)

def coeff0982 : CoefficientMerge.Poly :=
  [(557312, 1)]
noncomputable def atom0982 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 7) ^ 2 * (t) ^ 2)
theorem atom0982_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0982 g t z = CoefficientMerge.eval (monomial g t z) coeff0982 := by
  norm_num [atom0982, coeff0982, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0982_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0982 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0982]
  positivity
theorem weighted0982_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1765205199964375283549016501665371512941770221003100042555629127585772442928382039564196841695979821185564849870200944502879727069565849600 : Int) coeff0982) := by
  rw [CoefficientMerge.eval_scale, ← atom0982_identity]
  exact mul_nonneg (by norm_num) (atom0982_nonneg g t z hg hA hB ht hz hw)

def coeff0983 : CoefficientMerge.Poly :=
  [(606464, 1)]
noncomputable def atom0983 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (t) ^ 2)
theorem atom0983_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0983 g t z = CoefficientMerge.eval (monomial g t z) coeff0983 := by
  norm_num [atom0983, coeff0983, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0983_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0983 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0983]
  positivity
theorem weighted0983_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4860827570514110502763386670511967667342959709416836393164986896137192072443311332307506535001883925464976664248252011515781002184137523200 : Int) coeff0983) := by
  rw [CoefficientMerge.eval_scale, ← atom0983_identity]
  exact mul_nonneg (by norm_num) (atom0983_nonneg g t z hg hA hB ht hz hw)

def coeff0984 : CoefficientMerge.Poly :=
  [(1343744, 1)]
noncomputable def atom0984 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 7) ^ 2 * (t) ^ 1 * (z) ^ 1)
theorem atom0984_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0984 g t z = CoefficientMerge.eval (monomial g t z) coeff0984 := by
  norm_num [atom0984, coeff0984, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0984_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0984 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0984]
  positivity
theorem weighted0984_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3264569365271951591059079504243016551324695943990313498810986220152537098085269650748388739136509726497258788784251453210473198839220395520 : Int) coeff0984) := by
  rw [CoefficientMerge.eval_scale, ← atom0984_identity]
  exact mul_nonneg (by norm_num) (atom0984_nonneg g t z hg hA hB ht hz hw)

def sparseBlock080 : CoefficientMerge.Poly :=
  [(529664, 1434787149023949606455588328891236853738702048628286406409520973077306215004423785174471160456681075391116658817415433017685906396683673600), (532736, 926779280644271539065510756972912364699329418900504500576543959047728809352751503415476184618583609144373784880949478754572713042905702400), (541184, 1426406674616953354650267917950896135769292201440548365197605257776138205746847045608093648502022915055321085472741829155473509867158681600), (541952, 2116612727239539787819865208334782693945107027584633426357171490573334816052313208500642972307803601449647575423406798999386243403819315200), (545024, 2730556515903646896086538509810480761547613300738743352529586919358615365322880072015067034683515128169289955020492459594465042158269286400), (557312, 1765205199964375283549016501665371512941770221003100042555629127585772442928382039564196841695979821185564849870200944502879727069565849600), (590336, 2834747965964221937413631314105384604514121532993520833647527508645385422125229674075558193086597915347284085553556597691847667393760716800), (591104, 2963670319726344398539178672233824001500849458735112134637392220551467003150591411530965316346761709067110623288541092758025697539637248000), (594176, 3176508262636610531599405732520041783682380741407229016171803228354389735554139393041566397530776565914260851260370480763673737892921446400), (606464, 4860827570514110502763386670511967667342959709416836393164986896137192072443311332307506535001883925464976664248252011515781002184137523200), (1315328, 2475129607843638669431048320128806136434972094604122907329335005851390596670109791959190351629316002199834930147897861282664618160842362240), (1316096, 2926720845299117797839897913708623055323400416377574605804434522119142764802985480008465715267068982051176940250998633462735700928597624320), (1319168, 1919971807155932387433946907932023108994492549598839778202970143112920569435033126307275060129213880514936517312548769761248135574544421120), (1327616, 2753471936031993075361565604159427325660116216797207627892550564014314547198099993570091701008781741966320486063863102922492810581382645120), (1328384, 3905225908405272853532687964066714280128018928867171408183447634688660117674261252860812364093182318818743920559973773230759792496052651520), (1331456, 5177639630377967372236443925987677794244260301741844459972195219291539875514072233536495353882927576378038624356373610899469723835907312640), (1343744, 3264569365271951591059079504243016551324695943990313498810986220152537098085269650748388739136509726497258788784251453210473198839220395520), (1376768, 5530995597341581388279005627879777182142331010647579474981387573145222087435907643306963574909782585943569725076273108422020359464903178880), (1377536, 5462182046741434124311336481925311713196649965018901099900306581112131113114739285545585332244405375308039900981517630948488435566609118720), (1380608, 6319904101087655530222995565780758116145045875521806882327732871327300097311348340367140697263726589019769607082466583736109628021411987840)]
theorem sparseBlock080_data : sparseBlock080 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1426406674616953354650267917950896135769292201440548365197605257776138205746847045608093648502022915055321085472741829155473509867158681600 : Int) coeff0965) (CoefficientMerge.scale (2834747965964221937413631314105384604514121532993520833647527508645385422125229674075558193086597915347284085553556597691847667393760716800 : Int) coeff0966)) (CoefficientMerge.merge (CoefficientMerge.scale (2475129607843638669431048320128806136434972094604122907329335005851390596670109791959190351629316002199834930147897861282664618160842362240 : Int) coeff0967) (CoefficientMerge.merge (CoefficientMerge.scale (2753471936031993075361565604159427325660116216797207627892550564014314547198099993570091701008781741966320486063863102922492810581382645120 : Int) coeff0968) (CoefficientMerge.scale (5530995597341581388279005627879777182142331010647579474981387573145222087435907643306963574909782585943569725076273108422020359464903178880 : Int) coeff0969)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1434787149023949606455588328891236853738702048628286406409520973077306215004423785174471160456681075391116658817415433017685906396683673600 : Int) coeff0970) (CoefficientMerge.scale (2116612727239539787819865208334782693945107027584633426357171490573334816052313208500642972307803601449647575423406798999386243403819315200 : Int) coeff0971)) (CoefficientMerge.merge (CoefficientMerge.scale (2963670319726344398539178672233824001500849458735112134637392220551467003150591411530965316346761709067110623288541092758025697539637248000 : Int) coeff0972) (CoefficientMerge.merge (CoefficientMerge.scale (2926720845299117797839897913708623055323400416377574605804434522119142764802985480008465715267068982051176940250998633462735700928597624320 : Int) coeff0973) (CoefficientMerge.scale (3905225908405272853532687964066714280128018928867171408183447634688660117674261252860812364093182318818743920559973773230759792496052651520 : Int) coeff0974))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (5462182046741434124311336481925311713196649965018901099900306581112131113114739285545585332244405375308039900981517630948488435566609118720 : Int) coeff0975) (CoefficientMerge.scale (926779280644271539065510756972912364699329418900504500576543959047728809352751503415476184618583609144373784880949478754572713042905702400 : Int) coeff0976)) (CoefficientMerge.merge (CoefficientMerge.scale (2730556515903646896086538509810480761547613300738743352529586919358615365322880072015067034683515128169289955020492459594465042158269286400 : Int) coeff0977) (CoefficientMerge.merge (CoefficientMerge.scale (3176508262636610531599405732520041783682380741407229016171803228354389735554139393041566397530776565914260851260370480763673737892921446400 : Int) coeff0978) (CoefficientMerge.scale (1919971807155932387433946907932023108994492549598839778202970143112920569435033126307275060129213880514936517312548769761248135574544421120 : Int) coeff0979)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (5177639630377967372236443925987677794244260301741844459972195219291539875514072233536495353882927576378038624356373610899469723835907312640 : Int) coeff0980) (CoefficientMerge.scale (6319904101087655530222995565780758116145045875521806882327732871327300097311348340367140697263726589019769607082466583736109628021411987840 : Int) coeff0981)) (CoefficientMerge.merge (CoefficientMerge.scale (1765205199964375283549016501665371512941770221003100042555629127585772442928382039564196841695979821185564849870200944502879727069565849600 : Int) coeff0982) (CoefficientMerge.merge (CoefficientMerge.scale (4860827570514110502763386670511967667342959709416836393164986896137192072443311332307506535001883925464976664248252011515781002184137523200 : Int) coeff0983) (CoefficientMerge.scale (3264569365271951591059079504243016551324695943990313498810986220152537098085269650748388739136509726497258788784251453210473198839220395520 : Int) coeff0984)))))) := by decide +kernel
theorem sparseBlock080_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock080 := by
  rw [sparseBlock080_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted0965_nonneg g t z hg hA hB ht hz hw) (weighted0966_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0967_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0968_nonneg g t z hg hA hB ht hz hw) (weighted0969_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0970_nonneg g t z hg hA hB ht hz hw) (weighted0971_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0972_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0973_nonneg g t z hg hA hB ht hz hw) (weighted0974_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted0975_nonneg g t z hg hA hB ht hz hw) (weighted0976_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0977_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0978_nonneg g t z hg hA hB ht hz hw) (weighted0979_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0980_nonneg g t z hg hA hB ht hz hw) (weighted0981_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0982_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0983_nonneg g t z hg hA hB ht hz hw) (weighted0984_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
