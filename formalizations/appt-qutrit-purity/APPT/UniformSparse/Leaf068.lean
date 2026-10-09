import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff0725 : CoefficientMerge.Poly :=
  [(1052932, 1)]
noncomputable def atom0725 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (z) ^ 1)
theorem atom0725_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0725 g t z = CoefficientMerge.eval (monomial g t z) coeff0725 := by
  norm_num [atom0725, coeff0725, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0725_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0725 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0725]
  positivity
theorem weighted0725_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (10549151662862415375945538988920986296498622582733190687701834720283343299219213063784936927814597158958978783866618579685128697548635708160 : Int) coeff0725) := by
  rw [CoefficientMerge.eval_scale, ← atom0725_identity]
  exact mul_nonneg (by norm_num) (atom0725_nonneg g t z hg hA hB ht hz hw)

def coeff0726 : CoefficientMerge.Poly :=
  [(1065220, 1)]
noncomputable def atom0726 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (z) ^ 1)
theorem atom0726_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0726 g t z = CoefficientMerge.eval (monomial g t z) coeff0726 := by
  norm_num [atom0726, coeff0726, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0726_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0726 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0726]
  positivity
theorem weighted0726_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (14803906841177952514768809629759107555202790149030685687929474152976991075409872785389641801950514356497725607400392016567265091576390133760 : Int) coeff0726) := by
  rw [CoefficientMerge.eval_scale, ← atom0726_identity]
  exact mul_nonneg (by norm_num) (atom0726_nonneg g t z hg hA hB ht hz hw)

def coeff0727 : CoefficientMerge.Poly :=
  [(1114372, 1)]
noncomputable def atom0727 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (z) ^ 1)
theorem atom0727_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0727 g t z = CoefficientMerge.eval (monomial g t z) coeff0727 := by
  norm_num [atom0727, coeff0727, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0727_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0727 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0727]
  positivity
theorem weighted0727_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (17958953945660143472006870434084693113709520498152926734959136269655756533508326534607680242350818452135371551377943466971298850221624125440 : Int) coeff0727) := by
  rw [CoefficientMerge.eval_scale, ← atom0727_identity]
  exact mul_nonneg (by norm_num) (atom0727_nonneg g t z hg hA hB ht hz hw)

def coeff0728 : CoefficientMerge.Poly :=
  [(5124, 1)]
noncomputable def atom0728 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1)
theorem atom0728_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0728 g t z = CoefficientMerge.eval (monomial g t z) coeff0728 := by
  norm_num [atom0728, coeff0728, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0728_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0728 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0728]
  positivity
theorem weighted0728_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2975466978697866627229801096187478097794640305621046891074063546036786611087000439760826969257048966267611917499645685628871607485902438400 : Int) coeff0728) := by
  rw [CoefficientMerge.eval_scale, ← atom0728_identity]
  exact mul_nonneg (by norm_num) (atom0728_nonneg g t z hg hA hB ht hz hw)

def coeff0729 : CoefficientMerge.Poly :=
  [(17412, 1)]
noncomputable def atom0729 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1)
theorem atom0729_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0729 g t z = CoefficientMerge.eval (monomial g t z) coeff0729 := by
  norm_num [atom0729, coeff0729, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0729_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0729 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0729]
  positivity
theorem weighted0729_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (492326697400915709581362513870214597694158018887816306854823580245216601907150712991162651109319741417653249091318076063965100598693068800 : Int) coeff0729) := by
  rw [CoefficientMerge.eval_scale, ← atom0729_identity]
  exact mul_nonneg (by norm_num) (atom0729_nonneg g t z hg hA hB ht hz hw)

def coeff0730 : CoefficientMerge.Poly :=
  [(66564, 1)]
noncomputable def atom0730 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1)
theorem atom0730_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0730 g t z = CoefficientMerge.eval (monomial g t z) coeff0730 := by
  norm_num [atom0730, coeff0730, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0730_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0730 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0730]
  positivity
theorem weighted0730_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (8491174973596889321153417281621920853811973439369302118634900428345611600686768856959967127699169228344479247472699700400487983185781555200 : Int) coeff0730) := by
  rw [CoefficientMerge.eval_scale, ← atom0730_identity]
  exact mul_nonneg (by norm_num) (atom0730_nonneg g t z hg hA hB ht hz hw)

def coeff0731 : CoefficientMerge.Poly :=
  [(267268, 1)]
noncomputable def atom0731 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (t) ^ 1)
theorem atom0731_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0731 g t z = CoefficientMerge.eval (monomial g t z) coeff0731 := by
  norm_num [atom0731, coeff0731, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0731_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0731 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0731]
  positivity
theorem weighted0731_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5093301650639285019776582298373896758913175264104570258675094291349884975216577976634155241257582375123512344274089072919390788183225113600 : Int) coeff0731) := by
  rw [CoefficientMerge.eval_scale, ← atom0731_identity]
  exact mul_nonneg (by norm_num) (atom0731_nonneg g t z hg hA hB ht hz hw)

def coeff0732 : CoefficientMerge.Poly :=
  [(279556, 1)]
noncomputable def atom0732 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (t) ^ 1)
theorem atom0732_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0732 g t z = CoefficientMerge.eval (monomial g t z) coeff0732 := by
  norm_num [atom0732, coeff0732, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0732_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0732 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0732]
  positivity
theorem weighted0732_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2751873850162710309775181689560159517939352797398417134335122669654771957006949587793440212406886252043049573527400884826807616032014592000 : Int) coeff0732) := by
  rw [CoefficientMerge.eval_scale, ← atom0732_identity]
  exact mul_nonneg (by norm_num) (atom0732_nonneg g t z hg hA hB ht hz hw)

def coeff0733 : CoefficientMerge.Poly :=
  [(328708, 1)]
noncomputable def atom0733 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (t) ^ 1)
theorem atom0733_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0733 g t z = CoefficientMerge.eval (monomial g t z) coeff0733 := by
  norm_num [atom0733, coeff0733, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0733_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0733 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0733]
  positivity
theorem weighted0733_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (6742635418469644808006380919872897349718969949045681793802096088718832063022953023735893454953769357116195306942697899145773192572074649600 : Int) coeff0733) := by
  rw [CoefficientMerge.eval_scale, ← atom0733_identity]
  exact mul_nonneg (by norm_num) (atom0733_nonneg g t z hg hA hB ht hz hw)

def coeff0734 : CoefficientMerge.Poly :=
  [(1050628, 1)]
noncomputable def atom0734 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 2 * (z) ^ 1)
theorem atom0734_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0734 g t z = CoefficientMerge.eval (monomial g t z) coeff0734 := by
  norm_num [atom0734, coeff0734, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0734_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0734 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0734]
  positivity
theorem weighted0734_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1343683663509118038537405957715784063498452597544897972473133464122821832266268829851925670782361793761769647261012250032626356494713651200 : Int) coeff0734) := by
  rw [CoefficientMerge.eval_scale, ← atom0734_identity]
  exact mul_nonneg (by norm_num) (atom0734_nonneg g t z hg hA hB ht hz hw)

def coeff0735 : CoefficientMerge.Poly :=
  [(1053700, 1)]
noncomputable def atom0735 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (z) ^ 1)
theorem atom0735_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0735 g t z = CoefficientMerge.eval (monomial g t z) coeff0735 := by
  norm_num [atom0735, coeff0735, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0735_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0735 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0735]
  positivity
theorem weighted0735_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3565678734120387123975167873056379677580091540912935106671986484218870420843818863400911981328881738125548175322853643666565314511299361280 : Int) coeff0735) := by
  rw [CoefficientMerge.eval_scale, ← atom0735_identity]
  exact mul_nonneg (by norm_num) (atom0735_nonneg g t z hg hA hB ht hz hw)

def coeff0736 : CoefficientMerge.Poly :=
  [(1065988, 1)]
noncomputable def atom0736 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (z) ^ 1)
theorem atom0736_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0736 g t z = CoefficientMerge.eval (monomial g t z) coeff0736 := by
  norm_num [atom0736, coeff0736, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0736_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0736 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0736]
  positivity
theorem weighted0736_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4214925730659061918790728584100127313629386069913567742602516190254592839040042604941254063885031717711328235139826364563114295631262924800 : Int) coeff0736) := by
  rw [CoefficientMerge.eval_scale, ← atom0736_identity]
  exact mul_nonneg (by norm_num) (atom0736_nonneg g t z hg hA hB ht hz hw)

def coeff0737 : CoefficientMerge.Poly :=
  [(1115140, 1)]
noncomputable def atom0737 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (z) ^ 1)
theorem atom0737_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0737 g t z = CoefficientMerge.eval (monomial g t z) coeff0737 := by
  norm_num [atom0737, coeff0737, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0737_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0737 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0737]
  positivity
theorem weighted0737_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (6908035211450509395844221732799795476383815029695386371408951307323432207788217361725324971553483644497399393802022095245386899202121747200 : Int) coeff0737) := by
  rw [CoefficientMerge.eval_scale, ← atom0737_identity]
  exact mul_nonneg (by norm_num) (atom0737_nonneg g t z hg hA hB ht hz hw)

def coeff0738 : CoefficientMerge.Poly :=
  [(20484, 1)]
noncomputable def atom0738 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1)
theorem atom0738_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0738 g t z = CoefficientMerge.eval (monomial g t z) coeff0738 := by
  norm_num [atom0738, coeff0738, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0738_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0738 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0738]
  positivity
theorem weighted0738_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (837750913836314388290756601332760261225714361620630845985627184398646135866816623594530801099331970160527668833341847467525201968840294400 : Int) coeff0738) := by
  rw [CoefficientMerge.eval_scale, ← atom0738_identity]
  exact mul_nonneg (by norm_num) (atom0738_nonneg g t z hg hA hB ht hz hw)

def coeff0739 : CoefficientMerge.Poly :=
  [(69636, 1)]
noncomputable def atom0739 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1)
theorem atom0739_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0739 g t z = CoefficientMerge.eval (monomial g t z) coeff0739 := by
  norm_num [atom0739, coeff0739, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0739_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0739 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0739]
  positivity
theorem weighted0739_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3071844534294630773951211863049726386530989037537077184783611716018112442797343871808332878340773321699046868889370817229961340101758156800 : Int) coeff0739) := by
  rw [CoefficientMerge.eval_scale, ← atom0739_identity]
  exact mul_nonneg (by norm_num) (atom0739_nonneg g t z hg hA hB ht hz hw)

def coeff0740 : CoefficientMerge.Poly :=
  [(270340, 1)]
noncomputable def atom0740 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 6) ^ 2 * (t) ^ 1)
theorem atom0740_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0740 g t z = CoefficientMerge.eval (monomial g t z) coeff0740 := by
  norm_num [atom0740, coeff0740, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0740_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0740 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0740]
  positivity
theorem weighted0740_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4551862458152706046370739070633620357301959354037132883138040297898514818925815794308439612136211248669012797048676939437473952830362291200 : Int) coeff0740) := by
  rw [CoefficientMerge.eval_scale, ← atom0740_identity]
  exact mul_nonneg (by norm_num) (atom0740_nonneg g t z hg hA hB ht hz hw)

def coeff0741 : CoefficientMerge.Poly :=
  [(282628, 1)]
noncomputable def atom0741 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (t) ^ 1)
theorem atom0741_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0741 g t z = CoefficientMerge.eval (monomial g t z) coeff0741 := by
  norm_num [atom0741, coeff0741, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0741_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0741 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0741]
  positivity
theorem weighted0741_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2879322795499465383629656897828648515662614156808670985783943788375348040031073147336174294557667601527916030423919060494200240631872435200 : Int) coeff0741) := by
  rw [CoefficientMerge.eval_scale, ← atom0741_identity]
  exact mul_nonneg (by norm_num) (atom0741_nonneg g t z hg hA hB ht hz hw)

def coeff0742 : CoefficientMerge.Poly :=
  [(331780, 1)]
noncomputable def atom0742 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (t) ^ 1)
theorem atom0742_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0742 g t z = CoefficientMerge.eval (monomial g t z) coeff0742 := by
  norm_num [atom0742, coeff0742, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0742_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0742 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0742]
  positivity
theorem weighted0742_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (11904578980143482062883948539669243402643044479379306493318268237329997727884434544090290733866323529524005580441462387403997605759913446400 : Int) coeff0742) := by
  rw [CoefficientMerge.eval_scale, ← atom0742_identity]
  exact mul_nonneg (by norm_num) (atom0742_nonneg g t z hg hA hB ht hz hw)

def coeff0743 : CoefficientMerge.Poly :=
  [(1056772, 1)]
noncomputable def atom0743 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 6) ^ 2 * (z) ^ 1)
theorem atom0743_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0743 g t z = CoefficientMerge.eval (monomial g t z) coeff0743 := by
  norm_num [atom0743, coeff0743, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0743_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0743 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0743]
  positivity
theorem weighted0743_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1279178998135454942964046651943318129171356688626206866078748838271306273076695657383342438030098561329678391514017067170454333212686822400 : Int) coeff0743) := by
  rw [CoefficientMerge.eval_scale, ← atom0743_identity]
  exact mul_nonneg (by norm_num) (atom0743_nonneg g t z hg hA hB ht hz hw)

def coeff0744 : CoefficientMerge.Poly :=
  [(1069060, 1)]
noncomputable def atom0744 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (z) ^ 1)
theorem atom0744_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0744 g t z = CoefficientMerge.eval (monomial g t z) coeff0744 := by
  norm_num [atom0744, coeff0744, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0744_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0744 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0744]
  positivity
theorem weighted0744_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4204536705710727736770190807192005859374251781353033546466725197750260367486800207778575718675661186348871533680696014516769507774988851200 : Int) coeff0744) := by
  rw [CoefficientMerge.eval_scale, ← atom0744_identity]
  exact mul_nonneg (by norm_num) (atom0744_nonneg g t z hg hA hB ht hz hw)

def sparseBlock068 : CoefficientMerge.Poly :=
  [(5124, 2975466978697866627229801096187478097794640305621046891074063546036786611087000439760826969257048966267611917499645685628871607485902438400), (17412, 492326697400915709581362513870214597694158018887816306854823580245216601907150712991162651109319741417653249091318076063965100598693068800), (20484, 837750913836314388290756601332760261225714361620630845985627184398646135866816623594530801099331970160527668833341847467525201968840294400), (66564, 8491174973596889321153417281621920853811973439369302118634900428345611600686768856959967127699169228344479247472699700400487983185781555200), (69636, 3071844534294630773951211863049726386530989037537077184783611716018112442797343871808332878340773321699046868889370817229961340101758156800), (267268, 5093301650639285019776582298373896758913175264104570258675094291349884975216577976634155241257582375123512344274089072919390788183225113600), (270340, 4551862458152706046370739070633620357301959354037132883138040297898514818925815794308439612136211248669012797048676939437473952830362291200), (279556, 2751873850162710309775181689560159517939352797398417134335122669654771957006949587793440212406886252043049573527400884826807616032014592000), (282628, 2879322795499465383629656897828648515662614156808670985783943788375348040031073147336174294557667601527916030423919060494200240631872435200), (328708, 6742635418469644808006380919872897349718969949045681793802096088718832063022953023735893454953769357116195306942697899145773192572074649600), (331780, 11904578980143482062883948539669243402643044479379306493318268237329997727884434544090290733866323529524005580441462387403997605759913446400), (1050628, 1343683663509118038537405957715784063498452597544897972473133464122821832266268829851925670782361793761769647261012250032626356494713651200), (1052932, 10549151662862415375945538988920986296498622582733190687701834720283343299219213063784936927814597158958978783866618579685128697548635708160), (1053700, 3565678734120387123975167873056379677580091540912935106671986484218870420843818863400911981328881738125548175322853643666565314511299361280), (1056772, 1279178998135454942964046651943318129171356688626206866078748838271306273076695657383342438030098561329678391514017067170454333212686822400), (1065220, 14803906841177952514768809629759107555202790149030685687929474152976991075409872785389641801950514356497725607400392016567265091576390133760), (1065988, 4214925730659061918790728584100127313629386069913567742602516190254592839040042604941254063885031717711328235139826364563114295631262924800), (1069060, 4204536705710727736770190807192005859374251781353033546466725197750260367486800207778575718675661186348871533680696014516769507774988851200), (1114372, 17958953945660143472006870434084693113709520498152926734959136269655756533508326534607680242350818452135371551377943466971298850221624125440), (1115140, 6908035211450509395844221732799795476383815029695386371408951307323432207788217361725324971553483644497399393802022095245386899202121747200)]
theorem sparseBlock068_data : sparseBlock068 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (10549151662862415375945538988920986296498622582733190687701834720283343299219213063784936927814597158958978783866618579685128697548635708160 : Int) coeff0725) (CoefficientMerge.scale (14803906841177952514768809629759107555202790149030685687929474152976991075409872785389641801950514356497725607400392016567265091576390133760 : Int) coeff0726)) (CoefficientMerge.merge (CoefficientMerge.scale (17958953945660143472006870434084693113709520498152926734959136269655756533508326534607680242350818452135371551377943466971298850221624125440 : Int) coeff0727) (CoefficientMerge.merge (CoefficientMerge.scale (2975466978697866627229801096187478097794640305621046891074063546036786611087000439760826969257048966267611917499645685628871607485902438400 : Int) coeff0728) (CoefficientMerge.scale (492326697400915709581362513870214597694158018887816306854823580245216601907150712991162651109319741417653249091318076063965100598693068800 : Int) coeff0729)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (8491174973596889321153417281621920853811973439369302118634900428345611600686768856959967127699169228344479247472699700400487983185781555200 : Int) coeff0730) (CoefficientMerge.scale (5093301650639285019776582298373896758913175264104570258675094291349884975216577976634155241257582375123512344274089072919390788183225113600 : Int) coeff0731)) (CoefficientMerge.merge (CoefficientMerge.scale (2751873850162710309775181689560159517939352797398417134335122669654771957006949587793440212406886252043049573527400884826807616032014592000 : Int) coeff0732) (CoefficientMerge.merge (CoefficientMerge.scale (6742635418469644808006380919872897349718969949045681793802096088718832063022953023735893454953769357116195306942697899145773192572074649600 : Int) coeff0733) (CoefficientMerge.scale (1343683663509118038537405957715784063498452597544897972473133464122821832266268829851925670782361793761769647261012250032626356494713651200 : Int) coeff0734))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (3565678734120387123975167873056379677580091540912935106671986484218870420843818863400911981328881738125548175322853643666565314511299361280 : Int) coeff0735) (CoefficientMerge.scale (4214925730659061918790728584100127313629386069913567742602516190254592839040042604941254063885031717711328235139826364563114295631262924800 : Int) coeff0736)) (CoefficientMerge.merge (CoefficientMerge.scale (6908035211450509395844221732799795476383815029695386371408951307323432207788217361725324971553483644497399393802022095245386899202121747200 : Int) coeff0737) (CoefficientMerge.merge (CoefficientMerge.scale (837750913836314388290756601332760261225714361620630845985627184398646135866816623594530801099331970160527668833341847467525201968840294400 : Int) coeff0738) (CoefficientMerge.scale (3071844534294630773951211863049726386530989037537077184783611716018112442797343871808332878340773321699046868889370817229961340101758156800 : Int) coeff0739)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (4551862458152706046370739070633620357301959354037132883138040297898514818925815794308439612136211248669012797048676939437473952830362291200 : Int) coeff0740) (CoefficientMerge.scale (2879322795499465383629656897828648515662614156808670985783943788375348040031073147336174294557667601527916030423919060494200240631872435200 : Int) coeff0741)) (CoefficientMerge.merge (CoefficientMerge.scale (11904578980143482062883948539669243402643044479379306493318268237329997727884434544090290733866323529524005580441462387403997605759913446400 : Int) coeff0742) (CoefficientMerge.merge (CoefficientMerge.scale (1279178998135454942964046651943318129171356688626206866078748838271306273076695657383342438030098561329678391514017067170454333212686822400 : Int) coeff0743) (CoefficientMerge.scale (4204536705710727736770190807192005859374251781353033546466725197750260367486800207778575718675661186348871533680696014516769507774988851200 : Int) coeff0744)))))) := by decide +kernel
theorem sparseBlock068_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock068 := by
  rw [sparseBlock068_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted0725_nonneg g t z hg hA hB ht hz hw) (weighted0726_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0727_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0728_nonneg g t z hg hA hB ht hz hw) (weighted0729_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0730_nonneg g t z hg hA hB ht hz hw) (weighted0731_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0732_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0733_nonneg g t z hg hA hB ht hz hw) (weighted0734_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted0735_nonneg g t z hg hA hB ht hz hw) (weighted0736_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0737_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0738_nonneg g t z hg hA hB ht hz hw) (weighted0739_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0740_nonneg g t z hg hA hB ht hz hw) (weighted0741_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0742_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0743_nonneg g t z hg hA hB ht hz hw) (weighted0744_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
