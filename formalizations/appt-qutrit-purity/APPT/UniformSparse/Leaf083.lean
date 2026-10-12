import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff1025 : CoefficientMerge.Poly :=
  [(2103296, 1)]
noncomputable def atom1025 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 2 * (g 6) ^ 1 * (z) ^ 2)
theorem atom1025_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1025 g t z = CoefficientMerge.eval (monomial g t z) coeff1025 := by
  norm_num [atom1025, coeff1025, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1025_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1025 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1025]
  positivity
theorem weighted1025_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (934341250217093730606882051165708441602284397086836825612814898395762754610294507535089805930406981854813393953120899217447203397469447680 : Int) coeff1025) := by
  rw [CoefficientMerge.eval_scale, ← atom1025_identity]
  exact mul_nonneg (by norm_num) (atom1025_nonneg g t z hg hA hB ht hz hw)

def coeff1026 : CoefficientMerge.Poly :=
  [(2115584, 1)]
noncomputable def atom1026 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 2 * (g 7) ^ 1 * (z) ^ 2)
theorem atom1026_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1026 g t z = CoefficientMerge.eval (monomial g t z) coeff1026 := by
  norm_num [atom1026, coeff1026, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1026_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1026 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1026]
  positivity
theorem weighted1026_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1301021353322443096409436525296384236623721802615129198565382516374421405861464264267364828877207725618139446629612164616370156386241390080 : Int) coeff1026) := by
  rw [CoefficientMerge.eval_scale, ← atom1026_identity]
  exact mul_nonneg (by norm_num) (atom1026_nonneg g t z hg hA hB ht hz hw)

def coeff1027 : CoefficientMerge.Poly :=
  [(2164736, 1)]
noncomputable def atom1027 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 2 * (g 8) ^ 1 * (z) ^ 2)
theorem atom1027_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1027 g t z = CoefficientMerge.eval (monomial g t z) coeff1027 := by
  norm_num [atom1027, coeff1027, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1027_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1027 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1027]
  positivity
theorem weighted1027_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (422674692731644703659734768145483561782210117665705832762408769068859283162508623115567134754790667531485572821103610752997324192089445140 : Int) coeff1027) := by
  rw [CoefficientMerge.eval_scale, ← atom1027_identity]
  exact mul_nonneg (by norm_num) (atom1027_nonneg g t z hg hA hB ht hz hw)

def coeff1028 : CoefficientMerge.Poly :=
  [(2106368, 1)]
noncomputable def atom1028 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 6) ^ 2 * (z) ^ 2)
theorem atom1028_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1028 g t z = CoefficientMerge.eval (monomial g t z) coeff1028 := by
  norm_num [atom1028, coeff1028, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1028_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1028 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1028]
  positivity
theorem weighted1028_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1103744932032376495854520324269021363123151096910529497646547559704277977631282421926378738215726019142354694956374055237427909118822173440 : Int) coeff1028) := by
  rw [CoefficientMerge.eval_scale, ← atom1028_identity]
  exact mul_nonneg (by norm_num) (atom1028_nonneg g t z hg hA hB ht hz hw)

def coeff1029 : CoefficientMerge.Poly :=
  [(2118656, 1)]
noncomputable def atom1029 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (z) ^ 2)
theorem atom1029_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1029 g t z = CoefficientMerge.eval (monomial g t z) coeff1029 := by
  norm_num [atom1029, coeff1029, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1029_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1029 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1029]
  positivity
theorem weighted1029_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3078825027756218005949051110831968652906010980318309180963510699843148853332737321580867569811197421198949656730854269058828135494236490080 : Int) coeff1029) := by
  rw [CoefficientMerge.eval_scale, ← atom1029_identity]
  exact mul_nonneg (by norm_num) (atom1029_nonneg g t z hg hA hB ht hz hw)

def coeff1030 : CoefficientMerge.Poly :=
  [(2167808, 1)]
noncomputable def atom1030 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (z) ^ 2)
theorem atom1030_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1030 g t z = CoefficientMerge.eval (monomial g t z) coeff1030 := by
  norm_num [atom1030, coeff1030, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1030_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1030 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1030]
  positivity
theorem weighted1030_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1732469562595979583215899291731178161235285087438385376683262658394752206786664272301255134085467828731782824404878393299165712253264481060 : Int) coeff1030) := by
  rw [CoefficientMerge.eval_scale, ← atom1030_identity]
  exact mul_nonneg (by norm_num) (atom1030_nonneg g t z hg hA hB ht hz hw)

def coeff1031 : CoefficientMerge.Poly :=
  [(1082368, 1)]
noncomputable def atom1031 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 7) ^ 2 * (z) ^ 1)
theorem atom1031_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1031 g t z = CoefficientMerge.eval (monomial g t z) coeff1031 := by
  norm_num [atom1031, coeff1031, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1031_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1031 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1031]
  positivity
theorem weighted1031_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1838842666475242848023007209071669858259967681087685524064249218806167435048406123099034690670618974903269294157732157266796718708783685120 : Int) coeff1031) := by
  rw [CoefficientMerge.eval_scale, ← atom1031_identity]
  exact mul_nonneg (by norm_num) (atom1031_nonneg g t z hg hA hB ht hz hw)

def coeff1032 : CoefficientMerge.Poly :=
  [(2130944, 1)]
noncomputable def atom1032 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 7) ^ 2 * (z) ^ 2)
theorem atom1032_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1032 g t z = CoefficientMerge.eval (monomial g t z) coeff1032 := by
  norm_num [atom1032, coeff1032, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1032_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1032 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1032]
  positivity
theorem weighted1032_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1697967311605647304710730311186283977135294547511076951042269261830179891626495365871789201010360783773874016419134863485005289000129384960 : Int) coeff1032) := by
  rw [CoefficientMerge.eval_scale, ← atom1032_identity]
  exact mul_nonneg (by norm_num) (atom1032_nonneg g t z hg hA hB ht hz hw)

def coeff1033 : CoefficientMerge.Poly :=
  [(2180096, 1)]
noncomputable def atom1033 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (z) ^ 2)
theorem atom1033_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1033 g t z = CoefficientMerge.eval (monomial g t z) coeff1033 := by
  norm_num [atom1033, coeff1033, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1033_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1033 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1033]
  positivity
theorem weighted1033_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2341848760894617522635115458003229780869068539179592931833903225704247768860418688202301037004507973566006292073341360007222256212773383220 : Int) coeff1033) := by
  rw [CoefficientMerge.eval_scale, ← atom1033_identity]
  exact mul_nonneg (by norm_num) (atom1033_nonneg g t z hg hA hB ht hz hw)

def coeff1034 : CoefficientMerge.Poly :=
  [(2229248, 1)]
noncomputable def atom1034 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 8) ^ 2 * (z) ^ 2)
theorem atom1034_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1034 g t z = CoefficientMerge.eval (monomial g t z) coeff1034 := by
  norm_num [atom1034, coeff1034, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1034_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1034 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1034]
  positivity
theorem weighted1034_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (548523364807043267442940128102245647242667703854489246825252994612710546095252914075425703423964953989675991218839804006431716626556734660 : Int) coeff1034) := by
  rw [CoefficientMerge.eval_scale, ← atom1034_identity]
  exact mul_nonneg (by norm_num) (atom1034_nonneg g t z hg hA hB ht hz hw)

def coeff1035 : CoefficientMerge.Poly :=
  [(286720, 1)]
noncomputable def atom1035 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 2 * (g 7) ^ 1 * (t) ^ 1)
theorem atom1035_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1035 g t z = CoefficientMerge.eval (monomial g t z) coeff1035 := by
  norm_num [atom1035, coeff1035, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1035_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1035 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1035]
  positivity
theorem weighted1035_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1797032601324701056926971017987567588967308518544264297817652532371776022499663255273577444420187910667199683964012086846542564008667545600 : Int) coeff1035) := by
  rw [CoefficientMerge.eval_scale, ← atom1035_identity]
  exact mul_nonneg (by norm_num) (atom1035_nonneg g t z hg hA hB ht hz hw)

def coeff1036 : CoefficientMerge.Poly :=
  [(348160, 1)]
noncomputable def atom1036 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (t) ^ 1)
theorem atom1036_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1036 g t z = CoefficientMerge.eval (monomial g t z) coeff1036 := by
  norm_num [atom1036, coeff1036, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1036_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1036 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1036]
  positivity
theorem weighted1036_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (9756543660937062339142195574813593112897619557956262953542923276095118904438276460960615493859991646452224500155186044302542264464680140800 : Int) coeff1036) := by
  rw [CoefficientMerge.eval_scale, ← atom1036_identity]
  exact mul_nonneg (by norm_num) (atom1036_nonneg g t z hg hA hB ht hz hw)

def coeff1037 : CoefficientMerge.Poly :=
  [(1134592, 1)]
noncomputable def atom1037 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (z) ^ 1)
theorem atom1037_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1037 g t z = CoefficientMerge.eval (monomial g t z) coeff1037 := by
  norm_num [atom1037, coeff1037, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1037_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1037 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1037]
  positivity
theorem weighted1037_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5397548062251053980916914779604512943544452527036221585312092555754212004770488401890523170713860825184979291415603526585654758464726272000 : Int) coeff1037) := by
  rw [CoefficientMerge.eval_scale, ← atom1037_identity]
  exact mul_nonneg (by norm_num) (atom1037_nonneg g t z hg hA hB ht hz hw)

def coeff1038 : CoefficientMerge.Poly :=
  [(536576, 1)]
noncomputable def atom1038 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 3 * (t) ^ 2)
theorem atom1038_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1038 g t z = CoefficientMerge.eval (monomial g t z) coeff1038 := by
  norm_num [atom1038, coeff1038, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1038_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1038 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1038]
  positivity
theorem weighted1038_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (383537848904007221706108997712680302961356173282314417247164388526819542829630152541276308804572149395426269304271236589872535963131289600 : Int) coeff1038) := by
  rw [CoefficientMerge.eval_scale, ← atom1038_identity]
  exact mul_nonneg (by norm_num) (atom1038_nonneg g t z hg hA hB ht hz hw)

def coeff1039 : CoefficientMerge.Poly :=
  [(548864, 1)]
noncomputable def atom1039 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 2 * (g 7) ^ 1 * (t) ^ 2)
theorem atom1039_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1039 g t z = CoefficientMerge.eval (monomial g t z) coeff1039 := by
  norm_num [atom1039, coeff1039, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1039_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1039 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1039]
  positivity
theorem weighted1039_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1518087951595860439653544939496224751800455439851628687928487654717326872181882756421056898375467907787907028818709222581136069168872140800 : Int) coeff1039) := by
  rw [CoefficientMerge.eval_scale, ← atom1039_identity]
  exact mul_nonneg (by norm_num) (atom1039_nonneg g t z hg hA hB ht hz hw)

def coeff1040 : CoefficientMerge.Poly :=
  [(598016, 1)]
noncomputable def atom1040 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 2 * (g 8) ^ 1 * (t) ^ 2)
theorem atom1040_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1040 g t z = CoefficientMerge.eval (monomial g t z) coeff1040 := by
  norm_num [atom1040, coeff1040, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1040_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1040 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1040]
  positivity
theorem weighted1040_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1307903803760885617203977091695254684824034401340916877083032818844078409143972488016398074572020134853283524565453590063065775221775974400 : Int) coeff1040) := by
  rw [CoefficientMerge.eval_scale, ← atom1040_identity]
  exact mul_nonneg (by norm_num) (atom1040_nonneg g t z hg hA hB ht hz hw)

def coeff1041 : CoefficientMerge.Poly :=
  [(1323008, 1)]
noncomputable def atom1041 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 3 * (t) ^ 1 * (z) ^ 1)
theorem atom1041_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1041 g t z = CoefficientMerge.eval (monomial g t z) coeff1041 := by
  norm_num [atom1041, coeff1041, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1041_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1041 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1041]
  positivity
theorem weighted1041_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (750704847910469213445831565882302221189060888038376185253118577001686880781150645810083515764130700092545555099777803900172138908066841600 : Int) coeff1041) := by
  rw [CoefficientMerge.eval_scale, ← atom1041_identity]
  exact mul_nonneg (by norm_num) (atom1041_nonneg g t z hg hA hB ht hz hw)

def coeff1042 : CoefficientMerge.Poly :=
  [(1335296, 1)]
noncomputable def atom1042 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 2 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom1042_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1042 g t z = CoefficientMerge.eval (monomial g t z) coeff1042 := by
  norm_num [atom1042, coeff1042, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1042_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1042 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1042]
  positivity
theorem weighted1042_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2996254050752450024308601449328113446424227994521634353811648675428877983886928162185278934435757728975090640474356855086798411192004838400 : Int) coeff1042) := by
  rw [CoefficientMerge.eval_scale, ← atom1042_identity]
  exact mul_nonneg (by norm_num) (atom1042_nonneg g t z hg hA hB ht hz hw)

def coeff1043 : CoefficientMerge.Poly :=
  [(1384448, 1)]
noncomputable def atom1043 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 2 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom1043_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1043 g t z = CoefficientMerge.eval (monomial g t z) coeff1043 := by
  norm_num [atom1043, coeff1043, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1043_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1043 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1043]
  positivity
theorem weighted1043_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2336469197048906139536506426076193408905984084812464517129190301373704494738193711277846223007899415754691771126992260589129811373027148800 : Int) coeff1043) := by
  rw [CoefficientMerge.eval_scale, ← atom1043_identity]
  exact mul_nonneg (by norm_num) (atom1043_nonneg g t z hg hA hB ht hz hw)

def coeff1044 : CoefficientMerge.Poly :=
  [(299008, 1)]
noncomputable def atom1044 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 6) ^ 1 * (g 7) ^ 2 * (t) ^ 1)
theorem atom1044_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1044 g t z = CoefficientMerge.eval (monomial g t z) coeff1044 := by
  norm_num [atom1044, coeff1044, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1044_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1044 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1044]
  positivity
theorem weighted1044_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3715596104011145687728066664305900649620818845108006280915668593455231002650628380669381351650731456075774700375640530323047382658097152000 : Int) coeff1044) := by
  rw [CoefficientMerge.eval_scale, ← atom1044_identity]
  exact mul_nonneg (by norm_num) (atom1044_nonneg g t z hg hA hB ht hz hw)

def sparseBlock083 : CoefficientMerge.Poly :=
  [(286720, 1797032601324701056926971017987567588967308518544264297817652532371776022499663255273577444420187910667199683964012086846542564008667545600), (299008, 3715596104011145687728066664305900649620818845108006280915668593455231002650628380669381351650731456075774700375640530323047382658097152000), (348160, 9756543660937062339142195574813593112897619557956262953542923276095118904438276460960615493859991646452224500155186044302542264464680140800), (536576, 383537848904007221706108997712680302961356173282314417247164388526819542829630152541276308804572149395426269304271236589872535963131289600), (548864, 1518087951595860439653544939496224751800455439851628687928487654717326872181882756421056898375467907787907028818709222581136069168872140800), (598016, 1307903803760885617203977091695254684824034401340916877083032818844078409143972488016398074572020134853283524565453590063065775221775974400), (1082368, 1838842666475242848023007209071669858259967681087685524064249218806167435048406123099034690670618974903269294157732157266796718708783685120), (1134592, 5397548062251053980916914779604512943544452527036221585312092555754212004770488401890523170713860825184979291415603526585654758464726272000), (1323008, 750704847910469213445831565882302221189060888038376185253118577001686880781150645810083515764130700092545555099777803900172138908066841600), (1335296, 2996254050752450024308601449328113446424227994521634353811648675428877983886928162185278934435757728975090640474356855086798411192004838400), (1384448, 2336469197048906139536506426076193408905984084812464517129190301373704494738193711277846223007899415754691771126992260589129811373027148800), (2103296, 934341250217093730606882051165708441602284397086836825612814898395762754610294507535089805930406981854813393953120899217447203397469447680), (2106368, 1103744932032376495854520324269021363123151096910529497646547559704277977631282421926378738215726019142354694956374055237427909118822173440), (2115584, 1301021353322443096409436525296384236623721802615129198565382516374421405861464264267364828877207725618139446629612164616370156386241390080), (2118656, 3078825027756218005949051110831968652906010980318309180963510699843148853332737321580867569811197421198949656730854269058828135494236490080), (2130944, 1697967311605647304710730311186283977135294547511076951042269261830179891626495365871789201010360783773874016419134863485005289000129384960), (2164736, 422674692731644703659734768145483561782210117665705832762408769068859283162508623115567134754790667531485572821103610752997324192089445140), (2167808, 1732469562595979583215899291731178161235285087438385376683262658394752206786664272301255134085467828731782824404878393299165712253264481060), (2180096, 2341848760894617522635115458003229780869068539179592931833903225704247768860418688202301037004507973566006292073341360007222256212773383220), (2229248, 548523364807043267442940128102245647242667703854489246825252994612710546095252914075425703423964953989675991218839804006431716626556734660)]
theorem sparseBlock083_data : sparseBlock083 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (934341250217093730606882051165708441602284397086836825612814898395762754610294507535089805930406981854813393953120899217447203397469447680 : Int) coeff1025) (CoefficientMerge.scale (1301021353322443096409436525296384236623721802615129198565382516374421405861464264267364828877207725618139446629612164616370156386241390080 : Int) coeff1026)) (CoefficientMerge.merge (CoefficientMerge.scale (422674692731644703659734768145483561782210117665705832762408769068859283162508623115567134754790667531485572821103610752997324192089445140 : Int) coeff1027) (CoefficientMerge.merge (CoefficientMerge.scale (1103744932032376495854520324269021363123151096910529497646547559704277977631282421926378738215726019142354694956374055237427909118822173440 : Int) coeff1028) (CoefficientMerge.scale (3078825027756218005949051110831968652906010980318309180963510699843148853332737321580867569811197421198949656730854269058828135494236490080 : Int) coeff1029)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1732469562595979583215899291731178161235285087438385376683262658394752206786664272301255134085467828731782824404878393299165712253264481060 : Int) coeff1030) (CoefficientMerge.scale (1838842666475242848023007209071669858259967681087685524064249218806167435048406123099034690670618974903269294157732157266796718708783685120 : Int) coeff1031)) (CoefficientMerge.merge (CoefficientMerge.scale (1697967311605647304710730311186283977135294547511076951042269261830179891626495365871789201010360783773874016419134863485005289000129384960 : Int) coeff1032) (CoefficientMerge.merge (CoefficientMerge.scale (2341848760894617522635115458003229780869068539179592931833903225704247768860418688202301037004507973566006292073341360007222256212773383220 : Int) coeff1033) (CoefficientMerge.scale (548523364807043267442940128102245647242667703854489246825252994612710546095252914075425703423964953989675991218839804006431716626556734660 : Int) coeff1034))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1797032601324701056926971017987567588967308518544264297817652532371776022499663255273577444420187910667199683964012086846542564008667545600 : Int) coeff1035) (CoefficientMerge.scale (9756543660937062339142195574813593112897619557956262953542923276095118904438276460960615493859991646452224500155186044302542264464680140800 : Int) coeff1036)) (CoefficientMerge.merge (CoefficientMerge.scale (5397548062251053980916914779604512943544452527036221585312092555754212004770488401890523170713860825184979291415603526585654758464726272000 : Int) coeff1037) (CoefficientMerge.merge (CoefficientMerge.scale (383537848904007221706108997712680302961356173282314417247164388526819542829630152541276308804572149395426269304271236589872535963131289600 : Int) coeff1038) (CoefficientMerge.scale (1518087951595860439653544939496224751800455439851628687928487654717326872181882756421056898375467907787907028818709222581136069168872140800 : Int) coeff1039)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1307903803760885617203977091695254684824034401340916877083032818844078409143972488016398074572020134853283524565453590063065775221775974400 : Int) coeff1040) (CoefficientMerge.scale (750704847910469213445831565882302221189060888038376185253118577001686880781150645810083515764130700092545555099777803900172138908066841600 : Int) coeff1041)) (CoefficientMerge.merge (CoefficientMerge.scale (2996254050752450024308601449328113446424227994521634353811648675428877983886928162185278934435757728975090640474356855086798411192004838400 : Int) coeff1042) (CoefficientMerge.merge (CoefficientMerge.scale (2336469197048906139536506426076193408905984084812464517129190301373704494738193711277846223007899415754691771126992260589129811373027148800 : Int) coeff1043) (CoefficientMerge.scale (3715596104011145687728066664305900649620818845108006280915668593455231002650628380669381351650731456075774700375640530323047382658097152000 : Int) coeff1044)))))) := by decide +kernel
theorem sparseBlock083_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock083 := by
  rw [sparseBlock083_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted1025_nonneg g t z hg hA hB ht hz hw) (weighted1026_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1027_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1028_nonneg g t z hg hA hB ht hz hw) (weighted1029_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1030_nonneg g t z hg hA hB ht hz hw) (weighted1031_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1032_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1033_nonneg g t z hg hA hB ht hz hw) (weighted1034_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted1035_nonneg g t z hg hA hB ht hz hw) (weighted1036_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1037_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1038_nonneg g t z hg hA hB ht hz hw) (weighted1039_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1040_nonneg g t z hg hA hB ht hz hw) (weighted1041_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1042_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1043_nonneg g t z hg hA hB ht hz hw) (weighted1044_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
