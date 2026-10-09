import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff1005 : CoefficientMerge.Poly :=
  [(530432, 1)]
noncomputable def atom1005 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 2 * (g 6) ^ 1 * (t) ^ 2)
theorem atom1005_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1005 g t z = CoefficientMerge.eval (monomial g t z) coeff1005 := by
  norm_num [atom1005, coeff1005, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1005_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1005 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1005]
  positivity
theorem weighted1005_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (818325468630060111501906861127593081096543118653745472126322012934210820357690220437561258546103429269811905036177595925612333791590553600 : Int) coeff1005) := by
  rw [CoefficientMerge.eval_scale, ← atom1005_identity]
  exact mul_nonneg (by norm_num) (atom1005_nonneg g t z hg hA hB ht hz hw)

def coeff1006 : CoefficientMerge.Poly :=
  [(542720, 1)]
noncomputable def atom1006 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 2 * (g 7) ^ 1 * (t) ^ 2)
theorem atom1006_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1006 g t z = CoefficientMerge.eval (monomial g t z) coeff1006 := by
  norm_num [atom1006, coeff1006, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1006_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1006 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1006]
  positivity
theorem weighted1006_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1216479436972714806311494301228328013769385145232819282422373628513071701512952938784931269804012279972753708223233060445193247405653350400 : Int) coeff1006) := by
  rw [CoefficientMerge.eval_scale, ← atom1006_identity]
  exact mul_nonneg (by norm_num) (atom1006_nonneg g t z hg hA hB ht hz hw)

def coeff1007 : CoefficientMerge.Poly :=
  [(591872, 1)]
noncomputable def atom1007 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 2 * (g 8) ^ 1 * (t) ^ 2)
theorem atom1007_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1007 g t z = CoefficientMerge.eval (monomial g t z) coeff1007 := by
  norm_num [atom1007, coeff1007, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1007_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1007 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1007]
  positivity
theorem weighted1007_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (568744998499459818028677802726369719656692107293945353752248482495049863128349960404489145803240665658266431508248131607355569982708275200 : Int) coeff1007) := by
  rw [CoefficientMerge.eval_scale, ← atom1007_identity]
  exact mul_nonneg (by norm_num) (atom1007_nonneg g t z hg hA hB ht hz hw)

def coeff1008 : CoefficientMerge.Poly :=
  [(1313792, 1)]
noncomputable def atom1008 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 3 * (t) ^ 1 * (z) ^ 1)
theorem atom1008_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1008 g t z = CoefficientMerge.eval (monomial g t z) coeff1008 := by
  norm_num [atom1008, coeff1008, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1008_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1008 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1008]
  positivity
theorem weighted1008_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (436254786974735264790694538058885591190623301934781118762587461493567483323440667408265755865629740510445165779708339438396313431011210240 : Int) coeff1008) := by
  rw [CoefficientMerge.eval_scale, ← atom1008_identity]
  exact mul_nonneg (by norm_num) (atom1008_nonneg g t z hg hA hB ht hz hw)

def coeff1009 : CoefficientMerge.Poly :=
  [(1316864, 1)]
noncomputable def atom1009 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 2 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom1009_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1009 g t z = CoefficientMerge.eval (monomial g t z) coeff1009 := by
  norm_num [atom1009, coeff1009, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1009_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1009 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1009]
  positivity
theorem weighted1009_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1654282926256704745439469703016279201862821964843902241483675246429212797271485050761960136500032355917552752886864135594033236708369415680 : Int) coeff1009) := by
  rw [CoefficientMerge.eval_scale, ← atom1009_identity]
  exact mul_nonneg (by norm_num) (atom1009_nonneg g t z hg hA hB ht hz hw)

def coeff1010 : CoefficientMerge.Poly :=
  [(1329152, 1)]
noncomputable def atom1010 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 2 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom1010_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1010 g t z = CoefficientMerge.eval (monomial g t z) coeff1010 := by
  norm_num [atom1010, coeff1010, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1010_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1010 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1010]
  positivity
theorem weighted1010_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2301219103521892905990475404509446033239430999127186729175074320184920653766150929532805180743705213641255490575360627639876277868431572480 : Int) coeff1010) := by
  rw [CoefficientMerge.eval_scale, ← atom1010_identity]
  exact mul_nonneg (by norm_num) (atom1010_nonneg g t z hg hA hB ht hz hw)

def coeff1011 : CoefficientMerge.Poly :=
  [(1378304, 1)]
noncomputable def atom1011 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 2 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom1011_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1011 g t z = CoefficientMerge.eval (monomial g t z) coeff1011 := by
  norm_num [atom1011, coeff1011, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1011_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1011 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1011]
  positivity
theorem weighted1011_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (960306397419774027310047203591972056359617844357812634293716822365164768192336622132061794249645923807084325469726442196697619794303188480 : Int) coeff1011) := by
  rw [CoefficientMerge.eval_scale, ← atom1011_identity]
  exact mul_nonneg (by norm_num) (atom1011_nonneg g t z hg hA hB ht hz hw)

def coeff1012 : CoefficientMerge.Poly :=
  [(533504, 1)]
noncomputable def atom1012 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 6) ^ 2 * (t) ^ 2)
theorem atom1012_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1012 g t z = CoefficientMerge.eval (monomial g t z) coeff1012 := by
  norm_num [atom1012, coeff1012, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1012_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1012 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1012]
  positivity
theorem weighted1012_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1035391945073816030270843353562739247982011393173017261283300312771924635481700514209606431908737256973905589023425273880880789118617907200 : Int) coeff1012) := by
  rw [CoefficientMerge.eval_scale, ← atom1012_identity]
  exact mul_nonneg (by norm_num) (atom1012_nonneg g t z hg hA hB ht hz hw)

def coeff1013 : CoefficientMerge.Poly :=
  [(545792, 1)]
noncomputable def atom1013 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (t) ^ 2)
theorem atom1013_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1013 g t z = CoefficientMerge.eval (monomial g t z) coeff1013 := by
  norm_num [atom1013, coeff1013, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1013_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1013 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1013]
  positivity
theorem weighted1013_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3088088860445201462710484900975157392647088969789746502313527959956943207333566066939329219380260960127724220432991017966749493965417779200 : Int) coeff1013) := by
  rw [CoefficientMerge.eval_scale, ← atom1013_identity]
  exact mul_nonneg (by norm_num) (atom1013_nonneg g t z hg hA hB ht hz hw)

def coeff1014 : CoefficientMerge.Poly :=
  [(594944, 1)]
noncomputable def atom1014 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (t) ^ 2)
theorem atom1014_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1014 g t z = CoefficientMerge.eval (monomial g t z) coeff1014 := by
  norm_num [atom1014, coeff1014, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1014_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1014 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1014]
  positivity
theorem weighted1014_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2068273089959882489678957002722989202701484817960766327288415566754676687382895364228328956599309941202258075155229623983228217825699635200 : Int) coeff1014) := by
  rw [CoefficientMerge.eval_scale, ← atom1014_identity]
  exact mul_nonneg (by norm_num) (atom1014_nonneg g t z hg hA hB ht hz hw)

def coeff1015 : CoefficientMerge.Poly :=
  [(1319936, 1)]
noncomputable def atom1015 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 6) ^ 2 * (t) ^ 1 * (z) ^ 1)
theorem atom1015_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1015 g t z = CoefficientMerge.eval (monomial g t z) coeff1015 := by
  norm_num [atom1015, coeff1015, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1015_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1015 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1015]
  positivity
theorem weighted1015_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2038048781278025714807312514609379991809448040608614189288927468660686370149821164325232972097945149639780693145974994706585888015283824640 : Int) coeff1015) := by
  rw [CoefficientMerge.eval_scale, ← atom1015_identity]
  exact mul_nonneg (by norm_num) (atom1015_nonneg g t z hg hA hB ht hz hw)

def coeff1016 : CoefficientMerge.Poly :=
  [(1332224, 1)]
noncomputable def atom1016 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom1016_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1016 g t z = CoefficientMerge.eval (monomial g t z) coeff1016 := by
  norm_num [atom1016, coeff1016, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1016_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1016 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1016]
  positivity
theorem weighted1016_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5758083068694876011589131003790911312244377467087625518719465917755988125432313475662799641274012650348616094033052267371396387794941921280 : Int) coeff1016) := by
  rw [CoefficientMerge.eval_scale, ← atom1016_identity]
  exact mul_nonneg (by norm_num) (atom1016_nonneg g t z hg hA hB ht hz hw)

def coeff1017 : CoefficientMerge.Poly :=
  [(1381376, 1)]
noncomputable def atom1017 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom1017_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1017 g t z = CoefficientMerge.eval (monomial g t z) coeff1017 := by
  norm_num [atom1017, coeff1017, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1017_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1017 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1017]
  positivity
theorem weighted1017_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3635014027827622523510033652368372513328884508014333745758406899696515202664332312147654850219680335285314570032093322094809173602792212480 : Int) coeff1017) := by
  rw [CoefficientMerge.eval_scale, ← atom1017_identity]
  exact mul_nonneg (by norm_num) (atom1017_nonneg g t z hg hA hB ht hz hw)

def coeff1018 : CoefficientMerge.Poly :=
  [(558080, 1)]
noncomputable def atom1018 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 7) ^ 2 * (t) ^ 2)
theorem atom1018_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1018 g t z = CoefficientMerge.eval (monomial g t z) coeff1018 := by
  norm_num [atom1018, coeff1018, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1018_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1018 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1018]
  positivity
theorem weighted1018_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1937015052570608863700834507880693069644177306318076550412589464836681859878401417503080255414896735405590210386443380403167719829198438400 : Int) coeff1018) := by
  rw [CoefficientMerge.eval_scale, ← atom1018_identity]
  exact mul_nonneg (by norm_num) (atom1018_nonneg g t z hg hA hB ht hz hw)

def coeff1019 : CoefficientMerge.Poly :=
  [(607232, 1)]
noncomputable def atom1019 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (t) ^ 2)
theorem atom1019_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1019 g t z = CoefficientMerge.eval (monomial g t z) coeff1019 := by
  norm_num [atom1019, coeff1019, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1019_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1019 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1019]
  positivity
theorem weighted1019_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3073776694415216006103334321324721205864074942317742916642271862921507881094577913008405802834911375065845800563333739600121382623352294400 : Int) coeff1019) := by
  rw [CoefficientMerge.eval_scale, ← atom1019_identity]
  exact mul_nonneg (by norm_num) (atom1019_nonneg g t z hg hA hB ht hz hw)

def coeff1020 : CoefficientMerge.Poly :=
  [(1344512, 1)]
noncomputable def atom1020 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 7) ^ 2 * (t) ^ 1 * (z) ^ 1)
theorem atom1020_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1020 g t z = CoefficientMerge.eval (monomial g t z) coeff1020 := by
  norm_num [atom1020, coeff1020, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1020_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1020 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1020]
  positivity
theorem weighted1020_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3381453284865091631488912773750583323495466674719954940628529421818584492402733889695065330184537551584121524604404698614406601457310184960 : Int) coeff1020) := by
  rw [CoefficientMerge.eval_scale, ← atom1020_identity]
  exact mul_nonneg (by norm_num) (atom1020_nonneg g t z hg hA hB ht hz hw)

def coeff1021 : CoefficientMerge.Poly :=
  [(1393664, 1)]
noncomputable def atom1021 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom1021_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1021 g t z = CoefficientMerge.eval (monomial g t z) coeff1021 := by
  norm_num [atom1021, coeff1021, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1021_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1021 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1021]
  positivity
theorem weighted1021_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4773349397352119149368469343323599237231685223953237429859757543671212133404747790289600667809966563089579707929219656072570191452180267520 : Int) coeff1021) := by
  rw [CoefficientMerge.eval_scale, ← atom1021_identity]
  exact mul_nonneg (by norm_num) (atom1021_nonneg g t z hg hA hB ht hz hw)

def coeff1022 : CoefficientMerge.Poly :=
  [(656384, 1)]
noncomputable def atom1022 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 8) ^ 2 * (t) ^ 2)
theorem atom1022_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1022 g t z = CoefficientMerge.eval (monomial g t z) coeff1022 := by
  norm_num [atom1022, coeff1022, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1022_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1022 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1022]
  positivity
theorem weighted1022_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (534485630580126510394692494605572620652679141641053539396242536178700130678066505389444279021239629130673566966806288845667003537088204800 : Int) coeff1022) := by
  rw [CoefficientMerge.eval_scale, ← atom1022_identity]
  exact mul_nonneg (by norm_num) (atom1022_nonneg g t z hg hA hB ht hz hw)

def coeff1023 : CoefficientMerge.Poly :=
  [(1442816, 1)]
noncomputable def atom1023 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 1 * (g 8) ^ 2 * (t) ^ 1 * (z) ^ 1)
theorem atom1023_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1023 g t z = CoefficientMerge.eval (monomial g t z) coeff1023 := by
  norm_num [atom1023, coeff1023, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1023_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1023 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1023]
  positivity
theorem weighted1023_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (719994945669253130187721194459593984831546190729464118907464439330907113317306035962148068010461926819747935022508696505653657810370749440 : Int) coeff1023) := by
  rw [CoefficientMerge.eval_scale, ← atom1023_identity]
  exact mul_nonneg (by norm_num) (atom1023_nonneg g t z hg hA hB ht hz hw)

def coeff1024 : CoefficientMerge.Poly :=
  [(2100224, 1)]
noncomputable def atom1024 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 5) ^ 3 * (z) ^ 2)
theorem atom1024_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom1024 g t z = CoefficientMerge.eval (monomial g t z) coeff1024 := by
  norm_num [atom1024, coeff1024, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom1024_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom1024 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom1024]
  positivity
theorem weighted1024_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (258473966801207924941776239724114112300729049705474049682672106832491899737580580610337952530336210760274935628226208094758506436882979840 : Int) coeff1024) := by
  rw [CoefficientMerge.eval_scale, ← atom1024_identity]
  exact mul_nonneg (by norm_num) (atom1024_nonneg g t z hg hA hB ht hz hw)

def sparseBlock082 : CoefficientMerge.Poly :=
  [(530432, 818325468630060111501906861127593081096543118653745472126322012934210820357690220437561258546103429269811905036177595925612333791590553600), (533504, 1035391945073816030270843353562739247982011393173017261283300312771924635481700514209606431908737256973905589023425273880880789118617907200), (542720, 1216479436972714806311494301228328013769385145232819282422373628513071701512952938784931269804012279972753708223233060445193247405653350400), (545792, 3088088860445201462710484900975157392647088969789746502313527959956943207333566066939329219380260960127724220432991017966749493965417779200), (558080, 1937015052570608863700834507880693069644177306318076550412589464836681859878401417503080255414896735405590210386443380403167719829198438400), (591872, 568744998499459818028677802726369719656692107293945353752248482495049863128349960404489145803240665658266431508248131607355569982708275200), (594944, 2068273089959882489678957002722989202701484817960766327288415566754676687382895364228328956599309941202258075155229623983228217825699635200), (607232, 3073776694415216006103334321324721205864074942317742916642271862921507881094577913008405802834911375065845800563333739600121382623352294400), (656384, 534485630580126510394692494605572620652679141641053539396242536178700130678066505389444279021239629130673566966806288845667003537088204800), (1313792, 436254786974735264790694538058885591190623301934781118762587461493567483323440667408265755865629740510445165779708339438396313431011210240), (1316864, 1654282926256704745439469703016279201862821964843902241483675246429212797271485050761960136500032355917552752886864135594033236708369415680), (1319936, 2038048781278025714807312514609379991809448040608614189288927468660686370149821164325232972097945149639780693145974994706585888015283824640), (1329152, 2301219103521892905990475404509446033239430999127186729175074320184920653766150929532805180743705213641255490575360627639876277868431572480), (1332224, 5758083068694876011589131003790911312244377467087625518719465917755988125432313475662799641274012650348616094033052267371396387794941921280), (1344512, 3381453284865091631488912773750583323495466674719954940628529421818584492402733889695065330184537551584121524604404698614406601457310184960), (1378304, 960306397419774027310047203591972056359617844357812634293716822365164768192336622132061794249645923807084325469726442196697619794303188480), (1381376, 3635014027827622523510033652368372513328884508014333745758406899696515202664332312147654850219680335285314570032093322094809173602792212480), (1393664, 4773349397352119149368469343323599237231685223953237429859757543671212133404747790289600667809966563089579707929219656072570191452180267520), (1442816, 719994945669253130187721194459593984831546190729464118907464439330907113317306035962148068010461926819747935022508696505653657810370749440), (2100224, 258473966801207924941776239724114112300729049705474049682672106832491899737580580610337952530336210760274935628226208094758506436882979840)]
theorem sparseBlock082_data : sparseBlock082 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (818325468630060111501906861127593081096543118653745472126322012934210820357690220437561258546103429269811905036177595925612333791590553600 : Int) coeff1005) (CoefficientMerge.scale (1216479436972714806311494301228328013769385145232819282422373628513071701512952938784931269804012279972753708223233060445193247405653350400 : Int) coeff1006)) (CoefficientMerge.merge (CoefficientMerge.scale (568744998499459818028677802726369719656692107293945353752248482495049863128349960404489145803240665658266431508248131607355569982708275200 : Int) coeff1007) (CoefficientMerge.merge (CoefficientMerge.scale (436254786974735264790694538058885591190623301934781118762587461493567483323440667408265755865629740510445165779708339438396313431011210240 : Int) coeff1008) (CoefficientMerge.scale (1654282926256704745439469703016279201862821964843902241483675246429212797271485050761960136500032355917552752886864135594033236708369415680 : Int) coeff1009)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (2301219103521892905990475404509446033239430999127186729175074320184920653766150929532805180743705213641255490575360627639876277868431572480 : Int) coeff1010) (CoefficientMerge.scale (960306397419774027310047203591972056359617844357812634293716822365164768192336622132061794249645923807084325469726442196697619794303188480 : Int) coeff1011)) (CoefficientMerge.merge (CoefficientMerge.scale (1035391945073816030270843353562739247982011393173017261283300312771924635481700514209606431908737256973905589023425273880880789118617907200 : Int) coeff1012) (CoefficientMerge.merge (CoefficientMerge.scale (3088088860445201462710484900975157392647088969789746502313527959956943207333566066939329219380260960127724220432991017966749493965417779200 : Int) coeff1013) (CoefficientMerge.scale (2068273089959882489678957002722989202701484817960766327288415566754676687382895364228328956599309941202258075155229623983228217825699635200 : Int) coeff1014))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (2038048781278025714807312514609379991809448040608614189288927468660686370149821164325232972097945149639780693145974994706585888015283824640 : Int) coeff1015) (CoefficientMerge.scale (5758083068694876011589131003790911312244377467087625518719465917755988125432313475662799641274012650348616094033052267371396387794941921280 : Int) coeff1016)) (CoefficientMerge.merge (CoefficientMerge.scale (3635014027827622523510033652368372513328884508014333745758406899696515202664332312147654850219680335285314570032093322094809173602792212480 : Int) coeff1017) (CoefficientMerge.merge (CoefficientMerge.scale (1937015052570608863700834507880693069644177306318076550412589464836681859878401417503080255414896735405590210386443380403167719829198438400 : Int) coeff1018) (CoefficientMerge.scale (3073776694415216006103334321324721205864074942317742916642271862921507881094577913008405802834911375065845800563333739600121382623352294400 : Int) coeff1019)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (3381453284865091631488912773750583323495466674719954940628529421818584492402733889695065330184537551584121524604404698614406601457310184960 : Int) coeff1020) (CoefficientMerge.scale (4773349397352119149368469343323599237231685223953237429859757543671212133404747790289600667809966563089579707929219656072570191452180267520 : Int) coeff1021)) (CoefficientMerge.merge (CoefficientMerge.scale (534485630580126510394692494605572620652679141641053539396242536178700130678066505389444279021239629130673566966806288845667003537088204800 : Int) coeff1022) (CoefficientMerge.merge (CoefficientMerge.scale (719994945669253130187721194459593984831546190729464118907464439330907113317306035962148068010461926819747935022508696505653657810370749440 : Int) coeff1023) (CoefficientMerge.scale (258473966801207924941776239724114112300729049705474049682672106832491899737580580610337952530336210760274935628226208094758506436882979840 : Int) coeff1024)))))) := by decide +kernel
theorem sparseBlock082_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock082 := by
  rw [sparseBlock082_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted1005_nonneg g t z hg hA hB ht hz hw) (weighted1006_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1007_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1008_nonneg g t z hg hA hB ht hz hw) (weighted1009_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1010_nonneg g t z hg hA hB ht hz hw) (weighted1011_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1012_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1013_nonneg g t z hg hA hB ht hz hw) (weighted1014_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted1015_nonneg g t z hg hA hB ht hz hw) (weighted1016_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1017_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1018_nonneg g t z hg hA hB ht hz hw) (weighted1019_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted1020_nonneg g t z hg hA hB ht hz hw) (weighted1021_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted1022_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted1023_nonneg g t z hg hA hB ht hz hw) (weighted1024_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
