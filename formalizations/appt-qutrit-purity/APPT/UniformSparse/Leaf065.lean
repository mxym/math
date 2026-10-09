import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff0665 : CoefficientMerge.Poly :=
  [(2113601, 1)]
noncomputable def atom0665 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 7) ^ 1 * (z) ^ 2)
theorem atom0665_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0665 g t z = CoefficientMerge.eval (monomial g t z) coeff0665 := by
  norm_num [atom0665, coeff0665, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0665_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0665 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0665]
  positivity
theorem weighted0665_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1036144751910822415586259368390716503228249056858066069640832951435456918231550872903706456859309185260366805910882839816218003440140282880 : Int) coeff0665) := by
  rw [CoefficientMerge.eval_scale, ← atom0665_identity]
  exact mul_nonneg (by norm_num) (atom0665_nonneg g t z hg hA hB ht hz hw)

def coeff0666 : CoefficientMerge.Poly :=
  [(2162753, 1)]
noncomputable def atom0666 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 3) ^ 1 * (g 8) ^ 1 * (z) ^ 2)
theorem atom0666_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0666 g t z = CoefficientMerge.eval (monomial g t z) coeff0666 := by
  norm_num [atom0666, coeff0666, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0666_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0666 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0666]
  positivity
theorem weighted0666_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (923683528741399066426356399353468584353279753773844433535440650389823245375611020849554198123438907086733629233362852546967249233554396160 : Int) coeff0666) := by
  rw [CoefficientMerge.eval_scale, ← atom0666_identity]
  exact mul_nonneg (by norm_num) (atom0666_nonneg g t z hg hA hB ht hz hw)

def coeff0667 : CoefficientMerge.Poly :=
  [(2097665, 1)]
noncomputable def atom0667 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 2 * (z) ^ 2)
theorem atom0667_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0667 g t z = CoefficientMerge.eval (monomial g t z) coeff0667 := by
  norm_num [atom0667, coeff0667, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0667_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0667 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0667]
  positivity
theorem weighted0667_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (408793169165467741217682711265267050635443987156199076739562328581894211244884001001800964497327854595627065314905262051955746532773234304 : Int) coeff0667) := by
  rw [CoefficientMerge.eval_scale, ← atom0667_identity]
  exact mul_nonneg (by norm_num) (atom0667_nonneg g t z hg hA hB ht hz hw)

def coeff0668 : CoefficientMerge.Poly :=
  [(2098433, 1)]
noncomputable def atom0668 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 5) ^ 1 * (z) ^ 2)
theorem atom0668_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0668 g t z = CoefficientMerge.eval (monomial g t z) coeff0668 := by
  norm_num [atom0668, coeff0668, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0668_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0668 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0668]
  positivity
theorem weighted0668_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1377221656375432764414431394825180527770026793622063880589759441850763268005289433953153407520064624464703153033822286342242885115363602208 : Int) coeff0668) := by
  rw [CoefficientMerge.eval_scale, ← atom0668_identity]
  exact mul_nonneg (by norm_num) (atom0668_nonneg g t z hg hA hB ht hz hw)

def coeff0669 : CoefficientMerge.Poly :=
  [(2101505, 1)]
noncomputable def atom0669 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (z) ^ 2)
theorem atom0669_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0669 g t z = CoefficientMerge.eval (monomial g t z) coeff0669 := by
  norm_num [atom0669, coeff0669, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0669_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0669 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0669]
  positivity
theorem weighted0669_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1232607954496394111114018087270861467991373019429403346798403835393801686306505697057774851377861330573935166897343514604717364786712898080 : Int) coeff0669) := by
  rw [CoefficientMerge.eval_scale, ← atom0669_identity]
  exact mul_nonneg (by norm_num) (atom0669_nonneg g t z hg hA hB ht hz hw)

def coeff0670 : CoefficientMerge.Poly :=
  [(2113793, 1)]
noncomputable def atom0670 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (z) ^ 2)
theorem atom0670_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0670 g t z = CoefficientMerge.eval (monomial g t z) coeff0670 := by
  norm_num [atom0670, coeff0670, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0670_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0670 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0670]
  positivity
theorem weighted0670_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (483323302842009819375401197872452601354746473033723121029926998792333439086180618704666436033452333490824081909653573141879005932692997920 : Int) coeff0670) := by
  rw [CoefficientMerge.eval_scale, ← atom0670_identity]
  exact mul_nonneg (by norm_num) (atom0670_nonneg g t z hg hA hB ht hz hw)

def coeff0671 : CoefficientMerge.Poly :=
  [(2162945, 1)]
noncomputable def atom0671 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (z) ^ 2)
theorem atom0671_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0671 g t z = CoefficientMerge.eval (monomial g t z) coeff0671 := by
  norm_num [atom0671, coeff0671, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0671_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0671 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0671]
  positivity
theorem weighted0671_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (648270073962361714283831011907758399380976420820197900583386292410557633569501890949271894652401572751119117765823514009906506280153047840 : Int) coeff0671) := by
  rw [CoefficientMerge.eval_scale, ← atom0671_identity]
  exact mul_nonneg (by norm_num) (atom0671_nonneg g t z hg hA hB ht hz hw)

def coeff0672 : CoefficientMerge.Poly :=
  [(2099201, 1)]
noncomputable def atom0672 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 2 * (z) ^ 2)
theorem atom0672_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0672 g t z = CoefficientMerge.eval (monomial g t z) coeff0672 := by
  norm_num [atom0672, coeff0672, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0672_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0672 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0672]
  positivity
theorem weighted0672_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (939890298283914140724999115985036203570656852586285442744811087223846000103455034195237617811336513731679096211639330637348051632257433600 : Int) coeff0672) := by
  rw [CoefficientMerge.eval_scale, ← atom0672_identity]
  exact mul_nonneg (by norm_num) (atom0672_nonneg g t z hg hA hB ht hz hw)

def coeff0673 : CoefficientMerge.Poly :=
  [(2102273, 1)]
noncomputable def atom0673 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (z) ^ 2)
theorem atom0673_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0673 g t z = CoefficientMerge.eval (monomial g t z) coeff0673 := by
  norm_num [atom0673, coeff0673, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0673_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0673 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0673]
  positivity
theorem weighted0673_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1442251339261590816146308656029312203751354038297226644965365730916535900005362829303287496658159684502677405067775514844058541552999255040 : Int) coeff0673) := by
  rw [CoefficientMerge.eval_scale, ← atom0673_identity]
  exact mul_nonneg (by norm_num) (atom0673_nonneg g t z hg hA hB ht hz hw)

def coeff0674 : CoefficientMerge.Poly :=
  [(2114561, 1)]
noncomputable def atom0674 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (z) ^ 2)
theorem atom0674_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0674 g t z = CoefficientMerge.eval (monomial g t z) coeff0674 := by
  norm_num [atom0674, coeff0674, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0674_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0674 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0674]
  positivity
theorem weighted0674_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1040285941856602973208742434918666504924902086147373616551568646995015114366476191870048028473749463362451257595614468458333053330339246080 : Int) coeff0674) := by
  rw [CoefficientMerge.eval_scale, ← atom0674_identity]
  exact mul_nonneg (by norm_num) (atom0674_nonneg g t z hg hA hB ht hz hw)

def coeff0675 : CoefficientMerge.Poly :=
  [(2163713, 1)]
noncomputable def atom0675 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (z) ^ 2)
theorem atom0675_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0675 g t z = CoefficientMerge.eval (monomial g t z) coeff0675 := by
  norm_num [atom0675, coeff0675, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0675_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0675 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0675]
  positivity
theorem weighted0675_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (867019677836303148789019217209273597687143335743797085199069494950774866819449099486055737664153237382365449042759116815551168365885955440 : Int) coeff0675) := by
  rw [CoefficientMerge.eval_scale, ← atom0675_identity]
  exact mul_nonneg (by norm_num) (atom0675_nonneg g t z hg hA hB ht hz hw)

def coeff0676 : CoefficientMerge.Poly :=
  [(2105345, 1)]
noncomputable def atom0676 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 6) ^ 2 * (z) ^ 2)
theorem atom0676_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0676 g t z = CoefficientMerge.eval (monomial g t z) coeff0676 := by
  norm_num [atom0676, coeff0676, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0676_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0676 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0676]
  positivity
theorem weighted0676_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (538645425272286755923083444754705508389116443435272543876019244073910413053661674146817869606407826239542528868558622725972614105926169600 : Int) coeff0676) := by
  rw [CoefficientMerge.eval_scale, ← atom0676_identity]
  exact mul_nonneg (by norm_num) (atom0676_nonneg g t z hg hA hB ht hz hw)

def coeff0677 : CoefficientMerge.Poly :=
  [(2117633, 1)]
noncomputable def atom0677 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (z) ^ 2)
theorem atom0677_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0677 g t z = CoefficientMerge.eval (monomial g t z) coeff0677 := by
  norm_num [atom0677, coeff0677, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0677_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0677 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0677]
  positivity
theorem weighted0677_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (555228276248815327950354589928422546467040123674289885874154122426521903441830804357242215759562186802825014456085012359839522645239196800 : Int) coeff0677) := by
  rw [CoefficientMerge.eval_scale, ← atom0677_identity]
  exact mul_nonneg (by norm_num) (atom0677_nonneg g t z hg hA hB ht hz hw)

def coeff0678 : CoefficientMerge.Poly :=
  [(2166785, 1)]
noncomputable def atom0678 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (z) ^ 2)
theorem atom0678_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0678 g t z = CoefficientMerge.eval (monomial g t z) coeff0678 := by
  norm_num [atom0678, coeff0678, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0678_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0678 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0678]
  positivity
theorem weighted0678_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (325728845809502018400442137074983176792095847072691232671940021777876335422076239942696439752001520282057417816142337667287505371837094400 : Int) coeff0678) := by
  rw [CoefficientMerge.eval_scale, ← atom0678_identity]
  exact mul_nonneg (by norm_num) (atom0678_nonneg g t z hg hA hB ht hz hw)

def coeff0679 : CoefficientMerge.Poly :=
  [(1081345, 1)]
noncomputable def atom0679 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 7) ^ 2 * (z) ^ 1)
theorem atom0679_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0679 g t z = CoefficientMerge.eval (monomial g t z) coeff0679 := by
  norm_num [atom0679, coeff0679, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0679_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0679 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0679]
  positivity
theorem weighted0679_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1475776145246836498678416318302159401604567265795836482612456557935200182225220380452279484602038098110508532597509607325223766031356723200 : Int) coeff0679) := by
  rw [CoefficientMerge.eval_scale, ← atom0679_identity]
  exact mul_nonneg (by norm_num) (atom0679_nonneg g t z hg hA hB ht hz hw)

def coeff0680 : CoefficientMerge.Poly :=
  [(2179073, 1)]
noncomputable def atom0680 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 0) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (z) ^ 2)
theorem atom0680_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0680 g t z = CoefficientMerge.eval (monomial g t z) coeff0680 := by
  norm_num [atom0680, coeff0680, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0680_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0680 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0680]
  positivity
theorem weighted0680_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (54469153639069318511996999965925798475969816757859560573409617158564890427577928479643972033510362218164461745127772969549372142684697600 : Int) coeff0680) := by
  rw [CoefficientMerge.eval_scale, ← atom0680_identity]
  exact mul_nonneg (by norm_num) (atom0680_nonneg g t z hg hA hB ht hz hw)

def coeff0681 : CoefficientMerge.Poly :=
  [(72, 1)]
noncomputable def atom0681 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 2 * (g 3) ^ 1)
theorem atom0681_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0681 g t z = CoefficientMerge.eval (monomial g t z) coeff0681 := by
  norm_num [atom0681, coeff0681, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0681_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0681 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0681]
  positivity
theorem weighted0681_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (7570448507260256981091193515269756495033072430482923474196741348767917120506468717650762590632211152701163049130555189243128509666014003200 : Int) coeff0681) := by
  rw [CoefficientMerge.eval_scale, ← atom0681_identity]
  exact mul_nonneg (by norm_num) (atom0681_nonneg g t z hg hA hB ht hz hw)

def coeff0682 : CoefficientMerge.Poly :=
  [(4104, 1)]
noncomputable def atom0682 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 2 * (g 6) ^ 1)
theorem atom0682_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0682 g t z = CoefficientMerge.eval (monomial g t z) coeff0682 := by
  norm_num [atom0682, coeff0682, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0682_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0682 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0682]
  positivity
theorem weighted0682_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5111728781992554376704599467635074094203811282862897989450248669210296131441558323730925570463670477571958791257428298409212981571107225600 : Int) coeff0682) := by
  rw [CoefficientMerge.eval_scale, ← atom0682_identity]
  exact mul_nonneg (by norm_num) (atom0682_nonneg g t z hg hA hB ht hz hw)

def coeff0683 : CoefficientMerge.Poly :=
  [(263176, 1)]
noncomputable def atom0683 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 2 * (g 5) ^ 1 * (t) ^ 1)
theorem atom0683_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0683 g t z = CoefficientMerge.eval (monomial g t z) coeff0683 := by
  norm_num [atom0683, coeff0683, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0683_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0683 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0683]
  positivity
theorem weighted0683_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (305928916663729110708990872894007199939849903223137476758623763820669776562214038145739119465961228355868720230994610463711909238564454400 : Int) coeff0683) := by
  rw [CoefficientMerge.eval_scale, ← atom0683_identity]
  exact mul_nonneg (by norm_num) (atom0683_nonneg g t z hg hA hB ht hz hw)

def coeff0684 : CoefficientMerge.Poly :=
  [(1048648, 1)]
noncomputable def atom0684 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 2 * (g 3) ^ 1 * (z) ^ 1)
theorem atom0684_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0684 g t z = CoefficientMerge.eval (monomial g t z) coeff0684 := by
  norm_num [atom0684, coeff0684, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0684_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0684 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0684]
  positivity
theorem weighted0684_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (282444043899925025102096740449742868009138545274899704019014150107069711832295647199226777061439335053384217101651949327169904357706547200 : Int) coeff0684) := by
  rw [CoefficientMerge.eval_scale, ← atom0684_identity]
  exact mul_nonneg (by norm_num) (atom0684_nonneg g t z hg hA hB ht hz hw)

def sparseBlock065 : CoefficientMerge.Poly :=
  [(72, 7570448507260256981091193515269756495033072430482923474196741348767917120506468717650762590632211152701163049130555189243128509666014003200), (4104, 5111728781992554376704599467635074094203811282862897989450248669210296131441558323730925570463670477571958791257428298409212981571107225600), (263176, 305928916663729110708990872894007199939849903223137476758623763820669776562214038145739119465961228355868720230994610463711909238564454400), (1048648, 282444043899925025102096740449742868009138545274899704019014150107069711832295647199226777061439335053384217101651949327169904357706547200), (1081345, 1475776145246836498678416318302159401604567265795836482612456557935200182225220380452279484602038098110508532597509607325223766031356723200), (2097665, 408793169165467741217682711265267050635443987156199076739562328581894211244884001001800964497327854595627065314905262051955746532773234304), (2098433, 1377221656375432764414431394825180527770026793622063880589759441850763268005289433953153407520064624464703153033822286342242885115363602208), (2099201, 939890298283914140724999115985036203570656852586285442744811087223846000103455034195237617811336513731679096211639330637348051632257433600), (2101505, 1232607954496394111114018087270861467991373019429403346798403835393801686306505697057774851377861330573935166897343514604717364786712898080), (2102273, 1442251339261590816146308656029312203751354038297226644965365730916535900005362829303287496658159684502677405067775514844058541552999255040), (2105345, 538645425272286755923083444754705508389116443435272543876019244073910413053661674146817869606407826239542528868558622725972614105926169600), (2113601, 1036144751910822415586259368390716503228249056858066069640832951435456918231550872903706456859309185260366805910882839816218003440140282880), (2113793, 483323302842009819375401197872452601354746473033723121029926998792333439086180618704666436033452333490824081909653573141879005932692997920), (2114561, 1040285941856602973208742434918666504924902086147373616551568646995015114366476191870048028473749463362451257595614468458333053330339246080), (2117633, 555228276248815327950354589928422546467040123674289885874154122426521903441830804357242215759562186802825014456085012359839522645239196800), (2162753, 923683528741399066426356399353468584353279753773844433535440650389823245375611020849554198123438907086733629233362852546967249233554396160), (2162945, 648270073962361714283831011907758399380976420820197900583386292410557633569501890949271894652401572751119117765823514009906506280153047840), (2163713, 867019677836303148789019217209273597687143335743797085199069494950774866819449099486055737664153237382365449042759116815551168365885955440), (2166785, 325728845809502018400442137074983176792095847072691232671940021777876335422076239942696439752001520282057417816142337667287505371837094400), (2179073, 54469153639069318511996999965925798475969816757859560573409617158564890427577928479643972033510362218164461745127772969549372142684697600)]
theorem sparseBlock065_data : sparseBlock065 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1036144751910822415586259368390716503228249056858066069640832951435456918231550872903706456859309185260366805910882839816218003440140282880 : Int) coeff0665) (CoefficientMerge.scale (923683528741399066426356399353468584353279753773844433535440650389823245375611020849554198123438907086733629233362852546967249233554396160 : Int) coeff0666)) (CoefficientMerge.merge (CoefficientMerge.scale (408793169165467741217682711265267050635443987156199076739562328581894211244884001001800964497327854595627065314905262051955746532773234304 : Int) coeff0667) (CoefficientMerge.merge (CoefficientMerge.scale (1377221656375432764414431394825180527770026793622063880589759441850763268005289433953153407520064624464703153033822286342242885115363602208 : Int) coeff0668) (CoefficientMerge.scale (1232607954496394111114018087270861467991373019429403346798403835393801686306505697057774851377861330573935166897343514604717364786712898080 : Int) coeff0669)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (483323302842009819375401197872452601354746473033723121029926998792333439086180618704666436033452333490824081909653573141879005932692997920 : Int) coeff0670) (CoefficientMerge.scale (648270073962361714283831011907758399380976420820197900583386292410557633569501890949271894652401572751119117765823514009906506280153047840 : Int) coeff0671)) (CoefficientMerge.merge (CoefficientMerge.scale (939890298283914140724999115985036203570656852586285442744811087223846000103455034195237617811336513731679096211639330637348051632257433600 : Int) coeff0672) (CoefficientMerge.merge (CoefficientMerge.scale (1442251339261590816146308656029312203751354038297226644965365730916535900005362829303287496658159684502677405067775514844058541552999255040 : Int) coeff0673) (CoefficientMerge.scale (1040285941856602973208742434918666504924902086147373616551568646995015114366476191870048028473749463362451257595614468458333053330339246080 : Int) coeff0674))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (867019677836303148789019217209273597687143335743797085199069494950774866819449099486055737664153237382365449042759116815551168365885955440 : Int) coeff0675) (CoefficientMerge.scale (538645425272286755923083444754705508389116443435272543876019244073910413053661674146817869606407826239542528868558622725972614105926169600 : Int) coeff0676)) (CoefficientMerge.merge (CoefficientMerge.scale (555228276248815327950354589928422546467040123674289885874154122426521903441830804357242215759562186802825014456085012359839522645239196800 : Int) coeff0677) (CoefficientMerge.merge (CoefficientMerge.scale (325728845809502018400442137074983176792095847072691232671940021777876335422076239942696439752001520282057417816142337667287505371837094400 : Int) coeff0678) (CoefficientMerge.scale (1475776145246836498678416318302159401604567265795836482612456557935200182225220380452279484602038098110508532597509607325223766031356723200 : Int) coeff0679)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (54469153639069318511996999965925798475969816757859560573409617158564890427577928479643972033510362218164461745127772969549372142684697600 : Int) coeff0680) (CoefficientMerge.scale (7570448507260256981091193515269756495033072430482923474196741348767917120506468717650762590632211152701163049130555189243128509666014003200 : Int) coeff0681)) (CoefficientMerge.merge (CoefficientMerge.scale (5111728781992554376704599467635074094203811282862897989450248669210296131441558323730925570463670477571958791257428298409212981571107225600 : Int) coeff0682) (CoefficientMerge.merge (CoefficientMerge.scale (305928916663729110708990872894007199939849903223137476758623763820669776562214038145739119465961228355868720230994610463711909238564454400 : Int) coeff0683) (CoefficientMerge.scale (282444043899925025102096740449742868009138545274899704019014150107069711832295647199226777061439335053384217101651949327169904357706547200 : Int) coeff0684)))))) := by decide +kernel
theorem sparseBlock065_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock065 := by
  rw [sparseBlock065_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted0665_nonneg g t z hg hA hB ht hz hw) (weighted0666_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0667_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0668_nonneg g t z hg hA hB ht hz hw) (weighted0669_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0670_nonneg g t z hg hA hB ht hz hw) (weighted0671_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0672_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0673_nonneg g t z hg hA hB ht hz hw) (weighted0674_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted0675_nonneg g t z hg hA hB ht hz hw) (weighted0676_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0677_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0678_nonneg g t z hg hA hB ht hz hw) (weighted0679_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0680_nonneg g t z hg hA hB ht hz hw) (weighted0681_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0682_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0683_nonneg g t z hg hA hB ht hz hw) (weighted0684_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
