import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff0845 : CoefficientMerge.Poly :=
  [(1069072, 1)]
noncomputable def atom0845 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (z) ^ 1)
theorem atom0845_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0845 g t z = CoefficientMerge.eval (monomial g t z) coeff0845 := by
  norm_num [atom0845, coeff0845, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0845_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0845 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0845]
  positivity
theorem weighted0845_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3036143913990181027625125257494497147104170027682124443061117323074147919110665433297810311844781669265268159801848397212884195797322700800 : Int) coeff0845) := by
  rw [CoefficientMerge.eval_scale, ← atom0845_identity]
  exact mul_nonneg (by norm_num) (atom0845_nonneg g t z hg hA hB ht hz hw)

def coeff0846 : CoefficientMerge.Poly :=
  [(1118224, 1)]
noncomputable def atom0846 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (z) ^ 1)
theorem atom0846_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0846 g t z = CoefficientMerge.eval (monomial g t z) coeff0846 := by
  norm_num [atom0846, coeff0846, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0846_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0846 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0846]
  positivity
theorem weighted0846_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5120135338231974295244492626822693948979155425814836060605764836909860858485423990574470419407524050403441459151634505396278763842992793600 : Int) coeff0846) := by
  rw [CoefficientMerge.eval_scale, ← atom0846_identity]
  exact mul_nonneg (by norm_num) (atom0846_nonneg g t z hg hA hB ht hz hw)

def coeff0847 : CoefficientMerge.Poly :=
  [(525392, 1)]
noncomputable def atom0847 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 5) ^ 1 * (t) ^ 2)
theorem atom0847_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0847 g t z = CoefficientMerge.eval (monomial g t z) coeff0847 := by
  norm_num [atom0847, coeff0847, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0847_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0847 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0847]
  positivity
theorem weighted0847_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (421424155480274248858860747806391909641029590677151094607379644472765153491368511305244181183732612494827410026858046865235135051787686400 : Int) coeff0847) := by
  rw [CoefficientMerge.eval_scale, ← atom0847_identity]
  exact mul_nonneg (by norm_num) (atom0847_nonneg g t z hg hA hB ht hz hw)

def coeff0848 : CoefficientMerge.Poly :=
  [(528464, 1)]
noncomputable def atom0848 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 6) ^ 1 * (t) ^ 2)
theorem atom0848_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0848 g t z = CoefficientMerge.eval (monomial g t z) coeff0848 := by
  norm_num [atom0848, coeff0848, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0848_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0848 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0848]
  positivity
theorem weighted0848_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1579436069535654195162479160411827680378920184494685731882827153854977410149033144649438459026358202207357145904026876571224411466199575040 : Int) coeff0848) := by
  rw [CoefficientMerge.eval_scale, ← atom0848_identity]
  exact mul_nonneg (by norm_num) (atom0848_nonneg g t z hg hA hB ht hz hw)

def coeff0849 : CoefficientMerge.Poly :=
  [(540752, 1)]
noncomputable def atom0849 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 7) ^ 1 * (t) ^ 2)
theorem atom0849_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0849 g t z = CoefficientMerge.eval (monomial g t z) coeff0849 := by
  norm_num [atom0849, coeff0849, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0849_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0849 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0849]
  positivity
theorem weighted0849_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1809586998098636913190884246345895136083134481494719607775364098382536417854233941133346892807032973891757804679942732974827379318382144000 : Int) coeff0849) := by
  rw [CoefficientMerge.eval_scale, ← atom0849_identity]
  exact mul_nonneg (by norm_num) (atom0849_nonneg g t z hg hA hB ht hz hw)

def coeff0850 : CoefficientMerge.Poly :=
  [(589904, 1)]
noncomputable def atom0850 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 8) ^ 1 * (t) ^ 2)
theorem atom0850_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0850 g t z = CoefficientMerge.eval (monomial g t z) coeff0850 := by
  norm_num [atom0850, coeff0850, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0850_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0850 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0850]
  positivity
theorem weighted0850_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5442377596308693090002699928753813327231146775383468769827845729530179444366645715074987803468381152875865030119547904978417302638122867200 : Int) coeff0850) := by
  rw [CoefficientMerge.eval_scale, ← atom0850_identity]
  exact mul_nonneg (by norm_num) (atom0850_nonneg g t z hg hA hB ht hz hw)

def coeff0851 : CoefficientMerge.Poly :=
  [(1311824, 1)]
noncomputable def atom0851 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 5) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0851_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0851 g t z = CoefficientMerge.eval (monomial g t z) coeff0851 := by
  norm_num [atom0851, coeff0851, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0851_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0851 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0851]
  positivity
theorem weighted0851_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3855405311270485252226633733897866904322048979914161154202699487276463392068665392547077400231563896171635661726919371650282466544549577920 : Int) coeff0851) := by
  rw [CoefficientMerge.eval_scale, ← atom0851_identity]
  exact mul_nonneg (by norm_num) (atom0851_nonneg g t z hg hA hB ht hz hw)

def coeff0852 : CoefficientMerge.Poly :=
  [(1314896, 1)]
noncomputable def atom0852 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0852_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0852 g t z = CoefficientMerge.eval (monomial g t z) coeff0852 := by
  norm_num [atom0852, coeff0852, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0852_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0852 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0852]
  positivity
theorem weighted0852_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4155037924327370781850269665512641624386509233783523078057010979663170277272158635453919262562907383381235064175178698684447197846097556800 : Int) coeff0852) := by
  rw [CoefficientMerge.eval_scale, ← atom0852_identity]
  exact mul_nonneg (by norm_num) (atom0852_nonneg g t z hg hA hB ht hz hw)

def coeff0853 : CoefficientMerge.Poly :=
  [(1327184, 1)]
noncomputable def atom0853 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0853_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0853 g t z = CoefficientMerge.eval (monomial g t z) coeff0853 := by
  norm_num [atom0853, coeff0853, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0853_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0853 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0853]
  positivity
theorem weighted0853_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1899331146517732187508909621598060616287475195224003661531746906028480784529034356985347544688079369895507619444409903159798954807500759360 : Int) coeff0853) := by
  rw [CoefficientMerge.eval_scale, ← atom0853_identity]
  exact mul_nonneg (by norm_num) (atom0853_nonneg g t z hg hA hB ht hz hw)

def coeff0854 : CoefficientMerge.Poly :=
  [(1376336, 1)]
noncomputable def atom0854 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0854_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0854 g t z = CoefficientMerge.eval (monomial g t z) coeff0854 := by
  norm_num [atom0854, coeff0854, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0854_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0854 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0854]
  positivity
theorem weighted0854_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (6475524661594468425693652729766427189888299499310093525287728878413353270102098982584834651435931702043534250758000771462225626338847319360 : Int) coeff0854) := by
  rw [CoefficientMerge.eval_scale, ← atom0854_identity]
  exact mul_nonneg (by norm_num) (atom0854_nonneg g t z hg hA hB ht hz hw)

def coeff0855 : CoefficientMerge.Poly :=
  [(525584, 1)]
noncomputable def atom0855 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 5) ^ 1 * (t) ^ 2)
theorem atom0855_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0855 g t z = CoefficientMerge.eval (monomial g t z) coeff0855 := by
  norm_num [atom0855, coeff0855, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0855_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0855 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0855]
  positivity
theorem weighted0855_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (432490423069118746625635273510100531951186353987251216077357166379494813389593085013854737172171233911119156073280789011992005982839756800 : Int) coeff0855) := by
  rw [CoefficientMerge.eval_scale, ← atom0855_identity]
  exact mul_nonneg (by norm_num) (atom0855_nonneg g t z hg hA hB ht hz hw)

def coeff0856 : CoefficientMerge.Poly :=
  [(528656, 1)]
noncomputable def atom0856 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (t) ^ 2)
theorem atom0856_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0856 g t z = CoefficientMerge.eval (monomial g t z) coeff0856 := by
  norm_num [atom0856, coeff0856, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0856_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0856 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0856]
  positivity
theorem weighted0856_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2079927608321363983456966705465145896409487655652673584984012782642766688701904042477037524713650448348996327922240041604999171965136860160 : Int) coeff0856) := by
  rw [CoefficientMerge.eval_scale, ← atom0856_identity]
  exact mul_nonneg (by norm_num) (atom0856_nonneg g t z hg hA hB ht hz hw)

def coeff0857 : CoefficientMerge.Poly :=
  [(590096, 1)]
noncomputable def atom0857 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (t) ^ 2)
theorem atom0857_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0857 g t z = CoefficientMerge.eval (monomial g t z) coeff0857 := by
  norm_num [atom0857, coeff0857, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0857_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0857 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0857]
  positivity
theorem weighted0857_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4330334260774773215268711279822917851878681869261513475688617125166199633531285056213629357968498424460045306881000391306074980225717324800 : Int) coeff0857) := by
  rw [CoefficientMerge.eval_scale, ← atom0857_identity]
  exact mul_nonneg (by norm_num) (atom0857_nonneg g t z hg hA hB ht hz hw)

def coeff0858 : CoefficientMerge.Poly :=
  [(1312016, 1)]
noncomputable def atom0858 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 5) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0858_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0858 g t z = CoefficientMerge.eval (monomial g t z) coeff0858 := by
  norm_num [atom0858, coeff0858, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0858_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0858 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0858]
  positivity
theorem weighted0858_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2402602379353701451725721701173447719887055592111482784617981538285145486634842625473203693354491537186623280786166277095271421395911579904 : Int) coeff0858) := by
  rw [CoefficientMerge.eval_scale, ← atom0858_identity]
  exact mul_nonneg (by norm_num) (atom0858_nonneg g t z hg hA hB ht hz hw)

def coeff0859 : CoefficientMerge.Poly :=
  [(1315088, 1)]
noncomputable def atom0859 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0859_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0859 g t z = CoefficientMerge.eval (monomial g t z) coeff0859 := by
  norm_num [atom0859, coeff0859, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0859_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0859 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0859]
  positivity
theorem weighted0859_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3632019463439083196236945550826933607867375413244690053671443754373973896949326525212266603362490073363516852236605124377078370860866505600 : Int) coeff0859) := by
  rw [CoefficientMerge.eval_scale, ← atom0859_identity]
  exact mul_nonneg (by norm_num) (atom0859_nonneg g t z hg hA hB ht hz hw)

def coeff0860 : CoefficientMerge.Poly :=
  [(1327376, 1)]
noncomputable def atom0860 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0860_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0860 g t z = CoefficientMerge.eval (monomial g t z) coeff0860 := by
  norm_num [atom0860, coeff0860, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0860_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0860 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0860]
  positivity
theorem weighted0860_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1518102985096830433091183588656320939355736611574733948799932135569653874056864211494877638439126043693148692914498083688737572019101288000 : Int) coeff0860) := by
  rw [CoefficientMerge.eval_scale, ← atom0860_identity]
  exact mul_nonneg (by norm_num) (atom0860_nonneg g t z hg hA hB ht hz hw)

def coeff0861 : CoefficientMerge.Poly :=
  [(1376528, 1)]
noncomputable def atom0861 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0861_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0861 g t z = CoefficientMerge.eval (monomial g t z) coeff0861 := by
  norm_num [atom0861, coeff0861, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0861_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0861 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0861]
  positivity
theorem weighted0861_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2833944160650387589426577349961728169191851844632098305643813303335616792503198276154095366115019199191933672377949008778483126596802879520 : Int) coeff0861) := by
  rw [CoefficientMerge.eval_scale, ← atom0861_identity]
  exact mul_nonneg (by norm_num) (atom0861_nonneg g t z hg hA hB ht hz hw)

def coeff0862 : CoefficientMerge.Poly :=
  [(529424, 1)]
noncomputable def atom0862 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (t) ^ 2)
theorem atom0862_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0862 g t z = CoefficientMerge.eval (monomial g t z) coeff0862 := by
  norm_num [atom0862, coeff0862, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0862_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0862 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0862]
  positivity
theorem weighted0862_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (815818638425734346620666602502366889832626610793166750332463786617567605783770627869043907549968280862015494581476420403841995684552448000 : Int) coeff0862) := by
  rw [CoefficientMerge.eval_scale, ← atom0862_identity]
  exact mul_nonneg (by norm_num) (atom0862_nonneg g t z hg hA hB ht hz hw)

def coeff0863 : CoefficientMerge.Poly :=
  [(541712, 1)]
noncomputable def atom0863 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (t) ^ 2)
theorem atom0863_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0863 g t z = CoefficientMerge.eval (monomial g t z) coeff0863 := by
  norm_num [atom0863, coeff0863, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0863_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0863 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0863]
  positivity
theorem weighted0863_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1274926751921776254797911315858654818265835299554436650108898832251369643304438354260847935663804171719958333966023648001687606946358886400 : Int) coeff0863) := by
  rw [CoefficientMerge.eval_scale, ← atom0863_identity]
  exact mul_nonneg (by norm_num) (atom0863_nonneg g t z hg hA hB ht hz hw)

def coeff0864 : CoefficientMerge.Poly :=
  [(590864, 1)]
noncomputable def atom0864 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (t) ^ 2)
theorem atom0864_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0864 g t z = CoefficientMerge.eval (monomial g t z) coeff0864 := by
  norm_num [atom0864, coeff0864, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0864_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0864 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0864]
  positivity
theorem weighted0864_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4092181034573417433847527107416648910349685845268434975510760129545877381496424763834218732525352144985044039300917406521220763653975756800 : Int) coeff0864) := by
  rw [CoefficientMerge.eval_scale, ← atom0864_identity]
  exact mul_nonneg (by norm_num) (atom0864_nonneg g t z hg hA hB ht hz hw)

def sparseBlock074 : CoefficientMerge.Poly :=
  [(525392, 421424155480274248858860747806391909641029590677151094607379644472765153491368511305244181183732612494827410026858046865235135051787686400), (525584, 432490423069118746625635273510100531951186353987251216077357166379494813389593085013854737172171233911119156073280789011992005982839756800), (528464, 1579436069535654195162479160411827680378920184494685731882827153854977410149033144649438459026358202207357145904026876571224411466199575040), (528656, 2079927608321363983456966705465145896409487655652673584984012782642766688701904042477037524713650448348996327922240041604999171965136860160), (529424, 815818638425734346620666602502366889832626610793166750332463786617567605783770627869043907549968280862015494581476420403841995684552448000), (540752, 1809586998098636913190884246345895136083134481494719607775364098382536417854233941133346892807032973891757804679942732974827379318382144000), (541712, 1274926751921776254797911315858654818265835299554436650108898832251369643304438354260847935663804171719958333966023648001687606946358886400), (589904, 5442377596308693090002699928753813327231146775383468769827845729530179444366645715074987803468381152875865030119547904978417302638122867200), (590096, 4330334260774773215268711279822917851878681869261513475688617125166199633531285056213629357968498424460045306881000391306074980225717324800), (590864, 4092181034573417433847527107416648910349685845268434975510760129545877381496424763834218732525352144985044039300917406521220763653975756800), (1069072, 3036143913990181027625125257494497147104170027682124443061117323074147919110665433297810311844781669265268159801848397212884195797322700800), (1118224, 5120135338231974295244492626822693948979155425814836060605764836909860858485423990574470419407524050403441459151634505396278763842992793600), (1311824, 3855405311270485252226633733897866904322048979914161154202699487276463392068665392547077400231563896171635661726919371650282466544549577920), (1312016, 2402602379353701451725721701173447719887055592111482784617981538285145486634842625473203693354491537186623280786166277095271421395911579904), (1314896, 4155037924327370781850269665512641624386509233783523078057010979663170277272158635453919262562907383381235064175178698684447197846097556800), (1315088, 3632019463439083196236945550826933607867375413244690053671443754373973896949326525212266603362490073363516852236605124377078370860866505600), (1327184, 1899331146517732187508909621598060616287475195224003661531746906028480784529034356985347544688079369895507619444409903159798954807500759360), (1327376, 1518102985096830433091183588656320939355736611574733948799932135569653874056864211494877638439126043693148692914498083688737572019101288000), (1376336, 6475524661594468425693652729766427189888299499310093525287728878413353270102098982584834651435931702043534250758000771462225626338847319360), (1376528, 2833944160650387589426577349961728169191851844632098305643813303335616792503198276154095366115019199191933672377949008778483126596802879520)]
theorem sparseBlock074_data : sparseBlock074 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (3036143913990181027625125257494497147104170027682124443061117323074147919110665433297810311844781669265268159801848397212884195797322700800 : Int) coeff0845) (CoefficientMerge.scale (5120135338231974295244492626822693948979155425814836060605764836909860858485423990574470419407524050403441459151634505396278763842992793600 : Int) coeff0846)) (CoefficientMerge.merge (CoefficientMerge.scale (421424155480274248858860747806391909641029590677151094607379644472765153491368511305244181183732612494827410026858046865235135051787686400 : Int) coeff0847) (CoefficientMerge.merge (CoefficientMerge.scale (1579436069535654195162479160411827680378920184494685731882827153854977410149033144649438459026358202207357145904026876571224411466199575040 : Int) coeff0848) (CoefficientMerge.scale (1809586998098636913190884246345895136083134481494719607775364098382536417854233941133346892807032973891757804679942732974827379318382144000 : Int) coeff0849)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (5442377596308693090002699928753813327231146775383468769827845729530179444366645715074987803468381152875865030119547904978417302638122867200 : Int) coeff0850) (CoefficientMerge.scale (3855405311270485252226633733897866904322048979914161154202699487276463392068665392547077400231563896171635661726919371650282466544549577920 : Int) coeff0851)) (CoefficientMerge.merge (CoefficientMerge.scale (4155037924327370781850269665512641624386509233783523078057010979663170277272158635453919262562907383381235064175178698684447197846097556800 : Int) coeff0852) (CoefficientMerge.merge (CoefficientMerge.scale (1899331146517732187508909621598060616287475195224003661531746906028480784529034356985347544688079369895507619444409903159798954807500759360 : Int) coeff0853) (CoefficientMerge.scale (6475524661594468425693652729766427189888299499310093525287728878413353270102098982584834651435931702043534250758000771462225626338847319360 : Int) coeff0854))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (432490423069118746625635273510100531951186353987251216077357166379494813389593085013854737172171233911119156073280789011992005982839756800 : Int) coeff0855) (CoefficientMerge.scale (2079927608321363983456966705465145896409487655652673584984012782642766688701904042477037524713650448348996327922240041604999171965136860160 : Int) coeff0856)) (CoefficientMerge.merge (CoefficientMerge.scale (4330334260774773215268711279822917851878681869261513475688617125166199633531285056213629357968498424460045306881000391306074980225717324800 : Int) coeff0857) (CoefficientMerge.merge (CoefficientMerge.scale (2402602379353701451725721701173447719887055592111482784617981538285145486634842625473203693354491537186623280786166277095271421395911579904 : Int) coeff0858) (CoefficientMerge.scale (3632019463439083196236945550826933607867375413244690053671443754373973896949326525212266603362490073363516852236605124377078370860866505600 : Int) coeff0859)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1518102985096830433091183588656320939355736611574733948799932135569653874056864211494877638439126043693148692914498083688737572019101288000 : Int) coeff0860) (CoefficientMerge.scale (2833944160650387589426577349961728169191851844632098305643813303335616792503198276154095366115019199191933672377949008778483126596802879520 : Int) coeff0861)) (CoefficientMerge.merge (CoefficientMerge.scale (815818638425734346620666602502366889832626610793166750332463786617567605783770627869043907549968280862015494581476420403841995684552448000 : Int) coeff0862) (CoefficientMerge.merge (CoefficientMerge.scale (1274926751921776254797911315858654818265835299554436650108898832251369643304438354260847935663804171719958333966023648001687606946358886400 : Int) coeff0863) (CoefficientMerge.scale (4092181034573417433847527107416648910349685845268434975510760129545877381496424763834218732525352144985044039300917406521220763653975756800 : Int) coeff0864)))))) := by decide +kernel
theorem sparseBlock074_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock074 := by
  rw [sparseBlock074_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted0845_nonneg g t z hg hA hB ht hz hw) (weighted0846_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0847_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0848_nonneg g t z hg hA hB ht hz hw) (weighted0849_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0850_nonneg g t z hg hA hB ht hz hw) (weighted0851_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0852_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0853_nonneg g t z hg hA hB ht hz hw) (weighted0854_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted0855_nonneg g t z hg hA hB ht hz hw) (weighted0856_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0857_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0858_nonneg g t z hg hA hB ht hz hw) (weighted0859_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0860_nonneg g t z hg hA hB ht hz hw) (weighted0861_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0862_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0863_nonneg g t z hg hA hB ht hz hw) (weighted0864_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
