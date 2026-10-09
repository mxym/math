import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff0805 : CoefficientMerge.Poly :=
  [(2097476, 1)]
noncomputable def atom0805 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 4) ^ 1 * (z) ^ 2)
theorem atom0805_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0805 g t z = CoefficientMerge.eval (monomial g t z) coeff0805 := by
  norm_num [atom0805, coeff0805, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0805_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0805 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0805]
  positivity
theorem weighted0805_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1592462972654298920857317835244243030303820903547618570986026598954641601088876364017966227137684293809907264857252251898346343389809372672 : Int) coeff0805) := by
  rw [CoefficientMerge.eval_scale, ← atom0805_identity]
  exact mul_nonneg (by norm_num) (atom0805_nonneg g t z hg hA hB ht hz hw)

def coeff0806 : CoefficientMerge.Poly :=
  [(2098244, 1)]
noncomputable def atom0806 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 5) ^ 1 * (z) ^ 2)
theorem atom0806_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0806 g t z = CoefficientMerge.eval (monomial g t z) coeff0806 := by
  norm_num [atom0806, coeff0806, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0806_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0806 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0806]
  positivity
theorem weighted0806_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3313385236787724015484153416999227593805279754555535165059973542242593359643989740242205230077499016080703218789345122774137183728307184384 : Int) coeff0806) := by
  rw [CoefficientMerge.eval_scale, ← atom0806_identity]
  exact mul_nonneg (by norm_num) (atom0806_nonneg g t z hg hA hB ht hz hw)

def coeff0807 : CoefficientMerge.Poly :=
  [(2101316, 1)]
noncomputable def atom0807 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 6) ^ 1 * (z) ^ 2)
theorem atom0807_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0807 g t z = CoefficientMerge.eval (monomial g t z) coeff0807 := by
  norm_num [atom0807, coeff0807, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0807_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0807 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0807]
  positivity
theorem weighted0807_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2933853501851120252932528419033616332582740220567265376354135204305284356706784295897320802686495193831249934544550053537343591825269221120 : Int) coeff0807) := by
  rw [CoefficientMerge.eval_scale, ← atom0807_identity]
  exact mul_nonneg (by norm_num) (atom0807_nonneg g t z hg hA hB ht hz hw)

def coeff0808 : CoefficientMerge.Poly :=
  [(2113604, 1)]
noncomputable def atom0808 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 7) ^ 1 * (z) ^ 2)
theorem atom0808_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0808 g t z = CoefficientMerge.eval (monomial g t z) coeff0808 := by
  norm_num [atom0808, coeff0808, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0808_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0808 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0808]
  positivity
theorem weighted0808_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1608989100819091986083840159037717501105177442670675620198067664526314209847481375937511835869730947199433674128345804665944371545534465280 : Int) coeff0808) := by
  rw [CoefficientMerge.eval_scale, ← atom0808_identity]
  exact mul_nonneg (by norm_num) (atom0808_nonneg g t z hg hA hB ht hz hw)

def coeff0809 : CoefficientMerge.Poly :=
  [(2162756, 1)]
noncomputable def atom0809 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 8) ^ 1 * (z) ^ 2)
theorem atom0809_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0809 g t z = CoefficientMerge.eval (monomial g t z) coeff0809 := by
  norm_num [atom0809, coeff0809, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0809_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0809 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0809]
  positivity
theorem weighted0809_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1451029052477295424506372734983779326938922287710165142470510730061846750798622448561103573286251212974333879122517083837759291682594336000 : Int) coeff0809) := by
  rw [CoefficientMerge.eval_scale, ← atom0809_identity]
  exact mul_nonneg (by norm_num) (atom0809_nonneg g t z hg hA hB ht hz hw)

def coeff0810 : CoefficientMerge.Poly :=
  [(2097668, 1)]
noncomputable def atom0810 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 2 * (z) ^ 2)
theorem atom0810_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0810 g t z = CoefficientMerge.eval (monomial g t z) coeff0810 := by
  norm_num [atom0810, coeff0810, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0810_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0810 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0810]
  positivity
theorem weighted0810_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (111281932009546674078481459674690828241925505729174642261614026280108582114005436895629695841772484224337855738529118664143264240578818560 : Int) coeff0810) := by
  rw [CoefficientMerge.eval_scale, ← atom0810_identity]
  exact mul_nonneg (by norm_num) (atom0810_nonneg g t z hg hA hB ht hz hw)

def coeff0811 : CoefficientMerge.Poly :=
  [(2098436, 1)]
noncomputable def atom0811 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 5) ^ 1 * (z) ^ 2)
theorem atom0811_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0811 g t z = CoefficientMerge.eval (monomial g t z) coeff0811 := by
  norm_num [atom0811, coeff0811, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0811_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0811 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0811]
  positivity
theorem weighted0811_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1863547006678815626030078176192175500115164677858551897589712896796465327812647508069280683565337038161900998733437125545927854045324525568 : Int) coeff0811) := by
  rw [CoefficientMerge.eval_scale, ← atom0811_identity]
  exact mul_nonneg (by norm_num) (atom0811_nonneg g t z hg hA hB ht hz hw)

def coeff0812 : CoefficientMerge.Poly :=
  [(2101508, 1)]
noncomputable def atom0812 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (z) ^ 2)
theorem atom0812_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0812 g t z = CoefficientMerge.eval (monomial g t z) coeff0812 := by
  norm_num [atom0812, coeff0812, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0812_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0812 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0812]
  positivity
theorem weighted0812_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1798583202396507744282138671621425665823958910175780602342218483943757823996335522597938017666224460624441002483619190561084002264954707200 : Int) coeff0812) := by
  rw [CoefficientMerge.eval_scale, ← atom0812_identity]
  exact mul_nonneg (by norm_num) (atom0812_nonneg g t z hg hA hB ht hz hw)

def coeff0813 : CoefficientMerge.Poly :=
  [(2113796, 1)]
noncomputable def atom0813 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (z) ^ 2)
theorem atom0813_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0813 g t z = CoefficientMerge.eval (monomial g t z) coeff0813 := by
  norm_num [atom0813, coeff0813, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0813_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0813 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0813]
  positivity
theorem weighted0813_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (630765704491559128054506574579287165661382195273189430076186430194170359104785122928901356481984434329634628175393083888148973414243624960 : Int) coeff0813) := by
  rw [CoefficientMerge.eval_scale, ← atom0813_identity]
  exact mul_nonneg (by norm_num) (atom0813_nonneg g t z hg hA hB ht hz hw)

def coeff0814 : CoefficientMerge.Poly :=
  [(2162948, 1)]
noncomputable def atom0814 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (z) ^ 2)
theorem atom0814_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0814 g t z = CoefficientMerge.eval (monomial g t z) coeff0814 := by
  norm_num [atom0814, coeff0814, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0814_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0814 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0814]
  positivity
theorem weighted0814_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (716843400264848571476972908347268905963482253060288972249836367651017582807152184324775959790922518523574806337353359348770097195055503360 : Int) coeff0814) := by
  rw [CoefficientMerge.eval_scale, ← atom0814_identity]
  exact mul_nonneg (by norm_num) (atom0814_nonneg g t z hg hA hB ht hz hw)

def coeff0815 : CoefficientMerge.Poly :=
  [(2099204, 1)]
noncomputable def atom0815 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 2 * (z) ^ 2)
theorem atom0815_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0815 g t z = CoefficientMerge.eval (monomial g t z) coeff0815 := by
  norm_num [atom0815, coeff0815, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0815_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0815 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0815]
  positivity
theorem weighted0815_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1839449129205061410587972602402137830520737773568307089201809358918438089697955149790610884952669879851589281798529552806847618104566169600 : Int) coeff0815) := by
  rw [CoefficientMerge.eval_scale, ← atom0815_identity]
  exact mul_nonneg (by norm_num) (atom0815_nonneg g t z hg hA hB ht hz hw)

def coeff0816 : CoefficientMerge.Poly :=
  [(2102276, 1)]
noncomputable def atom0816 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (z) ^ 2)
theorem atom0816_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0816 g t z = CoefficientMerge.eval (monomial g t z) coeff0816 := by
  norm_num [atom0816, coeff0816, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0816_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0816 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0816]
  positivity
theorem weighted0816_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2820040398369045295692906026312481175050465820233681940895813793074866018854449961719933168335236022964226592265636156871652451555953927680 : Int) coeff0816) := by
  rw [CoefficientMerge.eval_scale, ← atom0816_identity]
  exact mul_nonneg (by norm_num) (atom0816_nonneg g t z hg hA hB ht hz hw)

def coeff0817 : CoefficientMerge.Poly :=
  [(2114564, 1)]
noncomputable def atom0817 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (z) ^ 2)
theorem atom0817_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0817 g t z = CoefficientMerge.eval (monomial g t z) coeff0817 := by
  norm_num [atom0817, coeff0817, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0817_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0817 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0817]
  positivity
theorem weighted0817_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2040232896735764199371123498827925017197668180867845253682890391659538833192853689782764095198669178298687007832684601366561875592699084800 : Int) coeff0817) := by
  rw [CoefficientMerge.eval_scale, ← atom0817_identity]
  exact mul_nonneg (by norm_num) (atom0817_nonneg g t z hg hA hB ht hz hw)

def coeff0818 : CoefficientMerge.Poly :=
  [(2163716, 1)]
noncomputable def atom0818 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (z) ^ 2)
theorem atom0818_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0818 g t z = CoefficientMerge.eval (monomial g t z) coeff0818 := by
  norm_num [atom0818, coeff0818, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0818_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0818 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0818]
  positivity
theorem weighted0818_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1908960452016725257831564161219924387551146566791272733912057449209394895033669078631404810593764814566377462779683336665079072867904505640 : Int) coeff0818) := by
  rw [CoefficientMerge.eval_scale, ← atom0818_identity]
  exact mul_nonneg (by norm_num) (atom0818_nonneg g t z hg hA hB ht hz hw)

def coeff0819 : CoefficientMerge.Poly :=
  [(2105348, 1)]
noncomputable def atom0819 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 6) ^ 2 * (z) ^ 2)
theorem atom0819_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0819 g t z = CoefficientMerge.eval (monomial g t z) coeff0819 := by
  norm_num [atom0819, coeff0819, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0819_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0819 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0819]
  positivity
theorem weighted0819_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1012715963980562169883672357084466536738983215893021180286984973702923363297694039908213486514192257239593012717404627038727891490478348800 : Int) coeff0819) := by
  rw [CoefficientMerge.eval_scale, ← atom0819_identity]
  exact mul_nonneg (by norm_num) (atom0819_nonneg g t z hg hA hB ht hz hw)

def coeff0820 : CoefficientMerge.Poly :=
  [(2117636, 1)]
noncomputable def atom0820 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (z) ^ 2)
theorem atom0820_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0820 g t z = CoefficientMerge.eval (monomial g t z) coeff0820 := by
  norm_num [atom0820, coeff0820, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0820_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0820 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0820]
  positivity
theorem weighted0820_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1085730006938514432815028607299036335015926366802661780462564587642918928563862569017108389260371933139324945083537194230811687008832158400 : Int) coeff0820) := by
  rw [CoefficientMerge.eval_scale, ← atom0820_identity]
  exact mul_nonneg (by norm_num) (atom0820_nonneg g t z hg hA hB ht hz hw)

def coeff0821 : CoefficientMerge.Poly :=
  [(2166788, 1)]
noncomputable def atom0821 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (z) ^ 2)
theorem atom0821_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0821 g t z = CoefficientMerge.eval (monomial g t z) coeff0821 := by
  norm_num [atom0821, coeff0821, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0821_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0821 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0821]
  positivity
theorem weighted0821_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (830607821359500240880814715677955031940361752560309016102676240832234292901109546713310580769908793304287106503784700262108442480379278080 : Int) coeff0821) := by
  rw [CoefficientMerge.eval_scale, ← atom0821_identity]
  exact mul_nonneg (by norm_num) (atom0821_nonneg g t z hg hA hB ht hz hw)

def coeff0822 : CoefficientMerge.Poly :=
  [(1081348, 1)]
noncomputable def atom0822 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 7) ^ 2 * (z) ^ 1)
theorem atom0822_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0822 g t z = CoefficientMerge.eval (monomial g t z) coeff0822 := by
  norm_num [atom0822, coeff0822, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0822_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0822 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0822]
  positivity
theorem weighted0822_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3970897889173501363011913732983845085526338908350904846564706587906998362715808085681007922307893502175799250933366401625332346233560857600 : Int) coeff0822) := by
  rw [CoefficientMerge.eval_scale, ← atom0822_identity]
  exact mul_nonneg (by norm_num) (atom0822_nonneg g t z hg hA hB ht hz hw)

def coeff0823 : CoefficientMerge.Poly :=
  [(2179076, 1)]
noncomputable def atom0823 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (z) ^ 2)
theorem atom0823_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0823 g t z = CoefficientMerge.eval (monomial g t z) coeff0823 := by
  norm_num [atom0823, coeff0823, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0823_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0823 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0823]
  positivity
theorem weighted0823_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (205643960337989950537335572690530616164929049102550909416545897345343514027742319190475767442890395561078355006304041547317349384727065600 : Int) coeff0823) := by
  rw [CoefficientMerge.eval_scale, ← atom0823_identity]
  exact mul_nonneg (by norm_num) (atom0823_nonneg g t z hg hA hB ht hz hw)

def coeff0824 : CoefficientMerge.Poly :=
  [(4176, 1)]
noncomputable def atom0824 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 3) ^ 1 * (g 6) ^ 1)
theorem atom0824_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0824 g t z = CoefficientMerge.eval (monomial g t z) coeff0824 := by
  norm_num [atom0824, coeff0824, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0824_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0824 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0824]
  positivity
theorem weighted0824_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2350676081758272726222829276143253240493738743975464164947344734682397192218775558017501924242354591575282467514516973855028232220444467200 : Int) coeff0824) := by
  rw [CoefficientMerge.eval_scale, ← atom0824_identity]
  exact mul_nonneg (by norm_num) (atom0824_nonneg g t z hg hA hB ht hz hw)

def sparseBlock072 : CoefficientMerge.Poly :=
  [(4176, 2350676081758272726222829276143253240493738743975464164947344734682397192218775558017501924242354591575282467514516973855028232220444467200), (1081348, 3970897889173501363011913732983845085526338908350904846564706587906998362715808085681007922307893502175799250933366401625332346233560857600), (2097476, 1592462972654298920857317835244243030303820903547618570986026598954641601088876364017966227137684293809907264857252251898346343389809372672), (2097668, 111281932009546674078481459674690828241925505729174642261614026280108582114005436895629695841772484224337855738529118664143264240578818560), (2098244, 3313385236787724015484153416999227593805279754555535165059973542242593359643989740242205230077499016080703218789345122774137183728307184384), (2098436, 1863547006678815626030078176192175500115164677858551897589712896796465327812647508069280683565337038161900998733437125545927854045324525568), (2099204, 1839449129205061410587972602402137830520737773568307089201809358918438089697955149790610884952669879851589281798529552806847618104566169600), (2101316, 2933853501851120252932528419033616332582740220567265376354135204305284356706784295897320802686495193831249934544550053537343591825269221120), (2101508, 1798583202396507744282138671621425665823958910175780602342218483943757823996335522597938017666224460624441002483619190561084002264954707200), (2102276, 2820040398369045295692906026312481175050465820233681940895813793074866018854449961719933168335236022964226592265636156871652451555953927680), (2105348, 1012715963980562169883672357084466536738983215893021180286984973702923363297694039908213486514192257239593012717404627038727891490478348800), (2113604, 1608989100819091986083840159037717501105177442670675620198067664526314209847481375937511835869730947199433674128345804665944371545534465280), (2113796, 630765704491559128054506574579287165661382195273189430076186430194170359104785122928901356481984434329634628175393083888148973414243624960), (2114564, 2040232896735764199371123498827925017197668180867845253682890391659538833192853689782764095198669178298687007832684601366561875592699084800), (2117636, 1085730006938514432815028607299036335015926366802661780462564587642918928563862569017108389260371933139324945083537194230811687008832158400), (2162756, 1451029052477295424506372734983779326938922287710165142470510730061846750798622448561103573286251212974333879122517083837759291682594336000), (2162948, 716843400264848571476972908347268905963482253060288972249836367651017582807152184324775959790922518523574806337353359348770097195055503360), (2163716, 1908960452016725257831564161219924387551146566791272733912057449209394895033669078631404810593764814566377462779683336665079072867904505640), (2166788, 830607821359500240880814715677955031940361752560309016102676240832234292901109546713310580769908793304287106503784700262108442480379278080), (2179076, 205643960337989950537335572690530616164929049102550909416545897345343514027742319190475767442890395561078355006304041547317349384727065600)]
theorem sparseBlock072_data : sparseBlock072 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1592462972654298920857317835244243030303820903547618570986026598954641601088876364017966227137684293809907264857252251898346343389809372672 : Int) coeff0805) (CoefficientMerge.scale (3313385236787724015484153416999227593805279754555535165059973542242593359643989740242205230077499016080703218789345122774137183728307184384 : Int) coeff0806)) (CoefficientMerge.merge (CoefficientMerge.scale (2933853501851120252932528419033616332582740220567265376354135204305284356706784295897320802686495193831249934544550053537343591825269221120 : Int) coeff0807) (CoefficientMerge.merge (CoefficientMerge.scale (1608989100819091986083840159037717501105177442670675620198067664526314209847481375937511835869730947199433674128345804665944371545534465280 : Int) coeff0808) (CoefficientMerge.scale (1451029052477295424506372734983779326938922287710165142470510730061846750798622448561103573286251212974333879122517083837759291682594336000 : Int) coeff0809)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (111281932009546674078481459674690828241925505729174642261614026280108582114005436895629695841772484224337855738529118664143264240578818560 : Int) coeff0810) (CoefficientMerge.scale (1863547006678815626030078176192175500115164677858551897589712896796465327812647508069280683565337038161900998733437125545927854045324525568 : Int) coeff0811)) (CoefficientMerge.merge (CoefficientMerge.scale (1798583202396507744282138671621425665823958910175780602342218483943757823996335522597938017666224460624441002483619190561084002264954707200 : Int) coeff0812) (CoefficientMerge.merge (CoefficientMerge.scale (630765704491559128054506574579287165661382195273189430076186430194170359104785122928901356481984434329634628175393083888148973414243624960 : Int) coeff0813) (CoefficientMerge.scale (716843400264848571476972908347268905963482253060288972249836367651017582807152184324775959790922518523574806337353359348770097195055503360 : Int) coeff0814))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1839449129205061410587972602402137830520737773568307089201809358918438089697955149790610884952669879851589281798529552806847618104566169600 : Int) coeff0815) (CoefficientMerge.scale (2820040398369045295692906026312481175050465820233681940895813793074866018854449961719933168335236022964226592265636156871652451555953927680 : Int) coeff0816)) (CoefficientMerge.merge (CoefficientMerge.scale (2040232896735764199371123498827925017197668180867845253682890391659538833192853689782764095198669178298687007832684601366561875592699084800 : Int) coeff0817) (CoefficientMerge.merge (CoefficientMerge.scale (1908960452016725257831564161219924387551146566791272733912057449209394895033669078631404810593764814566377462779683336665079072867904505640 : Int) coeff0818) (CoefficientMerge.scale (1012715963980562169883672357084466536738983215893021180286984973702923363297694039908213486514192257239593012717404627038727891490478348800 : Int) coeff0819)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1085730006938514432815028607299036335015926366802661780462564587642918928563862569017108389260371933139324945083537194230811687008832158400 : Int) coeff0820) (CoefficientMerge.scale (830607821359500240880814715677955031940361752560309016102676240832234292901109546713310580769908793304287106503784700262108442480379278080 : Int) coeff0821)) (CoefficientMerge.merge (CoefficientMerge.scale (3970897889173501363011913732983845085526338908350904846564706587906998362715808085681007922307893502175799250933366401625332346233560857600 : Int) coeff0822) (CoefficientMerge.merge (CoefficientMerge.scale (205643960337989950537335572690530616164929049102550909416545897345343514027742319190475767442890395561078355006304041547317349384727065600 : Int) coeff0823) (CoefficientMerge.scale (2350676081758272726222829276143253240493738743975464164947344734682397192218775558017501924242354591575282467514516973855028232220444467200 : Int) coeff0824)))))) := by decide +kernel
theorem sparseBlock072_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock072 := by
  rw [sparseBlock072_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted0805_nonneg g t z hg hA hB ht hz hw) (weighted0806_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0807_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0808_nonneg g t z hg hA hB ht hz hw) (weighted0809_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0810_nonneg g t z hg hA hB ht hz hw) (weighted0811_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0812_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0813_nonneg g t z hg hA hB ht hz hw) (weighted0814_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted0815_nonneg g t z hg hA hB ht hz hw) (weighted0816_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0817_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0818_nonneg g t z hg hA hB ht hz hw) (weighted0819_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0820_nonneg g t z hg hA hB ht hz hw) (weighted0821_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0822_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0823_nonneg g t z hg hA hB ht hz hw) (weighted0824_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
