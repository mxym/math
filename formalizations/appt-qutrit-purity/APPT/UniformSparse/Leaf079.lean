import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff0945 : CoefficientMerge.Poly :=
  [(2101568, 1)]
noncomputable def atom0945 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (z) ^ 2)
theorem atom0945_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0945 g t z = CoefficientMerge.eval (monomial g t z) coeff0945 := by
  norm_num [atom0945, coeff0945, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0945_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0945 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0945]
  positivity
theorem weighted0945_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2984842465328528303467157196698051980890527557106541800452595565949680668662846777562816052239694475826574986605727212313903865700171869120 : Int) coeff0945) := by
  rw [CoefficientMerge.eval_scale, ← atom0945_identity]
  exact mul_nonneg (by norm_num) (atom0945_nonneg g t z hg hA hB ht hz hw)

def coeff0946 : CoefficientMerge.Poly :=
  [(2113856, 1)]
noncomputable def atom0946 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (z) ^ 2)
theorem atom0946_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0946 g t z = CoefficientMerge.eval (monomial g t z) coeff0946 := by
  norm_num [atom0946, coeff0946, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0946_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0946 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0946]
  positivity
theorem weighted0946_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2525715726599302101513923324392930000605189728582125161397262575390872631734888239132789854931826808303390909011395244308076165903702141120 : Int) coeff0946) := by
  rw [CoefficientMerge.eval_scale, ← atom0946_identity]
  exact mul_nonneg (by norm_num) (atom0946_nonneg g t z hg hA hB ht hz hw)

def coeff0947 : CoefficientMerge.Poly :=
  [(2163008, 1)]
noncomputable def atom0947 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (z) ^ 2)
theorem atom0947_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0947 g t z = CoefficientMerge.eval (monomial g t z) coeff0947 := by
  norm_num [atom0947, coeff0947, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0947_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0947 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0947]
  positivity
theorem weighted0947_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4537106282683951526574001812858143257636950754873944408661531007948451093048658431434383587595618790222986833134422395935162379057838123200 : Int) coeff0947) := by
  rw [CoefficientMerge.eval_scale, ← atom0947_identity]
  exact mul_nonneg (by norm_num) (atom0947_nonneg g t z hg hA hB ht hz hw)

def coeff0948 : CoefficientMerge.Poly :=
  [(2099264, 1)]
noncomputable def atom0948 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 5) ^ 2 * (z) ^ 2)
theorem atom0948_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0948 g t z = CoefficientMerge.eval (monomial g t z) coeff0948 := by
  norm_num [atom0948, coeff0948, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0948_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0948 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0948]
  positivity
theorem weighted0948_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (657572364553274835928388795775612964664827874805426823436256184741125993852409208162610760954284033506706453223616594526327676403803607040 : Int) coeff0948) := by
  rw [CoefficientMerge.eval_scale, ← atom0948_identity]
  exact mul_nonneg (by norm_num) (atom0948_nonneg g t z hg hA hB ht hz hw)

def coeff0949 : CoefficientMerge.Poly :=
  [(2102336, 1)]
noncomputable def atom0949 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (z) ^ 2)
theorem atom0949_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0949 g t z = CoefficientMerge.eval (monomial g t z) coeff0949 := by
  norm_num [atom0949, coeff0949, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0949_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0949 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0949]
  positivity
theorem weighted0949_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2106954871992850960046683306587444812155003510659103447784152301295117938923705805871780099127765416345195594899042899898816689405216343040 : Int) coeff0949) := by
  rw [CoefficientMerge.eval_scale, ← atom0949_identity]
  exact mul_nonneg (by norm_num) (atom0949_nonneg g t z hg hA hB ht hz hw)

def coeff0950 : CoefficientMerge.Poly :=
  [(2114624, 1)]
noncomputable def atom0950 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (z) ^ 2)
theorem atom0950_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0950 g t z = CoefficientMerge.eval (monomial g t z) coeff0950 := by
  norm_num [atom0950, coeff0950, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0950_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0950 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0950]
  positivity
theorem weighted0950_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1888709092707894294237549565276635997500540919116397480833024935798118093227677081181307667794831405745327016189655326322578627426403459840 : Int) coeff0950) := by
  rw [CoefficientMerge.eval_scale, ← atom0950_identity]
  exact mul_nonneg (by norm_num) (atom0950_nonneg g t z hg hA hB ht hz hw)

def coeff0951 : CoefficientMerge.Poly :=
  [(2163776, 1)]
noncomputable def atom0951 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (z) ^ 2)
theorem atom0951_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0951 g t z = CoefficientMerge.eval (monomial g t z) coeff0951 := by
  norm_num [atom0951, coeff0951, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0951_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0951 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0951]
  positivity
theorem weighted0951_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1858139951864537722605365117513833410573755356182019714643275236228499004116156963374670848027473869934339420759595790857869053458830823300 : Int) coeff0951) := by
  rw [CoefficientMerge.eval_scale, ← atom0951_identity]
  exact mul_nonneg (by norm_num) (atom0951_nonneg g t z hg hA hB ht hz hw)

def coeff0952 : CoefficientMerge.Poly :=
  [(2105408, 1)]
noncomputable def atom0952 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 6) ^ 2 * (z) ^ 2)
theorem atom0952_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0952 g t z = CoefficientMerge.eval (monomial g t z) coeff0952 := by
  norm_num [atom0952, coeff0952, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0952_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0952 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0952]
  positivity
theorem weighted0952_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (917278894642060913388655243219830477867648238120666640132794625223930248145319294395586020136185187853648411260953195007159636334204870400 : Int) coeff0952) := by
  rw [CoefficientMerge.eval_scale, ← atom0952_identity]
  exact mul_nonneg (by norm_num) (atom0952_nonneg g t z hg hA hB ht hz hw)

def coeff0953 : CoefficientMerge.Poly :=
  [(2117696, 1)]
noncomputable def atom0953 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (z) ^ 2)
theorem atom0953_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0953 g t z = CoefficientMerge.eval (monomial g t z) coeff0953 := by
  norm_num [atom0953, coeff0953, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0953_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0953 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0953]
  positivity
theorem weighted0953_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2302836605366033992065222305855270313344930162855963008141995345106414690106636258416531840042201420716635952707766149825049056673477554400 : Int) coeff0953) := by
  rw [CoefficientMerge.eval_scale, ← atom0953_identity]
  exact mul_nonneg (by norm_num) (atom0953_nonneg g t z hg hA hB ht hz hw)

def coeff0954 : CoefficientMerge.Poly :=
  [(2166848, 1)]
noncomputable def atom0954 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (z) ^ 2)
theorem atom0954_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0954 g t z = CoefficientMerge.eval (monomial g t z) coeff0954 := by
  norm_num [atom0954, coeff0954, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0954_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0954 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0954]
  positivity
theorem weighted0954_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2792992488230113907887285598696716491462727402292186425518127450874822625800629422604246750181141569965701041184235203192436056393549036160 : Int) coeff0954) := by
  rw [CoefficientMerge.eval_scale, ← atom0954_identity]
  exact mul_nonneg (by norm_num) (atom0954_nonneg g t z hg hA hB ht hz hw)

def coeff0955 : CoefficientMerge.Poly :=
  [(2129984, 1)]
noncomputable def atom0955 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 7) ^ 2 * (z) ^ 2)
theorem atom0955_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0955 g t z = CoefficientMerge.eval (monomial g t z) coeff0955 := by
  norm_num [atom0955, coeff0955, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0955_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0955 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0955]
  positivity
theorem weighted0955_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1683078425729402701463184888686317574422894345817441218585527395956686407786638972315150501027902426716613391048265874177546588537607776000 : Int) coeff0955) := by
  rw [CoefficientMerge.eval_scale, ← atom0955_identity]
  exact mul_nonneg (by norm_num) (atom0955_nonneg g t z hg hA hB ht hz hw)

def coeff0956 : CoefficientMerge.Poly :=
  [(2179136, 1)]
noncomputable def atom0956 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (z) ^ 2)
theorem atom0956_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0956 g t z = CoefficientMerge.eval (monomial g t z) coeff0956 := by
  norm_num [atom0956, coeff0956, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0956_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0956 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0956]
  positivity
theorem weighted0956_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4425673221386900419246697284066223124168568284920595493543097383392754426313477661385160111650875880837678008262952778217108940347847731200 : Int) coeff0956) := by
  rw [CoefficientMerge.eval_scale, ← atom0956_identity]
  exact mul_nonneg (by norm_num) (atom0956_nonneg g t z hg hA hB ht hz hw)

def coeff0957 : CoefficientMerge.Poly :=
  [(2228288, 1)]
noncomputable def atom0957 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 8) ^ 2 * (z) ^ 2)
theorem atom0957_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0957 g t z = CoefficientMerge.eval (monomial g t z) coeff0957 := by
  norm_num [atom0957, coeff0957, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0957_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0957 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0957]
  positivity
theorem weighted0957_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2378223957493267226271721384155099965669458295704834230521097626994272528765407670987214306798959560883613506774968526677614740369070301440 : Int) coeff0957) := by
  rw [CoefficientMerge.eval_scale, ← atom0957_identity]
  exact mul_nonneg (by norm_num) (atom0957_nonneg g t z hg hA hB ht hz hw)

def coeff0958 : CoefficientMerge.Poly :=
  [(1053184, 1)]
noncomputable def atom0958 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 2 * (g 6) ^ 1 * (z) ^ 1)
theorem atom0958_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0958 g t z = CoefficientMerge.eval (monomial g t z) coeff0958 := by
  norm_num [atom0958, coeff0958, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0958_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0958 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0958]
  positivity
theorem weighted0958_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (235326018508732818959413488303382213573520692810682746101156372793439064172398493434973646831923109093175889716940583553320222491742238720 : Int) coeff0958) := by
  rw [CoefficientMerge.eval_scale, ← atom0958_identity]
  exact mul_nonneg (by norm_num) (atom0958_nonneg g t z hg hA hB ht hz hw)

def coeff0959 : CoefficientMerge.Poly :=
  [(20736, 1)]
noncomputable def atom0959 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1)
theorem atom0959_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0959 g t z = CoefficientMerge.eval (monomial g t z) coeff0959 := by
  norm_num [atom0959, coeff0959, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0959_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0959 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0959]
  positivity
theorem weighted0959_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4782436066416926974122951102119433586836977463608823904352103187295447799921841916827581886899839436571739343904794972539044187278225612800 : Int) coeff0959) := by
  rw [CoefficientMerge.eval_scale, ← atom0959_identity]
  exact mul_nonneg (by norm_num) (atom0959_nonneg g t z hg hA hB ht hz hw)

def coeff0960 : CoefficientMerge.Poly :=
  [(69888, 1)]
noncomputable def atom0960 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1)
theorem atom0960_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0960 g t z = CoefficientMerge.eval (monomial g t z) coeff0960 := by
  norm_num [atom0960, coeff0960, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0960_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0960 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0960]
  positivity
theorem weighted0960_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (6147087897018463317519057406638545034496376956952920040616971855463260214764179867352603723203362364033747713091902248737340069068454707200 : Int) coeff0960) := by
  rw [CoefficientMerge.eval_scale, ← atom0960_identity]
  exact mul_nonneg (by norm_num) (atom0960_nonneg g t z hg hA hB ht hz hw)

def coeff0961 : CoefficientMerge.Poly :=
  [(332032, 1)]
noncomputable def atom0961 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (t) ^ 1)
theorem atom0961_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0961 g t z = CoefficientMerge.eval (monomial g t z) coeff0961 := by
  norm_num [atom0961, coeff0961, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0961_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0961 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0961]
  positivity
theorem weighted0961_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5774809852338193921962503926458644569464652063318527144530865442169833495973470326867987019426261435166765972085967466429421116565245337600 : Int) coeff0961) := by
  rw [CoefficientMerge.eval_scale, ← atom0961_identity]
  exact mul_nonneg (by norm_num) (atom0961_nonneg g t z hg hA hB ht hz hw)

def coeff0962 : CoefficientMerge.Poly :=
  [(1057024, 1)]
noncomputable def atom0962 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 6) ^ 2 * (z) ^ 1)
theorem atom0962_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0962 g t z = CoefficientMerge.eval (monomial g t z) coeff0962 := by
  norm_num [atom0962, coeff0962, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0962_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0962 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0962]
  positivity
theorem weighted0962_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (147366643866817692833148883590719501128519557303742484645708073381936872522871836602881794762945664966909732519046553440333185076922246400 : Int) coeff0962) := by
  rw [CoefficientMerge.eval_scale, ← atom0962_identity]
  exact mul_nonneg (by norm_num) (atom0962_nonneg g t z hg hA hB ht hz hw)

def coeff0963 : CoefficientMerge.Poly :=
  [(1118464, 1)]
noncomputable def atom0963 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (z) ^ 1)
theorem atom0963_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0963 g t z = CoefficientMerge.eval (monomial g t z) coeff0963 := by
  norm_num [atom0963, coeff0963, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0963_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0963 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0963]
  positivity
theorem weighted0963_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2381922144057178892521770672447648502893854297326085046885885422105583222664426366838497022861868676070970325583398092974113148204399836800 : Int) coeff0963) := by
  rw [CoefficientMerge.eval_scale, ← atom0963_identity]
  exact mul_nonneg (by norm_num) (atom0963_nonneg g t z hg hA hB ht hz hw)

def coeff0964 : CoefficientMerge.Poly :=
  [(528896, 1)]
noncomputable def atom0964 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 4) ^ 2 * (g 6) ^ 1 * (t) ^ 2)
theorem atom0964_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0964 g t z = CoefficientMerge.eval (monomial g t z) coeff0964 := by
  norm_num [atom0964, coeff0964, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0964_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0964 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0964]
  positivity
theorem weighted0964_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1183298310393508566133315303254338412746390287055599381212644425537674538932456731195973399610361729367409613038988297177983712003393587200 : Int) coeff0964) := by
  rw [CoefficientMerge.eval_scale, ← atom0964_identity]
  exact mul_nonneg (by norm_num) (atom0964_nonneg g t z hg hA hB ht hz hw)

def sparseBlock079 : CoefficientMerge.Poly :=
  [(20736, 4782436066416926974122951102119433586836977463608823904352103187295447799921841916827581886899839436571739343904794972539044187278225612800), (69888, 6147087897018463317519057406638545034496376956952920040616971855463260214764179867352603723203362364033747713091902248737340069068454707200), (332032, 5774809852338193921962503926458644569464652063318527144530865442169833495973470326867987019426261435166765972085967466429421116565245337600), (528896, 1183298310393508566133315303254338412746390287055599381212644425537674538932456731195973399610361729367409613038988297177983712003393587200), (1053184, 235326018508732818959413488303382213573520692810682746101156372793439064172398493434973646831923109093175889716940583553320222491742238720), (1057024, 147366643866817692833148883590719501128519557303742484645708073381936872522871836602881794762945664966909732519046553440333185076922246400), (1118464, 2381922144057178892521770672447648502893854297326085046885885422105583222664426366838497022861868676070970325583398092974113148204399836800), (2099264, 657572364553274835928388795775612964664827874805426823436256184741125993852409208162610760954284033506706453223616594526327676403803607040), (2101568, 2984842465328528303467157196698051980890527557106541800452595565949680668662846777562816052239694475826574986605727212313903865700171869120), (2102336, 2106954871992850960046683306587444812155003510659103447784152301295117938923705805871780099127765416345195594899042899898816689405216343040), (2105408, 917278894642060913388655243219830477867648238120666640132794625223930248145319294395586020136185187853648411260953195007159636334204870400), (2113856, 2525715726599302101513923324392930000605189728582125161397262575390872631734888239132789854931826808303390909011395244308076165903702141120), (2114624, 1888709092707894294237549565276635997500540919116397480833024935798118093227677081181307667794831405745327016189655326322578627426403459840), (2117696, 2302836605366033992065222305855270313344930162855963008141995345106414690106636258416531840042201420716635952707766149825049056673477554400), (2129984, 1683078425729402701463184888686317574422894345817441218585527395956686407786638972315150501027902426716613391048265874177546588537607776000), (2163008, 4537106282683951526574001812858143257636950754873944408661531007948451093048658431434383587595618790222986833134422395935162379057838123200), (2163776, 1858139951864537722605365117513833410573755356182019714643275236228499004116156963374670848027473869934339420759595790857869053458830823300), (2166848, 2792992488230113907887285598696716491462727402292186425518127450874822625800629422604246750181141569965701041184235203192436056393549036160), (2179136, 4425673221386900419246697284066223124168568284920595493543097383392754426313477661385160111650875880837678008262952778217108940347847731200), (2228288, 2378223957493267226271721384155099965669458295704834230521097626994272528765407670987214306798959560883613506774968526677614740369070301440)]
theorem sparseBlock079_data : sparseBlock079 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (2984842465328528303467157196698051980890527557106541800452595565949680668662846777562816052239694475826574986605727212313903865700171869120 : Int) coeff0945) (CoefficientMerge.scale (2525715726599302101513923324392930000605189728582125161397262575390872631734888239132789854931826808303390909011395244308076165903702141120 : Int) coeff0946)) (CoefficientMerge.merge (CoefficientMerge.scale (4537106282683951526574001812858143257636950754873944408661531007948451093048658431434383587595618790222986833134422395935162379057838123200 : Int) coeff0947) (CoefficientMerge.merge (CoefficientMerge.scale (657572364553274835928388795775612964664827874805426823436256184741125993852409208162610760954284033506706453223616594526327676403803607040 : Int) coeff0948) (CoefficientMerge.scale (2106954871992850960046683306587444812155003510659103447784152301295117938923705805871780099127765416345195594899042899898816689405216343040 : Int) coeff0949)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1888709092707894294237549565276635997500540919116397480833024935798118093227677081181307667794831405745327016189655326322578627426403459840 : Int) coeff0950) (CoefficientMerge.scale (1858139951864537722605365117513833410573755356182019714643275236228499004116156963374670848027473869934339420759595790857869053458830823300 : Int) coeff0951)) (CoefficientMerge.merge (CoefficientMerge.scale (917278894642060913388655243219830477867648238120666640132794625223930248145319294395586020136185187853648411260953195007159636334204870400 : Int) coeff0952) (CoefficientMerge.merge (CoefficientMerge.scale (2302836605366033992065222305855270313344930162855963008141995345106414690106636258416531840042201420716635952707766149825049056673477554400 : Int) coeff0953) (CoefficientMerge.scale (2792992488230113907887285598696716491462727402292186425518127450874822625800629422604246750181141569965701041184235203192436056393549036160 : Int) coeff0954))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1683078425729402701463184888686317574422894345817441218585527395956686407786638972315150501027902426716613391048265874177546588537607776000 : Int) coeff0955) (CoefficientMerge.scale (4425673221386900419246697284066223124168568284920595493543097383392754426313477661385160111650875880837678008262952778217108940347847731200 : Int) coeff0956)) (CoefficientMerge.merge (CoefficientMerge.scale (2378223957493267226271721384155099965669458295704834230521097626994272528765407670987214306798959560883613506774968526677614740369070301440 : Int) coeff0957) (CoefficientMerge.merge (CoefficientMerge.scale (235326018508732818959413488303382213573520692810682746101156372793439064172398493434973646831923109093175889716940583553320222491742238720 : Int) coeff0958) (CoefficientMerge.scale (4782436066416926974122951102119433586836977463608823904352103187295447799921841916827581886899839436571739343904794972539044187278225612800 : Int) coeff0959)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (6147087897018463317519057406638545034496376956952920040616971855463260214764179867352603723203362364033747713091902248737340069068454707200 : Int) coeff0960) (CoefficientMerge.scale (5774809852338193921962503926458644569464652063318527144530865442169833495973470326867987019426261435166765972085967466429421116565245337600 : Int) coeff0961)) (CoefficientMerge.merge (CoefficientMerge.scale (147366643866817692833148883590719501128519557303742484645708073381936872522871836602881794762945664966909732519046553440333185076922246400 : Int) coeff0962) (CoefficientMerge.merge (CoefficientMerge.scale (2381922144057178892521770672447648502893854297326085046885885422105583222664426366838497022861868676070970325583398092974113148204399836800 : Int) coeff0963) (CoefficientMerge.scale (1183298310393508566133315303254338412746390287055599381212644425537674538932456731195973399610361729367409613038988297177983712003393587200 : Int) coeff0964)))))) := by decide +kernel
theorem sparseBlock079_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock079 := by
  rw [sparseBlock079_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted0945_nonneg g t z hg hA hB ht hz hw) (weighted0946_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0947_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0948_nonneg g t z hg hA hB ht hz hw) (weighted0949_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0950_nonneg g t z hg hA hB ht hz hw) (weighted0951_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0952_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0953_nonneg g t z hg hA hB ht hz hw) (weighted0954_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted0955_nonneg g t z hg hA hB ht hz hw) (weighted0956_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0957_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0958_nonneg g t z hg hA hB ht hz hw) (weighted0959_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0960_nonneg g t z hg hA hB ht hz hw) (weighted0961_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0962_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0963_nonneg g t z hg hA hB ht hz hw) (weighted0964_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
