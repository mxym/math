import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff0925 : CoefficientMerge.Poly :=
  [(1315904, 1)]
noncomputable def atom0925 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0925_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0925 g t z = CoefficientMerge.eval (monomial g t z) coeff0925 := by
  norm_num [atom0925, coeff0925, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0925_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0925 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0925]
  positivity
theorem weighted0925_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3920930863929070620982086708766203381327772600152717926548218521198009610356351631757423720648416997277768429490212117073654863241801815040 : Int) coeff0925) := by
  rw [CoefficientMerge.eval_scale, ← atom0925_identity]
  exact mul_nonneg (by norm_num) (atom0925_nonneg g t z hg hA hB ht hz hw)

def coeff0926 : CoefficientMerge.Poly :=
  [(1328192, 1)]
noncomputable def atom0926 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0926_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0926 g t z = CoefficientMerge.eval (monomial g t z) coeff0926 := by
  norm_num [atom0926, coeff0926, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0926_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0926 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0926]
  positivity
theorem weighted0926_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3451941769676586150786395288536651906231985933956798013740528050665673489841596585431504188085643489300011174010525458270021681948714787840 : Int) coeff0926) := by
  rw [CoefficientMerge.eval_scale, ← atom0926_identity]
  exact mul_nonneg (by norm_num) (atom0926_nonneg g t z hg hA hB ht hz hw)

def coeff0927 : CoefficientMerge.Poly :=
  [(1377344, 1)]
noncomputable def atom0927 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0927_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0927 g t z = CoefficientMerge.eval (monomial g t z) coeff0927 := by
  norm_num [atom0927, coeff0927, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0927_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0927 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0927]
  positivity
theorem weighted0927_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4414208038878255434505934911101338472930763173260854668757785953292026467981782499422679679984432728020582282916181973665973394517647459840 : Int) coeff0927) := by
  rw [CoefficientMerge.eval_scale, ← atom0927_identity]
  exact mul_nonneg (by norm_num) (atom0927_nonneg g t z hg hA hB ht hz hw)

def coeff0928 : CoefficientMerge.Poly :=
  [(532544, 1)]
noncomputable def atom0928 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 6) ^ 2 * (t) ^ 2)
theorem atom0928_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0928 g t z = CoefficientMerge.eval (monomial g t z) coeff0928 := by
  norm_num [atom0928, coeff0928, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0928_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0928 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0928]
  positivity
theorem weighted0928_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (711141831127032522722753364249646027660122935532958884127395917114266247439314260802227829027078897584766305596558240679808305702383513600 : Int) coeff0928) := by
  rw [CoefficientMerge.eval_scale, ← atom0928_identity]
  exact mul_nonneg (by norm_num) (atom0928_nonneg g t z hg hA hB ht hz hw)

def coeff0929 : CoefficientMerge.Poly :=
  [(544832, 1)]
noncomputable def atom0929 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (t) ^ 2)
theorem atom0929_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0929 g t z = CoefficientMerge.eval (monomial g t z) coeff0929 := by
  norm_num [atom0929, coeff0929, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0929_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0929 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0929]
  positivity
theorem weighted0929_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2286104566896884229158222792115086984528524375270062725669021781838465463767877873625831547655261150404690118513360886320859338238841190400 : Int) coeff0929) := by
  rw [CoefficientMerge.eval_scale, ← atom0929_identity]
  exact mul_nonneg (by norm_num) (atom0929_nonneg g t z hg hA hB ht hz hw)

def coeff0930 : CoefficientMerge.Poly :=
  [(593984, 1)]
noncomputable def atom0930 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (t) ^ 2)
theorem atom0930_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0930 g t z = CoefficientMerge.eval (monomial g t z) coeff0930 := by
  norm_num [atom0930, coeff0930, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0930_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0930 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0930]
  positivity
theorem weighted0930_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2563160395306741767232503813618390929352795611723498504666675402959535599230649431274435346454998649996213013290891244302279425720247244800 : Int) coeff0930) := by
  rw [CoefficientMerge.eval_scale, ← atom0930_identity]
  exact mul_nonneg (by norm_num) (atom0930_nonneg g t z hg hA hB ht hz hw)

def coeff0931 : CoefficientMerge.Poly :=
  [(1318976, 1)]
noncomputable def atom0931 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 6) ^ 2 * (t) ^ 1 * (z) ^ 1)
theorem atom0931_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0931 g t z = CoefficientMerge.eval (monomial g t z) coeff0931 := by
  norm_num [atom0931, coeff0931, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0931_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0931 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0931]
  positivity
theorem weighted0931_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1659644209817377114141360081118219898258825527386888629405736774069888479455070435119727630369344519052162550082954450545844713613898086400 : Int) coeff0931) := by
  rw [CoefficientMerge.eval_scale, ← atom0931_identity]
  exact mul_nonneg (by norm_num) (atom0931_nonneg g t z hg hA hB ht hz hw)

def coeff0932 : CoefficientMerge.Poly :=
  [(1331264, 1)]
noncomputable def atom0932 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0932_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0932 g t z = CoefficientMerge.eval (monomial g t z) coeff0932 := by
  norm_num [atom0932, coeff0932, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0932_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0932 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0932]
  positivity
theorem weighted0932_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4433185762468333386812934558643500252352807238802560100687142301141575846872054298568697270410852160836081459688959736727659825925027123200 : Int) coeff0932) := by
  rw [CoefficientMerge.eval_scale, ← atom0932_identity]
  exact mul_nonneg (by norm_num) (atom0932_nonneg g t z hg hA hB ht hz hw)

def coeff0933 : CoefficientMerge.Poly :=
  [(1380416, 1)]
noncomputable def atom0933 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0933_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0933 g t z = CoefficientMerge.eval (monomial g t z) coeff0933 := by
  norm_num [atom0933, coeff0933, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0933_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0933 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0933]
  positivity
theorem weighted0933_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5505590555377539478066807252803581536204592295845629762011745444492792563161274277344891881774190797862553597511480442642458260718579520000 : Int) coeff0933) := by
  rw [CoefficientMerge.eval_scale, ← atom0933_identity]
  exact mul_nonneg (by norm_num) (atom0933_nonneg g t z hg hA hB ht hz hw)

def coeff0934 : CoefficientMerge.Poly :=
  [(557120, 1)]
noncomputable def atom0934 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 7) ^ 2 * (t) ^ 2)
theorem atom0934_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0934 g t z = CoefficientMerge.eval (monomial g t z) coeff0934 := by
  norm_num [atom0934, coeff0934, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0934_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0934 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0934]
  positivity
theorem weighted0934_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1477576696499591559937127562442196627883471380363426538801050027846016117230707776701292222427235522345742224738415481383460239611620147200 : Int) coeff0934) := by
  rw [CoefficientMerge.eval_scale, ← atom0934_identity]
  exact mul_nonneg (by norm_num) (atom0934_nonneg g t z hg hA hB ht hz hw)

def coeff0935 : CoefficientMerge.Poly :=
  [(606272, 1)]
noncomputable def atom0935 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (t) ^ 2)
theorem atom0935_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0935 g t z = CoefficientMerge.eval (monomial g t z) coeff0935 := by
  norm_num [atom0935, coeff0935, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0935_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0935 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0935]
  positivity
theorem weighted0935_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3709410573615616637148007562102621193966195253403392995554759947870460844486530456865519059824751667717164508581286901769131015887142041600 : Int) coeff0935) := by
  rw [CoefficientMerge.eval_scale, ← atom0935_identity]
  exact mul_nonneg (by norm_num) (atom0935_nonneg g t z hg hA hB ht hz hw)

def coeff0936 : CoefficientMerge.Poly :=
  [(1343552, 1)]
noncomputable def atom0936 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 7) ^ 2 * (t) ^ 1 * (z) ^ 1)
theorem atom0936_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0936 g t z = CoefficientMerge.eval (monomial g t z) coeff0936 := by
  norm_num [atom0936, coeff0936, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0936_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0936 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0936]
  positivity
theorem weighted0936_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2799752911107970939874398981760955820580945798628716828025457463009897746886465041748841410850854271507707246447791034257818130069201305600 : Int) coeff0936) := by
  rw [CoefficientMerge.eval_scale, ← atom0936_identity]
  exact mul_nonneg (by norm_num) (atom0936_nonneg g t z hg hA hB ht hz hw)

def coeff0937 : CoefficientMerge.Poly :=
  [(1392704, 1)]
noncomputable def atom0937 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 7) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0937_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0937 g t z = CoefficientMerge.eval (monomial g t z) coeff0937 := by
  norm_num [atom0937, coeff0937, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0937_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0937 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0937]
  positivity
theorem weighted0937_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (7539376560674033656855187253676900216212452220729955172255710061240916821507648203280303622039364390902745879872292882962574776311148403200 : Int) coeff0937) := by
  rw [CoefficientMerge.eval_scale, ← atom0937_identity]
  exact mul_nonneg (by norm_num) (atom0937_nonneg g t z hg hA hB ht hz hw)

def coeff0938 : CoefficientMerge.Poly :=
  [(655424, 1)]
noncomputable def atom0938 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 8) ^ 2 * (t) ^ 2)
theorem atom0938_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0938 g t z = CoefficientMerge.eval (monomial g t z) coeff0938 := by
  norm_num [atom0938, coeff0938, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0938_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0938 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0938]
  positivity
theorem weighted0938_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1699126415809230640570488035692821860720087244992569842115112370306016310133888051409978706452180473851929259781581453356164420031085568000 : Int) coeff0938) := by
  rw [CoefficientMerge.eval_scale, ← atom0938_identity]
  exact mul_nonneg (by norm_num) (atom0938_nonneg g t z hg hA hB ht hz hw)

def coeff0939 : CoefficientMerge.Poly :=
  [(1441856, 1)]
noncomputable def atom0939 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 8) ^ 2 * (t) ^ 1 * (z) ^ 1)
theorem atom0939_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0939 g t z = CoefficientMerge.eval (monomial g t z) coeff0939 := by
  norm_num [atom0939, coeff0939, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0939_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0939 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0939]
  positivity
theorem weighted0939_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3266255888121289389515578245930458028955494893357460507402207926532116754384027452926990686909427023013408510035164841671967283752736627200 : Int) coeff0939) := by
  rw [CoefficientMerge.eval_scale, ← atom0939_identity]
  exact mul_nonneg (by norm_num) (atom0939_nonneg g t z hg hA hB ht hz hw)

def coeff0940 : CoefficientMerge.Poly :=
  [(2098304, 1)]
noncomputable def atom0940 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 2 * (g 5) ^ 1 * (z) ^ 2)
theorem atom0940_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0940 g t z = CoefficientMerge.eval (monomial g t z) coeff0940 := by
  norm_num [atom0940, coeff0940, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0940_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0940 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0940]
  positivity
theorem weighted0940_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (940628505338215416842636358932128724076053111014612288813653673801304878181708764861118496146272482359882925999956267009405658528337562880 : Int) coeff0940) := by
  rw [CoefficientMerge.eval_scale, ← atom0940_identity]
  exact mul_nonneg (by norm_num) (atom0940_nonneg g t z hg hA hB ht hz hw)

def coeff0941 : CoefficientMerge.Poly :=
  [(2101376, 1)]
noncomputable def atom0941 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 2 * (g 6) ^ 1 * (z) ^ 2)
theorem atom0941_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0941 g t z = CoefficientMerge.eval (monomial g t z) coeff0941 := by
  norm_num [atom0941, coeff0941, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0941_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0941 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0941]
  positivity
theorem weighted0941_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2167842373727202880748118273908471720968067635799559118120412330746866180837189777014007162679920370647279488889961673661542264341187961600 : Int) coeff0941) := by
  rw [CoefficientMerge.eval_scale, ← atom0941_identity]
  exact mul_nonneg (by norm_num) (atom0941_nonneg g t z hg hA hB ht hz hw)

def coeff0942 : CoefficientMerge.Poly :=
  [(2113664, 1)]
noncomputable def atom0942 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 2 * (g 7) ^ 1 * (z) ^ 2)
theorem atom0942_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0942 g t z = CoefficientMerge.eval (monomial g t z) coeff0942 := by
  norm_num [atom0942, coeff0942, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0942_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0942 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0942]
  positivity
theorem weighted0942_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1589583132834114593300153606382573788452385687962072317135411828454088775933061890495933112759919522465180149975439633094647120838209126400 : Int) coeff0942) := by
  rw [CoefficientMerge.eval_scale, ← atom0942_identity]
  exact mul_nonneg (by norm_num) (atom0942_nonneg g t z hg hA hB ht hz hw)

def coeff0943 : CoefficientMerge.Poly :=
  [(2162816, 1)]
noncomputable def atom0943 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 2 * (g 8) ^ 1 * (z) ^ 2)
theorem atom0943_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0943 g t z = CoefficientMerge.eval (monomial g t z) coeff0943 := by
  norm_num [atom0943, coeff0943, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0943_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0943 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0943]
  positivity
theorem weighted0943_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2907126297960387562518677195537553180070980895632272660441356058898947462267270298832306628559812115539266501671608767114859626687373107200 : Int) coeff0943) := by
  rw [CoefficientMerge.eval_scale, ← atom0943_identity]
  exact mul_nonneg (by norm_num) (atom0943_nonneg g t z hg hA hB ht hz hw)

def coeff0944 : CoefficientMerge.Poly :=
  [(2098496, 1)]
noncomputable def atom0944 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 1 * (g 5) ^ 1 * (z) ^ 2)
theorem atom0944_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0944 g t z = CoefficientMerge.eval (monomial g t z) coeff0944 := by
  norm_num [atom0944, coeff0944, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0944_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0944 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0944]
  positivity
theorem weighted0944_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (738260024603607088744040243700389590222957478045416184018492381214949823962544689701732280334553595240977033592841053359590303752014869760 : Int) coeff0944) := by
  rw [CoefficientMerge.eval_scale, ← atom0944_identity]
  exact mul_nonneg (by norm_num) (atom0944_nonneg g t z hg hA hB ht hz hw)

def sparseBlock078 : CoefficientMerge.Poly :=
  [(532544, 711141831127032522722753364249646027660122935532958884127395917114266247439314260802227829027078897584766305596558240679808305702383513600), (544832, 2286104566896884229158222792115086984528524375270062725669021781838465463767877873625831547655261150404690118513360886320859338238841190400), (557120, 1477576696499591559937127562442196627883471380363426538801050027846016117230707776701292222427235522345742224738415481383460239611620147200), (593984, 2563160395306741767232503813618390929352795611723498504666675402959535599230649431274435346454998649996213013290891244302279425720247244800), (606272, 3709410573615616637148007562102621193966195253403392995554759947870460844486530456865519059824751667717164508581286901769131015887142041600), (655424, 1699126415809230640570488035692821860720087244992569842115112370306016310133888051409978706452180473851929259781581453356164420031085568000), (1315904, 3920930863929070620982086708766203381327772600152717926548218521198009610356351631757423720648416997277768429490212117073654863241801815040), (1318976, 1659644209817377114141360081118219898258825527386888629405736774069888479455070435119727630369344519052162550082954450545844713613898086400), (1328192, 3451941769676586150786395288536651906231985933956798013740528050665673489841596585431504188085643489300011174010525458270021681948714787840), (1331264, 4433185762468333386812934558643500252352807238802560100687142301141575846872054298568697270410852160836081459688959736727659825925027123200), (1343552, 2799752911107970939874398981760955820580945798628716828025457463009897746886465041748841410850854271507707246447791034257818130069201305600), (1377344, 4414208038878255434505934911101338472930763173260854668757785953292026467981782499422679679984432728020582282916181973665973394517647459840), (1380416, 5505590555377539478066807252803581536204592295845629762011745444492792563161274277344891881774190797862553597511480442642458260718579520000), (1392704, 7539376560674033656855187253676900216212452220729955172255710061240916821507648203280303622039364390902745879872292882962574776311148403200), (1441856, 3266255888121289389515578245930458028955494893357460507402207926532116754384027452926990686909427023013408510035164841671967283752736627200), (2098304, 940628505338215416842636358932128724076053111014612288813653673801304878181708764861118496146272482359882925999956267009405658528337562880), (2098496, 738260024603607088744040243700389590222957478045416184018492381214949823962544689701732280334553595240977033592841053359590303752014869760), (2101376, 2167842373727202880748118273908471720968067635799559118120412330746866180837189777014007162679920370647279488889961673661542264341187961600), (2113664, 1589583132834114593300153606382573788452385687962072317135411828454088775933061890495933112759919522465180149975439633094647120838209126400), (2162816, 2907126297960387562518677195537553180070980895632272660441356058898947462267270298832306628559812115539266501671608767114859626687373107200)]
theorem sparseBlock078_data : sparseBlock078 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (3920930863929070620982086708766203381327772600152717926548218521198009610356351631757423720648416997277768429490212117073654863241801815040 : Int) coeff0925) (CoefficientMerge.scale (3451941769676586150786395288536651906231985933956798013740528050665673489841596585431504188085643489300011174010525458270021681948714787840 : Int) coeff0926)) (CoefficientMerge.merge (CoefficientMerge.scale (4414208038878255434505934911101338472930763173260854668757785953292026467981782499422679679984432728020582282916181973665973394517647459840 : Int) coeff0927) (CoefficientMerge.merge (CoefficientMerge.scale (711141831127032522722753364249646027660122935532958884127395917114266247439314260802227829027078897584766305596558240679808305702383513600 : Int) coeff0928) (CoefficientMerge.scale (2286104566896884229158222792115086984528524375270062725669021781838465463767877873625831547655261150404690118513360886320859338238841190400 : Int) coeff0929)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (2563160395306741767232503813618390929352795611723498504666675402959535599230649431274435346454998649996213013290891244302279425720247244800 : Int) coeff0930) (CoefficientMerge.scale (1659644209817377114141360081118219898258825527386888629405736774069888479455070435119727630369344519052162550082954450545844713613898086400 : Int) coeff0931)) (CoefficientMerge.merge (CoefficientMerge.scale (4433185762468333386812934558643500252352807238802560100687142301141575846872054298568697270410852160836081459688959736727659825925027123200 : Int) coeff0932) (CoefficientMerge.merge (CoefficientMerge.scale (5505590555377539478066807252803581536204592295845629762011745444492792563161274277344891881774190797862553597511480442642458260718579520000 : Int) coeff0933) (CoefficientMerge.scale (1477576696499591559937127562442196627883471380363426538801050027846016117230707776701292222427235522345742224738415481383460239611620147200 : Int) coeff0934))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (3709410573615616637148007562102621193966195253403392995554759947870460844486530456865519059824751667717164508581286901769131015887142041600 : Int) coeff0935) (CoefficientMerge.scale (2799752911107970939874398981760955820580945798628716828025457463009897746886465041748841410850854271507707246447791034257818130069201305600 : Int) coeff0936)) (CoefficientMerge.merge (CoefficientMerge.scale (7539376560674033656855187253676900216212452220729955172255710061240916821507648203280303622039364390902745879872292882962574776311148403200 : Int) coeff0937) (CoefficientMerge.merge (CoefficientMerge.scale (1699126415809230640570488035692821860720087244992569842115112370306016310133888051409978706452180473851929259781581453356164420031085568000 : Int) coeff0938) (CoefficientMerge.scale (3266255888121289389515578245930458028955494893357460507402207926532116754384027452926990686909427023013408510035164841671967283752736627200 : Int) coeff0939)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (940628505338215416842636358932128724076053111014612288813653673801304878181708764861118496146272482359882925999956267009405658528337562880 : Int) coeff0940) (CoefficientMerge.scale (2167842373727202880748118273908471720968067635799559118120412330746866180837189777014007162679920370647279488889961673661542264341187961600 : Int) coeff0941)) (CoefficientMerge.merge (CoefficientMerge.scale (1589583132834114593300153606382573788452385687962072317135411828454088775933061890495933112759919522465180149975439633094647120838209126400 : Int) coeff0942) (CoefficientMerge.merge (CoefficientMerge.scale (2907126297960387562518677195537553180070980895632272660441356058898947462267270298832306628559812115539266501671608767114859626687373107200 : Int) coeff0943) (CoefficientMerge.scale (738260024603607088744040243700389590222957478045416184018492381214949823962544689701732280334553595240977033592841053359590303752014869760 : Int) coeff0944)))))) := by decide +kernel
theorem sparseBlock078_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock078 := by
  rw [sparseBlock078_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted0925_nonneg g t z hg hA hB ht hz hw) (weighted0926_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0927_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0928_nonneg g t z hg hA hB ht hz hw) (weighted0929_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0930_nonneg g t z hg hA hB ht hz hw) (weighted0931_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0932_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0933_nonneg g t z hg hA hB ht hz hw) (weighted0934_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted0935_nonneg g t z hg hA hB ht hz hw) (weighted0936_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0937_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0938_nonneg g t z hg hA hB ht hz hw) (weighted0939_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0940_nonneg g t z hg hA hB ht hz hw) (weighted0941_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0942_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0943_nonneg g t z hg hA hB ht hz hw) (weighted0944_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
