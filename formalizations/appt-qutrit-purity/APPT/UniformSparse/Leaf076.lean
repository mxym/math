import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff0885 : CoefficientMerge.Poly :=
  [(2102288, 1)]
noncomputable def atom0885 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (z) ^ 2)
theorem atom0885_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0885 g t z = CoefficientMerge.eval (monomial g t z) coeff0885 := by
  norm_num [atom0885, coeff0885, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0885_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0885 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0885]
  positivity
theorem weighted0885_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3068397992897829570883058285016703595301038582253768067496176309943746342957342442394506811579564714835568440072913582086404580152930263040 : Int) coeff0885) := by
  rw [CoefficientMerge.eval_scale, ← atom0885_identity]
  exact mul_nonneg (by norm_num) (atom0885_nonneg g t z hg hA hB ht hz hw)

def coeff0886 : CoefficientMerge.Poly :=
  [(2114576, 1)]
noncomputable def atom0886 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1 * (z) ^ 2)
theorem atom0886_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0886 g t z = CoefficientMerge.eval (monomial g t z) coeff0886 := by
  norm_num [atom0886, coeff0886, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0886_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0886 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0886]
  positivity
theorem weighted0886_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1918354807449539324393094265256836882770163932047052992416766883669568016677781951586038769731770518932276264748086606382093290837809958400 : Int) coeff0886) := by
  rw [CoefficientMerge.eval_scale, ← atom0886_identity]
  exact mul_nonneg (by norm_num) (atom0886_nonneg g t z hg hA hB ht hz hw)

def coeff0887 : CoefficientMerge.Poly :=
  [(2163728, 1)]
noncomputable def atom0887 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (z) ^ 2)
theorem atom0887_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0887 g t z = CoefficientMerge.eval (monomial g t z) coeff0887 := by
  norm_num [atom0887, coeff0887, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0887_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0887 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0887]
  positivity
theorem weighted0887_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1958092775708052061678139304688592463746028413358935531506371466197629948901316368529862161285328720720114196061282570289639285092851428640 : Int) coeff0887) := by
  rw [CoefficientMerge.eval_scale, ← atom0887_identity]
  exact mul_nonneg (by norm_num) (atom0887_nonneg g t z hg hA hB ht hz hw)

def coeff0888 : CoefficientMerge.Poly :=
  [(2105360, 1)]
noncomputable def atom0888 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 6) ^ 2 * (z) ^ 2)
theorem atom0888_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0888 g t z = CoefficientMerge.eval (monomial g t z) coeff0888 := by
  norm_num [atom0888, coeff0888, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0888_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0888 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0888]
  positivity
theorem weighted0888_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (884525691086052317325485231915621419385095285254577248551690955430338231995672693583331283316041129484182265464797915131558247034899292160 : Int) coeff0888) := by
  rw [CoefficientMerge.eval_scale, ← atom0888_identity]
  exact mul_nonneg (by norm_num) (atom0888_nonneg g t z hg hA hB ht hz hw)

def coeff0889 : CoefficientMerge.Poly :=
  [(2117648, 1)]
noncomputable def atom0889 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1 * (z) ^ 2)
theorem atom0889_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0889 g t z = CoefficientMerge.eval (monomial g t z) coeff0889 := by
  norm_num [atom0889, coeff0889, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0889_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0889 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0889]
  positivity
theorem weighted0889_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (485301787428897675532242844937402496395295059206423252353352098826181027945604009072742978803589003705390787421824367256291397312987408640 : Int) coeff0889) := by
  rw [CoefficientMerge.eval_scale, ← atom0889_identity]
  exact mul_nonneg (by norm_num) (atom0889_nonneg g t z hg hA hB ht hz hw)

def coeff0890 : CoefficientMerge.Poly :=
  [(2166800, 1)]
noncomputable def atom0890 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 2) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (z) ^ 2)
theorem atom0890_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0890 g t z = CoefficientMerge.eval (monomial g t z) coeff0890 := by
  norm_num [atom0890, coeff0890, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0890_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0890 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0890]
  positivity
theorem weighted0890_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (249924797850241150306027442631729359983306430540489187656804970659636260733293926084348323943549252118284569576318123127954756066279459840 : Int) coeff0890) := by
  rw [CoefficientMerge.eval_scale, ← atom0890_identity]
  exact mul_nonneg (by norm_num) (atom0890_nonneg g t z hg hA hB ht hz hw)

def coeff0891 : CoefficientMerge.Poly :=
  [(1048960, 1)]
noncomputable def atom0891 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 2 * (g 4) ^ 1 * (z) ^ 1)
theorem atom0891_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0891 g t z = CoefficientMerge.eval (monomial g t z) coeff0891 := by
  norm_num [atom0891, coeff0891, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0891_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0891 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0891]
  positivity
theorem weighted0891_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1590698739270268930649229813969462244037289901369993602729790905156125979220020653769666175099424558845543378858589313645759509514238602240 : Int) coeff0891) := by
  rw [CoefficientMerge.eval_scale, ← atom0891_identity]
  exact mul_nonneg (by norm_num) (atom0891_nonneg g t z hg hA hB ht hz hw)

def coeff0892 : CoefficientMerge.Poly :=
  [(1052800, 1)]
noncomputable def atom0892 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 2 * (g 6) ^ 1 * (z) ^ 1)
theorem atom0892_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0892 g t z = CoefficientMerge.eval (monomial g t z) coeff0892 := by
  norm_num [atom0892, coeff0892, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0892_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0892 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0892]
  positivity
theorem weighted0892_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (329324680851720809124124180698473178454743722636056980868696735377257804539408218702865416972337688479034288642103057987945794038334016000 : Int) coeff0892) := by
  rw [CoefficientMerge.eval_scale, ← atom0892_identity]
  exact mul_nonneg (by norm_num) (atom0892_nonneg g t z hg hA hB ht hz hw)

def coeff0893 : CoefficientMerge.Poly :=
  [(16704, 1)]
noncomputable def atom0893 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1)
theorem atom0893_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0893 g t z = CoefficientMerge.eval (monomial g t z) coeff0893 := by
  norm_num [atom0893, coeff0893, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0893_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0893 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0893]
  positivity
theorem weighted0893_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3273092917265644430475392776550046717202846724749578687211120567144982160681339600296778306859198871692817767916549951493543327043616870400 : Int) coeff0893) := by
  rw [CoefficientMerge.eval_scale, ← atom0893_identity]
  exact mul_nonneg (by norm_num) (atom0893_nonneg g t z hg hA hB ht hz hw)

def coeff0894 : CoefficientMerge.Poly :=
  [(266560, 1)]
noncomputable def atom0894 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (t) ^ 1)
theorem atom0894_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0894 g t z = CoefficientMerge.eval (monomial g t z) coeff0894 := by
  norm_num [atom0894, coeff0894, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0894_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0894 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0894]
  positivity
theorem weighted0894_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1595742650991162577740552500167192439085882684525351882306009194475240148476083168626837498075891060971741609844044642050075459775168614400 : Int) coeff0894) := by
  rw [CoefficientMerge.eval_scale, ← atom0894_identity]
  exact mul_nonneg (by norm_num) (atom0894_nonneg g t z hg hA hB ht hz hw)

def coeff0895 : CoefficientMerge.Poly :=
  [(278848, 1)]
noncomputable def atom0895 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (t) ^ 1)
theorem atom0895_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0895 g t z = CoefficientMerge.eval (monomial g t z) coeff0895 := by
  norm_num [atom0895, coeff0895, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0895_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0895 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0895]
  positivity
theorem weighted0895_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1646399857628353241586360681443380018201173473177065309235101347712601223023839364364043441160318079549952664588590643573279181282782976000 : Int) coeff0895) := by
  rw [CoefficientMerge.eval_scale, ← atom0895_identity]
  exact mul_nonneg (by norm_num) (atom0895_nonneg g t z hg hA hB ht hz hw)

def coeff0896 : CoefficientMerge.Poly :=
  [(328000, 1)]
noncomputable def atom0896 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (t) ^ 1)
theorem atom0896_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0896 g t z = CoefficientMerge.eval (monomial g t z) coeff0896 := by
  norm_num [atom0896, coeff0896, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0896_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0896 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0896]
  positivity
theorem weighted0896_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3868468433582223374058779058844352941714664465089329094834025805487107797158207314328636127884889325937442481158299661285865667001006592000 : Int) coeff0896) := by
  rw [CoefficientMerge.eval_scale, ← atom0896_identity]
  exact mul_nonneg (by norm_num) (atom0896_nonneg g t z hg hA hB ht hz hw)

def coeff0897 : CoefficientMerge.Poly :=
  [(17472, 1)]
noncomputable def atom0897 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 5) ^ 1 * (g 7) ^ 1)
theorem atom0897_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0897 g t z = CoefficientMerge.eval (monomial g t z) coeff0897 := by
  norm_num [atom0897, coeff0897, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0897_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0897 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0897]
  positivity
theorem weighted0897_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4472708572792816744635577337001968488775611595422025514236852497517147076581629162131032503981212541036000648897241115167853745646556364800 : Int) coeff0897) := by
  rw [CoefficientMerge.eval_scale, ← atom0897_identity]
  exact mul_nonneg (by norm_num) (atom0897_nonneg g t z hg hA hB ht hz hw)

def coeff0898 : CoefficientMerge.Poly :=
  [(267328, 1)]
noncomputable def atom0898 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 5) ^ 1 * (g 6) ^ 1 * (t) ^ 1)
theorem atom0898_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0898 g t z = CoefficientMerge.eval (monomial g t z) coeff0898 := by
  norm_num [atom0898, coeff0898, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0898_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0898 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0898]
  positivity
theorem weighted0898_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (728393594105380589413174764606845901214501981648637359374531392955828117593498759015869955715405116883101477390903578342284878928296448000 : Int) coeff0898) := by
  rw [CoefficientMerge.eval_scale, ← atom0898_identity]
  exact mul_nonneg (by norm_num) (atom0898_nonneg g t z hg hA hB ht hz hw)

def coeff0899 : CoefficientMerge.Poly :=
  [(328768, 1)]
noncomputable def atom0899 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 5) ^ 1 * (g 8) ^ 1 * (t) ^ 1)
theorem atom0899_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0899 g t z = CoefficientMerge.eval (monomial g t z) coeff0899 := by
  norm_num [atom0899, coeff0899, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0899_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0899 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0899]
  positivity
theorem weighted0899_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1068094679674810927955012305893559289613032906620535189679277848088915317085667538762046956343445712368853692105379005695932358513697740800 : Int) coeff0899) := by
  rw [CoefficientMerge.eval_scale, ← atom0899_identity]
  exact mul_nonneg (by norm_num) (atom0899_nonneg g t z hg hA hB ht hz hw)

def coeff0900 : CoefficientMerge.Poly :=
  [(20544, 1)]
noncomputable def atom0900 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 6) ^ 1 * (g 7) ^ 1)
theorem atom0900_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0900 g t z = CoefficientMerge.eval (monomial g t z) coeff0900 := by
  norm_num [atom0900, coeff0900, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0900_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0900 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0900]
  positivity
theorem weighted0900_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (11095568786728271306344241424996487889396832714567921152292269203193761446932624836038605019009175609019744059307938872090500444842656768000 : Int) coeff0900) := by
  rw [CoefficientMerge.eval_scale, ← atom0900_identity]
  exact mul_nonneg (by norm_num) (atom0900_nonneg g t z hg hA hB ht hz hw)

def coeff0901 : CoefficientMerge.Poly :=
  [(69696, 1)]
noncomputable def atom0901 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1)
theorem atom0901_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0901 g t z = CoefficientMerge.eval (monomial g t z) coeff0901 := by
  norm_num [atom0901, coeff0901, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0901_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0901 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0901]
  positivity
theorem weighted0901_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (12178666767822414278803609955864812377685837443591956364426650086419471725497416560393847210868491171147925929348911860168497479806439424000 : Int) coeff0901) := by
  rw [CoefficientMerge.eval_scale, ← atom0901_identity]
  exact mul_nonneg (by norm_num) (atom0901_nonneg g t z hg hA hB ht hz hw)

def coeff0902 : CoefficientMerge.Poly :=
  [(270400, 1)]
noncomputable def atom0902 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 6) ^ 2 * (t) ^ 1)
theorem atom0902_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0902 g t z = CoefficientMerge.eval (monomial g t z) coeff0902 := by
  norm_num [atom0902, coeff0902, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0902_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0902 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0902]
  positivity
theorem weighted0902_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1208549822892032921200770340273045360906696329178976647636655981002591218791126023621239708409070775740867175279213929953928384259533721600 : Int) coeff0902) := by
  rw [CoefficientMerge.eval_scale, ← atom0902_identity]
  exact mul_nonneg (by norm_num) (atom0902_nonneg g t z hg hA hB ht hz hw)

def coeff0903 : CoefficientMerge.Poly :=
  [(331840, 1)]
noncomputable def atom0903 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 1 * (g 6) ^ 1 * (g 8) ^ 1 * (t) ^ 1)
theorem atom0903_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0903 g t z = CoefficientMerge.eval (monomial g t z) coeff0903 := by
  norm_num [atom0903, coeff0903, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0903_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0903 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0903]
  positivity
theorem weighted0903_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3623035090608854501529041313534815746834679172141905578837258895665871842380197529227556814226721392845926518082780251720860591901039462400 : Int) coeff0903) := by
  rw [CoefficientMerge.eval_scale, ← atom0903_identity]
  exact mul_nonneg (by norm_num) (atom0903_nonneg g t z hg hA hB ht hz hw)

def coeff0904 : CoefficientMerge.Poly :=
  [(525440, 1)]
noncomputable def atom0904 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 3) ^ 2 * (g 5) ^ 1 * (t) ^ 2)
theorem atom0904_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0904 g t z = CoefficientMerge.eval (monomial g t z) coeff0904 := by
  norm_num [atom0904, coeff0904, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0904_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0904 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0904]
  positivity
theorem weighted0904_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (283129310728561682553715897317590641122455492352458681392743174302699570869853715594883057786329619298672178433404267995898320175542438400 : Int) coeff0904) := by
  rw [CoefficientMerge.eval_scale, ← atom0904_identity]
  exact mul_nonneg (by norm_num) (atom0904_nonneg g t z hg hA hB ht hz hw)

def sparseBlock076 : CoefficientMerge.Poly :=
  [(16704, 3273092917265644430475392776550046717202846724749578687211120567144982160681339600296778306859198871692817767916549951493543327043616870400), (17472, 4472708572792816744635577337001968488775611595422025514236852497517147076581629162131032503981212541036000648897241115167853745646556364800), (20544, 11095568786728271306344241424996487889396832714567921152292269203193761446932624836038605019009175609019744059307938872090500444842656768000), (69696, 12178666767822414278803609955864812377685837443591956364426650086419471725497416560393847210868491171147925929348911860168497479806439424000), (266560, 1595742650991162577740552500167192439085882684525351882306009194475240148476083168626837498075891060971741609844044642050075459775168614400), (267328, 728393594105380589413174764606845901214501981648637359374531392955828117593498759015869955715405116883101477390903578342284878928296448000), (270400, 1208549822892032921200770340273045360906696329178976647636655981002591218791126023621239708409070775740867175279213929953928384259533721600), (278848, 1646399857628353241586360681443380018201173473177065309235101347712601223023839364364043441160318079549952664588590643573279181282782976000), (328000, 3868468433582223374058779058844352941714664465089329094834025805487107797158207314328636127884889325937442481158299661285865667001006592000), (328768, 1068094679674810927955012305893559289613032906620535189679277848088915317085667538762046956343445712368853692105379005695932358513697740800), (331840, 3623035090608854501529041313534815746834679172141905578837258895665871842380197529227556814226721392845926518082780251720860591901039462400), (525440, 283129310728561682553715897317590641122455492352458681392743174302699570869853715594883057786329619298672178433404267995898320175542438400), (1048960, 1590698739270268930649229813969462244037289901369993602729790905156125979220020653769666175099424558845543378858589313645759509514238602240), (1052800, 329324680851720809124124180698473178454743722636056980868696735377257804539408218702865416972337688479034288642103057987945794038334016000), (2102288, 3068397992897829570883058285016703595301038582253768067496176309943746342957342442394506811579564714835568440072913582086404580152930263040), (2105360, 884525691086052317325485231915621419385095285254577248551690955430338231995672693583331283316041129484182265464797915131558247034899292160), (2114576, 1918354807449539324393094265256836882770163932047052992416766883669568016677781951586038769731770518932276264748086606382093290837809958400), (2117648, 485301787428897675532242844937402496395295059206423252353352098826181027945604009072742978803589003705390787421824367256291397312987408640), (2163728, 1958092775708052061678139304688592463746028413358935531506371466197629948901316368529862161285328720720114196061282570289639285092851428640), (2166800, 249924797850241150306027442631729359983306430540489187656804970659636260733293926084348323943549252118284569576318123127954756066279459840)]
theorem sparseBlock076_data : sparseBlock076 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (3068397992897829570883058285016703595301038582253768067496176309943746342957342442394506811579564714835568440072913582086404580152930263040 : Int) coeff0885) (CoefficientMerge.scale (1918354807449539324393094265256836882770163932047052992416766883669568016677781951586038769731770518932276264748086606382093290837809958400 : Int) coeff0886)) (CoefficientMerge.merge (CoefficientMerge.scale (1958092775708052061678139304688592463746028413358935531506371466197629948901316368529862161285328720720114196061282570289639285092851428640 : Int) coeff0887) (CoefficientMerge.merge (CoefficientMerge.scale (884525691086052317325485231915621419385095285254577248551690955430338231995672693583331283316041129484182265464797915131558247034899292160 : Int) coeff0888) (CoefficientMerge.scale (485301787428897675532242844937402496395295059206423252353352098826181027945604009072742978803589003705390787421824367256291397312987408640 : Int) coeff0889)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (249924797850241150306027442631729359983306430540489187656804970659636260733293926084348323943549252118284569576318123127954756066279459840 : Int) coeff0890) (CoefficientMerge.scale (1590698739270268930649229813969462244037289901369993602729790905156125979220020653769666175099424558845543378858589313645759509514238602240 : Int) coeff0891)) (CoefficientMerge.merge (CoefficientMerge.scale (329324680851720809124124180698473178454743722636056980868696735377257804539408218702865416972337688479034288642103057987945794038334016000 : Int) coeff0892) (CoefficientMerge.merge (CoefficientMerge.scale (3273092917265644430475392776550046717202846724749578687211120567144982160681339600296778306859198871692817767916549951493543327043616870400 : Int) coeff0893) (CoefficientMerge.scale (1595742650991162577740552500167192439085882684525351882306009194475240148476083168626837498075891060971741609844044642050075459775168614400 : Int) coeff0894))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1646399857628353241586360681443380018201173473177065309235101347712601223023839364364043441160318079549952664588590643573279181282782976000 : Int) coeff0895) (CoefficientMerge.scale (3868468433582223374058779058844352941714664465089329094834025805487107797158207314328636127884889325937442481158299661285865667001006592000 : Int) coeff0896)) (CoefficientMerge.merge (CoefficientMerge.scale (4472708572792816744635577337001968488775611595422025514236852497517147076581629162131032503981212541036000648897241115167853745646556364800 : Int) coeff0897) (CoefficientMerge.merge (CoefficientMerge.scale (728393594105380589413174764606845901214501981648637359374531392955828117593498759015869955715405116883101477390903578342284878928296448000 : Int) coeff0898) (CoefficientMerge.scale (1068094679674810927955012305893559289613032906620535189679277848088915317085667538762046956343445712368853692105379005695932358513697740800 : Int) coeff0899)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (11095568786728271306344241424996487889396832714567921152292269203193761446932624836038605019009175609019744059307938872090500444842656768000 : Int) coeff0900) (CoefficientMerge.scale (12178666767822414278803609955864812377685837443591956364426650086419471725497416560393847210868491171147925929348911860168497479806439424000 : Int) coeff0901)) (CoefficientMerge.merge (CoefficientMerge.scale (1208549822892032921200770340273045360906696329178976647636655981002591218791126023621239708409070775740867175279213929953928384259533721600 : Int) coeff0902) (CoefficientMerge.merge (CoefficientMerge.scale (3623035090608854501529041313534815746834679172141905578837258895665871842380197529227556814226721392845926518082780251720860591901039462400 : Int) coeff0903) (CoefficientMerge.scale (283129310728561682553715897317590641122455492352458681392743174302699570869853715594883057786329619298672178433404267995898320175542438400 : Int) coeff0904)))))) := by decide +kernel
theorem sparseBlock076_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock076 := by
  rw [sparseBlock076_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted0885_nonneg g t z hg hA hB ht hz hw) (weighted0886_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0887_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0888_nonneg g t z hg hA hB ht hz hw) (weighted0889_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0890_nonneg g t z hg hA hB ht hz hw) (weighted0891_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0892_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0893_nonneg g t z hg hA hB ht hz hw) (weighted0894_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted0895_nonneg g t z hg hA hB ht hz hw) (weighted0896_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0897_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0898_nonneg g t z hg hA hB ht hz hw) (weighted0899_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0900_nonneg g t z hg hA hB ht hz hw) (weighted0901_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0902_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0903_nonneg g t z hg hA hB ht hz hw) (weighted0904_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
