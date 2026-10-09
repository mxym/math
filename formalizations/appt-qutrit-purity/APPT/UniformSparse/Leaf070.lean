import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff0765 : CoefficientMerge.Poly :=
  [(524612, 1)]
noncomputable def atom0765 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 4) ^ 1 * (t) ^ 2)
theorem atom0765_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0765 g t z = CoefficientMerge.eval (monomial g t z) coeff0765 := by
  norm_num [atom0765, coeff0765, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0765_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0765 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0765]
  positivity
theorem weighted0765_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1122031580973396099217022439308821506977199669702608006969054342996167154581636276307672014966800339750941415458826566681567568387897699840 : Int) coeff0765) := by
  rw [CoefficientMerge.eval_scale, ← atom0765_identity]
  exact mul_nonneg (by norm_num) (atom0765_nonneg g t z hg hA hB ht hz hw)

def coeff0766 : CoefficientMerge.Poly :=
  [(525380, 1)]
noncomputable def atom0766 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 5) ^ 1 * (t) ^ 2)
theorem atom0766_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0766 g t z = CoefficientMerge.eval (monomial g t z) coeff0766 := by
  norm_num [atom0766, coeff0766, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0766_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0766 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0766]
  positivity
theorem weighted0766_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3248538881447742412754246876280977324319607204950283968330781690736717175039605830730822024790045771377541554484837147836136163301995315200 : Int) coeff0766) := by
  rw [CoefficientMerge.eval_scale, ← atom0766_identity]
  exact mul_nonneg (by norm_num) (atom0766_nonneg g t z hg hA hB ht hz hw)

def coeff0767 : CoefficientMerge.Poly :=
  [(528452, 1)]
noncomputable def atom0767 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 6) ^ 1 * (t) ^ 2)
theorem atom0767_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0767 g t z = CoefficientMerge.eval (monomial g t z) coeff0767 := by
  norm_num [atom0767, coeff0767, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0767_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0767 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0767]
  positivity
theorem weighted0767_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2698786099839228758739186999429692442461932617764093697615550855904748097293801413775185177379682337112541073579202238976648888833754572800 : Int) coeff0767) := by
  rw [CoefficientMerge.eval_scale, ← atom0767_identity]
  exact mul_nonneg (by norm_num) (atom0767_nonneg g t z hg hA hB ht hz hw)

def coeff0768 : CoefficientMerge.Poly :=
  [(540740, 1)]
noncomputable def atom0768 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 7) ^ 1 * (t) ^ 2)
theorem atom0768_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0768 g t z = CoefficientMerge.eval (monomial g t z) coeff0768 := by
  norm_num [atom0768, coeff0768, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0768_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0768 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0768]
  positivity
theorem weighted0768_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1652578282059319982188675410668247697743391303583480745153335295489439040493672406248830615010632267035694190899104836333634386285828771840 : Int) coeff0768) := by
  rw [CoefficientMerge.eval_scale, ← atom0768_identity]
  exact mul_nonneg (by norm_num) (atom0768_nonneg g t z hg hA hB ht hz hw)

def coeff0769 : CoefficientMerge.Poly :=
  [(589892, 1)]
noncomputable def atom0769 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 8) ^ 1 * (t) ^ 2)
theorem atom0769_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0769 g t z = CoefficientMerge.eval (monomial g t z) coeff0769 := by
  norm_num [atom0769, coeff0769, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0769_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0769 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0769]
  positivity
theorem weighted0769_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2019178545070688611752363091016364717850656664589263736534098263353006112392056846938945388703103829995652157808816724904170995516723609600 : Int) coeff0769) := by
  rw [CoefficientMerge.eval_scale, ← atom0769_identity]
  exact mul_nonneg (by norm_num) (atom0769_nonneg g t z hg hA hB ht hz hw)

def coeff0770 : CoefficientMerge.Poly :=
  [(1310852, 1)]
noncomputable def atom0770 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 2 * (t) ^ 1 * (z) ^ 1)
theorem atom0770_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0770 g t z = CoefficientMerge.eval (monomial g t z) coeff0770 := by
  norm_num [atom0770, coeff0770, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0770_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0770 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0770]
  positivity
theorem weighted0770_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2038797330683524834678844033914376222521549872221783682798854690366742163511529218655437051969661242515676679037335239633188561960335376896 : Int) coeff0770) := by
  rw [CoefficientMerge.eval_scale, ← atom0770_identity]
  exact mul_nonneg (by norm_num) (atom0770_nonneg g t z hg hA hB ht hz hw)

def coeff0771 : CoefficientMerge.Poly :=
  [(1311044, 1)]
noncomputable def atom0771 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 4) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0771_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0771 g t z = CoefficientMerge.eval (monomial g t z) coeff0771 := by
  norm_num [atom0771, coeff0771, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0771_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0771 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0771]
  positivity
theorem weighted0771_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2917257510955992398987787476343499040026568756409246954290009950481265694698656791358571928685128587695044400850022516993175740979255962752 : Int) coeff0771) := by
  rw [CoefficientMerge.eval_scale, ← atom0771_identity]
  exact mul_nonneg (by norm_num) (atom0771_nonneg g t z hg hA hB ht hz hw)

def coeff0772 : CoefficientMerge.Poly :=
  [(1311812, 1)]
noncomputable def atom0772 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 5) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0772_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0772 g t z = CoefficientMerge.eval (monomial g t z) coeff0772 := by
  norm_num [atom0772, coeff0772, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0772_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0772 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0772]
  positivity
theorem weighted0772_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (6563043423686394299501721673119025902803932286009262716263913860544566548044284265493462425844344091857030483184550342534562527212424176384 : Int) coeff0772) := by
  rw [CoefficientMerge.eval_scale, ← atom0772_identity]
  exact mul_nonneg (by norm_num) (atom0772_nonneg g t z hg hA hB ht hz hw)

def coeff0773 : CoefficientMerge.Poly :=
  [(1314884, 1)]
noncomputable def atom0773 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0773_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0773 g t z = CoefficientMerge.eval (monomial g t z) coeff0773 := by
  norm_num [atom0773, coeff0773, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0773_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0773 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0773]
  positivity
theorem weighted0773_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5604543290240455892860260982516776761221804900972502772789461827058860200139446616199786068339322897849852560565703804120617776132632088320 : Int) coeff0773) := by
  rw [CoefficientMerge.eval_scale, ← atom0773_identity]
  exact mul_nonneg (by norm_num) (atom0773_nonneg g t z hg hA hB ht hz hw)

def coeff0774 : CoefficientMerge.Poly :=
  [(1327172, 1)]
noncomputable def atom0774 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0774_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0774 g t z = CoefficientMerge.eval (monomial g t z) coeff0774 := by
  norm_num [atom0774, coeff0774, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0774_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0774 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0774]
  positivity
theorem weighted0774_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3315649625204986866902207861839271571216119417106288570252500436052167176117007202600269993767269766672068219192209113373768357174292657920 : Int) coeff0774) := by
  rw [CoefficientMerge.eval_scale, ← atom0774_identity]
  exact mul_nonneg (by norm_num) (atom0774_nonneg g t z hg hA hB ht hz hw)

def coeff0775 : CoefficientMerge.Poly :=
  [(1376324, 1)]
noncomputable def atom0775 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 3) ^ 1 * (g 8) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0775_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0775 g t z = CoefficientMerge.eval (monomial g t z) coeff0775 := by
  norm_num [atom0775, coeff0775, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0775_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0775 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0775]
  positivity
theorem weighted0775_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3949260550909911439858339232695921781118966022438217975627728719519758088535368591086871440386684535178794660546678782697426183207569785600 : Int) coeff0775) := by
  rw [CoefficientMerge.eval_scale, ← atom0775_identity]
  exact mul_nonneg (by norm_num) (atom0775_nonneg g t z hg hA hB ht hz hw)

def coeff0776 : CoefficientMerge.Poly :=
  [(524804, 1)]
noncomputable def atom0776 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 2 * (t) ^ 2)
theorem atom0776_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0776 g t z = CoefficientMerge.eval (monomial g t z) coeff0776 := by
  norm_num [atom0776, coeff0776, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0776_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0776 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0776]
  positivity
theorem weighted0776_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (535073388316484760415667299271518603848599142225102319033602514529265661114025894506541031467085767187540081150336944332964013432605491200 : Int) coeff0776) := by
  rw [CoefficientMerge.eval_scale, ← atom0776_identity]
  exact mul_nonneg (by norm_num) (atom0776_nonneg g t z hg hA hB ht hz hw)

def coeff0777 : CoefficientMerge.Poly :=
  [(525572, 1)]
noncomputable def atom0777 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 5) ^ 1 * (t) ^ 2)
theorem atom0777_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0777 g t z = CoefficientMerge.eval (monomial g t z) coeff0777 := by
  norm_num [atom0777, coeff0777, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0777_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0777 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0777]
  positivity
theorem weighted0777_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2458734620227596442115065873560314051149775588642568028703000371017071095003935242907274330705246590010351853469497125943646473381285068800 : Int) coeff0777) := by
  rw [CoefficientMerge.eval_scale, ← atom0777_identity]
  exact mul_nonneg (by norm_num) (atom0777_nonneg g t z hg hA hB ht hz hw)

def coeff0778 : CoefficientMerge.Poly :=
  [(528644, 1)]
noncomputable def atom0778 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (t) ^ 2)
theorem atom0778_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0778 g t z = CoefficientMerge.eval (monomial g t z) coeff0778 := by
  norm_num [atom0778, coeff0778, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0778_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0778 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0778]
  positivity
theorem weighted0778_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2215767830434279877300942611783312211353098564979609544821734412300474381393381766902414678568967946547935950804606721970508177791199129600 : Int) coeff0778) := by
  rw [CoefficientMerge.eval_scale, ← atom0778_identity]
  exact mul_nonneg (by norm_num) (atom0778_nonneg g t z hg hA hB ht hz hw)

def coeff0779 : CoefficientMerge.Poly :=
  [(540932, 1)]
noncomputable def atom0779 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (t) ^ 2)
theorem atom0779_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0779 g t z = CoefficientMerge.eval (monomial g t z) coeff0779 := by
  norm_num [atom0779, coeff0779, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0779_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0779 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0779]
  positivity
theorem weighted0779_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1555550518434332124973739326368079081747411189410396095554790124918121626839733047902313511584578404034642389825686620690174686809218682880 : Int) coeff0779) := by
  rw [CoefficientMerge.eval_scale, ← atom0779_identity]
  exact mul_nonneg (by norm_num) (atom0779_nonneg g t z hg hA hB ht hz hw)

def coeff0780 : CoefficientMerge.Poly :=
  [(590084, 1)]
noncomputable def atom0780 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 8) ^ 1 * (t) ^ 2)
theorem atom0780_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0780 g t z = CoefficientMerge.eval (monomial g t z) coeff0780 := by
  norm_num [atom0780, coeff0780, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0780_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0780 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0780]
  positivity
theorem weighted0780_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1297290034915231206374297999509841673619212497697922241746586472640946676250346065997634491808885135694409318795433318638938346764658073600 : Int) coeff0780) := by
  rw [CoefficientMerge.eval_scale, ← atom0780_identity]
  exact mul_nonneg (by norm_num) (atom0780_nonneg g t z hg hA hB ht hz hw)

def coeff0781 : CoefficientMerge.Poly :=
  [(1311236, 1)]
noncomputable def atom0781 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 2 * (t) ^ 1 * (z) ^ 1)
theorem atom0781_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0781 g t z = CoefficientMerge.eval (monomial g t z) coeff0781 := by
  norm_num [atom0781, coeff0781, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0781_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0781 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0781]
  positivity
theorem weighted0781_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (646069264673999695367497441085373548063344601464227169284529449655536627159204008798660527148461502353834182730385712367655179251480015360 : Int) coeff0781) := by
  rw [CoefficientMerge.eval_scale, ← atom0781_identity]
  exact mul_nonneg (by norm_num) (atom0781_nonneg g t z hg hA hB ht hz hw)

def coeff0782 : CoefficientMerge.Poly :=
  [(1312004, 1)]
noncomputable def atom0782 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 5) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0782_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0782 g t z = CoefficientMerge.eval (monomial g t z) coeff0782 := by
  norm_num [atom0782, coeff0782, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0782_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0782 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0782]
  positivity
theorem weighted0782_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (4323400932357339939408465429591310535943985593004563509165871895378792436177271445496990185247382932571038562113302323413863507608731271168 : Int) coeff0782) := by
  rw [CoefficientMerge.eval_scale, ← atom0782_identity]
  exact mul_nonneg (by norm_num) (atom0782_nonneg g t z hg hA hB ht hz hw)

def coeff0783 : CoefficientMerge.Poly :=
  [(1315076, 1)]
noncomputable def atom0783 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 6) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0783_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0783 g t z = CoefficientMerge.eval (monomial g t z) coeff0783 := by
  norm_num [atom0783, coeff0783, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0783_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0783 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0783]
  positivity
theorem weighted0783_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (3994118778565417257216813076093880219288048921904750050886257249048344814878145181246404073481498098357824488370488220462351906296328736000 : Int) coeff0783) := by
  rw [CoefficientMerge.eval_scale, ← atom0783_identity]
  exact mul_nonneg (by norm_num) (atom0783_nonneg g t z hg hA hB ht hz hw)

def coeff0784 : CoefficientMerge.Poly :=
  [(1327364, 1)]
noncomputable def atom0784 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := ((g 1) ^ 1 * (g 4) ^ 1 * (g 7) ^ 1 * (t) ^ 1 * (z) ^ 1)
theorem atom0784_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0784 g t z = CoefficientMerge.eval (monomial g t z) coeff0784 := by
  norm_num [atom0784, coeff0784, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0784_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0784 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0784]
  positivity
theorem weighted0784_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (2190742707254693465750411034640760897017578058122934595615313164731011399722089257842163079551903460393068725829966977127296303797685975040 : Int) coeff0784) := by
  rw [CoefficientMerge.eval_scale, ← atom0784_identity]
  exact mul_nonneg (by norm_num) (atom0784_nonneg g t z hg hA hB ht hz hw)

def sparseBlock070 : CoefficientMerge.Poly :=
  [(524612, 1122031580973396099217022439308821506977199669702608006969054342996167154581636276307672014966800339750941415458826566681567568387897699840), (524804, 535073388316484760415667299271518603848599142225102319033602514529265661114025894506541031467085767187540081150336944332964013432605491200), (525380, 3248538881447742412754246876280977324319607204950283968330781690736717175039605830730822024790045771377541554484837147836136163301995315200), (525572, 2458734620227596442115065873560314051149775588642568028703000371017071095003935242907274330705246590010351853469497125943646473381285068800), (528452, 2698786099839228758739186999429692442461932617764093697615550855904748097293801413775185177379682337112541073579202238976648888833754572800), (528644, 2215767830434279877300942611783312211353098564979609544821734412300474381393381766902414678568967946547935950804606721970508177791199129600), (540740, 1652578282059319982188675410668247697743391303583480745153335295489439040493672406248830615010632267035694190899104836333634386285828771840), (540932, 1555550518434332124973739326368079081747411189410396095554790124918121626839733047902313511584578404034642389825686620690174686809218682880), (589892, 2019178545070688611752363091016364717850656664589263736534098263353006112392056846938945388703103829995652157808816724904170995516723609600), (590084, 1297290034915231206374297999509841673619212497697922241746586472640946676250346065997634491808885135694409318795433318638938346764658073600), (1310852, 2038797330683524834678844033914376222521549872221783682798854690366742163511529218655437051969661242515676679037335239633188561960335376896), (1311044, 2917257510955992398987787476343499040026568756409246954290009950481265694698656791358571928685128587695044400850022516993175740979255962752), (1311236, 646069264673999695367497441085373548063344601464227169284529449655536627159204008798660527148461502353834182730385712367655179251480015360), (1311812, 6563043423686394299501721673119025902803932286009262716263913860544566548044284265493462425844344091857030483184550342534562527212424176384), (1312004, 4323400932357339939408465429591310535943985593004563509165871895378792436177271445496990185247382932571038562113302323413863507608731271168), (1314884, 5604543290240455892860260982516776761221804900972502772789461827058860200139446616199786068339322897849852560565703804120617776132632088320), (1315076, 3994118778565417257216813076093880219288048921904750050886257249048344814878145181246404073481498098357824488370488220462351906296328736000), (1327172, 3315649625204986866902207861839271571216119417106288570252500436052167176117007202600269993767269766672068219192209113373768357174292657920), (1327364, 2190742707254693465750411034640760897017578058122934595615313164731011399722089257842163079551903460393068725829966977127296303797685975040), (1376324, 3949260550909911439858339232695921781118966022438217975627728719519758088535368591086871440386684535178794660546678782697426183207569785600)]
theorem sparseBlock070_data : sparseBlock070 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1122031580973396099217022439308821506977199669702608006969054342996167154581636276307672014966800339750941415458826566681567568387897699840 : Int) coeff0765) (CoefficientMerge.scale (3248538881447742412754246876280977324319607204950283968330781690736717175039605830730822024790045771377541554484837147836136163301995315200 : Int) coeff0766)) (CoefficientMerge.merge (CoefficientMerge.scale (2698786099839228758739186999429692442461932617764093697615550855904748097293801413775185177379682337112541073579202238976648888833754572800 : Int) coeff0767) (CoefficientMerge.merge (CoefficientMerge.scale (1652578282059319982188675410668247697743391303583480745153335295489439040493672406248830615010632267035694190899104836333634386285828771840 : Int) coeff0768) (CoefficientMerge.scale (2019178545070688611752363091016364717850656664589263736534098263353006112392056846938945388703103829995652157808816724904170995516723609600 : Int) coeff0769)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (2038797330683524834678844033914376222521549872221783682798854690366742163511529218655437051969661242515676679037335239633188561960335376896 : Int) coeff0770) (CoefficientMerge.scale (2917257510955992398987787476343499040026568756409246954290009950481265694698656791358571928685128587695044400850022516993175740979255962752 : Int) coeff0771)) (CoefficientMerge.merge (CoefficientMerge.scale (6563043423686394299501721673119025902803932286009262716263913860544566548044284265493462425844344091857030483184550342534562527212424176384 : Int) coeff0772) (CoefficientMerge.merge (CoefficientMerge.scale (5604543290240455892860260982516776761221804900972502772789461827058860200139446616199786068339322897849852560565703804120617776132632088320 : Int) coeff0773) (CoefficientMerge.scale (3315649625204986866902207861839271571216119417106288570252500436052167176117007202600269993767269766672068219192209113373768357174292657920 : Int) coeff0774))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (3949260550909911439858339232695921781118966022438217975627728719519758088535368591086871440386684535178794660546678782697426183207569785600 : Int) coeff0775) (CoefficientMerge.scale (535073388316484760415667299271518603848599142225102319033602514529265661114025894506541031467085767187540081150336944332964013432605491200 : Int) coeff0776)) (CoefficientMerge.merge (CoefficientMerge.scale (2458734620227596442115065873560314051149775588642568028703000371017071095003935242907274330705246590010351853469497125943646473381285068800 : Int) coeff0777) (CoefficientMerge.merge (CoefficientMerge.scale (2215767830434279877300942611783312211353098564979609544821734412300474381393381766902414678568967946547935950804606721970508177791199129600 : Int) coeff0778) (CoefficientMerge.scale (1555550518434332124973739326368079081747411189410396095554790124918121626839733047902313511584578404034642389825686620690174686809218682880 : Int) coeff0779)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1297290034915231206374297999509841673619212497697922241746586472640946676250346065997634491808885135694409318795433318638938346764658073600 : Int) coeff0780) (CoefficientMerge.scale (646069264673999695367497441085373548063344601464227169284529449655536627159204008798660527148461502353834182730385712367655179251480015360 : Int) coeff0781)) (CoefficientMerge.merge (CoefficientMerge.scale (4323400932357339939408465429591310535943985593004563509165871895378792436177271445496990185247382932571038562113302323413863507608731271168 : Int) coeff0782) (CoefficientMerge.merge (CoefficientMerge.scale (3994118778565417257216813076093880219288048921904750050886257249048344814878145181246404073481498098357824488370488220462351906296328736000 : Int) coeff0783) (CoefficientMerge.scale (2190742707254693465750411034640760897017578058122934595615313164731011399722089257842163079551903460393068725829966977127296303797685975040 : Int) coeff0784)))))) := by decide +kernel
theorem sparseBlock070_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock070 := by
  rw [sparseBlock070_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted0765_nonneg g t z hg hA hB ht hz hw) (weighted0766_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0767_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0768_nonneg g t z hg hA hB ht hz hw) (weighted0769_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0770_nonneg g t z hg hA hB ht hz hw) (weighted0771_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0772_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0773_nonneg g t z hg hA hB ht hz hw) (weighted0774_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted0775_nonneg g t z hg hA hB ht hz hw) (weighted0776_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0777_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0778_nonneg g t z hg hA hB ht hz hw) (weighted0779_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0780_nonneg g t z hg hA hB ht hz hw) (weighted0781_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0782_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0783_nonneg g t z hg hA hB ht hz hw) (weighted0784_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
