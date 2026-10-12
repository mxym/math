import APPT.UniformSparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
namespace APPT.Uniform
open CoefficientMerge

def coeff0020 : CoefficientMerge.Poly :=
  [(1049602, 324), (1311746, -36), (1573890, 1), (2098178, -36), (2360322, 2), (3146754, 1)]
noncomputable def atom0020 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 0) * (g 0) * (g 5)) * z * (t+z-18) * (t+z-18))
theorem atom0020_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0020 g t z = CoefficientMerge.eval (monomial g t z) coeff0020 := by
  norm_num [atom0020, coeff0020, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0020_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0020 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0020]
  positivity
theorem weighted0020_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1129727369895011130951301616497577280282555624233907122132568031410243963237151734307538345717539444579747350398214842266530095185827840 : Int) coeff0020) := by
  rw [CoefficientMerge.eval_scale, ← atom0020_identity]
  exact mul_nonneg (by norm_num) (atom0020_nonneg g t z hg hA hB ht hz hw)

def coeff0021 : CoefficientMerge.Poly :=
  [(528386, -18), (790530, 1), (1576962, 1)]
noncomputable def atom0021 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 0) * (g 0) * (g 6)) * t * t * (t+z-18))
theorem atom0021_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0021 g t z = CoefficientMerge.eval (monomial g t z) coeff0021 := by
  norm_num [atom0021, coeff0021, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0021_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0021 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0021]
  positivity
theorem weighted0021_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (10594653778953300987085846697625334340001721853696000395818190882874669215826763092970376310990705853472376240012986276003645248307200 : Int) coeff0021) := by
  rw [CoefficientMerge.eval_scale, ← atom0021_identity]
  exact mul_nonneg (by norm_num) (atom0021_nonneg g t z hg hA hB ht hz hw)

def coeff0022 : CoefficientMerge.Poly :=
  [(266242, 324), (528386, -36), (790530, 1), (1314818, -36), (1576962, 2), (2363394, 1)]
noncomputable def atom0022 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 0) * (g 0) * (g 6)) * t * (t+z-18) * (t+z-18))
theorem atom0022_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0022 g t z = CoefficientMerge.eval (monomial g t z) coeff0022 := by
  norm_num [atom0022, coeff0022, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0022_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0022 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0022]
  positivity
theorem weighted0022_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (881790050131848336544387224228724141615687856583156731385584977675258652402031909645368336289005379676999368584637442618121617073971200 : Int) coeff0022) := by
  rw [CoefficientMerge.eval_scale, ← atom0022_identity]
  exact mul_nonneg (by norm_num) (atom0022_nonneg g t z hg hA hB ht hz hw)

def coeff0023 : CoefficientMerge.Poly :=
  [(1052674, 324), (1314818, -36), (1576962, 1), (2101250, -36), (2363394, 2), (3149826, 1)]
noncomputable def atom0023 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 0) * (g 0) * (g 6)) * z * (t+z-18) * (t+z-18))
theorem atom0023_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0023 g t z = CoefficientMerge.eval (monomial g t z) coeff0023 := by
  norm_num [atom0023, coeff0023, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0023_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0023 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0023]
  positivity
theorem weighted0023_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (663967110469998579438377765289540094534601988997327438026330791664230101838928162707309679478872824373556997315131187168662431192268800 : Int) coeff0023) := by
  rw [CoefficientMerge.eval_scale, ← atom0023_identity]
  exact mul_nonneg (by norm_num) (atom0023_nonneg g t z hg hA hB ht hz hw)

def coeff0024 : CoefficientMerge.Poly :=
  [(524297, -18), (786441, 1), (1572873, 1)]
noncomputable def atom0024 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 0) * (g 1) * (g 1)) * t * t * (t+z-18))
theorem atom0024_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0024 g t z = CoefficientMerge.eval (monomial g t z) coeff0024 := by
  norm_num [atom0024, coeff0024, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0024_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0024 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0024]
  positivity
theorem weighted0024_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5356964125851331445717546847527450187285639516233373856300095446595727811802061447586439930224803335388880705454904191550539690671923200 : Int) coeff0024) := by
  rw [CoefficientMerge.eval_scale, ← atom0024_identity]
  exact mul_nonneg (by norm_num) (atom0024_nonneg g t z hg hA hB ht hz hw)

def coeff0025 : CoefficientMerge.Poly :=
  [(1310729, -18), (1572873, 1), (2359305, 1)]
noncomputable def atom0025 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 0) * (g 1) * (g 1)) * t * z * (t+z-18))
theorem atom0025_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0025 g t z = CoefficientMerge.eval (monomial g t z) coeff0025 := by
  norm_num [atom0025, coeff0025, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0025_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0025 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0025]
  positivity
theorem weighted0025_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (10792533162964085990117481654297925028828727337809192112021162714964969583451613335773312096174215590201315895181700987490851293506734080 : Int) coeff0025) := by
  rw [CoefficientMerge.eval_scale, ← atom0025_identity]
  exact mul_nonneg (by norm_num) (atom0025_nonneg g t z hg hA hB ht hz hw)

def coeff0026 : CoefficientMerge.Poly :=
  [(2097161, -18), (2359305, 1), (3145737, 1)]
noncomputable def atom0026 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 0) * (g 1) * (g 1)) * z * z * (t+z-18))
theorem atom0026_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0026 g t z = CoefficientMerge.eval (monomial g t z) coeff0026 := by
  norm_num [atom0026, coeff0026, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0026_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0026 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0026]
  positivity
theorem weighted0026_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5410549875842388007085344429202507643968430372272626054623489111729619103730478367858953307376758989964931321430754586459386017987829760 : Int) coeff0026) := by
  rw [CoefficientMerge.eval_scale, ← atom0026_identity]
  exact mul_nonneg (by norm_num) (atom0026_nonneg g t z hg hA hB ht hz hw)

def coeff0027 : CoefficientMerge.Poly :=
  [(21, -5832), (262165, 972), (524309, -54), (786453, 1), (1048597, 972), (1310741, -108), (1572885, 3), (2097173, -54), (2359317, 3), (3145749, 1)]
noncomputable def atom0027 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 0) * (g 1) * (g 2)) * (t+z-18) * (t+z-18) * (t+z-18))
theorem atom0027_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0027 g t z = CoefficientMerge.eval (monomial g t z) coeff0027 := by
  norm_num [atom0027, coeff0027, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0027_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0027 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0027]
  positivity
theorem weighted0027_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1403703875780069880687818258396795826065953599385919532614113298019766522184531622414988782996060239173399701390387065487034994099650560 : Int) coeff0027) := by
  rw [CoefficientMerge.eval_scale, ← atom0027_identity]
  exact mul_nonneg (by norm_num) (atom0027_nonneg g t z hg hA hB ht hz hw)

def coeff0028 : CoefficientMerge.Poly :=
  [(540677, -18), (802821, 1), (1589253, 1)]
noncomputable def atom0028 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 0) * (g 1) * (g 7)) * t * t * (t+z-18))
theorem atom0028_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0028 g t z = CoefficientMerge.eval (monomial g t z) coeff0028 := by
  norm_num [atom0028, coeff0028, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0028_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0028 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0028]
  positivity
theorem weighted0028_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (325370580740952842316129758696622209964832671476002429528659348975258938097791247124513330654877876825554440605774877180948975384268800 : Int) coeff0028) := by
  rw [CoefficientMerge.eval_scale, ← atom0028_identity]
  exact mul_nonneg (by norm_num) (atom0028_nonneg g t z hg hA hB ht hz hw)

def coeff0029 : CoefficientMerge.Poly :=
  [(1327109, -18), (1589253, 1), (2375685, 1)]
noncomputable def atom0029 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 0) * (g 1) * (g 7)) * t * z * (t+z-18))
theorem atom0029_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0029 g t z = CoefficientMerge.eval (monomial g t z) coeff0029 := by
  norm_num [atom0029, coeff0029, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0029_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0029 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0029]
  positivity
theorem weighted0029_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (843272461549944565133437301936462832816999747442714807960172506515377789482299098052152597317565134012071686807683092467670777246336000 : Int) coeff0029) := by
  rw [CoefficientMerge.eval_scale, ← atom0029_identity]
  exact mul_nonneg (by norm_num) (atom0029_nonneg g t z hg hA hB ht hz hw)

def coeff0030 : CoefficientMerge.Poly :=
  [(2113541, -18), (2375685, 1), (3162117, 1)]
noncomputable def atom0030 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 0) * (g 1) * (g 7)) * z * z * (t+z-18))
theorem atom0030_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0030 g t z = CoefficientMerge.eval (monomial g t z) coeff0030 := by
  norm_num [atom0030, coeff0030, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0030_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0030 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0030]
  positivity
theorem weighted0030_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (294985892434848171435808475937461081420026186518517476216359221094358095454401681194234147286948934842817916150566772985042844596736000 : Int) coeff0030) := by
  rw [CoefficientMerge.eval_scale, ← atom0030_identity]
  exact mul_nonneg (by norm_num) (atom0030_nonneg g t z hg hA hB ht hz hw)

def coeff0031 : CoefficientMerge.Poly :=
  [(16389, -5832), (278533, 972), (540677, -54), (802821, 1), (1064965, 972), (1327109, -108), (1589253, 3), (2113541, -54), (2375685, 3), (3162117, 1)]
noncomputable def atom0031 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 0) * (g 1) * (g 7)) * (t+z-18) * (t+z-18) * (t+z-18))
theorem atom0031_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0031 g t z = CoefficientMerge.eval (monomial g t z) coeff0031 := by
  norm_num [atom0031, coeff0031, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0031_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0031 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0031]
  positivity
theorem weighted0031_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (152716630222114341711049470296458400848733405123201515972655985674179887843265578586407518431929126499954010345409540344708226346368000 : Int) coeff0031) := by
  rw [CoefficientMerge.eval_scale, ← atom0031_identity]
  exact mul_nonneg (by norm_num) (atom0031_nonneg g t z hg hA hB ht hz hw)

def coeff0032 : CoefficientMerge.Poly :=
  [(524300, -18), (786444, 1), (1572876, 1)]
noncomputable def atom0032 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 1) * (g 1) * (g 1)) * t * t * (t+z-18))
theorem atom0032_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0032 g t z = CoefficientMerge.eval (monomial g t z) coeff0032 := by
  norm_num [atom0032, coeff0032, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0032_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0032 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0032]
  positivity
theorem weighted0032_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5429898824129880242964580905684561791658431037939445139425350958807312062692909433001271090786223553409275582420717635047795959792435200 : Int) coeff0032) := by
  rw [CoefficientMerge.eval_scale, ← atom0032_identity]
  exact mul_nonneg (by norm_num) (atom0032_nonneg g t z hg hA hB ht hz hw)

def coeff0033 : CoefficientMerge.Poly :=
  [(1310732, -18), (1572876, 1), (2359308, 1)]
noncomputable def atom0033 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 1) * (g 1) * (g 1)) * t * z * (t+z-18))
theorem atom0033_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0033 g t z = CoefficientMerge.eval (monomial g t z) coeff0033 := by
  norm_num [atom0033, coeff0033, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0033_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0033 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0033]
  positivity
theorem weighted0033_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (10859797648259760485929161811369123583316862075878890278850701917614624125385818866002542181572447106818551164841435270095591919584870400 : Int) coeff0033) := by
  rw [CoefficientMerge.eval_scale, ← atom0033_identity]
  exact mul_nonneg (by norm_num) (atom0033_nonneg g t z hg hA hB ht hz hw)

def coeff0034 : CoefficientMerge.Poly :=
  [(2097164, -18), (2359308, 1), (3145740, 1)]
noncomputable def atom0034 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 1) * (g 1) * (g 1)) * z * z * (t+z-18))
theorem atom0034_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0034 g t z = CoefficientMerge.eval (monomial g t z) coeff0034 := by
  norm_num [atom0034, coeff0034, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0034_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0034 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0034]
  positivity
theorem weighted0034_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (5429898824129880242964580905684561791658431037939445139425350958807312062692909433001271090786223553409275582420717635047795959792435200 : Int) coeff0034) := by
  rw [CoefficientMerge.eval_scale, ← atom0034_identity]
  exact mul_nonneg (by norm_num) (atom0034_nonneg g t z hg hA hB ht hz hw)

def coeff0035 : CoefficientMerge.Poly :=
  [(524312, -18), (786456, 1), (1572888, 1)]
noncomputable def atom0035 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 1) * (g 1) * (g 2)) * t * t * (t+z-18))
theorem atom0035_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0035 g t z = CoefficientMerge.eval (monomial g t z) coeff0035 := by
  norm_num [atom0035, coeff0035, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0035_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0035 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0035]
  positivity
theorem weighted0035_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (28541843147012745699119035363857595897512270560181903862093329948349993676763777533302661129071241977687128802337852299902863483993548800 : Int) coeff0035) := by
  rw [CoefficientMerge.eval_scale, ← atom0035_identity]
  exact mul_nonneg (by norm_num) (atom0035_nonneg g t z hg hA hB ht hz hw)

def coeff0036 : CoefficientMerge.Poly :=
  [(1310744, -18), (1572888, 1), (2359320, 1)]
noncomputable def atom0036 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 1) * (g 1) * (g 2)) * t * z * (t+z-18))
theorem atom0036_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0036 g t z = CoefficientMerge.eval (monomial g t z) coeff0036 := by
  norm_num [atom0036, coeff0036, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0036_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0036 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0036]
  positivity
theorem weighted0036_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (17935523060239800983752740687163109396277984298286935435462008298179213843839316710772669785649905541432157044418050486969779441265454080 : Int) coeff0036) := by
  rw [CoefficientMerge.eval_scale, ← atom0036_identity]
  exact mul_nonneg (by norm_num) (atom0036_nonneg g t z hg hA hB ht hz hw)

def coeff0037 : CoefficientMerge.Poly :=
  [(2097176, -18), (2359320, 1), (3145752, 1)]
noncomputable def atom0037 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 1) * (g 1) * (g 2)) * z * z * (t+z-18))
theorem atom0037_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0037 g t z = CoefficientMerge.eval (monomial g t z) coeff0037 := by
  norm_num [atom0037, coeff0037, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0037_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0037 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0037]
  positivity
theorem weighted0037_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (8992916463247131469087257537455123313412077327060593653604883581366362259998104066413006843929301032975695988784281820604577348204339200 : Int) coeff0037) := by
  rw [CoefficientMerge.eval_scale, ← atom0037_identity]
  exact mul_nonneg (by norm_num) (atom0037_nonneg g t z hg hA hB ht hz hw)

def coeff0038 : CoefficientMerge.Poly :=
  [(24, -5832), (262168, 972), (524312, -54), (786456, 1), (1048600, 972), (1310744, -108), (1572888, 3), (2097176, -54), (2359320, 3), (3145752, 1)]
noncomputable def atom0038 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 1) * (g 1) * (g 2)) * (t+z-18) * (t+z-18) * (t+z-18))
theorem atom0038_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0038 g t z = CoefficientMerge.eval (monomial g t z) coeff0038 := by
  norm_num [atom0038, coeff0038, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0038_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0038 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0038]
  positivity
theorem weighted0038_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1302052203843392463068906960450503954525310553082920034076821713521034086020222453164931688092179850331193674232483737064398444622950400 : Int) coeff0038) := by
  rw [CoefficientMerge.eval_scale, ← atom0038_identity]
  exact mul_nonneg (by norm_num) (atom0038_nonneg g t z hg hA hB ht hz hw)

def coeff0039 : CoefficientMerge.Poly :=
  [(262216, 324), (524360, -36), (786504, 1), (1310792, -36), (1572936, 2), (2359368, 1)]
noncomputable def atom0039 (g : Fin 9 → ℝ) (t z : ℝ) : ℝ := (((g 1) * (g 1) * (g 3)) * t * (t+z-18) * (t+z-18))
theorem atom0039_identity (g : Fin 9 → ℝ) (t z : ℝ) : atom0039 g t z = CoefficientMerge.eval (monomial g t z) coeff0039 := by
  norm_num [atom0039, coeff0039, CoefficientMerge.eval, monomial, total, squareTotal, outer, spectrum, detA, detB, minorA, minorB, quadA, quadB, ratio, matA, matB, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mix, score]
  <;> ring
theorem atom0039_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ atom0039 g t z := by
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  dsimp only [atom0039]
  positivity
theorem weighted0039_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) (CoefficientMerge.scale (1027856993045772449727579351157927060618844577867794386838948182068783547657186169847318101949421529568255085463702589883248894688358400 : Int) coeff0039) := by
  rw [CoefficientMerge.eval_scale, ← atom0039_identity]
  exact mul_nonneg (by norm_num) (atom0039_nonneg g t z hg hA hB ht hz hw)

def sparseBlock001 : CoefficientMerge.Poly :=
  [(21, -8186401003549367544171356082970113257616641391618682714205508754051278357380188421924214582433023314859267058508737365920388085589162065920), (24, -7593568452814664844617865393347339062791611145579589638736024233254670789669937346857881604953592887131521508123845154559571729041046732800), (16389, -890643387455370840858840510768945393749813218678511241152529708451817105901924854315928647495010665747731788334428439290338376052018176000), (262165, 1364400167258227924028559347161685542936106898603113785700918125675213059563364736987369097072170552476544509751456227653398014264860344320), (262168, 1265594742135777474102977565557889843798601857596598273122670705542445131611656224476313600825598814521920251353974192426595288173507788800), (262216, 333025665746830273711735709775168367640505643229165381335819210990285869440928319030531065031612575580114647690239639122172641879028121600), (266242, 285699976242718861040381460650106621883482865532942780968929532766783803378258338725099340957637743015347795421422531408271403931966668800), (278533, 148440564575895140143140085128157565624968869779751873525421618075302850983654142385988107915835110957955298055738073215056396008669696000), (524297, -96425354265323966022915843255494103371141511292200729413401718038723100612437106056555918744046460036999852698188275447909714432094617600), (524300, -97738178834337844373362456302322112249851758682910012509656317258531617128472369794022879634152023961366960483572917430860327276263833600), (524309, -75800009292123773557142185953426974607561494366839654761162118093067392197964707610409394281787252915363583875080901536299889681381130240), (524312, -584063995653772615589863612413763939699587639949751951357828311600435726826840008070354211480260067516252776850635463199729058721523200000), (524360, -37002851749647808190192856641685374182278404803240597926202134554476207715658702114503451670179175064457183076693293235796960208780902400), (528386, -31935145572767699533365485312791325116284793830360170337005786632201055532358030482906726880002026373734480041367181687220443829132492800), (540677, -14103368485331325614087007052547953425198591963220925594039291507960374829296583691907245947111974613857496489556062967871325779620710400), (786441, 5356964125851331445717546847527450187285639516233373856300095446595727811802061447586439930224803335388880705454904191550539690671923200), (786444, 5429898824129880242964580905684561791658431037939445139425350958807312062692909433001271090786223553409275582420717635047795959792435200), (786453, 1403703875780069880687818258396795826065953599385919532614113298019766522184531622414988782996060239173399701390387065487034994099650560), (786456, 29843895350856138162187942324308099852037581113264823896170151661871027762783999986467592817163421828018322476570336036967261928616499200), (786504, 1027856993045772449727579351157927060618844577867794386838948182068783547657186169847318101949421529568255085463702589883248894688358400), (790530, 892384703910801637531473070926349475955689578436852731781403168558133321617858672738338712599996085530471744824650428894125262322278400), (802821, 478087210963067184027179228993080610813566076599203945501315334649438825941056825710920849086807003325508450951184417525657201730636800), (1048597, 1364400167258227924028559347161685542936106898603113785700918125675213059563364736987369097072170552476544509751456227653398014264860344320), (1048600, 1265594742135777474102977565557889843798601857596598273122670705542445131611656224476313600825598814521920251353974192426595288173507788800), (1049602, 366031667845983606428221723745215038811548022251785907570952042176919044088837161915642424012482780043838141529021608894355750840208220160), (1052674, 215125343792279539738034395953810990629211044435134089920531176499210552995812724717168336151154795097032467130102504642646627706295091200), (1064965, 148440564575895140143140085128157565624968869779751873525421618075302850983654142385988107915835110957955298055738073215056396008669696000), (1310729, -194265596933353547822114669777362650518917092080565458016380928869369452502129040043919617731135880623623686113270617774835323283121213440), (1310732, -195476357668675688746724912604644224499703517365820025019312634517063234256944739588045759268304047922733920967145834861720654552527667200), (1310741, -151600018584247547114284371906853949215122988733679309522324236186134784395929415220818788563574505830727167750161803072599779362762260480), (1310744, -463461053099402803718991284097590396221737257102120201518612894427497530479291725735720678455653723581547743616633152368411061962056816640), (1310792, -37002851749647808190192856641685374182278404803240597926202134554476207715658702114503451670179175064457183076693293235796960208780902400), (1311746, -40670185316220400714246858193912782090172002472420656396772449130768782676537462435071380445831420004870904614335734321595083426689802240), (1314818, -55647257781666488975379539622657512501410434440897430098828967696221595152674562604696408567643615345820029172391670672324225737584640000), (1327109, -31672300371887351077195214226873838282369203207274630268329951570088228097754066252270758742364518074212323479842526021646562435841792000), (1572873, 16149497288815417435835028501825375216114366854042565968321258161560697395253674783359752026399018925590196600636605179041390984178657280), (1572876, 16289696472389640728893742717053685374975293113818335418276052876421936188078728299003813272358670660227826747262152905143387879377305600), (1572885, 4211111627340209642063454775190387478197860798157758597842339894059299566553594867244966348988180717520199104171161196461104982298951680), (1572888, 50383522818782724072078496932372217157366186517717599399785803387092309778663761603570125978997687070112866869453353998065838259127854080), (1572936, 2055713986091544899455158702315854121237689155735588773677896364137567095314372339694636203898843059136510170927405179766497789376716800), (1573890, 1129727369895011130951301616497577280282555624233907122132568031410243963237151734307538345717539444579747350398214842266530095185827840), (1576962, 2438141864512648553514238060444613712105979424017336901193318937897622075858818745091016728367874289581028110724419058680909310588518400), (1589253, 1626792932957240432582715471522460245328032634288321785406799812513176391109887080935888483268230390337488158449686590682744431669708800), (2097161, -97389897765162984127536199725645137591431746700907268983222804011133143867148610621461159532781661819368763785753582556268948323780935680), (2097164, -97738178834337844373362456302322112249851758682910012509656317258531617128472369794022879634152023961366960483572917430860327276263833600), (2097173, -75800009292123773557142185953426974607561494366839654761162118093067392197964707610409394281787252915363583875080901536299889681381130240), (2097176, -232183315345991559449291611538519433185784161753568367605036276994730361325057885666340434347705130511446986206671194572359908277317427200), (2098178, -40670185316220400714246858193912782090172002472420656396772449130768782676537462435071380445831420004870904614335734321595083426689802240), (2101250, -23902815976919948859781599550423443403245671603903787768947908499912283666201413857463148461239421677448051903344722738071847522921676800), (2113541, -13556444095821441538241223962883053111392075233986196434417889206104159661715571505162220646489253658168239049362317092345015425445120000), (2359305, 16203083038806473997202826083500432672797157710081818166644651826694588687182091703632265403550974580166247216612455573950237311494563840), (2359308, 16289696472389640728893742717053685374975293113818335418276052876421936188078728299003813272358670660227826747262152905143387879377305600), (2359317, 4211111627340209642063454775190387478197860798157758597842339894059299566553594867244966348988180717520199104171161196461104982298951680), (2359320, 30834596135017109842046719105969744573265993284596289191297357020108678361898088136680471693855746125401434055899783518767552123338644480), (2359368, 1027856993045772449727579351157927060618844577867794386838948182068783547657186169847318101949421529568255085463702589883248894688358400), (2360322, 2259454739790022261902603232995154560565111248467814244265136062820487926474303468615076691435078889159494700796429684533060190371655680), (2363394, 2209724271071845495421142754807804330684891834577811607438246561003718856079888235059987695246751028424113363214899816955446479458508800), (2375685, 1596408244651135761702394188763299116783226149330836832094499684632275548466497515005609299900301448354751633994478486486838300882176000), (3145737, 5410549875842388007085344429202507643968430372272626054623489111729619103730478367858953307376758989964931321430754586459386017987829760), (3145740, 5429898824129880242964580905684561791658431037939445139425350958807312062692909433001271090786223553409275582420717635047795959792435200), (3145749, 1403703875780069880687818258396795826065953599385919532614113298019766522184531622414988782996060239173399701390387065487034994099650560), (3145752, 10294968667090523932156164497905627267937387880143513687681705294887396346018326519577938532021480883306889663016765557668975792827289600), (3146754, 1129727369895011130951301616497577280282555624233907122132568031410243963237151734307538345717539444579747350398214842266530095185827840), (3149826, 663967110469998579438377765289540094534601988997327438026330791664230101838928162707309679478872824373556997315131187168662431192268800), (3162117, 447702522656962513146857946233919482268759591641718992189015206768537983297667259780641665718878061342771926495976313329751070943104000)]
theorem sparseBlock001_data : sparseBlock001 = (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (1129727369895011130951301616497577280282555624233907122132568031410243963237151734307538345717539444579747350398214842266530095185827840 : Int) coeff0020) (CoefficientMerge.scale (10594653778953300987085846697625334340001721853696000395818190882874669215826763092970376310990705853472376240012986276003645248307200 : Int) coeff0021)) (CoefficientMerge.merge (CoefficientMerge.scale (881790050131848336544387224228724141615687856583156731385584977675258652402031909645368336289005379676999368584637442618121617073971200 : Int) coeff0022) (CoefficientMerge.merge (CoefficientMerge.scale (663967110469998579438377765289540094534601988997327438026330791664230101838928162707309679478872824373556997315131187168662431192268800 : Int) coeff0023) (CoefficientMerge.scale (5356964125851331445717546847527450187285639516233373856300095446595727811802061447586439930224803335388880705454904191550539690671923200 : Int) coeff0024)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (10792533162964085990117481654297925028828727337809192112021162714964969583451613335773312096174215590201315895181700987490851293506734080 : Int) coeff0025) (CoefficientMerge.scale (5410549875842388007085344429202507643968430372272626054623489111729619103730478367858953307376758989964931321430754586459386017987829760 : Int) coeff0026)) (CoefficientMerge.merge (CoefficientMerge.scale (1403703875780069880687818258396795826065953599385919532614113298019766522184531622414988782996060239173399701390387065487034994099650560 : Int) coeff0027) (CoefficientMerge.merge (CoefficientMerge.scale (325370580740952842316129758696622209964832671476002429528659348975258938097791247124513330654877876825554440605774877180948975384268800 : Int) coeff0028) (CoefficientMerge.scale (843272461549944565133437301936462832816999747442714807960172506515377789482299098052152597317565134012071686807683092467670777246336000 : Int) coeff0029))))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (294985892434848171435808475937461081420026186518517476216359221094358095454401681194234147286948934842817916150566772985042844596736000 : Int) coeff0030) (CoefficientMerge.scale (152716630222114341711049470296458400848733405123201515972655985674179887843265578586407518431929126499954010345409540344708226346368000 : Int) coeff0031)) (CoefficientMerge.merge (CoefficientMerge.scale (5429898824129880242964580905684561791658431037939445139425350958807312062692909433001271090786223553409275582420717635047795959792435200 : Int) coeff0032) (CoefficientMerge.merge (CoefficientMerge.scale (10859797648259760485929161811369123583316862075878890278850701917614624125385818866002542181572447106818551164841435270095591919584870400 : Int) coeff0033) (CoefficientMerge.scale (5429898824129880242964580905684561791658431037939445139425350958807312062692909433001271090786223553409275582420717635047795959792435200 : Int) coeff0034)))) (CoefficientMerge.merge (CoefficientMerge.merge (CoefficientMerge.scale (28541843147012745699119035363857595897512270560181903862093329948349993676763777533302661129071241977687128802337852299902863483993548800 : Int) coeff0035) (CoefficientMerge.scale (17935523060239800983752740687163109396277984298286935435462008298179213843839316710772669785649905541432157044418050486969779441265454080 : Int) coeff0036)) (CoefficientMerge.merge (CoefficientMerge.scale (8992916463247131469087257537455123313412077327060593653604883581366362259998104066413006843929301032975695988784281820604577348204339200 : Int) coeff0037) (CoefficientMerge.merge (CoefficientMerge.scale (1302052203843392463068906960450503954525310553082920034076821713521034086020222453164931688092179850331193674232483737064398444622950400 : Int) coeff0038) (CoefficientMerge.scale (1027856993045772449727579351157927060618844577867794386838948182068783547657186169847318101949421529568255085463702589883248894688358400 : Int) coeff0039)))))) := by decide +kernel
theorem sparseBlock001_nonneg (g : Fin 9 → ℝ) (t z : ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 0 ≤ t+z-18) : 0 ≤ CoefficientMerge.eval (monomial g t z) sparseBlock001 := by
  rw [sparseBlock001_data]
  try simp only [CoefficientMerge.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (weighted0020_nonneg g t z hg hA hB ht hz hw) (weighted0021_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0022_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0023_nonneg g t z hg hA hB ht hz hw) (weighted0024_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0025_nonneg g t z hg hA hB ht hz hw) (weighted0026_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0027_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0028_nonneg g t z hg hA hB ht hz hw) (weighted0029_nonneg g t z hg hA hB ht hz hw))))) (add_nonneg (add_nonneg (add_nonneg (weighted0030_nonneg g t z hg hA hB ht hz hw) (weighted0031_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0032_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0033_nonneg g t z hg hA hB ht hz hw) (weighted0034_nonneg g t z hg hA hB ht hz hw)))) (add_nonneg (add_nonneg (weighted0035_nonneg g t z hg hA hB ht hz hw) (weighted0036_nonneg g t z hg hA hB ht hz hw)) (add_nonneg (weighted0037_nonneg g t z hg hA hB ht hz hw) (add_nonneg (weighted0038_nonneg g t z hg hA hB ht hz hw) (weighted0039_nonneg g t z hg hA hB ht hz hw))))))

end APPT.Uniform
