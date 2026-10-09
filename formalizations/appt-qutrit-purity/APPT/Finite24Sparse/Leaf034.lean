import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom2529 : SparsePolynomial.Poly := [([17,19,21], 1)]
theorem eval_atom2529 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2529 = ((g 17) * (g 19) * (g 21)) := by
  norm_num [atom2529, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2529_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (636169476096000 : Int) atom2529) := by
  rw [SparsePolynomial.eval_scale, eval_atom2529]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 17) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2529Coded : CoefficientMerge.Poly := [(10269, 1)]
theorem atom2529Coded_decode : atom2529 = SparsePolynomial.decodeCubic 24 atom2529Coded := by decide +kernel
theorem atom2529Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (636169476096000 : Int) atom2529Coded) := by
  have h := atom2529_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2529Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2530 : SparsePolynomial.Poly := [([17,19,22], 1)]
theorem eval_atom2530 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2530 = ((g 17) * (g 19) * (g 22)) := by
  norm_num [atom2530, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2530_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (597975854515200 : Int) atom2530) := by
  rw [SparsePolynomial.eval_scale, eval_atom2530]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 17) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2530Coded : CoefficientMerge.Poly := [(10270, 1)]
theorem atom2530Coded_decode : atom2530 = SparsePolynomial.decodeCubic 24 atom2530Coded := by decide +kernel
theorem atom2530Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (597975854515200 : Int) atom2530Coded) := by
  have h := atom2530_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2530Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2531 : SparsePolynomial.Poly := [([17,19,23], 1)]
theorem eval_atom2531 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2531 = ((g 17) * (g 19) * (g 23)) := by
  norm_num [atom2531, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2531_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (820556564889600 : Int) atom2531) := by
  rw [SparsePolynomial.eval_scale, eval_atom2531]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 17) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2531Coded : CoefficientMerge.Poly := [(10271, 1)]
theorem atom2531Coded_decode : atom2531 = SparsePolynomial.decodeCubic 24 atom2531Coded := by decide +kernel
theorem atom2531Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (820556564889600 : Int) atom2531Coded) := by
  have h := atom2531_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2531Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2532 : SparsePolynomial.Poly := [([17,20,20], 1)]
theorem eval_atom2532 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2532 = ((g 17) * (g 20) * (g 20)) := by
  norm_num [atom2532, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2532_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (368221356518400 : Int) atom2532) := by
  rw [SparsePolynomial.eval_scale, eval_atom2532]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 17) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2532Coded : CoefficientMerge.Poly := [(10292, 1)]
theorem atom2532Coded_decode : atom2532 = SparsePolynomial.decodeCubic 24 atom2532Coded := by decide +kernel
theorem atom2532Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (368221356518400 : Int) atom2532Coded) := by
  have h := atom2532_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2532Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2533 : SparsePolynomial.Poly := [([17,20,21], 1)]
theorem eval_atom2533 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2533 = ((g 17) * (g 20) * (g 21)) := by
  norm_num [atom2533, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2533_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (781603941888000 : Int) atom2533) := by
  rw [SparsePolynomial.eval_scale, eval_atom2533]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 17) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2533Coded : CoefficientMerge.Poly := [(10293, 1)]
theorem atom2533Coded_decode : atom2533 = SparsePolynomial.decodeCubic 24 atom2533Coded := by decide +kernel
theorem atom2533Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (781603941888000 : Int) atom2533Coded) := by
  have h := atom2533_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2533Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2534 : SparsePolynomial.Poly := [([17,20,22], 1)]
theorem eval_atom2534 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2534 = ((g 17) * (g 20) * (g 22)) := by
  norm_num [atom2534, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2534_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (761659858713600 : Int) atom2534) := by
  rw [SparsePolynomial.eval_scale, eval_atom2534]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 17) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2534Coded : CoefficientMerge.Poly := [(10294, 1)]
theorem atom2534Coded_decode : atom2534 = SparsePolynomial.decodeCubic 24 atom2534Coded := by decide +kernel
theorem atom2534Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (761659858713600 : Int) atom2534Coded) := by
  have h := atom2534_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2534Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2535 : SparsePolynomial.Poly := [([17,20,23], 1)]
theorem eval_atom2535 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2535 = ((g 17) * (g 20) * (g 23)) := by
  norm_num [atom2535, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2535_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (841818913689600 : Int) atom2535) := by
  rw [SparsePolynomial.eval_scale, eval_atom2535]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 17) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2535Coded : CoefficientMerge.Poly := [(10295, 1)]
theorem atom2535Coded_decode : atom2535 = SparsePolynomial.decodeCubic 24 atom2535Coded := by decide +kernel
theorem atom2535Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (841818913689600 : Int) atom2535Coded) := by
  have h := atom2535_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2535Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2536 : SparsePolynomial.Poly := [([17,21,21], 1)]
theorem eval_atom2536 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2536 = ((g 17) * (g 21) * (g 21)) := by
  norm_num [atom2536, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2536_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (357887855001600 : Int) atom2536) := by
  rw [SparsePolynomial.eval_scale, eval_atom2536]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 17) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2536Coded : CoefficientMerge.Poly := [(10317, 1)]
theorem atom2536Coded_decode : atom2536 = SparsePolynomial.decodeCubic 24 atom2536Coded := by decide +kernel
theorem atom2536Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (357887855001600 : Int) atom2536Coded) := by
  have h := atom2536_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2536Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2537 : SparsePolynomial.Poly := [([17,21,22], 1)]
theorem eval_atom2537 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2537 = ((g 17) * (g 21) * (g 22)) := by
  norm_num [atom2537, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2537_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (784623195417600 : Int) atom2537) := by
  rw [SparsePolynomial.eval_scale, eval_atom2537]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 17) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2537Coded : CoefficientMerge.Poly := [(10318, 1)]
theorem atom2537Coded_decode : atom2537 = SparsePolynomial.decodeCubic 24 atom2537Coded := by decide +kernel
theorem atom2537Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (784623195417600 : Int) atom2537Coded) := by
  have h := atom2537_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2537Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2538 : SparsePolynomial.Poly := [([17,21,23], 1)]
theorem eval_atom2538 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2538 = ((g 17) * (g 21) * (g 23)) := by
  norm_num [atom2538, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2538_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (883152919756800 : Int) atom2538) := by
  rw [SparsePolynomial.eval_scale, eval_atom2538]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 17) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2538Coded : CoefficientMerge.Poly := [(10319, 1)]
theorem atom2538Coded_decode : atom2538 = SparsePolynomial.decodeCubic 24 atom2538Coded := by decide +kernel
theorem atom2538Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (883152919756800 : Int) atom2538Coded) := by
  have h := atom2538_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2538Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2539 : SparsePolynomial.Poly := [([17,22,22], 1)]
theorem eval_atom2539 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2539 = ((g 17) * (g 22) * (g 22)) := by
  norm_num [atom2539, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2539_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (397355445648000 : Int) atom2539) := by
  rw [SparsePolynomial.eval_scale, eval_atom2539]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 17) * (g 22) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2539Coded : CoefficientMerge.Poly := [(10342, 1)]
theorem atom2539Coded_decode : atom2539 = SparsePolynomial.decodeCubic 24 atom2539Coded := by decide +kernel
theorem atom2539Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (397355445648000 : Int) atom2539Coded) := by
  have h := atom2539_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2539Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2540 : SparsePolynomial.Poly := [([17,22,23], 1)]
theorem eval_atom2540 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2540 = ((g 17) * (g 22) * (g 23)) := by
  norm_num [atom2540, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2540_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (924486925824000 : Int) atom2540) := by
  rw [SparsePolynomial.eval_scale, eval_atom2540]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 17) * (g 22) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2540Coded : CoefficientMerge.Poly := [(10343, 1)]
theorem atom2540Coded_decode : atom2540 = SparsePolynomial.decodeCubic 24 atom2540Coded := by decide +kernel
theorem atom2540Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (924486925824000 : Int) atom2540Coded) := by
  have h := atom2540_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2540Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2541 : SparsePolynomial.Poly := [([17,23,23], 1)]
theorem eval_atom2541 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2541 = ((g 17) * (g 23) * (g 23)) := by
  norm_num [atom2541, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2541_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (472874637312000 : Int) atom2541) := by
  rw [SparsePolynomial.eval_scale, eval_atom2541]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 17) * (g 23) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2541Coded : CoefficientMerge.Poly := [(10367, 1)]
theorem atom2541Coded_decode : atom2541 = SparsePolynomial.decodeCubic 24 atom2541Coded := by decide +kernel
theorem atom2541Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (472874637312000 : Int) atom2541Coded) := by
  have h := atom2541_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2541Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2542 : SparsePolynomial.Poly := [([18,18,18], 1)]
theorem eval_atom2542 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2542 = ((g 18) * (g 18) * (g 18)) := by
  norm_num [atom2542, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2542_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10354763865600 : Int) atom2542) := by
  rw [SparsePolynomial.eval_scale, eval_atom2542]
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 18) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2542Coded : CoefficientMerge.Poly := [(10818, 1)]
theorem atom2542Coded_decode : atom2542 = SparsePolynomial.decodeCubic 24 atom2542Coded := by decide +kernel
theorem atom2542Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (10354763865600 : Int) atom2542Coded) := by
  have h := atom2542_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2542Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2543 : SparsePolynomial.Poly := [([18,18,19], 1)]
theorem eval_atom2543 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2543 = ((g 18) * (g 18) * (g 19)) := by
  norm_num [atom2543, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2543_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (76586980377600 : Int) atom2543) := by
  rw [SparsePolynomial.eval_scale, eval_atom2543]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 18) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2543Coded : CoefficientMerge.Poly := [(10819, 1)]
theorem atom2543Coded_decode : atom2543 = SparsePolynomial.decodeCubic 24 atom2543Coded := by decide +kernel
theorem atom2543Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (76586980377600 : Int) atom2543Coded) := by
  have h := atom2543_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2543Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2544 : SparsePolynomial.Poly := [([18,18,20], 1)]
theorem eval_atom2544 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2544 = ((g 18) * (g 18) * (g 20)) := by
  norm_num [atom2544, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2544_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (262951467609600 : Int) atom2544) := by
  rw [SparsePolynomial.eval_scale, eval_atom2544]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 18) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2544Coded : CoefficientMerge.Poly := [(10820, 1)]
theorem atom2544Coded_decode : atom2544 = SparsePolynomial.decodeCubic 24 atom2544Coded := by decide +kernel
theorem atom2544Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (262951467609600 : Int) atom2544Coded) := by
  have h := atom2544_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2544Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2545 : SparsePolynomial.Poly := [([18,18,21], 1)]
theorem eval_atom2545 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2545 = ((g 18) * (g 18) * (g 21)) := by
  norm_num [atom2545, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2545_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (308474156390400 : Int) atom2545) := by
  rw [SparsePolynomial.eval_scale, eval_atom2545]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 18) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2545Coded : CoefficientMerge.Poly := [(10821, 1)]
theorem atom2545Coded_decode : atom2545 = SparsePolynomial.decodeCubic 24 atom2545Coded := by decide +kernel
theorem atom2545Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (308474156390400 : Int) atom2545Coded) := by
  have h := atom2545_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2545Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2546 : SparsePolynomial.Poly := [([18,18,22], 1)]
theorem eval_atom2546 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2546 = ((g 18) * (g 18) * (g 22)) := by
  norm_num [atom2546, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2546_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (220891320115200 : Int) atom2546) := by
  rw [SparsePolynomial.eval_scale, eval_atom2546]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 18) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2546Coded : CoefficientMerge.Poly := [(10822, 1)]
theorem atom2546Coded_decode : atom2546 = SparsePolynomial.decodeCubic 24 atom2546Coded := by decide +kernel
theorem atom2546Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (220891320115200 : Int) atom2546Coded) := by
  have h := atom2546_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2546Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2547 : SparsePolynomial.Poly := [([18,18,23], 1)]
theorem eval_atom2547 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2547 = ((g 18) * (g 18) * (g 23)) := by
  norm_num [atom2547, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2547_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (399519533952000 : Int) atom2547) := by
  rw [SparsePolynomial.eval_scale, eval_atom2547]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 18) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2547Coded : CoefficientMerge.Poly := [(10823, 1)]
theorem atom2547Coded_decode : atom2547 = SparsePolynomial.decodeCubic 24 atom2547Coded := by decide +kernel
theorem atom2547Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (399519533952000 : Int) atom2547Coded) := by
  have h := atom2547_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2547Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2548 : SparsePolynomial.Poly := [([18,19,19], 1)]
theorem eval_atom2548 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2548 = ((g 18) * (g 19) * (g 19)) := by
  norm_num [atom2548, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2548_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (72104877250560 : Int) atom2548) := by
  rw [SparsePolynomial.eval_scale, eval_atom2548]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 18) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2548Coded : CoefficientMerge.Poly := [(10843, 1)]
theorem atom2548Coded_decode : atom2548 = SparsePolynomial.decodeCubic 24 atom2548Coded := by decide +kernel
theorem atom2548Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (72104877250560 : Int) atom2548Coded) := by
  have h := atom2548_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2548Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2549 : SparsePolynomial.Poly := [([18,19,20], 1)]
theorem eval_atom2549 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2549 = ((g 18) * (g 19) * (g 20)) := by
  norm_num [atom2549, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2549_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (519184032998400 : Int) atom2549) := by
  rw [SparsePolynomial.eval_scale, eval_atom2549]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 18) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2549Coded : CoefficientMerge.Poly := [(10844, 1)]
theorem atom2549Coded_decode : atom2549 = SparsePolynomial.decodeCubic 24 atom2549Coded := by decide +kernel
theorem atom2549Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (519184032998400 : Int) atom2549Coded) := by
  have h := atom2549_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2549Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2550 : SparsePolynomial.Poly := [([18,19,21], 1)]
theorem eval_atom2550 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2550 = ((g 18) * (g 19) * (g 21)) := by
  norm_num [atom2550, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2550_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (700041571891200 : Int) atom2550) := by
  rw [SparsePolynomial.eval_scale, eval_atom2550]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 18) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2550Coded : CoefficientMerge.Poly := [(10845, 1)]
theorem atom2550Coded_decode : atom2550 = SparsePolynomial.decodeCubic 24 atom2550Coded := by decide +kernel
theorem atom2550Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (700041571891200 : Int) atom2550Coded) := by
  have h := atom2550_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2550Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2551 : SparsePolynomial.Poly := [([18,19,22], 1)]
theorem eval_atom2551 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2551 = ((g 18) * (g 19) * (g 22)) := by
  norm_num [atom2551, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2551_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (614688060672000 : Int) atom2551) := by
  rw [SparsePolynomial.eval_scale, eval_atom2551]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 18) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2551Coded : CoefficientMerge.Poly := [(10846, 1)]
theorem atom2551Coded_decode : atom2551 = SparsePolynomial.decodeCubic 24 atom2551Coded := by decide +kernel
theorem atom2551Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (614688060672000 : Int) atom2551Coded) := by
  have h := atom2551_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2551Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2552 : SparsePolynomial.Poly := [([18,19,23], 1)]
theorem eval_atom2552 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2552 = ((g 18) * (g 19) * (g 23)) := by
  norm_num [atom2552, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2552_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (850493952000000 : Int) atom2552) := by
  rw [SparsePolynomial.eval_scale, eval_atom2552]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 18) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2552Coded : CoefficientMerge.Poly := [(10847, 1)]
theorem atom2552Coded_decode : atom2552 = SparsePolynomial.decodeCubic 24 atom2552Coded := by decide +kernel
theorem atom2552Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (850493952000000 : Int) atom2552Coded) := by
  have h := atom2552_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2552Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2553 : SparsePolynomial.Poly := [([18,20,20], 1)]
theorem eval_atom2553 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2553 = ((g 18) * (g 20) * (g 20)) := by
  norm_num [atom2553, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2553_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (397074363840000 : Int) atom2553) := by
  rw [SparsePolynomial.eval_scale, eval_atom2553]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 18) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2553Coded : CoefficientMerge.Poly := [(10868, 1)]
theorem atom2553Coded_decode : atom2553 = SparsePolynomial.decodeCubic 24 atom2553Coded := by decide +kernel
theorem atom2553Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (397074363840000 : Int) atom2553Coded) := by
  have h := atom2553_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2553Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2554 : SparsePolynomial.Poly := [([18,20,21], 1)]
theorem eval_atom2554 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2554 = ((g 18) * (g 20) * (g 21)) := by
  norm_num [atom2554, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2554_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (853555730227200 : Int) atom2554) := by
  rw [SparsePolynomial.eval_scale, eval_atom2554]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 18) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2554Coded : CoefficientMerge.Poly := [(10869, 1)]
theorem atom2554Coded_decode : atom2554 = SparsePolynomial.decodeCubic 24 atom2554Coded := by decide +kernel
theorem atom2554Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (853555730227200 : Int) atom2554Coded) := by
  have h := atom2554_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2554Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2555 : SparsePolynomial.Poly := [([18,20,22], 1)]
theorem eval_atom2555 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2555 = ((g 18) * (g 20) * (g 22)) := by
  norm_num [atom2555, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2555_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (787472350156800 : Int) atom2555) := by
  rw [SparsePolynomial.eval_scale, eval_atom2555]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 18) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2555Coded : CoefficientMerge.Poly := [(10870, 1)]
theorem atom2555Coded_decode : atom2555 = SparsePolynomial.decodeCubic 24 atom2555Coded := by decide +kernel
theorem atom2555Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (787472350156800 : Int) atom2555Coded) := by
  have h := atom2555_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2555Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2556 : SparsePolynomial.Poly := [([18,20,23], 1)]
theorem eval_atom2556 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2556 = ((g 18) * (g 20) * (g 23)) := by
  norm_num [atom2556, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2556_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (761107037644800 : Int) atom2556) := by
  rw [SparsePolynomial.eval_scale, eval_atom2556]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 18) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2556Coded : CoefficientMerge.Poly := [(10871, 1)]
theorem atom2556Coded_decode : atom2556 = SparsePolynomial.decodeCubic 24 atom2556Coded := by decide +kernel
theorem atom2556Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (761107037644800 : Int) atom2556Coded) := by
  have h := atom2556_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2556Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2557 : SparsePolynomial.Poly := [([18,21,21], 1)]
theorem eval_atom2557 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2557 = ((g 18) * (g 21) * (g 21)) := by
  norm_num [atom2557, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2557_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (397903595443200 : Int) atom2557) := by
  rw [SparsePolynomial.eval_scale, eval_atom2557]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 18) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2557Coded : CoefficientMerge.Poly := [(10893, 1)]
theorem atom2557Coded_decode : atom2557 = SparsePolynomial.decodeCubic 24 atom2557Coded := by decide +kernel
theorem atom2557Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (397903595443200 : Int) atom2557Coded) := by
  have h := atom2557_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2557Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2558 : SparsePolynomial.Poly := [([18,21,22], 1)]
theorem eval_atom2558 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2558 = ((g 18) * (g 21) * (g 22)) := by
  norm_num [atom2558, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2558_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (819535972147200 : Int) atom2558) := by
  rw [SparsePolynomial.eval_scale, eval_atom2558]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 18) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2558Coded : CoefficientMerge.Poly := [(10894, 1)]
theorem atom2558Coded_decode : atom2558 = SparsePolynomial.decodeCubic 24 atom2558Coded := by decide +kernel
theorem atom2558Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (819535972147200 : Int) atom2558Coded) := by
  have h := atom2558_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2558Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2559 : SparsePolynomial.Poly := [([18,21,23], 1)]
theorem eval_atom2559 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2559 = ((g 18) * (g 21) * (g 23)) := by
  norm_num [atom2559, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2559_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (812561921740800 : Int) atom2559) := by
  rw [SparsePolynomial.eval_scale, eval_atom2559]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 18) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2559Coded : CoefficientMerge.Poly := [(10895, 1)]
theorem atom2559Coded_decode : atom2559 = SparsePolynomial.decodeCubic 24 atom2559Coded := by decide +kernel
theorem atom2559Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (812561921740800 : Int) atom2559Coded) := by
  have h := atom2559_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2559Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2560 : SparsePolynomial.Poly := [([18,22,22], 1)]
theorem eval_atom2560 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2560 = ((g 18) * (g 22) * (g 22)) := by
  norm_num [atom2560, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2560_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (418743032904000 : Int) atom2560) := by
  rw [SparsePolynomial.eval_scale, eval_atom2560]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 18) * (g 22) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2560Coded : CoefficientMerge.Poly := [(10918, 1)]
theorem atom2560Coded_decode : atom2560 = SparsePolynomial.decodeCubic 24 atom2560Coded := by decide +kernel
theorem atom2560Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (418743032904000 : Int) atom2560Coded) := by
  have h := atom2560_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2560Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2561 : SparsePolynomial.Poly := [([18,22,23], 1)]
theorem eval_atom2561 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2561 = ((g 18) * (g 22) * (g 23)) := by
  norm_num [atom2561, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2561_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (863774543923200 : Int) atom2561) := by
  rw [SparsePolynomial.eval_scale, eval_atom2561]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 18) * (g 22) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2561Coded : CoefficientMerge.Poly := [(10919, 1)]
theorem atom2561Coded_decode : atom2561 = SparsePolynomial.decodeCubic 24 atom2561Coded := by decide +kernel
theorem atom2561Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (863774543923200 : Int) atom2561Coded) := by
  have h := atom2561_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2561Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2562 : SparsePolynomial.Poly := [([18,23,23], 1)]
theorem eval_atom2562 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2562 = ((g 18) * (g 23) * (g 23)) := by
  norm_num [atom2562, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2562_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (387314945740800 : Int) atom2562) := by
  rw [SparsePolynomial.eval_scale, eval_atom2562]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 18) * (g 23) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2562Coded : CoefficientMerge.Poly := [(10943, 1)]
theorem atom2562Coded_decode : atom2562 = SparsePolynomial.decodeCubic 24 atom2562Coded := by decide +kernel
theorem atom2562Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (387314945740800 : Int) atom2562Coded) := by
  have h := atom2562_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2562Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2563 : SparsePolynomial.Poly := [([19,19,20], 1)]
theorem eval_atom2563 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2563 = ((g 19) * (g 19) * (g 20)) := by
  norm_num [atom2563, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2563_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (185526750689280 : Int) atom2563) := by
  rw [SparsePolynomial.eval_scale, eval_atom2563]
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 19) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2563Coded : CoefficientMerge.Poly := [(11420, 1)]
theorem atom2563Coded_decode : atom2563 = SparsePolynomial.decodeCubic 24 atom2563Coded := by decide +kernel
theorem atom2563Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (185526750689280 : Int) atom2563Coded) := by
  have h := atom2563_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2563Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2564 : SparsePolynomial.Poly := [([19,19,21], 1)]
theorem eval_atom2564 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2564 = ((g 19) * (g 19) * (g 21)) := by
  norm_num [atom2564, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2564_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (315329137643520 : Int) atom2564) := by
  rw [SparsePolynomial.eval_scale, eval_atom2564]
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 19) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2564Coded : CoefficientMerge.Poly := [(11421, 1)]
theorem atom2564Coded_decode : atom2564 = SparsePolynomial.decodeCubic 24 atom2564Coded := by decide +kernel
theorem atom2564Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (315329137643520 : Int) atom2564Coded) := by
  have h := atom2564_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2564Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2565 : SparsePolynomial.Poly := [([19,19,22], 1)]
theorem eval_atom2565 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2565 = ((g 19) * (g 19) * (g 22)) := by
  norm_num [atom2565, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2565_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (309576576960000 : Int) atom2565) := by
  rw [SparsePolynomial.eval_scale, eval_atom2565]
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 19) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2565Coded : CoefficientMerge.Poly := [(11422, 1)]
theorem atom2565Coded_decode : atom2565 = SparsePolynomial.decodeCubic 24 atom2565Coded := by decide +kernel
theorem atom2565Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (309576576960000 : Int) atom2565Coded) := by
  have h := atom2565_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2565Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2566 : SparsePolynomial.Poly := [([19,19,23], 1)]
theorem eval_atom2566 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2566 = ((g 19) * (g 19) * (g 23)) := by
  norm_num [atom2566, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2566_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (429193267937280 : Int) atom2566) := by
  rw [SparsePolynomial.eval_scale, eval_atom2566]
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 19) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2566Coded : CoefficientMerge.Poly := [(11423, 1)]
theorem atom2566Coded_decode : atom2566 = SparsePolynomial.decodeCubic 24 atom2566Coded := by decide +kernel
theorem atom2566Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (429193267937280 : Int) atom2566Coded) := by
  have h := atom2566_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2566Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2567 : SparsePolynomial.Poly := [([19,20,20], 1)]
theorem eval_atom2567 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2567 = ((g 19) * (g 20) * (g 20)) := by
  norm_num [atom2567, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2567_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (325313936640000 : Int) atom2567) := by
  rw [SparsePolynomial.eval_scale, eval_atom2567]
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 19) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2567Coded : CoefficientMerge.Poly := [(11444, 1)]
theorem atom2567Coded_decode : atom2567 = SparsePolynomial.decodeCubic 24 atom2567Coded := by decide +kernel
theorem atom2567Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (325313936640000 : Int) atom2567Coded) := by
  have h := atom2567_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2567Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2568 : SparsePolynomial.Poly := [([19,20,21], 1)]
theorem eval_atom2568 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2568 = ((g 19) * (g 20) * (g 21)) := by
  norm_num [atom2568, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2568_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (794701548748800 : Int) atom2568) := by
  rw [SparsePolynomial.eval_scale, eval_atom2568]
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 19) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2568Coded : CoefficientMerge.Poly := [(11445, 1)]
theorem atom2568Coded_decode : atom2568 = SparsePolynomial.decodeCubic 24 atom2568Coded := by decide +kernel
theorem atom2568Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (794701548748800 : Int) atom2568Coded) := by
  have h := atom2568_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2568Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2569 : SparsePolynomial.Poly := [([19,20,22], 1)]
theorem eval_atom2569 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2569 = ((g 19) * (g 20) * (g 22)) := by
  norm_num [atom2569, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2569_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (813284841600000 : Int) atom2569) := by
  rw [SparsePolynomial.eval_scale, eval_atom2569]
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 19) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2569Coded : CoefficientMerge.Poly := [(11446, 1)]
theorem atom2569Coded_decode : atom2569 = SparsePolynomial.decodeCubic 24 atom2569Coded := by decide +kernel
theorem atom2569Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (813284841600000 : Int) atom2569Coded) := by
  have h := atom2569_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2569Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2570 : SparsePolynomial.Poly := [([19,20,23], 1)]
theorem eval_atom2570 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2570 = ((g 19) * (g 20) * (g 23)) := by
  norm_num [atom2570, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2570_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (801165302784000 : Int) atom2570) := by
  rw [SparsePolynomial.eval_scale, eval_atom2570]
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 19) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2570Coded : CoefficientMerge.Poly := [(11447, 1)]
theorem atom2570Coded_decode : atom2570 = SparsePolynomial.decodeCubic 24 atom2570Coded := by decide +kernel
theorem atom2570Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (801165302784000 : Int) atom2570Coded) := by
  have h := atom2570_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2570Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2571 : SparsePolynomial.Poly := [([19,21,21], 1)]
theorem eval_atom2571 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2571 = ((g 19) * (g 21) * (g 21)) := by
  norm_num [atom2571, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2571_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (407726800588800 : Int) atom2571) := by
  rw [SparsePolynomial.eval_scale, eval_atom2571]
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 19) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2571Coded : CoefficientMerge.Poly := [(11469, 1)]
theorem atom2571Coded_decode : atom2571 = SparsePolynomial.decodeCubic 24 atom2571Coded := by decide +kernel
theorem atom2571Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (407726800588800 : Int) atom2571Coded) := by
  have h := atom2571_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2571Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2572 : SparsePolynomial.Poly := [([19,21,22], 1)]
theorem eval_atom2572 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2572 = ((g 19) * (g 21) * (g 22)) := by
  norm_num [atom2572, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2572_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (854448748876800 : Int) atom2572) := by
  rw [SparsePolynomial.eval_scale, eval_atom2572]
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 19) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2572Coded : CoefficientMerge.Poly := [(11470, 1)]
theorem atom2572Coded_decode : atom2572 = SparsePolynomial.decodeCubic 24 atom2572Coded := by decide +kernel
theorem atom2572Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (854448748876800 : Int) atom2572Coded) := by
  have h := atom2572_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2572Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2573 : SparsePolynomial.Poly := [([19,21,23], 1)]
theorem eval_atom2573 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2573 = ((g 19) * (g 21) * (g 23)) := by
  norm_num [atom2573, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2573_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (862741064908800 : Int) atom2573) := by
  rw [SparsePolynomial.eval_scale, eval_atom2573]
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 19) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2573Coded : CoefficientMerge.Poly := [(11471, 1)]
theorem atom2573Coded_decode : atom2573 = SparsePolynomial.decodeCubic 24 atom2573Coded := by decide +kernel
theorem atom2573Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (862741064908800 : Int) atom2573Coded) := by
  have h := atom2573_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2573Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2574 : SparsePolynomial.Poly := [([19,22,22], 1)]
theorem eval_atom2574 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2574 = ((g 19) * (g 22) * (g 22)) := by
  norm_num [atom2574, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2574_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (440130620160000 : Int) atom2574) := by
  rw [SparsePolynomial.eval_scale, eval_atom2574]
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 19) * (g 22) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2574Coded : CoefficientMerge.Poly := [(11494, 1)]
theorem atom2574Coded_decode : atom2574 = SparsePolynomial.decodeCubic 24 atom2574Coded := by decide +kernel
theorem atom2574Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (440130620160000 : Int) atom2574Coded) := by
  have h := atom2574_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2574Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2575 : SparsePolynomial.Poly := [([19,22,23], 1)]
theorem eval_atom2575 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2575 = ((g 19) * (g 22) * (g 23)) := by
  norm_num [atom2575, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2575_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (924074565120000 : Int) atom2575) := by
  rw [SparsePolynomial.eval_scale, eval_atom2575]
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 19) * (g 22) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2575Coded : CoefficientMerge.Poly := [(11495, 1)]
theorem atom2575Coded_decode : atom2575 = SparsePolynomial.decodeCubic 24 atom2575Coded := by decide +kernel
theorem atom2575Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (924074565120000 : Int) atom2575Coded) := by
  have h := atom2575_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2575Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2576 : SparsePolynomial.Poly := [([19,23,23], 1)]
theorem eval_atom2576 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2576 = ((g 19) * (g 23) * (g 23)) := by
  norm_num [atom2576, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2576_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (422525395353600 : Int) atom2576) := by
  rw [SparsePolynomial.eval_scale, eval_atom2576]
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 19) * (g 23) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2576Coded : CoefficientMerge.Poly := [(11519, 1)]
theorem atom2576Coded_decode : atom2576 = SparsePolynomial.decodeCubic 24 atom2576Coded := by decide +kernel
theorem atom2576Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (422525395353600 : Int) atom2576Coded) := by
  have h := atom2576_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2576Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2577 : SparsePolynomial.Poly := [([20,20,20], 1)]
theorem eval_atom2577 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2577 = ((g 20) * (g 20) * (g 20)) := by
  norm_num [atom2577, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2577_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (131465102630400 : Int) atom2577) := by
  rw [SparsePolynomial.eval_scale, eval_atom2577]
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 20) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2577Coded : CoefficientMerge.Poly := [(12020, 1)]
theorem atom2577Coded_decode : atom2577 = SparsePolynomial.decodeCubic 24 atom2577Coded := by decide +kernel
theorem atom2577Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (131465102630400 : Int) atom2577Coded) := by
  have h := atom2577_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2577Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2578 : SparsePolynomial.Poly := [([20,20,21], 1)]
theorem eval_atom2578 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2578 = ((g 20) * (g 20) * (g 21)) := by
  norm_num [atom2578, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2578_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (403134133248000 : Int) atom2578) := by
  rw [SparsePolynomial.eval_scale, eval_atom2578]
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 20) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2578Coded : CoefficientMerge.Poly := [(12021, 1)]
theorem atom2578Coded_decode : atom2578 = SparsePolynomial.decodeCubic 24 atom2578Coded := by decide +kernel
theorem atom2578Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (403134133248000 : Int) atom2578Coded) := by
  have h := atom2578_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2578Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2579 : SparsePolynomial.Poly := [([20,20,22], 1)]
theorem eval_atom2579 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2579 = ((g 20) * (g 20) * (g 22)) := by
  norm_num [atom2579, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2579_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (419548666521600 : Int) atom2579) := by
  rw [SparsePolynomial.eval_scale, eval_atom2579]
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 20) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2579Coded : CoefficientMerge.Poly := [(12022, 1)]
theorem atom2579Coded_decode : atom2579 = SparsePolynomial.decodeCubic 24 atom2579Coded := by decide +kernel
theorem atom2579Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (419548666521600 : Int) atom2579Coded) := by
  have h := atom2579_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2579Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2580 : SparsePolynomial.Poly := [([20,20,23], 1)]
theorem eval_atom2580 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2580 = ((g 20) * (g 20) * (g 23)) := by
  norm_num [atom2580, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2580_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (279769985510400 : Int) atom2580) := by
  rw [SparsePolynomial.eval_scale, eval_atom2580]
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 20) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2580Coded : CoefficientMerge.Poly := [(12023, 1)]
theorem atom2580Coded_decode : atom2580 = SparsePolynomial.decodeCubic 24 atom2580Coded := by decide +kernel
theorem atom2580Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (279769985510400 : Int) atom2580Coded) := by
  have h := atom2580_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2580Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2581 : SparsePolynomial.Poly := [([20,21,21], 1)]
theorem eval_atom2581 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2581 = ((g 20) * (g 21) * (g 21)) := by
  norm_num [atom2581, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2581_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (417550005734400 : Int) atom2581) := by
  rw [SparsePolynomial.eval_scale, eval_atom2581]
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 20) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2581Coded : CoefficientMerge.Poly := [(12045, 1)]
theorem atom2581Coded_decode : atom2581 = SparsePolynomial.decodeCubic 24 atom2581Coded := by decide +kernel
theorem atom2581Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (417550005734400 : Int) atom2581Coded) := by
  have h := atom2581_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2581Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2582 : SparsePolynomial.Poly := [([20,21,22], 1)]
theorem eval_atom2582 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2582 = ((g 20) * (g 21) * (g 22)) := by
  norm_num [atom2582, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2582_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (889361525606400 : Int) atom2582) := by
  rw [SparsePolynomial.eval_scale, eval_atom2582]
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 20) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2582Coded : CoefficientMerge.Poly := [(12046, 1)]
theorem atom2582Coded_decode : atom2582 = SparsePolynomial.decodeCubic 24 atom2582Coded := by decide +kernel
theorem atom2582Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (889361525606400 : Int) atom2582Coded) := by
  have h := atom2582_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2582Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2583 : SparsePolynomial.Poly := [([20,21,23], 1)]
theorem eval_atom2583 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2583 = ((g 20) * (g 21) * (g 23)) := by
  norm_num [atom2583, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2583_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (631236611174400 : Int) atom2583) := by
  rw [SparsePolynomial.eval_scale, eval_atom2583]
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 20) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2583Coded : CoefficientMerge.Poly := [(12047, 1)]
theorem atom2583Coded_decode : atom2583 = SparsePolynomial.decodeCubic 24 atom2583Coded := by decide +kernel
theorem atom2583Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (631236611174400 : Int) atom2583Coded) := by
  have h := atom2583_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2583Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2584 : SparsePolynomial.Poly := [([20,22,22], 1)]
theorem eval_atom2584 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2584 = ((g 20) * (g 22) * (g 22)) := by
  norm_num [atom2584, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2584_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (461518207416000 : Int) atom2584) := by
  rw [SparsePolynomial.eval_scale, eval_atom2584]
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 20) * (g 22) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2584Coded : CoefficientMerge.Poly := [(12070, 1)]
theorem atom2584Coded_decode : atom2584 = SparsePolynomial.decodeCubic 24 atom2584Coded := by decide +kernel
theorem atom2584Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (461518207416000 : Int) atom2584Coded) := by
  have h := atom2584_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2584Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2585 : SparsePolynomial.Poly := [([20,22,23], 1)]
theorem eval_atom2585 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2585 = ((g 20) * (g 22) * (g 23)) := by
  norm_num [atom2585, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2585_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (671988157747200 : Int) atom2585) := by
  rw [SparsePolynomial.eval_scale, eval_atom2585]
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 20) * (g 22) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2585Coded : CoefficientMerge.Poly := [(12071, 1)]
theorem atom2585Coded_decode : atom2585 = SparsePolynomial.decodeCubic 24 atom2585Coded := by decide +kernel
theorem atom2585Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (671988157747200 : Int) atom2585Coded) := by
  have h := atom2585_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2585Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2586 : SparsePolynomial.Poly := [([20,23,23], 1)]
theorem eval_atom2586 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2586 = ((g 20) * (g 23) * (g 23)) := by
  norm_num [atom2586, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2586_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (176052248064000 : Int) atom2586) := by
  rw [SparsePolynomial.eval_scale, eval_atom2586]
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 20) * (g 23) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2586Coded : CoefficientMerge.Poly := [(12095, 1)]
theorem atom2586Coded_decode : atom2586 = SparsePolynomial.decodeCubic 24 atom2586Coded := by decide +kernel
theorem atom2586Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (176052248064000 : Int) atom2586Coded) := by
  have h := atom2586_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2586Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2587 : SparsePolynomial.Poly := [([21,21,21], 1)]
theorem eval_atom2587 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2587 = ((g 21) * (g 21) * (g 21)) := by
  norm_num [atom2587, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2587_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (142457736960000 : Int) atom2587) := by
  rw [SparsePolynomial.eval_scale, eval_atom2587]
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 21) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2587Coded : CoefficientMerge.Poly := [(12621, 1)]
theorem atom2587Coded_decode : atom2587 = SparsePolynomial.decodeCubic 24 atom2587Coded := by decide +kernel
theorem atom2587Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (142457736960000 : Int) atom2587Coded) := by
  have h := atom2587_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2587Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2588 : SparsePolynomial.Poly := [([21,21,22], 1)]
theorem eval_atom2588 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2588 = ((g 21) * (g 21) * (g 22)) := by
  norm_num [atom2588, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2588_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (462137151168000 : Int) atom2588) := by
  rw [SparsePolynomial.eval_scale, eval_atom2588]
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 21) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2588Coded : CoefficientMerge.Poly := [(12622, 1)]
theorem atom2588Coded_decode : atom2588 = SparsePolynomial.decodeCubic 24 atom2588Coded := by decide +kernel
theorem atom2588Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (462137151168000 : Int) atom2588Coded) := by
  have h := atom2588_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2588Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2589 : SparsePolynomial.Poly := [([21,21,23], 1)]
theorem eval_atom2589 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2589 = ((g 21) * (g 21) * (g 23)) := by
  norm_num [atom2589, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2589_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (340707877171200 : Int) atom2589) := by
  rw [SparsePolynomial.eval_scale, eval_atom2589]
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 21) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2589Coded : CoefficientMerge.Poly := [(12623, 1)]
theorem atom2589Coded_decode : atom2589 = SparsePolynomial.decodeCubic 24 atom2589Coded := by decide +kernel
theorem atom2589Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (340707877171200 : Int) atom2589Coded) := by
  have h := atom2589_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2589Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2590 : SparsePolynomial.Poly := [([21,22,22], 1)]
theorem eval_atom2590 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2590 = ((g 21) * (g 22) * (g 22)) := by
  norm_num [atom2590, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2590_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (483215266548000 : Int) atom2590) := by
  rw [SparsePolynomial.eval_scale, eval_atom2590]
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 21) * (g 22) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2590Coded : CoefficientMerge.Poly := [(12646, 1)]
theorem atom2590Coded_decode : atom2590 = SparsePolynomial.decodeCubic 24 atom2590Coded := by decide +kernel
theorem atom2590Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (483215266548000 : Int) atom2590Coded) := by
  have h := atom2590_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2590Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2591 : SparsePolynomial.Poly := [([21,22,23], 1)]
theorem eval_atom2591 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2591 = ((g 21) * (g 22) * (g 23)) := by
  norm_num [atom2591, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2591_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (732288178944000 : Int) atom2591) := by
  rw [SparsePolynomial.eval_scale, eval_atom2591]
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 21) * (g 22) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2591Coded : CoefficientMerge.Poly := [(12647, 1)]
theorem atom2591Coded_decode : atom2591 = SparsePolynomial.decodeCubic 24 atom2591Coded := by decide +kernel
theorem atom2591Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (732288178944000 : Int) atom2591Coded) := by
  have h := atom2591_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2591Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2592 : SparsePolynomial.Poly := [([21,23,23], 1)]
theorem eval_atom2592 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2592 = ((g 21) * (g 23) * (g 23)) := by
  norm_num [atom2592, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2592_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (211262697676800 : Int) atom2592) := by
  rw [SparsePolynomial.eval_scale, eval_atom2592]
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 21) * (g 23) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2592Coded : CoefficientMerge.Poly := [(12671, 1)]
theorem atom2592Coded_decode : atom2592 = SparsePolynomial.decodeCubic 24 atom2592Coded := by decide +kernel
theorem atom2592Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (211262697676800 : Int) atom2592Coded) := by
  have h := atom2592_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2592Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2593 : SparsePolynomial.Poly := [([22,22,22], 1)]
theorem eval_atom2593 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2593 = ((g 22) * (g 22) * (g 22)) := by
  norm_num [atom2593, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2593_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (167478850224000 : Int) atom2593) := by
  rw [SparsePolynomial.eval_scale, eval_atom2593]
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 22) * (g 22) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2593Coded : CoefficientMerge.Poly := [(13222, 1)]
theorem atom2593Coded_decode : atom2593 = SparsePolynomial.decodeCubic 24 atom2593Coded := by decide +kernel
theorem atom2593Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (167478850224000 : Int) atom2593Coded) := by
  have h := atom2593_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2593Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2594 : SparsePolynomial.Poly := [([22,22,23], 1)]
theorem eval_atom2594 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2594 = ((g 22) * (g 22) * (g 23)) := by
  norm_num [atom2594, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2594_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (379428929838000 : Int) atom2594) := by
  rw [SparsePolynomial.eval_scale, eval_atom2594]
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 22) * (g 22) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2594Coded : CoefficientMerge.Poly := [(13223, 1)]
theorem atom2594Coded_decode : atom2594 = SparsePolynomial.decodeCubic 24 atom2594Coded := by decide +kernel
theorem atom2594Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (379428929838000 : Int) atom2594Coded) := by
  have h := atom2594_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2594Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2595 : SparsePolynomial.Poly := [([22,23,23], 1)]
theorem eval_atom2595 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2595 = ((g 22) * (g 23) * (g 23)) := by
  norm_num [atom2595, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2595_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (215528053708800 : Int) atom2595) := by
  rw [SparsePolynomial.eval_scale, eval_atom2595]
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 22) * (g 23) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2595Coded : CoefficientMerge.Poly := [(13247, 1)]
theorem atom2595Coded_decode : atom2595 = SparsePolynomial.decodeCubic 24 atom2595Coded := by decide +kernel
theorem atom2595Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (215528053708800 : Int) atom2595Coded) := by
  have h := atom2595_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2595Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block034 : CoefficientMerge.Poly := [(10269, 636169476096000), (10270, 597975854515200), (10271, 820556564889600), (10292, 368221356518400), (10293, 781603941888000), (10294, 761659858713600), (10295, 841818913689600), (10317, 357887855001600), (10318, 784623195417600), (10319, 883152919756800), (10342, 397355445648000), (10343, 924486925824000), (10367, 472874637312000), (10818, 10354763865600), (10819, 76586980377600), (10820, 262951467609600), (10821, 308474156390400), (10822, 220891320115200), (10823, 399519533952000), (10843, 72104877250560), (10844, 519184032998400), (10845, 700041571891200), (10846, 614688060672000), (10847, 850493952000000), (10868, 397074363840000), (10869, 853555730227200), (10870, 787472350156800), (10871, 761107037644800), (10893, 397903595443200), (10894, 819535972147200), (10895, 812561921740800), (10918, 418743032904000), (10919, 863774543923200), (10943, 387314945740800), (11420, 185526750689280), (11421, 315329137643520), (11422, 309576576960000), (11423, 429193267937280), (11444, 325313936640000), (11445, 794701548748800), (11446, 813284841600000), (11447, 801165302784000), (11469, 407726800588800), (11470, 854448748876800), (11471, 862741064908800), (11494, 440130620160000), (11495, 924074565120000), (11519, 422525395353600), (12020, 131465102630400), (12021, 403134133248000), (12022, 419548666521600), (12023, 279769985510400), (12045, 417550005734400), (12046, 889361525606400), (12047, 631236611174400), (12070, 461518207416000), (12071, 671988157747200), (12095, 176052248064000), (12621, 142457736960000), (12622, 462137151168000), (12623, 340707877171200), (12646, 483215266548000), (12647, 732288178944000), (12671, 211262697676800), (13222, 167478850224000), (13223, 379428929838000), (13247, 215528053708800)]
theorem block034_data : block034 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (636169476096000 : Int) atom2529Coded) (CoefficientMerge.scale (597975854515200 : Int) atom2530Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (820556564889600 : Int) atom2531Coded) (CoefficientMerge.scale (368221356518400 : Int) atom2532Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (781603941888000 : Int) atom2533Coded) (CoefficientMerge.scale (761659858713600 : Int) atom2534Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (841818913689600 : Int) atom2535Coded) (CoefficientMerge.scale (357887855001600 : Int) atom2536Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (784623195417600 : Int) atom2537Coded) (CoefficientMerge.scale (883152919756800 : Int) atom2538Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (397355445648000 : Int) atom2539Coded) (CoefficientMerge.scale (924486925824000 : Int) atom2540Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (472874637312000 : Int) atom2541Coded) (CoefficientMerge.scale (10354763865600 : Int) atom2542Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (76586980377600 : Int) atom2543Coded) (CoefficientMerge.scale (262951467609600 : Int) atom2544Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (308474156390400 : Int) atom2545Coded) (CoefficientMerge.scale (220891320115200 : Int) atom2546Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (399519533952000 : Int) atom2547Coded) (CoefficientMerge.scale (72104877250560 : Int) atom2548Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (519184032998400 : Int) atom2549Coded) (CoefficientMerge.scale (700041571891200 : Int) atom2550Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (614688060672000 : Int) atom2551Coded) (CoefficientMerge.scale (850493952000000 : Int) atom2552Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (397074363840000 : Int) atom2553Coded) (CoefficientMerge.scale (853555730227200 : Int) atom2554Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (787472350156800 : Int) atom2555Coded) (CoefficientMerge.scale (761107037644800 : Int) atom2556Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (397903595443200 : Int) atom2557Coded) (CoefficientMerge.scale (819535972147200 : Int) atom2558Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (812561921740800 : Int) atom2559Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (418743032904000 : Int) atom2560Coded) (CoefficientMerge.scale (863774543923200 : Int) atom2561Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (387314945740800 : Int) atom2562Coded) (CoefficientMerge.scale (185526750689280 : Int) atom2563Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (315329137643520 : Int) atom2564Coded) (CoefficientMerge.scale (309576576960000 : Int) atom2565Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (429193267937280 : Int) atom2566Coded) (CoefficientMerge.scale (325313936640000 : Int) atom2567Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (794701548748800 : Int) atom2568Coded) (CoefficientMerge.scale (813284841600000 : Int) atom2569Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (801165302784000 : Int) atom2570Coded) (CoefficientMerge.scale (407726800588800 : Int) atom2571Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (854448748876800 : Int) atom2572Coded) (CoefficientMerge.scale (862741064908800 : Int) atom2573Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (440130620160000 : Int) atom2574Coded) (CoefficientMerge.scale (924074565120000 : Int) atom2575Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (422525395353600 : Int) atom2576Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (131465102630400 : Int) atom2577Coded) (CoefficientMerge.scale (403134133248000 : Int) atom2578Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (419548666521600 : Int) atom2579Coded) (CoefficientMerge.scale (279769985510400 : Int) atom2580Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (417550005734400 : Int) atom2581Coded) (CoefficientMerge.scale (889361525606400 : Int) atom2582Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (631236611174400 : Int) atom2583Coded) (CoefficientMerge.scale (461518207416000 : Int) atom2584Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (671988157747200 : Int) atom2585Coded) (CoefficientMerge.scale (176052248064000 : Int) atom2586Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142457736960000 : Int) atom2587Coded) (CoefficientMerge.scale (462137151168000 : Int) atom2588Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (340707877171200 : Int) atom2589Coded) (CoefficientMerge.scale (483215266548000 : Int) atom2590Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (732288178944000 : Int) atom2591Coded) (CoefficientMerge.scale (211262697676800 : Int) atom2592Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (167478850224000 : Int) atom2593Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (379428929838000 : Int) atom2594Coded) (CoefficientMerge.scale (215528053708800 : Int) atom2595Coded)))))))) := by decide +kernel
theorem block034_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block034 := by
  rw [block034_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2529Coded_nonneg g hg hA hB) (atom2530Coded_nonneg g hg hA hB)) (add_nonneg (atom2531Coded_nonneg g hg hA hB) (atom2532Coded_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom2533Coded_nonneg g hg hA hB) (atom2534Coded_nonneg g hg hA hB)) (add_nonneg (atom2535Coded_nonneg g hg hA hB) (atom2536Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (add_nonneg (atom2537Coded_nonneg g hg hA hB) (atom2538Coded_nonneg g hg hA hB)) (add_nonneg (atom2539Coded_nonneg g hg hA hB) (atom2540Coded_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom2541Coded_nonneg g hg hA hB) (atom2542Coded_nonneg g hg hA hB)) (add_nonneg (atom2543Coded_nonneg g hg hA hB) (atom2544Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2545Coded_nonneg g hg hA hB) (atom2546Coded_nonneg g hg hA hB)) (add_nonneg (atom2547Coded_nonneg g hg hA hB) (atom2548Coded_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom2549Coded_nonneg g hg hA hB) (atom2550Coded_nonneg g hg hA hB)) (add_nonneg (atom2551Coded_nonneg g hg hA hB) (atom2552Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (add_nonneg (atom2553Coded_nonneg g hg hA hB) (atom2554Coded_nonneg g hg hA hB)) (add_nonneg (atom2555Coded_nonneg g hg hA hB) (atom2556Coded_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom2557Coded_nonneg g hg hA hB) (atom2558Coded_nonneg g hg hA hB)) (add_nonneg (atom2559Coded_nonneg g hg hA hB) (add_nonneg (atom2560Coded_nonneg g hg hA hB) (atom2561Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2562Coded_nonneg g hg hA hB) (atom2563Coded_nonneg g hg hA hB)) (add_nonneg (atom2564Coded_nonneg g hg hA hB) (atom2565Coded_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom2566Coded_nonneg g hg hA hB) (atom2567Coded_nonneg g hg hA hB)) (add_nonneg (atom2568Coded_nonneg g hg hA hB) (atom2569Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (add_nonneg (atom2570Coded_nonneg g hg hA hB) (atom2571Coded_nonneg g hg hA hB)) (add_nonneg (atom2572Coded_nonneg g hg hA hB) (atom2573Coded_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom2574Coded_nonneg g hg hA hB) (atom2575Coded_nonneg g hg hA hB)) (add_nonneg (atom2576Coded_nonneg g hg hA hB) (add_nonneg (atom2577Coded_nonneg g hg hA hB) (atom2578Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2579Coded_nonneg g hg hA hB) (atom2580Coded_nonneg g hg hA hB)) (add_nonneg (atom2581Coded_nonneg g hg hA hB) (atom2582Coded_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom2583Coded_nonneg g hg hA hB) (atom2584Coded_nonneg g hg hA hB)) (add_nonneg (atom2585Coded_nonneg g hg hA hB) (atom2586Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (add_nonneg (atom2587Coded_nonneg g hg hA hB) (atom2588Coded_nonneg g hg hA hB)) (add_nonneg (atom2589Coded_nonneg g hg hA hB) (atom2590Coded_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom2591Coded_nonneg g hg hA hB) (atom2592Coded_nonneg g hg hA hB)) (add_nonneg (atom2593Coded_nonneg g hg hA hB) (add_nonneg (atom2594Coded_nonneg g hg hA hB) (atom2595Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
