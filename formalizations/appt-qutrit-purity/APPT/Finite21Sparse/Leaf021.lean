import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom1536 : SparsePolynomial.Poly := [([10,12,17], 1)]
theorem eval_atom1536 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1536 = ((g 10) * (g 12) * (g 17)) := by
  norm_num [atom1536, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1536_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12235036884000 : Int) atom1536) := by
  rw [SparsePolynomial.eval_scale, eval_atom1536]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1536Coded : CoefficientMerge.Poly := [(4679, 1)]
theorem atom1536Coded_decode : atom1536 = SparsePolynomial.decodeCubic 21 atom1536Coded := by decide +kernel
theorem atom1536Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (12235036884000 : Int) atom1536Coded) := by
  have h := atom1536_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1536Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1537 : SparsePolynomial.Poly := [([10,12,18], 1)]
theorem eval_atom1537 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1537 = ((g 10) * (g 12) * (g 18)) := by
  norm_num [atom1537, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1537_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10060008291200 : Int) atom1537) := by
  rw [SparsePolynomial.eval_scale, eval_atom1537]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 10) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1537Coded : CoefficientMerge.Poly := [(4680, 1)]
theorem atom1537Coded_decode : atom1537 = SparsePolynomial.decodeCubic 21 atom1537Coded := by decide +kernel
theorem atom1537Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10060008291200 : Int) atom1537Coded) := by
  have h := atom1537_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1537Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1538 : SparsePolynomial.Poly := [([10,12,19], 1)]
theorem eval_atom1538 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1538 = ((g 10) * (g 12) * (g 19)) := by
  norm_num [atom1538, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1538_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19067301227520 : Int) atom1538) := by
  rw [SparsePolynomial.eval_scale, eval_atom1538]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 10) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1538Coded : CoefficientMerge.Poly := [(4681, 1)]
theorem atom1538Coded_decode : atom1538 = SparsePolynomial.decodeCubic 21 atom1538Coded := by decide +kernel
theorem atom1538Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19067301227520 : Int) atom1538Coded) := by
  have h := atom1538_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1538Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1539 : SparsePolynomial.Poly := [([10,12,20], 1)]
theorem eval_atom1539 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1539 = ((g 10) * (g 12) * (g 20)) := by
  norm_num [atom1539, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1539_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30545055374400 : Int) atom1539) := by
  rw [SparsePolynomial.eval_scale, eval_atom1539]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 10) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1539Coded : CoefficientMerge.Poly := [(4682, 1)]
theorem atom1539Coded_decode : atom1539 = SparsePolynomial.decodeCubic 21 atom1539Coded := by decide +kernel
theorem atom1539Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30545055374400 : Int) atom1539Coded) := by
  have h := atom1539_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1539Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1540 : SparsePolynomial.Poly := [([10,13,13], 1)]
theorem eval_atom1540 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1540 = ((g 10) * (g 13) * (g 13)) := by
  norm_num [atom1540, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1540_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3637196294400 : Int) atom1540) := by
  rw [SparsePolynomial.eval_scale, eval_atom1540]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 10) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1540Coded : CoefficientMerge.Poly := [(4696, 1)]
theorem atom1540Coded_decode : atom1540 = SparsePolynomial.decodeCubic 21 atom1540Coded := by decide +kernel
theorem atom1540Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3637196294400 : Int) atom1540Coded) := by
  have h := atom1540_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1540Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1541 : SparsePolynomial.Poly := [([10,13,14], 1)]
theorem eval_atom1541 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1541 = ((g 10) * (g 13) * (g 14)) := by
  norm_num [atom1541, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1541_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6880901068800 : Int) atom1541) := by
  rw [SparsePolynomial.eval_scale, eval_atom1541]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 10) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1541Coded : CoefficientMerge.Poly := [(4697, 1)]
theorem atom1541Coded_decode : atom1541 = SparsePolynomial.decodeCubic 21 atom1541Coded := by decide +kernel
theorem atom1541Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6880901068800 : Int) atom1541Coded) := by
  have h := atom1541_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1541Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1542 : SparsePolynomial.Poly := [([10,13,15], 1)]
theorem eval_atom1542 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1542 = ((g 10) * (g 13) * (g 15)) := by
  norm_num [atom1542, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1542_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8610848568000 : Int) atom1542) := by
  rw [SparsePolynomial.eval_scale, eval_atom1542]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 10) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1542Coded : CoefficientMerge.Poly := [(4698, 1)]
theorem atom1542Coded_decode : atom1542 = SparsePolynomial.decodeCubic 21 atom1542Coded := by decide +kernel
theorem atom1542Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8610848568000 : Int) atom1542Coded) := by
  have h := atom1542_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1542Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1543 : SparsePolynomial.Poly := [([10,13,16], 1)]
theorem eval_atom1543 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1543 = ((g 10) * (g 13) * (g 16)) := by
  norm_num [atom1543, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1543_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7226753652000 : Int) atom1543) := by
  rw [SparsePolynomial.eval_scale, eval_atom1543]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 10) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1543Coded : CoefficientMerge.Poly := [(4699, 1)]
theorem atom1543Coded_decode : atom1543 = SparsePolynomial.decodeCubic 21 atom1543Coded := by decide +kernel
theorem atom1543Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7226753652000 : Int) atom1543Coded) := by
  have h := atom1543_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1543Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1544 : SparsePolynomial.Poly := [([10,13,17], 1)]
theorem eval_atom1544 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1544 = ((g 10) * (g 13) * (g 17)) := by
  norm_num [atom1544, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1544_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24723029116800 : Int) atom1544) := by
  rw [SparsePolynomial.eval_scale, eval_atom1544]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1544Coded : CoefficientMerge.Poly := [(4700, 1)]
theorem atom1544Coded_decode : atom1544 = SparsePolynomial.decodeCubic 21 atom1544Coded := by decide +kernel
theorem atom1544Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24723029116800 : Int) atom1544Coded) := by
  have h := atom1544_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1544Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1545 : SparsePolynomial.Poly := [([10,13,18], 1)]
theorem eval_atom1545 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1545 = ((g 10) * (g 13) * (g 18)) := by
  norm_num [atom1545, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1545_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25487556040800 : Int) atom1545) := by
  rw [SparsePolynomial.eval_scale, eval_atom1545]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 10) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1545Coded : CoefficientMerge.Poly := [(4701, 1)]
theorem atom1545Coded_decode : atom1545 = SparsePolynomial.decodeCubic 21 atom1545Coded := by decide +kernel
theorem atom1545Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25487556040800 : Int) atom1545Coded) := by
  have h := atom1545_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1545Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1546 : SparsePolynomial.Poly := [([10,13,19], 1)]
theorem eval_atom1546 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1546 = ((g 10) * (g 13) * (g 19)) := by
  norm_num [atom1546, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1546_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29609621330400 : Int) atom1546) := by
  rw [SparsePolynomial.eval_scale, eval_atom1546]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 10) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1546Coded : CoefficientMerge.Poly := [(4702, 1)]
theorem atom1546Coded_decode : atom1546 = SparsePolynomial.decodeCubic 21 atom1546Coded := by decide +kernel
theorem atom1546Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (29609621330400 : Int) atom1546Coded) := by
  have h := atom1546_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1546Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1547 : SparsePolynomial.Poly := [([10,13,20], 1)]
theorem eval_atom1547 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1547 = ((g 10) * (g 13) * (g 20)) := by
  norm_num [atom1547, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1547_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48203677670400 : Int) atom1547) := by
  rw [SparsePolynomial.eval_scale, eval_atom1547]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 10) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1547Coded : CoefficientMerge.Poly := [(4703, 1)]
theorem atom1547Coded_decode : atom1547 = SparsePolynomial.decodeCubic 21 atom1547Coded := by decide +kernel
theorem atom1547Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (48203677670400 : Int) atom1547Coded) := by
  have h := atom1547_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1547Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1548 : SparsePolynomial.Poly := [([10,14,14], 1)]
theorem eval_atom1548 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1548 = ((g 10) * (g 14) * (g 14)) := by
  norm_num [atom1548, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1548_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7524616377600 : Int) atom1548) := by
  rw [SparsePolynomial.eval_scale, eval_atom1548]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 10) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1548Coded : CoefficientMerge.Poly := [(4718, 1)]
theorem atom1548Coded_decode : atom1548 = SparsePolynomial.decodeCubic 21 atom1548Coded := by decide +kernel
theorem atom1548Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7524616377600 : Int) atom1548Coded) := by
  have h := atom1548_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1548Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1549 : SparsePolynomial.Poly := [([10,14,15], 1)]
theorem eval_atom1549 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1549 = ((g 10) * (g 14) * (g 15)) := by
  norm_num [atom1549, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1549_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13837762108800 : Int) atom1549) := by
  rw [SparsePolynomial.eval_scale, eval_atom1549]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 10) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1549Coded : CoefficientMerge.Poly := [(4719, 1)]
theorem atom1549Coded_decode : atom1549 = SparsePolynomial.decodeCubic 21 atom1549Coded := by decide +kernel
theorem atom1549Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13837762108800 : Int) atom1549Coded) := by
  have h := atom1549_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1549Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1550 : SparsePolynomial.Poly := [([10,14,16], 1)]
theorem eval_atom1550 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1550 = ((g 10) * (g 14) * (g 16)) := by
  norm_num [atom1550, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1550_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14444665250400 : Int) atom1550) := by
  rw [SparsePolynomial.eval_scale, eval_atom1550]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 10) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1550Coded : CoefficientMerge.Poly := [(4720, 1)]
theorem atom1550Coded_decode : atom1550 = SparsePolynomial.decodeCubic 21 atom1550Coded := by decide +kernel
theorem atom1550Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14444665250400 : Int) atom1550Coded) := by
  have h := atom1550_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1550Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1551 : SparsePolynomial.Poly := [([10,14,17], 1)]
theorem eval_atom1551 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1551 = ((g 10) * (g 14) * (g 17)) := by
  norm_num [atom1551, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1551_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39514858588800 : Int) atom1551) := by
  rw [SparsePolynomial.eval_scale, eval_atom1551]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1551Coded : CoefficientMerge.Poly := [(4721, 1)]
theorem atom1551Coded_decode : atom1551 = SparsePolynomial.decodeCubic 21 atom1551Coded := by decide +kernel
theorem atom1551Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39514858588800 : Int) atom1551Coded) := by
  have h := atom1551_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1551Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1552 : SparsePolynomial.Poly := [([10,14,18], 1)]
theorem eval_atom1552 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1552 = ((g 10) * (g 14) * (g 18)) := by
  norm_num [atom1552, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1552_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43438294015200 : Int) atom1552) := by
  rw [SparsePolynomial.eval_scale, eval_atom1552]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 10) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1552Coded : CoefficientMerge.Poly := [(4722, 1)]
theorem atom1552Coded_decode : atom1552 = SparsePolynomial.decodeCubic 21 atom1552Coded := by decide +kernel
theorem atom1552Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (43438294015200 : Int) atom1552Coded) := by
  have h := atom1552_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1552Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1553 : SparsePolynomial.Poly := [([10,14,19], 1)]
theorem eval_atom1553 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1553 = ((g 10) * (g 14) * (g 19)) := by
  norm_num [atom1553, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1553_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44668852452000 : Int) atom1553) := by
  rw [SparsePolynomial.eval_scale, eval_atom1553]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 10) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1553Coded : CoefficientMerge.Poly := [(4723, 1)]
theorem atom1553Coded_decode : atom1553 = SparsePolynomial.decodeCubic 21 atom1553Coded := by decide +kernel
theorem atom1553Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (44668852452000 : Int) atom1553Coded) := by
  have h := atom1553_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1553Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1554 : SparsePolynomial.Poly := [([10,14,20], 1)]
theorem eval_atom1554 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1554 = ((g 10) * (g 14) * (g 20)) := by
  norm_num [atom1554, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1554_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (70445302603200 : Int) atom1554) := by
  rw [SparsePolynomial.eval_scale, eval_atom1554]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 10) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1554Coded : CoefficientMerge.Poly := [(4724, 1)]
theorem atom1554Coded_decode : atom1554 = SparsePolynomial.decodeCubic 21 atom1554Coded := by decide +kernel
theorem atom1554Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (70445302603200 : Int) atom1554Coded) := by
  have h := atom1554_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1554Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1555 : SparsePolynomial.Poly := [([10,15,15], 1)]
theorem eval_atom1555 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1555 = ((g 10) * (g 15) * (g 15)) := by
  norm_num [atom1555, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1555_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14207114880000 : Int) atom1555) := by
  rw [SparsePolynomial.eval_scale, eval_atom1555]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 10) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1555Coded : CoefficientMerge.Poly := [(4740, 1)]
theorem atom1555Coded_decode : atom1555 = SparsePolynomial.decodeCubic 21 atom1555Coded := by decide +kernel
theorem atom1555Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14207114880000 : Int) atom1555Coded) := by
  have h := atom1555_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1555Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1556 : SparsePolynomial.Poly := [([10,15,16], 1)]
theorem eval_atom1556 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1556 = ((g 10) * (g 15) * (g 16)) := by
  norm_num [atom1556, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1556_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31648905514800 : Int) atom1556) := by
  rw [SparsePolynomial.eval_scale, eval_atom1556]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 10) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1556Coded : CoefficientMerge.Poly := [(4741, 1)]
theorem atom1556Coded_decode : atom1556 = SparsePolynomial.decodeCubic 21 atom1556Coded := by decide +kernel
theorem atom1556Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31648905514800 : Int) atom1556Coded) := by
  have h := atom1556_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1556Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1557 : SparsePolynomial.Poly := [([10,15,17], 1)]
theorem eval_atom1557 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1557 = ((g 10) * (g 15) * (g 17)) := by
  norm_num [atom1557, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1557_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (63044385868800 : Int) atom1557) := by
  rw [SparsePolynomial.eval_scale, eval_atom1557]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1557Coded : CoefficientMerge.Poly := [(4742, 1)]
theorem atom1557Coded_decode : atom1557 = SparsePolynomial.decodeCubic 21 atom1557Coded := by decide +kernel
theorem atom1557Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (63044385868800 : Int) atom1557Coded) := by
  have h := atom1557_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1557Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1558 : SparsePolynomial.Poly := [([10,15,18], 1)]
theorem eval_atom1558 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1558 = ((g 10) * (g 15) * (g 18)) := by
  norm_num [atom1558, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1558_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (68251193312400 : Int) atom1558) := by
  rw [SparsePolynomial.eval_scale, eval_atom1558]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 10) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1558Coded : CoefficientMerge.Poly := [(4743, 1)]
theorem atom1558Coded_decode : atom1558 = SparsePolynomial.decodeCubic 21 atom1558Coded := by decide +kernel
theorem atom1558Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (68251193312400 : Int) atom1558Coded) := by
  have h := atom1558_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1558Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1559 : SparsePolynomial.Poly := [([10,15,19], 1)]
theorem eval_atom1559 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1559 = ((g 10) * (g 15) * (g 19)) := by
  norm_num [atom1559, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1559_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52704630997200 : Int) atom1559) := by
  rw [SparsePolynomial.eval_scale, eval_atom1559]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 10) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1559Coded : CoefficientMerge.Poly := [(4744, 1)]
theorem atom1559Coded_decode : atom1559 = SparsePolynomial.decodeCubic 21 atom1559Coded := by decide +kernel
theorem atom1559Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (52704630997200 : Int) atom1559Coded) := by
  have h := atom1559_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1559Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1560 : SparsePolynomial.Poly := [([10,15,20], 1)]
theorem eval_atom1560 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1560 = ((g 10) * (g 15) * (g 20)) := by
  norm_num [atom1560, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1560_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (84534447690000 : Int) atom1560) := by
  rw [SparsePolynomial.eval_scale, eval_atom1560]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 10) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1560Coded : CoefficientMerge.Poly := [(4745, 1)]
theorem atom1560Coded_decode : atom1560 = SparsePolynomial.decodeCubic 21 atom1560Coded := by decide +kernel
theorem atom1560Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (84534447690000 : Int) atom1560Coded) := by
  have h := atom1560_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1560Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1561 : SparsePolynomial.Poly := [([10,16,16], 1)]
theorem eval_atom1561 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1561 = ((g 10) * (g 16) * (g 16)) := by
  norm_num [atom1561, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1561_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13258427535360 : Int) atom1561) := by
  rw [SparsePolynomial.eval_scale, eval_atom1561]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 10) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1561Coded : CoefficientMerge.Poly := [(4762, 1)]
theorem atom1561Coded_decode : atom1561 = SparsePolynomial.decodeCubic 21 atom1561Coded := by decide +kernel
theorem atom1561Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13258427535360 : Int) atom1561Coded) := by
  have h := atom1561_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1561Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1562 : SparsePolynomial.Poly := [([10,16,17], 1)]
theorem eval_atom1562 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1562 = ((g 10) * (g 16) * (g 17)) := by
  norm_num [atom1562, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1562_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (55380479086800 : Int) atom1562) := by
  rw [SparsePolynomial.eval_scale, eval_atom1562]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1562Coded : CoefficientMerge.Poly := [(4763, 1)]
theorem atom1562Coded_decode : atom1562 = SparsePolynomial.decodeCubic 21 atom1562Coded := by decide +kernel
theorem atom1562Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (55380479086800 : Int) atom1562Coded) := by
  have h := atom1562_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1562Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1563 : SparsePolynomial.Poly := [([10,16,18], 1)]
theorem eval_atom1563 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1563 = ((g 10) * (g 16) * (g 18)) := by
  norm_num [atom1563, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1563_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (67640031660600 : Int) atom1563) := by
  rw [SparsePolynomial.eval_scale, eval_atom1563]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 10) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1563Coded : CoefficientMerge.Poly := [(4764, 1)]
theorem atom1563Coded_decode : atom1563 = SparsePolynomial.decodeCubic 21 atom1563Coded := by decide +kernel
theorem atom1563Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (67640031660600 : Int) atom1563Coded) := by
  have h := atom1563_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1563Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1564 : SparsePolynomial.Poly := [([10,16,19], 1)]
theorem eval_atom1564 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1564 = ((g 10) * (g 16) * (g 19)) := by
  norm_num [atom1564, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1564_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (51789484202400 : Int) atom1564) := by
  rw [SparsePolynomial.eval_scale, eval_atom1564]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 10) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1564Coded : CoefficientMerge.Poly := [(4765, 1)]
theorem atom1564Coded_decode : atom1564 = SparsePolynomial.decodeCubic 21 atom1564Coded := by decide +kernel
theorem atom1564Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (51789484202400 : Int) atom1564Coded) := by
  have h := atom1564_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1564Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1565 : SparsePolynomial.Poly := [([10,16,20], 1)]
theorem eval_atom1565 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1565 = ((g 10) * (g 16) * (g 20)) := by
  norm_num [atom1565, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1565_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (71505263913300 : Int) atom1565) := by
  rw [SparsePolynomial.eval_scale, eval_atom1565]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 10) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1565Coded : CoefficientMerge.Poly := [(4766, 1)]
theorem atom1565Coded_decode : atom1565 = SparsePolynomial.decodeCubic 21 atom1565Coded := by decide +kernel
theorem atom1565Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (71505263913300 : Int) atom1565Coded) := by
  have h := atom1565_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1565Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1566 : SparsePolynomial.Poly := [([10,17,17], 1)]
theorem eval_atom1566 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1566 = ((g 10) * (g 17) * (g 17)) := by
  norm_num [atom1566, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1566_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41806301644800 : Int) atom1566) := by
  rw [SparsePolynomial.eval_scale, eval_atom1566]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1566Coded : CoefficientMerge.Poly := [(4784, 1)]
theorem atom1566Coded_decode : atom1566 = SparsePolynomial.decodeCubic 21 atom1566Coded := by decide +kernel
theorem atom1566Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (41806301644800 : Int) atom1566Coded) := by
  have h := atom1566_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1566Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1567 : SparsePolynomial.Poly := [([10,17,18], 1)]
theorem eval_atom1567 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1567 = ((g 10) * (g 17) * (g 18)) := by
  norm_num [atom1567, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1567_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (79803065286000 : Int) atom1567) := by
  rw [SparsePolynomial.eval_scale, eval_atom1567]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 10) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1567Coded : CoefficientMerge.Poly := [(4785, 1)]
theorem atom1567Coded_decode : atom1567 = SparsePolynomial.decodeCubic 21 atom1567Coded := by decide +kernel
theorem atom1567Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (79803065286000 : Int) atom1567Coded) := by
  have h := atom1567_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1567Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1568 : SparsePolynomial.Poly := [([10,17,19], 1)]
theorem eval_atom1568 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1568 = ((g 10) * (g 17) * (g 19)) := by
  norm_num [atom1568, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1568_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (57575234833200 : Int) atom1568) := by
  rw [SparsePolynomial.eval_scale, eval_atom1568]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 10) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1568Coded : CoefficientMerge.Poly := [(4786, 1)]
theorem atom1568Coded_decode : atom1568 = SparsePolynomial.decodeCubic 21 atom1568Coded := by decide +kernel
theorem atom1568Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (57575234833200 : Int) atom1568Coded) := by
  have h := atom1568_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1568Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1569 : SparsePolynomial.Poly := [([10,17,20], 1)]
theorem eval_atom1569 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1569 = ((g 10) * (g 17) * (g 20)) := by
  norm_num [atom1569, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1569_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (64172281244400 : Int) atom1569) := by
  rw [SparsePolynomial.eval_scale, eval_atom1569]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 10) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1569Coded : CoefficientMerge.Poly := [(4787, 1)]
theorem atom1569Coded_decode : atom1569 = SparsePolynomial.decodeCubic 21 atom1569Coded := by decide +kernel
theorem atom1569Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (64172281244400 : Int) atom1569Coded) := by
  have h := atom1569_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1569Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1570 : SparsePolynomial.Poly := [([10,18,18], 1)]
theorem eval_atom1570 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1570 = ((g 10) * (g 18) * (g 18)) := by
  norm_num [atom1570, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1570_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32379144373800 : Int) atom1570) := by
  rw [SparsePolynomial.eval_scale, eval_atom1570]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 10) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1570Coded : CoefficientMerge.Poly := [(4806, 1)]
theorem atom1570Coded_decode : atom1570 = SparsePolynomial.decodeCubic 21 atom1570Coded := by decide +kernel
theorem atom1570Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32379144373800 : Int) atom1570Coded) := by
  have h := atom1570_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1570Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1571 : SparsePolynomial.Poly := [([10,18,19], 1)]
theorem eval_atom1571 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1571 = ((g 10) * (g 18) * (g 19)) := by
  norm_num [atom1571, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1571_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46613159346600 : Int) atom1571) := by
  rw [SparsePolynomial.eval_scale, eval_atom1571]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 10) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1571Coded : CoefficientMerge.Poly := [(4807, 1)]
theorem atom1571Coded_decode : atom1571 = SparsePolynomial.decodeCubic 21 atom1571Coded := by decide +kernel
theorem atom1571Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (46613159346600 : Int) atom1571Coded) := by
  have h := atom1571_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1571Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1572 : SparsePolynomial.Poly := [([10,18,20], 1)]
theorem eval_atom1572 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1572 = ((g 10) * (g 18) * (g 20)) := by
  norm_num [atom1572, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1572_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (56384774100900 : Int) atom1572) := by
  rw [SparsePolynomial.eval_scale, eval_atom1572]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 10) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1572Coded : CoefficientMerge.Poly := [(4808, 1)]
theorem atom1572Coded_decode : atom1572 = SparsePolynomial.decodeCubic 21 atom1572Coded := by decide +kernel
theorem atom1572Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (56384774100900 : Int) atom1572Coded) := by
  have h := atom1572_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1572Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1573 : SparsePolynomial.Poly := [([10,19,19], 1)]
theorem eval_atom1573 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1573 = ((g 10) * (g 19) * (g 19)) := by
  norm_num [atom1573, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1573_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9434482696800 : Int) atom1573) := by
  rw [SparsePolynomial.eval_scale, eval_atom1573]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 10) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1573Coded : CoefficientMerge.Poly := [(4828, 1)]
theorem atom1573Coded_decode : atom1573 = SparsePolynomial.decodeCubic 21 atom1573Coded := by decide +kernel
theorem atom1573Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (9434482696800 : Int) atom1573Coded) := by
  have h := atom1573_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1573Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1574 : SparsePolynomial.Poly := [([10,19,20], 1)]
theorem eval_atom1574 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1574 = ((g 10) * (g 19) * (g 20)) := by
  norm_num [atom1574, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1574_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29846674802700 : Int) atom1574) := by
  rw [SparsePolynomial.eval_scale, eval_atom1574]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 10) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1574Coded : CoefficientMerge.Poly := [(4829, 1)]
theorem atom1574Coded_decode : atom1574 = SparsePolynomial.decodeCubic 21 atom1574Coded := by decide +kernel
theorem atom1574Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (29846674802700 : Int) atom1574Coded) := by
  have h := atom1574_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1574Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1575 : SparsePolynomial.Poly := [([10,20,20], 1)]
theorem eval_atom1575 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1575 = ((g 10) * (g 20) * (g 20)) := by
  norm_num [atom1575, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1575_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16605245065500 : Int) atom1575) := by
  rw [SparsePolynomial.eval_scale, eval_atom1575]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 10) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1575Coded : CoefficientMerge.Poly := [(4850, 1)]
theorem atom1575Coded_decode : atom1575 = SparsePolynomial.decodeCubic 21 atom1575Coded := by decide +kernel
theorem atom1575Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16605245065500 : Int) atom1575Coded) := by
  have h := atom1575_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1575Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1576 : SparsePolynomial.Poly := [([11,11,11], 1)]
theorem eval_atom1576 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1576 = ((g 11) * (g 11) * (g 11)) := by
  norm_num [atom1576, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1576_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (625628505600 : Int) atom1576) := by
  rw [SparsePolynomial.eval_scale, eval_atom1576]
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 11) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1576Coded : CoefficientMerge.Poly := [(5093, 1)]
theorem atom1576Coded_decode : atom1576 = SparsePolynomial.decodeCubic 21 atom1576Coded := by decide +kernel
theorem atom1576Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (625628505600 : Int) atom1576Coded) := by
  have h := atom1576_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1576Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1577 : SparsePolynomial.Poly := [([11,11,15], 1)]
theorem eval_atom1577 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1577 = ((g 11) * (g 11) * (g 15)) := by
  norm_num [atom1577, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1577_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3027061094400 : Int) atom1577) := by
  rw [SparsePolynomial.eval_scale, eval_atom1577]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 11) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1577Coded : CoefficientMerge.Poly := [(5097, 1)]
theorem atom1577Coded_decode : atom1577 = SparsePolynomial.decodeCubic 21 atom1577Coded := by decide +kernel
theorem atom1577Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3027061094400 : Int) atom1577Coded) := by
  have h := atom1577_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1577Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1578 : SparsePolynomial.Poly := [([11,11,17], 1)]
theorem eval_atom1578 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1578 = ((g 11) * (g 11) * (g 17)) := by
  norm_num [atom1578, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1578_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4622441241600 : Int) atom1578) := by
  rw [SparsePolynomial.eval_scale, eval_atom1578]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1578Coded : CoefficientMerge.Poly := [(5099, 1)]
theorem atom1578Coded_decode : atom1578 = SparsePolynomial.decodeCubic 21 atom1578Coded := by decide +kernel
theorem atom1578Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (4622441241600 : Int) atom1578Coded) := by
  have h := atom1578_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1578Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1579 : SparsePolynomial.Poly := [([11,12,14], 1)]
theorem eval_atom1579 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1579 = ((g 11) * (g 12) * (g 14)) := by
  norm_num [atom1579, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1579_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (427179916800 : Int) atom1579) := by
  rw [SparsePolynomial.eval_scale, eval_atom1579]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 11) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1579Coded : CoefficientMerge.Poly := [(5117, 1)]
theorem atom1579Coded_decode : atom1579 = SparsePolynomial.decodeCubic 21 atom1579Coded := by decide +kernel
theorem atom1579Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (427179916800 : Int) atom1579Coded) := by
  have h := atom1579_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1579Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1580 : SparsePolynomial.Poly := [([11,12,15], 1)]
theorem eval_atom1580 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1580 = ((g 11) * (g 12) * (g 15)) := by
  norm_num [atom1580, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1580_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2412192625920 : Int) atom1580) := by
  rw [SparsePolynomial.eval_scale, eval_atom1580]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 11) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1580Coded : CoefficientMerge.Poly := [(5118, 1)]
theorem atom1580Coded_decode : atom1580 = SparsePolynomial.decodeCubic 21 atom1580Coded := by decide +kernel
theorem atom1580Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2412192625920 : Int) atom1580Coded) := by
  have h := atom1580_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1580Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1581 : SparsePolynomial.Poly := [([11,12,17], 1)]
theorem eval_atom1581 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1581 = ((g 11) * (g 12) * (g 17)) := by
  norm_num [atom1581, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1581_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12512392569600 : Int) atom1581) := by
  rw [SparsePolynomial.eval_scale, eval_atom1581]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1581Coded : CoefficientMerge.Poly := [(5120, 1)]
theorem atom1581Coded_decode : atom1581 = SparsePolynomial.decodeCubic 21 atom1581Coded := by decide +kernel
theorem atom1581Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (12512392569600 : Int) atom1581Coded) := by
  have h := atom1581_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1581Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1582 : SparsePolynomial.Poly := [([11,12,18], 1)]
theorem eval_atom1582 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1582 = ((g 11) * (g 12) * (g 18)) := by
  norm_num [atom1582, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1582_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6764344227200 : Int) atom1582) := by
  rw [SparsePolynomial.eval_scale, eval_atom1582]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 11) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1582Coded : CoefficientMerge.Poly := [(5121, 1)]
theorem atom1582Coded_decode : atom1582 = SparsePolynomial.decodeCubic 21 atom1582Coded := by decide +kernel
theorem atom1582Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6764344227200 : Int) atom1582Coded) := by
  have h := atom1582_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1582Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1583 : SparsePolynomial.Poly := [([11,12,19], 1)]
theorem eval_atom1583 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1583 = ((g 11) * (g 12) * (g 19)) := by
  norm_num [atom1583, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1583_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11598417976320 : Int) atom1583) := by
  rw [SparsePolynomial.eval_scale, eval_atom1583]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 11) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1583Coded : CoefficientMerge.Poly := [(5122, 1)]
theorem atom1583Coded_decode : atom1583 = SparsePolynomial.decodeCubic 21 atom1583Coded := by decide +kernel
theorem atom1583Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11598417976320 : Int) atom1583Coded) := by
  have h := atom1583_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1583Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1584 : SparsePolynomial.Poly := [([11,12,20], 1)]
theorem eval_atom1584 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1584 = ((g 11) * (g 12) * (g 20)) := by
  norm_num [atom1584, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1584_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17871729019200 : Int) atom1584) := by
  rw [SparsePolynomial.eval_scale, eval_atom1584]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 11) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1584Coded : CoefficientMerge.Poly := [(5123, 1)]
theorem atom1584Coded_decode : atom1584 = SparsePolynomial.decodeCubic 21 atom1584Coded := by decide +kernel
theorem atom1584Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17871729019200 : Int) atom1584Coded) := by
  have h := atom1584_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1584Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1585 : SparsePolynomial.Poly := [([11,13,13], 1)]
theorem eval_atom1585 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1585 = ((g 11) * (g 13) * (g 13)) := by
  norm_num [atom1585, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1585_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1585379635200 : Int) atom1585) := by
  rw [SparsePolynomial.eval_scale, eval_atom1585]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 11) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1585Coded : CoefficientMerge.Poly := [(5137, 1)]
theorem atom1585Coded_decode : atom1585 = SparsePolynomial.decodeCubic 21 atom1585Coded := by decide +kernel
theorem atom1585Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1585379635200 : Int) atom1585Coded) := by
  have h := atom1585_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1585Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1586 : SparsePolynomial.Poly := [([11,13,14], 1)]
theorem eval_atom1586 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1586 = ((g 11) * (g 13) * (g 14)) := by
  norm_num [atom1586, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1586_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2686419532800 : Int) atom1586) := by
  rw [SparsePolynomial.eval_scale, eval_atom1586]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 11) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1586Coded : CoefficientMerge.Poly := [(5138, 1)]
theorem atom1586Coded_decode : atom1586 = SparsePolynomial.decodeCubic 21 atom1586Coded := by decide +kernel
theorem atom1586Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2686419532800 : Int) atom1586Coded) := by
  have h := atom1586_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1586Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1587 : SparsePolynomial.Poly := [([11,13,15], 1)]
theorem eval_atom1587 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1587 = ((g 11) * (g 13) * (g 15)) := by
  norm_num [atom1587, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1587_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2932238030400 : Int) atom1587) := by
  rw [SparsePolynomial.eval_scale, eval_atom1587]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 11) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1587Coded : CoefficientMerge.Poly := [(5139, 1)]
theorem atom1587Coded_decode : atom1587 = SparsePolynomial.decodeCubic 21 atom1587Coded := by decide +kernel
theorem atom1587Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2932238030400 : Int) atom1587Coded) := by
  have h := atom1587_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1587Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1588 : SparsePolynomial.Poly := [([11,13,16], 1)]
theorem eval_atom1588 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1588 = ((g 11) * (g 13) * (g 16)) := by
  norm_num [atom1588, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1588_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (229178692800 : Int) atom1588) := by
  rw [SparsePolynomial.eval_scale, eval_atom1588]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 11) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1588Coded : CoefficientMerge.Poly := [(5140, 1)]
theorem atom1588Coded_decode : atom1588 = SparsePolynomial.decodeCubic 21 atom1588Coded := by decide +kernel
theorem atom1588Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (229178692800 : Int) atom1588Coded) := by
  have h := atom1588_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1588Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1589 : SparsePolynomial.Poly := [([11,13,17], 1)]
theorem eval_atom1589 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1589 = ((g 11) * (g 13) * (g 17)) := by
  norm_num [atom1589, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1589_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18882297907200 : Int) atom1589) := by
  rw [SparsePolynomial.eval_scale, eval_atom1589]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1589Coded : CoefficientMerge.Poly := [(5141, 1)]
theorem atom1589Coded_decode : atom1589 = SparsePolynomial.decodeCubic 21 atom1589Coded := by decide +kernel
theorem atom1589Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18882297907200 : Int) atom1589Coded) := by
  have h := atom1589_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1589Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1590 : SparsePolynomial.Poly := [([11,13,18], 1)]
theorem eval_atom1590 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1590 = ((g 11) * (g 13) * (g 18)) := by
  norm_num [atom1590, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1590_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16597632038400 : Int) atom1590) := by
  rw [SparsePolynomial.eval_scale, eval_atom1590]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 11) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1590Coded : CoefficientMerge.Poly := [(5142, 1)]
theorem atom1590Coded_decode : atom1590 = SparsePolynomial.decodeCubic 21 atom1590Coded := by decide +kernel
theorem atom1590Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16597632038400 : Int) atom1590Coded) := by
  have h := atom1590_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1590Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1591 : SparsePolynomial.Poly := [([11,13,19], 1)]
theorem eval_atom1591 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1591 = ((g 11) * (g 13) * (g 19)) := by
  norm_num [atom1591, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1591_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20194842312000 : Int) atom1591) := by
  rw [SparsePolynomial.eval_scale, eval_atom1591]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 11) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1591Coded : CoefficientMerge.Poly := [(5143, 1)]
theorem atom1591Coded_decode : atom1591 = SparsePolynomial.decodeCubic 21 atom1591Coded := by decide +kernel
theorem atom1591Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20194842312000 : Int) atom1591Coded) := by
  have h := atom1591_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1591Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1592 : SparsePolynomial.Poly := [([11,13,20], 1)]
theorem eval_atom1592 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1592 = ((g 11) * (g 13) * (g 20)) := by
  norm_num [atom1592, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1592_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38617257772800 : Int) atom1592) := by
  rw [SparsePolynomial.eval_scale, eval_atom1592]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 11) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1592Coded : CoefficientMerge.Poly := [(5144, 1)]
theorem atom1592Coded_decode : atom1592 = SparsePolynomial.decodeCubic 21 atom1592Coded := by decide +kernel
theorem atom1592Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (38617257772800 : Int) atom1592Coded) := by
  have h := atom1592_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1592Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1593 : SparsePolynomial.Poly := [([11,14,14], 1)]
theorem eval_atom1593 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1593 = ((g 11) * (g 14) * (g 14)) := by
  norm_num [atom1593, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1593_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4954771584000 : Int) atom1593) := by
  rw [SparsePolynomial.eval_scale, eval_atom1593]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 11) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1593Coded : CoefficientMerge.Poly := [(5159, 1)]
theorem atom1593Coded_decode : atom1593 = SparsePolynomial.decodeCubic 21 atom1593Coded := by decide +kernel
theorem atom1593Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (4954771584000 : Int) atom1593Coded) := by
  have h := atom1593_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1593Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1594 : SparsePolynomial.Poly := [([11,14,15], 1)]
theorem eval_atom1594 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1594 = ((g 11) * (g 14) * (g 15)) := by
  norm_num [atom1594, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1594_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8093431584000 : Int) atom1594) := by
  rw [SparsePolynomial.eval_scale, eval_atom1594]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 11) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1594Coded : CoefficientMerge.Poly := [(5160, 1)]
theorem atom1594Coded_decode : atom1594 = SparsePolynomial.decodeCubic 21 atom1594Coded := by decide +kernel
theorem atom1594Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8093431584000 : Int) atom1594Coded) := by
  have h := atom1594_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1594Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1595 : SparsePolynomial.Poly := [([11,14,16], 1)]
theorem eval_atom1595 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1595 = ((g 11) * (g 14) * (g 16)) := by
  norm_num [atom1595, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1595_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8260858368000 : Int) atom1595) := by
  rw [SparsePolynomial.eval_scale, eval_atom1595]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 11) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1595Coded : CoefficientMerge.Poly := [(5161, 1)]
theorem atom1595Coded_decode : atom1595 = SparsePolynomial.decodeCubic 21 atom1595Coded := by decide +kernel
theorem atom1595Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8260858368000 : Int) atom1595Coded) := by
  have h := atom1595_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1595Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1596 : SparsePolynomial.Poly := [([11,14,17], 1)]
theorem eval_atom1596 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1596 = ((g 11) * (g 14) * (g 17)) := by
  norm_num [atom1596, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1596_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35367383520000 : Int) atom1596) := by
  rw [SparsePolynomial.eval_scale, eval_atom1596]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1596Coded : CoefficientMerge.Poly := [(5162, 1)]
theorem atom1596Coded_decode : atom1596 = SparsePolynomial.decodeCubic 21 atom1596Coded := by decide +kernel
theorem atom1596Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35367383520000 : Int) atom1596Coded) := by
  have h := atom1596_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1596Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1597 : SparsePolynomial.Poly := [([11,14,18], 1)]
theorem eval_atom1597 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1597 = ((g 11) * (g 14) * (g 18)) := by
  norm_num [atom1597, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1597_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36765453110400 : Int) atom1597) := by
  rw [SparsePolynomial.eval_scale, eval_atom1597]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 11) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1597Coded : CoefficientMerge.Poly := [(5163, 1)]
theorem atom1597Coded_decode : atom1597 = SparsePolynomial.decodeCubic 21 atom1597Coded := by decide +kernel
theorem atom1597Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36765453110400 : Int) atom1597Coded) := by
  have h := atom1597_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1597Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1598 : SparsePolynomial.Poly := [([11,14,19], 1)]
theorem eval_atom1598 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1598 = ((g 11) * (g 14) * (g 19)) := by
  norm_num [atom1598, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1598_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37994983488000 : Int) atom1598) := by
  rw [SparsePolynomial.eval_scale, eval_atom1598]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 11) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1598Coded : CoefficientMerge.Poly := [(5164, 1)]
theorem atom1598Coded_decode : atom1598 = SparsePolynomial.decodeCubic 21 atom1598Coded := by decide +kernel
theorem atom1598Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (37994983488000 : Int) atom1598Coded) := by
  have h := atom1598_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1598Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1599 : SparsePolynomial.Poly := [([11,14,20], 1)]
theorem eval_atom1599 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1599 = ((g 11) * (g 14) * (g 20)) := by
  norm_num [atom1599, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1599_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (63945789163200 : Int) atom1599) := by
  rw [SparsePolynomial.eval_scale, eval_atom1599]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 11) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1599Coded : CoefficientMerge.Poly := [(5165, 1)]
theorem atom1599Coded_decode : atom1599 = SparsePolynomial.decodeCubic 21 atom1599Coded := by decide +kernel
theorem atom1599Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (63945789163200 : Int) atom1599Coded) := by
  have h := atom1599_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1599Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1600 : SparsePolynomial.Poly := [([11,15,15], 1)]
theorem eval_atom1600 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1600 = ((g 11) * (g 15) * (g 15)) := by
  norm_num [atom1600, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1600_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11306983564800 : Int) atom1600) := by
  rw [SparsePolynomial.eval_scale, eval_atom1600]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 11) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1600Coded : CoefficientMerge.Poly := [(5181, 1)]
theorem atom1600Coded_decode : atom1600 = SparsePolynomial.decodeCubic 21 atom1600Coded := by decide +kernel
theorem atom1600Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11306983564800 : Int) atom1600Coded) := by
  have h := atom1600_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1600Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1601 : SparsePolynomial.Poly := [([11,15,16], 1)]
theorem eval_atom1601 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1601 = ((g 11) * (g 15) * (g 16)) := by
  norm_num [atom1601, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1601_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26897818752000 : Int) atom1601) := by
  rw [SparsePolynomial.eval_scale, eval_atom1601]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 11) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1601Coded : CoefficientMerge.Poly := [(5182, 1)]
theorem atom1601Coded_decode : atom1601 = SparsePolynomial.decodeCubic 21 atom1601Coded := by decide +kernel
theorem atom1601Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (26897818752000 : Int) atom1601Coded) := by
  have h := atom1601_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1601Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1602 : SparsePolynomial.Poly := [([11,15,17], 1)]
theorem eval_atom1602 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1602 = ((g 11) * (g 15) * (g 17)) := by
  norm_num [atom1602, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1602_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (60580379059200 : Int) atom1602) := by
  rw [SparsePolynomial.eval_scale, eval_atom1602]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1602Coded : CoefficientMerge.Poly := [(5183, 1)]
theorem atom1602Coded_decode : atom1602 = SparsePolynomial.decodeCubic 21 atom1602Coded := by decide +kernel
theorem atom1602Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (60580379059200 : Int) atom1602Coded) := by
  have h := atom1602_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1602Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1603 : SparsePolynomial.Poly := [([11,15,18], 1)]
theorem eval_atom1603 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1603 = ((g 11) * (g 15) * (g 18)) := by
  norm_num [atom1603, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1603_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65618034048000 : Int) atom1603) := by
  rw [SparsePolynomial.eval_scale, eval_atom1603]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 11) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1603Coded : CoefficientMerge.Poly := [(5184, 1)]
theorem atom1603Coded_decode : atom1603 = SparsePolynomial.decodeCubic 21 atom1603Coded := by decide +kernel
theorem atom1603Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (65618034048000 : Int) atom1603Coded) := by
  have h := atom1603_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1603Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1604 : SparsePolynomial.Poly := [([11,15,19], 1)]
theorem eval_atom1604 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1604 = ((g 11) * (g 15) * (g 19)) := by
  norm_num [atom1604, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1604_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (51049231833600 : Int) atom1604) := by
  rw [SparsePolynomial.eval_scale, eval_atom1604]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 11) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1604Coded : CoefficientMerge.Poly := [(5185, 1)]
theorem atom1604Coded_decode : atom1604 = SparsePolynomial.decodeCubic 21 atom1604Coded := by decide +kernel
theorem atom1604Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (51049231833600 : Int) atom1604Coded) := by
  have h := atom1604_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1604Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1605 : SparsePolynomial.Poly := [([11,15,20], 1)]
theorem eval_atom1605 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1605 = ((g 11) * (g 15) * (g 20)) := by
  norm_num [atom1605, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1605_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (83972064960000 : Int) atom1605) := by
  rw [SparsePolynomial.eval_scale, eval_atom1605]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 11) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1605Coded : CoefficientMerge.Poly := [(5186, 1)]
theorem atom1605Coded_decode : atom1605 = SparsePolynomial.decodeCubic 21 atom1605Coded := by decide +kernel
theorem atom1605Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (83972064960000 : Int) atom1605Coded) := by
  have h := atom1605_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1605Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1606 : SparsePolynomial.Poly := [([11,16,16], 1)]
theorem eval_atom1606 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1606 = ((g 11) * (g 16) * (g 16)) := by
  norm_num [atom1606, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1606_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11599244213760 : Int) atom1606) := by
  rw [SparsePolynomial.eval_scale, eval_atom1606]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 11) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1606Coded : CoefficientMerge.Poly := [(5203, 1)]
theorem atom1606Coded_decode : atom1606 = SparsePolynomial.decodeCubic 21 atom1606Coded := by decide +kernel
theorem atom1606Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11599244213760 : Int) atom1606Coded) := by
  have h := atom1606_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1606Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1607 : SparsePolynomial.Poly := [([11,16,17], 1)]
theorem eval_atom1607 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1607 = ((g 11) * (g 16) * (g 17)) := by
  norm_num [atom1607, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1607_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (54517358246400 : Int) atom1607) := by
  rw [SparsePolynomial.eval_scale, eval_atom1607]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1607Coded : CoefficientMerge.Poly := [(5204, 1)]
theorem atom1607Coded_decode : atom1607 = SparsePolynomial.decodeCubic 21 atom1607Coded := by decide +kernel
theorem atom1607Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (54517358246400 : Int) atom1607Coded) := by
  have h := atom1607_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1607Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1608 : SparsePolynomial.Poly := [([11,16,18], 1)]
theorem eval_atom1608 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1608 = ((g 11) * (g 16) * (g 18)) := by
  norm_num [atom1608, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1608_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (68922680601600 : Int) atom1608) := by
  rw [SparsePolynomial.eval_scale, eval_atom1608]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 11) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1608Coded : CoefficientMerge.Poly := [(5205, 1)]
theorem atom1608Coded_decode : atom1608 = SparsePolynomial.decodeCubic 21 atom1608Coded := by decide +kernel
theorem atom1608Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (68922680601600 : Int) atom1608Coded) := by
  have h := atom1608_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1608Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1609 : SparsePolynomial.Poly := [([11,16,19], 1)]
theorem eval_atom1609 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1609 = ((g 11) * (g 16) * (g 19)) := by
  norm_num [atom1609, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1609_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (54987390259200 : Int) atom1609) := by
  rw [SparsePolynomial.eval_scale, eval_atom1609]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 11) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1609Coded : CoefficientMerge.Poly := [(5206, 1)]
theorem atom1609Coded_decode : atom1609 = SparsePolynomial.decodeCubic 21 atom1609Coded := by decide +kernel
theorem atom1609Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (54987390259200 : Int) atom1609Coded) := by
  have h := atom1609_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1609Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1610 : SparsePolynomial.Poly := [([11,16,20], 1)]
theorem eval_atom1610 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1610 = ((g 11) * (g 16) * (g 20)) := by
  norm_num [atom1610, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1610_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (76694201740800 : Int) atom1610) := by
  rw [SparsePolynomial.eval_scale, eval_atom1610]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 11) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1610Coded : CoefficientMerge.Poly := [(5207, 1)]
theorem atom1610Coded_decode : atom1610 = SparsePolynomial.decodeCubic 21 atom1610Coded := by decide +kernel
theorem atom1610Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (76694201740800 : Int) atom1610Coded) := by
  have h := atom1610_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1610Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1611 : SparsePolynomial.Poly := [([11,17,17], 1)]
theorem eval_atom1611 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1611 = ((g 11) * (g 17) * (g 17)) := by
  norm_num [atom1611, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1611_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41556232166400 : Int) atom1611) := by
  rw [SparsePolynomial.eval_scale, eval_atom1611]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1611Coded : CoefficientMerge.Poly := [(5225, 1)]
theorem atom1611Coded_decode : atom1611 = SparsePolynomial.decodeCubic 21 atom1611Coded := by decide +kernel
theorem atom1611Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (41556232166400 : Int) atom1611Coded) := by
  have h := atom1611_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1611Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1612 : SparsePolynomial.Poly := [([11,17,18], 1)]
theorem eval_atom1612 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1612 = ((g 11) * (g 17) * (g 18)) := by
  norm_num [atom1612, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1612_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (83144666304000 : Int) atom1612) := by
  rw [SparsePolynomial.eval_scale, eval_atom1612]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 11) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1612Coded : CoefficientMerge.Poly := [(5226, 1)]
theorem atom1612Coded_decode : atom1612 = SparsePolynomial.decodeCubic 21 atom1612Coded := by decide +kernel
theorem atom1612Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (83144666304000 : Int) atom1612Coded) := by
  have h := atom1612_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1612Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1613 : SparsePolynomial.Poly := [([11,17,19], 1)]
theorem eval_atom1613 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1613 = ((g 11) * (g 17) * (g 19)) := by
  norm_num [atom1613, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1613_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (63150637939200 : Int) atom1613) := by
  rw [SparsePolynomial.eval_scale, eval_atom1613]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 11) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1613Coded : CoefficientMerge.Poly := [(5227, 1)]
theorem atom1613Coded_decode : atom1613 = SparsePolynomial.decodeCubic 21 atom1613Coded := by decide +kernel
theorem atom1613Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (63150637939200 : Int) atom1613Coded) := by
  have h := atom1613_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1613Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1614 : SparsePolynomial.Poly := [([11,17,20], 1)]
theorem eval_atom1614 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1614 = ((g 11) * (g 17) * (g 20)) := by
  norm_num [atom1614, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1614_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (71866230105600 : Int) atom1614) := by
  rw [SparsePolynomial.eval_scale, eval_atom1614]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 11) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1614Coded : CoefficientMerge.Poly := [(5228, 1)]
theorem atom1614Coded_decode : atom1614 = SparsePolynomial.decodeCubic 21 atom1614Coded := by decide +kernel
theorem atom1614Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (71866230105600 : Int) atom1614Coded) := by
  have h := atom1614_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1614Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1615 : SparsePolynomial.Poly := [([11,18,18], 1)]
theorem eval_atom1615 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1615 = ((g 11) * (g 18) * (g 18)) := by
  norm_num [atom1615, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1615_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36462275136000 : Int) atom1615) := by
  rw [SparsePolynomial.eval_scale, eval_atom1615]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 11) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1615Coded : CoefficientMerge.Poly := [(5247, 1)]
theorem atom1615Coded_decode : atom1615 = SparsePolynomial.decodeCubic 21 atom1615Coded := by decide +kernel
theorem atom1615Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36462275136000 : Int) atom1615Coded) := by
  have h := atom1615_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1615Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block021 : CoefficientMerge.Poly := [(4679, 12235036884000), (4680, 10060008291200), (4681, 19067301227520), (4682, 30545055374400), (4696, 3637196294400), (4697, 6880901068800), (4698, 8610848568000), (4699, 7226753652000), (4700, 24723029116800), (4701, 25487556040800), (4702, 29609621330400), (4703, 48203677670400), (4718, 7524616377600), (4719, 13837762108800), (4720, 14444665250400), (4721, 39514858588800), (4722, 43438294015200), (4723, 44668852452000), (4724, 70445302603200), (4740, 14207114880000), (4741, 31648905514800), (4742, 63044385868800), (4743, 68251193312400), (4744, 52704630997200), (4745, 84534447690000), (4762, 13258427535360), (4763, 55380479086800), (4764, 67640031660600), (4765, 51789484202400), (4766, 71505263913300), (4784, 41806301644800), (4785, 79803065286000), (4786, 57575234833200), (4787, 64172281244400), (4806, 32379144373800), (4807, 46613159346600), (4808, 56384774100900), (4828, 9434482696800), (4829, 29846674802700), (4850, 16605245065500), (5093, 625628505600), (5097, 3027061094400), (5099, 4622441241600), (5117, 427179916800), (5118, 2412192625920), (5120, 12512392569600), (5121, 6764344227200), (5122, 11598417976320), (5123, 17871729019200), (5137, 1585379635200), (5138, 2686419532800), (5139, 2932238030400), (5140, 229178692800), (5141, 18882297907200), (5142, 16597632038400), (5143, 20194842312000), (5144, 38617257772800), (5159, 4954771584000), (5160, 8093431584000), (5161, 8260858368000), (5162, 35367383520000), (5163, 36765453110400), (5164, 37994983488000), (5165, 63945789163200), (5181, 11306983564800), (5182, 26897818752000), (5183, 60580379059200), (5184, 65618034048000), (5185, 51049231833600), (5186, 83972064960000), (5203, 11599244213760), (5204, 54517358246400), (5205, 68922680601600), (5206, 54987390259200), (5207, 76694201740800), (5225, 41556232166400), (5226, 83144666304000), (5227, 63150637939200), (5228, 71866230105600), (5247, 36462275136000)]
theorem block021_data : block021 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12235036884000 : Int) atom1536Coded) (CoefficientMerge.scale (10060008291200 : Int) atom1537Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19067301227520 : Int) atom1538Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30545055374400 : Int) atom1539Coded) (CoefficientMerge.scale (3637196294400 : Int) atom1540Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6880901068800 : Int) atom1541Coded) (CoefficientMerge.scale (8610848568000 : Int) atom1542Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7226753652000 : Int) atom1543Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24723029116800 : Int) atom1544Coded) (CoefficientMerge.scale (25487556040800 : Int) atom1545Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (29609621330400 : Int) atom1546Coded) (CoefficientMerge.scale (48203677670400 : Int) atom1547Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7524616377600 : Int) atom1548Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13837762108800 : Int) atom1549Coded) (CoefficientMerge.scale (14444665250400 : Int) atom1550Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39514858588800 : Int) atom1551Coded) (CoefficientMerge.scale (43438294015200 : Int) atom1552Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44668852452000 : Int) atom1553Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70445302603200 : Int) atom1554Coded) (CoefficientMerge.scale (14207114880000 : Int) atom1555Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31648905514800 : Int) atom1556Coded) (CoefficientMerge.scale (63044385868800 : Int) atom1557Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68251193312400 : Int) atom1558Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52704630997200 : Int) atom1559Coded) (CoefficientMerge.scale (84534447690000 : Int) atom1560Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13258427535360 : Int) atom1561Coded) (CoefficientMerge.scale (55380479086800 : Int) atom1562Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67640031660600 : Int) atom1563Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (51789484202400 : Int) atom1564Coded) (CoefficientMerge.scale (71505263913300 : Int) atom1565Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (41806301644800 : Int) atom1566Coded) (CoefficientMerge.scale (79803065286000 : Int) atom1567Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57575234833200 : Int) atom1568Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64172281244400 : Int) atom1569Coded) (CoefficientMerge.scale (32379144373800 : Int) atom1570Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46613159346600 : Int) atom1571Coded) (CoefficientMerge.scale (56384774100900 : Int) atom1572Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9434482696800 : Int) atom1573Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29846674802700 : Int) atom1574Coded) (CoefficientMerge.scale (16605245065500 : Int) atom1575Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (625628505600 : Int) atom1576Coded) (CoefficientMerge.scale (3027061094400 : Int) atom1577Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4622441241600 : Int) atom1578Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1579Coded) (CoefficientMerge.scale (2412192625920 : Int) atom1580Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12512392569600 : Int) atom1581Coded) (CoefficientMerge.scale (6764344227200 : Int) atom1582Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11598417976320 : Int) atom1583Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17871729019200 : Int) atom1584Coded) (CoefficientMerge.scale (1585379635200 : Int) atom1585Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2686419532800 : Int) atom1586Coded) (CoefficientMerge.scale (2932238030400 : Int) atom1587Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229178692800 : Int) atom1588Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18882297907200 : Int) atom1589Coded) (CoefficientMerge.scale (16597632038400 : Int) atom1590Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20194842312000 : Int) atom1591Coded) (CoefficientMerge.scale (38617257772800 : Int) atom1592Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4954771584000 : Int) atom1593Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8093431584000 : Int) atom1594Coded) (CoefficientMerge.scale (8260858368000 : Int) atom1595Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35367383520000 : Int) atom1596Coded) (CoefficientMerge.scale (36765453110400 : Int) atom1597Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37994983488000 : Int) atom1598Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (63945789163200 : Int) atom1599Coded) (CoefficientMerge.scale (11306983564800 : Int) atom1600Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26897818752000 : Int) atom1601Coded) (CoefficientMerge.scale (60580379059200 : Int) atom1602Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65618034048000 : Int) atom1603Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (51049231833600 : Int) atom1604Coded) (CoefficientMerge.scale (83972064960000 : Int) atom1605Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11599244213760 : Int) atom1606Coded) (CoefficientMerge.scale (54517358246400 : Int) atom1607Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68922680601600 : Int) atom1608Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54987390259200 : Int) atom1609Coded) (CoefficientMerge.scale (76694201740800 : Int) atom1610Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (41556232166400 : Int) atom1611Coded) (CoefficientMerge.scale (83144666304000 : Int) atom1612Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (63150637939200 : Int) atom1613Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (71866230105600 : Int) atom1614Coded) (CoefficientMerge.scale (36462275136000 : Int) atom1615Coded)))))))) := by decide +kernel
theorem block021_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) block021 := by
  rw [block021_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1536Coded_nonneg g hg hA hB) (atom1537Coded_nonneg g hg hA hB)) (add_nonneg (atom1538Coded_nonneg g hg hA hB) (add_nonneg (atom1539Coded_nonneg g hg hA hB) (atom1540Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1541Coded_nonneg g hg hA hB) (atom1542Coded_nonneg g hg hA hB)) (add_nonneg (atom1543Coded_nonneg g hg hA hB) (add_nonneg (atom1544Coded_nonneg g hg hA hB) (atom1545Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1546Coded_nonneg g hg hA hB) (atom1547Coded_nonneg g hg hA hB)) (add_nonneg (atom1548Coded_nonneg g hg hA hB) (add_nonneg (atom1549Coded_nonneg g hg hA hB) (atom1550Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1551Coded_nonneg g hg hA hB) (atom1552Coded_nonneg g hg hA hB)) (add_nonneg (atom1553Coded_nonneg g hg hA hB) (add_nonneg (atom1554Coded_nonneg g hg hA hB) (atom1555Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1556Coded_nonneg g hg hA hB) (atom1557Coded_nonneg g hg hA hB)) (add_nonneg (atom1558Coded_nonneg g hg hA hB) (add_nonneg (atom1559Coded_nonneg g hg hA hB) (atom1560Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1561Coded_nonneg g hg hA hB) (atom1562Coded_nonneg g hg hA hB)) (add_nonneg (atom1563Coded_nonneg g hg hA hB) (add_nonneg (atom1564Coded_nonneg g hg hA hB) (atom1565Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1566Coded_nonneg g hg hA hB) (atom1567Coded_nonneg g hg hA hB)) (add_nonneg (atom1568Coded_nonneg g hg hA hB) (add_nonneg (atom1569Coded_nonneg g hg hA hB) (atom1570Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1571Coded_nonneg g hg hA hB) (atom1572Coded_nonneg g hg hA hB)) (add_nonneg (atom1573Coded_nonneg g hg hA hB) (add_nonneg (atom1574Coded_nonneg g hg hA hB) (atom1575Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1576Coded_nonneg g hg hA hB) (atom1577Coded_nonneg g hg hA hB)) (add_nonneg (atom1578Coded_nonneg g hg hA hB) (add_nonneg (atom1579Coded_nonneg g hg hA hB) (atom1580Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1581Coded_nonneg g hg hA hB) (atom1582Coded_nonneg g hg hA hB)) (add_nonneg (atom1583Coded_nonneg g hg hA hB) (add_nonneg (atom1584Coded_nonneg g hg hA hB) (atom1585Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1586Coded_nonneg g hg hA hB) (atom1587Coded_nonneg g hg hA hB)) (add_nonneg (atom1588Coded_nonneg g hg hA hB) (add_nonneg (atom1589Coded_nonneg g hg hA hB) (atom1590Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1591Coded_nonneg g hg hA hB) (atom1592Coded_nonneg g hg hA hB)) (add_nonneg (atom1593Coded_nonneg g hg hA hB) (add_nonneg (atom1594Coded_nonneg g hg hA hB) (atom1595Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1596Coded_nonneg g hg hA hB) (atom1597Coded_nonneg g hg hA hB)) (add_nonneg (atom1598Coded_nonneg g hg hA hB) (add_nonneg (atom1599Coded_nonneg g hg hA hB) (atom1600Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1601Coded_nonneg g hg hA hB) (atom1602Coded_nonneg g hg hA hB)) (add_nonneg (atom1603Coded_nonneg g hg hA hB) (add_nonneg (atom1604Coded_nonneg g hg hA hB) (atom1605Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1606Coded_nonneg g hg hA hB) (atom1607Coded_nonneg g hg hA hB)) (add_nonneg (atom1608Coded_nonneg g hg hA hB) (add_nonneg (atom1609Coded_nonneg g hg hA hB) (atom1610Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1611Coded_nonneg g hg hA hB) (atom1612Coded_nonneg g hg hA hB)) (add_nonneg (atom1613Coded_nonneg g hg hA hB) (add_nonneg (atom1614Coded_nonneg g hg hA hB) (atom1615Coded_nonneg g hg hA hB))))))))

end APPT.Finite21
