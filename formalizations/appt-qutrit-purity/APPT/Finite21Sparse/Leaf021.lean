-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom1536 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 12, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1536Coded : CoefficientMerge.Poly := [(nat_lit 4679, Int.ofNat (nat_lit 1))]
theorem atom1536Coded_decode : atom1536 = SparsePolynomial.decodeCubic 21 atom1536Coded := by decide +kernel
theorem atom1536Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (12235036884000 : Int) atom1536Coded) := by
  have h := atom1536_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1536Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1537 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 12, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1537Coded : CoefficientMerge.Poly := [(nat_lit 4680, Int.ofNat (nat_lit 1))]
theorem atom1537Coded_decode : atom1537 = SparsePolynomial.decodeCubic 21 atom1537Coded := by decide +kernel
theorem atom1537Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10060008291200 : Int) atom1537Coded) := by
  have h := atom1537_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1537Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1538 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 12, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1538Coded : CoefficientMerge.Poly := [(nat_lit 4681, Int.ofNat (nat_lit 1))]
theorem atom1538Coded_decode : atom1538 = SparsePolynomial.decodeCubic 21 atom1538Coded := by decide +kernel
theorem atom1538Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19067301227520 : Int) atom1538Coded) := by
  have h := atom1538_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1538Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1539 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 12, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1539Coded : CoefficientMerge.Poly := [(nat_lit 4682, Int.ofNat (nat_lit 1))]
theorem atom1539Coded_decode : atom1539 = SparsePolynomial.decodeCubic 21 atom1539Coded := by decide +kernel
theorem atom1539Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30545055374400 : Int) atom1539Coded) := by
  have h := atom1539_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1539Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1540 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1540 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1540 = ((g 10) * (g 13) * (g 13)) := by
  norm_num [atom1540, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1540_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3637196294400 : Int) atom1540) := by
  rw [SparsePolynomial.eval_scale, eval_atom1540]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 10) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1540Coded : CoefficientMerge.Poly := [(nat_lit 4696, Int.ofNat (nat_lit 1))]
theorem atom1540Coded_decode : atom1540 = SparsePolynomial.decodeCubic 21 atom1540Coded := by decide +kernel
theorem atom1540Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3637196294400 : Int) atom1540Coded) := by
  have h := atom1540_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1540Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1541 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
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
def atom1541Coded : CoefficientMerge.Poly := [(nat_lit 4697, Int.ofNat (nat_lit 1))]
theorem atom1541Coded_decode : atom1541 = SparsePolynomial.decodeCubic 21 atom1541Coded := by decide +kernel
theorem atom1541Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6880901068800 : Int) atom1541Coded) := by
  have h := atom1541_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1541Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1542 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 13, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom1542Coded : CoefficientMerge.Poly := [(nat_lit 4698, Int.ofNat (nat_lit 1))]
theorem atom1542Coded_decode : atom1542 = SparsePolynomial.decodeCubic 21 atom1542Coded := by decide +kernel
theorem atom1542Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8610848568000 : Int) atom1542Coded) := by
  have h := atom1542_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1542Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1543 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 13, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom1543Coded : CoefficientMerge.Poly := [(nat_lit 4699, Int.ofNat (nat_lit 1))]
theorem atom1543Coded_decode : atom1543 = SparsePolynomial.decodeCubic 21 atom1543Coded := by decide +kernel
theorem atom1543Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7226753652000 : Int) atom1543Coded) := by
  have h := atom1543_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1543Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1544 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 13, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1544Coded : CoefficientMerge.Poly := [(nat_lit 4700, Int.ofNat (nat_lit 1))]
theorem atom1544Coded_decode : atom1544 = SparsePolynomial.decodeCubic 21 atom1544Coded := by decide +kernel
theorem atom1544Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24723029116800 : Int) atom1544Coded) := by
  have h := atom1544_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1544Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1545 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 13, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1545Coded : CoefficientMerge.Poly := [(nat_lit 4701, Int.ofNat (nat_lit 1))]
theorem atom1545Coded_decode : atom1545 = SparsePolynomial.decodeCubic 21 atom1545Coded := by decide +kernel
theorem atom1545Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25487556040800 : Int) atom1545Coded) := by
  have h := atom1545_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1545Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1546 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 13, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1546Coded : CoefficientMerge.Poly := [(nat_lit 4702, Int.ofNat (nat_lit 1))]
theorem atom1546Coded_decode : atom1546 = SparsePolynomial.decodeCubic 21 atom1546Coded := by decide +kernel
theorem atom1546Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (29609621330400 : Int) atom1546Coded) := by
  have h := atom1546_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1546Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1547 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 13, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1547Coded : CoefficientMerge.Poly := [(nat_lit 4703, Int.ofNat (nat_lit 1))]
theorem atom1547Coded_decode : atom1547 = SparsePolynomial.decodeCubic 21 atom1547Coded := by decide +kernel
theorem atom1547Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (48203677670400 : Int) atom1547Coded) := by
  have h := atom1547_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1547Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1548 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1548 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1548 = ((g 10) * (g 14) * (g 14)) := by
  norm_num [atom1548, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1548_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7524616377600 : Int) atom1548) := by
  rw [SparsePolynomial.eval_scale, eval_atom1548]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 10) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1548Coded : CoefficientMerge.Poly := [(nat_lit 4718, Int.ofNat (nat_lit 1))]
theorem atom1548Coded_decode : atom1548 = SparsePolynomial.decodeCubic 21 atom1548Coded := by decide +kernel
theorem atom1548Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7524616377600 : Int) atom1548Coded) := by
  have h := atom1548_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1548Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1549 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 14, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom1549Coded : CoefficientMerge.Poly := [(nat_lit 4719, Int.ofNat (nat_lit 1))]
theorem atom1549Coded_decode : atom1549 = SparsePolynomial.decodeCubic 21 atom1549Coded := by decide +kernel
theorem atom1549Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13837762108800 : Int) atom1549Coded) := by
  have h := atom1549_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1549Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1550 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 14, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom1550Coded : CoefficientMerge.Poly := [(nat_lit 4720, Int.ofNat (nat_lit 1))]
theorem atom1550Coded_decode : atom1550 = SparsePolynomial.decodeCubic 21 atom1550Coded := by decide +kernel
theorem atom1550Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14444665250400 : Int) atom1550Coded) := by
  have h := atom1550_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1550Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1551 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 14, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1551Coded : CoefficientMerge.Poly := [(nat_lit 4721, Int.ofNat (nat_lit 1))]
theorem atom1551Coded_decode : atom1551 = SparsePolynomial.decodeCubic 21 atom1551Coded := by decide +kernel
theorem atom1551Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39514858588800 : Int) atom1551Coded) := by
  have h := atom1551_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1551Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1552 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 14, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1552Coded : CoefficientMerge.Poly := [(nat_lit 4722, Int.ofNat (nat_lit 1))]
theorem atom1552Coded_decode : atom1552 = SparsePolynomial.decodeCubic 21 atom1552Coded := by decide +kernel
theorem atom1552Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (43438294015200 : Int) atom1552Coded) := by
  have h := atom1552_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1552Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1553 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 14, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1553Coded : CoefficientMerge.Poly := [(nat_lit 4723, Int.ofNat (nat_lit 1))]
theorem atom1553Coded_decode : atom1553 = SparsePolynomial.decodeCubic 21 atom1553Coded := by decide +kernel
theorem atom1553Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (44668852452000 : Int) atom1553Coded) := by
  have h := atom1553_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1553Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1554 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 14, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1554Coded : CoefficientMerge.Poly := [(nat_lit 4724, Int.ofNat (nat_lit 1))]
theorem atom1554Coded_decode : atom1554 = SparsePolynomial.decodeCubic 21 atom1554Coded := by decide +kernel
theorem atom1554Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (70445302603200 : Int) atom1554Coded) := by
  have h := atom1554_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1554Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1555 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1555 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1555 = ((g 10) * (g 15) * (g 15)) := by
  norm_num [atom1555, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1555_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14207114880000 : Int) atom1555) := by
  rw [SparsePolynomial.eval_scale, eval_atom1555]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 10) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1555Coded : CoefficientMerge.Poly := [(nat_lit 4740, Int.ofNat (nat_lit 1))]
theorem atom1555Coded_decode : atom1555 = SparsePolynomial.decodeCubic 21 atom1555Coded := by decide +kernel
theorem atom1555Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14207114880000 : Int) atom1555Coded) := by
  have h := atom1555_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1555Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1556 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 15, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom1556Coded : CoefficientMerge.Poly := [(nat_lit 4741, Int.ofNat (nat_lit 1))]
theorem atom1556Coded_decode : atom1556 = SparsePolynomial.decodeCubic 21 atom1556Coded := by decide +kernel
theorem atom1556Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31648905514800 : Int) atom1556Coded) := by
  have h := atom1556_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1556Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1557 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 15, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1557Coded : CoefficientMerge.Poly := [(nat_lit 4742, Int.ofNat (nat_lit 1))]
theorem atom1557Coded_decode : atom1557 = SparsePolynomial.decodeCubic 21 atom1557Coded := by decide +kernel
theorem atom1557Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (63044385868800 : Int) atom1557Coded) := by
  have h := atom1557_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1557Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1558 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 15, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1558Coded : CoefficientMerge.Poly := [(nat_lit 4743, Int.ofNat (nat_lit 1))]
theorem atom1558Coded_decode : atom1558 = SparsePolynomial.decodeCubic 21 atom1558Coded := by decide +kernel
theorem atom1558Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (68251193312400 : Int) atom1558Coded) := by
  have h := atom1558_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1558Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1559 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 15, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1559Coded : CoefficientMerge.Poly := [(nat_lit 4744, Int.ofNat (nat_lit 1))]
theorem atom1559Coded_decode : atom1559 = SparsePolynomial.decodeCubic 21 atom1559Coded := by decide +kernel
theorem atom1559Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (52704630997200 : Int) atom1559Coded) := by
  have h := atom1559_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1559Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1560 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 15, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1560Coded : CoefficientMerge.Poly := [(nat_lit 4745, Int.ofNat (nat_lit 1))]
theorem atom1560Coded_decode : atom1560 = SparsePolynomial.decodeCubic 21 atom1560Coded := by decide +kernel
theorem atom1560Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (84534447690000 : Int) atom1560Coded) := by
  have h := atom1560_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1560Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1561 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 16, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1561 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1561 = ((g 10) * (g 16) * (g 16)) := by
  norm_num [atom1561, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1561_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13258427535360 : Int) atom1561) := by
  rw [SparsePolynomial.eval_scale, eval_atom1561]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 10) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1561Coded : CoefficientMerge.Poly := [(nat_lit 4762, Int.ofNat (nat_lit 1))]
theorem atom1561Coded_decode : atom1561 = SparsePolynomial.decodeCubic 21 atom1561Coded := by decide +kernel
theorem atom1561Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13258427535360 : Int) atom1561Coded) := by
  have h := atom1561_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1561Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1562 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1562Coded : CoefficientMerge.Poly := [(nat_lit 4763, Int.ofNat (nat_lit 1))]
theorem atom1562Coded_decode : atom1562 = SparsePolynomial.decodeCubic 21 atom1562Coded := by decide +kernel
theorem atom1562Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (55380479086800 : Int) atom1562Coded) := by
  have h := atom1562_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1562Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1563 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 16, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1563Coded : CoefficientMerge.Poly := [(nat_lit 4764, Int.ofNat (nat_lit 1))]
theorem atom1563Coded_decode : atom1563 = SparsePolynomial.decodeCubic 21 atom1563Coded := by decide +kernel
theorem atom1563Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (67640031660600 : Int) atom1563Coded) := by
  have h := atom1563_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1563Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1564 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 16, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1564Coded : CoefficientMerge.Poly := [(nat_lit 4765, Int.ofNat (nat_lit 1))]
theorem atom1564Coded_decode : atom1564 = SparsePolynomial.decodeCubic 21 atom1564Coded := by decide +kernel
theorem atom1564Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (51789484202400 : Int) atom1564Coded) := by
  have h := atom1564_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1564Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1565 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 16, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1565Coded : CoefficientMerge.Poly := [(nat_lit 4766, Int.ofNat (nat_lit 1))]
theorem atom1565Coded_decode : atom1565 = SparsePolynomial.decodeCubic 21 atom1565Coded := by decide +kernel
theorem atom1565Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (71505263913300 : Int) atom1565Coded) := by
  have h := atom1565_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1565Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1566 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1566 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1566 = ((g 10) * (g 17) * (g 17)) := by
  norm_num [atom1566, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1566_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41806301644800 : Int) atom1566) := by
  rw [SparsePolynomial.eval_scale, eval_atom1566]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1566Coded : CoefficientMerge.Poly := [(nat_lit 4784, Int.ofNat (nat_lit 1))]
theorem atom1566Coded_decode : atom1566 = SparsePolynomial.decodeCubic 21 atom1566Coded := by decide +kernel
theorem atom1566Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (41806301644800 : Int) atom1566Coded) := by
  have h := atom1566_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1566Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1567 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 17, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1567Coded : CoefficientMerge.Poly := [(nat_lit 4785, Int.ofNat (nat_lit 1))]
theorem atom1567Coded_decode : atom1567 = SparsePolynomial.decodeCubic 21 atom1567Coded := by decide +kernel
theorem atom1567Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (79803065286000 : Int) atom1567Coded) := by
  have h := atom1567_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1567Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1568 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 17, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1568Coded : CoefficientMerge.Poly := [(nat_lit 4786, Int.ofNat (nat_lit 1))]
theorem atom1568Coded_decode : atom1568 = SparsePolynomial.decodeCubic 21 atom1568Coded := by decide +kernel
theorem atom1568Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (57575234833200 : Int) atom1568Coded) := by
  have h := atom1568_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1568Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1569 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 17, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1569Coded : CoefficientMerge.Poly := [(nat_lit 4787, Int.ofNat (nat_lit 1))]
theorem atom1569Coded_decode : atom1569 = SparsePolynomial.decodeCubic 21 atom1569Coded := by decide +kernel
theorem atom1569Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (64172281244400 : Int) atom1569Coded) := by
  have h := atom1569_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1569Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1570 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 18, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1570 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1570 = ((g 10) * (g 18) * (g 18)) := by
  norm_num [atom1570, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1570_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32379144373800 : Int) atom1570) := by
  rw [SparsePolynomial.eval_scale, eval_atom1570]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 10) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1570Coded : CoefficientMerge.Poly := [(nat_lit 4806, Int.ofNat (nat_lit 1))]
theorem atom1570Coded_decode : atom1570 = SparsePolynomial.decodeCubic 21 atom1570Coded := by decide +kernel
theorem atom1570Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32379144373800 : Int) atom1570Coded) := by
  have h := atom1570_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1570Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1571 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 18, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1571Coded : CoefficientMerge.Poly := [(nat_lit 4807, Int.ofNat (nat_lit 1))]
theorem atom1571Coded_decode : atom1571 = SparsePolynomial.decodeCubic 21 atom1571Coded := by decide +kernel
theorem atom1571Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (46613159346600 : Int) atom1571Coded) := by
  have h := atom1571_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1571Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1572 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 18, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1572Coded : CoefficientMerge.Poly := [(nat_lit 4808, Int.ofNat (nat_lit 1))]
theorem atom1572Coded_decode : atom1572 = SparsePolynomial.decodeCubic 21 atom1572Coded := by decide +kernel
theorem atom1572Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (56384774100900 : Int) atom1572Coded) := by
  have h := atom1572_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1572Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1573 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 19, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1573 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1573 = ((g 10) * (g 19) * (g 19)) := by
  norm_num [atom1573, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1573_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9434482696800 : Int) atom1573) := by
  rw [SparsePolynomial.eval_scale, eval_atom1573]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 10) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1573Coded : CoefficientMerge.Poly := [(nat_lit 4828, Int.ofNat (nat_lit 1))]
theorem atom1573Coded_decode : atom1573 = SparsePolynomial.decodeCubic 21 atom1573Coded := by decide +kernel
theorem atom1573Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (9434482696800 : Int) atom1573Coded) := by
  have h := atom1573_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1573Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1574 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 19, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1574Coded : CoefficientMerge.Poly := [(nat_lit 4829, Int.ofNat (nat_lit 1))]
theorem atom1574Coded_decode : atom1574 = SparsePolynomial.decodeCubic 21 atom1574Coded := by decide +kernel
theorem atom1574Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (29846674802700 : Int) atom1574Coded) := by
  have h := atom1574_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1574Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1575 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 20, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1575 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1575 = ((g 10) * (g 20) * (g 20)) := by
  norm_num [atom1575, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1575_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16605245065500 : Int) atom1575) := by
  rw [SparsePolynomial.eval_scale, eval_atom1575]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 10) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1575Coded : CoefficientMerge.Poly := [(nat_lit 4850, Int.ofNat (nat_lit 1))]
theorem atom1575Coded_decode : atom1575 = SparsePolynomial.decodeCubic 21 atom1575Coded := by decide +kernel
theorem atom1575Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16605245065500 : Int) atom1575Coded) := by
  have h := atom1575_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1575Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1576 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1576 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1576 = ((g 11) * (g 11) * (g 11)) := by
  norm_num [atom1576, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1576_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (625628505600 : Int) atom1576) := by
  rw [SparsePolynomial.eval_scale, eval_atom1576]
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 11) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1576Coded : CoefficientMerge.Poly := [(nat_lit 5093, Int.ofNat (nat_lit 1))]
theorem atom1576Coded_decode : atom1576 = SparsePolynomial.decodeCubic 21 atom1576Coded := by decide +kernel
theorem atom1576Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (625628505600 : Int) atom1576Coded) := by
  have h := atom1576_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1576Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1577 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 11, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1577 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1577 = ((g 11) * (g 11) * (g 15)) := by
  norm_num [atom1577, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1577_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3027061094400 : Int) atom1577) := by
  rw [SparsePolynomial.eval_scale, eval_atom1577]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 11) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1577Coded : CoefficientMerge.Poly := [(nat_lit 5097, Int.ofNat (nat_lit 1))]
theorem atom1577Coded_decode : atom1577 = SparsePolynomial.decodeCubic 21 atom1577Coded := by decide +kernel
theorem atom1577Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3027061094400 : Int) atom1577Coded) := by
  have h := atom1577_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1577Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1578 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 11, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1578 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1578 = ((g 11) * (g 11) * (g 17)) := by
  norm_num [atom1578, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1578_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4622441241600 : Int) atom1578) := by
  rw [SparsePolynomial.eval_scale, eval_atom1578]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1578Coded : CoefficientMerge.Poly := [(nat_lit 5099, Int.ofNat (nat_lit 1))]
theorem atom1578Coded_decode : atom1578 = SparsePolynomial.decodeCubic 21 atom1578Coded := by decide +kernel
theorem atom1578Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (4622441241600 : Int) atom1578Coded) := by
  have h := atom1578_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1578Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1579 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
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
def atom1579Coded : CoefficientMerge.Poly := [(nat_lit 5117, Int.ofNat (nat_lit 1))]
theorem atom1579Coded_decode : atom1579 = SparsePolynomial.decodeCubic 21 atom1579Coded := by decide +kernel
theorem atom1579Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (427179916800 : Int) atom1579Coded) := by
  have h := atom1579_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1579Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1580 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 12, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom1580Coded : CoefficientMerge.Poly := [(nat_lit 5118, Int.ofNat (nat_lit 1))]
theorem atom1580Coded_decode : atom1580 = SparsePolynomial.decodeCubic 21 atom1580Coded := by decide +kernel
theorem atom1580Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2412192625920 : Int) atom1580Coded) := by
  have h := atom1580_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1580Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1581 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 12, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1581Coded : CoefficientMerge.Poly := [(nat_lit 5120, Int.ofNat (nat_lit 1))]
theorem atom1581Coded_decode : atom1581 = SparsePolynomial.decodeCubic 21 atom1581Coded := by decide +kernel
theorem atom1581Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (12512392569600 : Int) atom1581Coded) := by
  have h := atom1581_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1581Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1582 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 12, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1582Coded : CoefficientMerge.Poly := [(nat_lit 5121, Int.ofNat (nat_lit 1))]
theorem atom1582Coded_decode : atom1582 = SparsePolynomial.decodeCubic 21 atom1582Coded := by decide +kernel
theorem atom1582Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6764344227200 : Int) atom1582Coded) := by
  have h := atom1582_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1582Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1583 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 12, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1583Coded : CoefficientMerge.Poly := [(nat_lit 5122, Int.ofNat (nat_lit 1))]
theorem atom1583Coded_decode : atom1583 = SparsePolynomial.decodeCubic 21 atom1583Coded := by decide +kernel
theorem atom1583Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11598417976320 : Int) atom1583Coded) := by
  have h := atom1583_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1583Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1584 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 12, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1584Coded : CoefficientMerge.Poly := [(nat_lit 5123, Int.ofNat (nat_lit 1))]
theorem atom1584Coded_decode : atom1584 = SparsePolynomial.decodeCubic 21 atom1584Coded := by decide +kernel
theorem atom1584Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17871729019200 : Int) atom1584Coded) := by
  have h := atom1584_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1584Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1585 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1585 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1585 = ((g 11) * (g 13) * (g 13)) := by
  norm_num [atom1585, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1585_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1585379635200 : Int) atom1585) := by
  rw [SparsePolynomial.eval_scale, eval_atom1585]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 11) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1585Coded : CoefficientMerge.Poly := [(nat_lit 5137, Int.ofNat (nat_lit 1))]
theorem atom1585Coded_decode : atom1585 = SparsePolynomial.decodeCubic 21 atom1585Coded := by decide +kernel
theorem atom1585Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1585379635200 : Int) atom1585Coded) := by
  have h := atom1585_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1585Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1586 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
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
def atom1586Coded : CoefficientMerge.Poly := [(nat_lit 5138, Int.ofNat (nat_lit 1))]
theorem atom1586Coded_decode : atom1586 = SparsePolynomial.decodeCubic 21 atom1586Coded := by decide +kernel
theorem atom1586Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2686419532800 : Int) atom1586Coded) := by
  have h := atom1586_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1586Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1587 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 13, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom1587Coded : CoefficientMerge.Poly := [(nat_lit 5139, Int.ofNat (nat_lit 1))]
theorem atom1587Coded_decode : atom1587 = SparsePolynomial.decodeCubic 21 atom1587Coded := by decide +kernel
theorem atom1587Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2932238030400 : Int) atom1587Coded) := by
  have h := atom1587_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1587Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1588 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 13, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom1588Coded : CoefficientMerge.Poly := [(nat_lit 5140, Int.ofNat (nat_lit 1))]
theorem atom1588Coded_decode : atom1588 = SparsePolynomial.decodeCubic 21 atom1588Coded := by decide +kernel
theorem atom1588Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (229178692800 : Int) atom1588Coded) := by
  have h := atom1588_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1588Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1589 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 13, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1589Coded : CoefficientMerge.Poly := [(nat_lit 5141, Int.ofNat (nat_lit 1))]
theorem atom1589Coded_decode : atom1589 = SparsePolynomial.decodeCubic 21 atom1589Coded := by decide +kernel
theorem atom1589Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18882297907200 : Int) atom1589Coded) := by
  have h := atom1589_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1589Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1590 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 13, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1590Coded : CoefficientMerge.Poly := [(nat_lit 5142, Int.ofNat (nat_lit 1))]
theorem atom1590Coded_decode : atom1590 = SparsePolynomial.decodeCubic 21 atom1590Coded := by decide +kernel
theorem atom1590Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16597632038400 : Int) atom1590Coded) := by
  have h := atom1590_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1590Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1591 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 13, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1591Coded : CoefficientMerge.Poly := [(nat_lit 5143, Int.ofNat (nat_lit 1))]
theorem atom1591Coded_decode : atom1591 = SparsePolynomial.decodeCubic 21 atom1591Coded := by decide +kernel
theorem atom1591Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20194842312000 : Int) atom1591Coded) := by
  have h := atom1591_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1591Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1592 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 13, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1592Coded : CoefficientMerge.Poly := [(nat_lit 5144, Int.ofNat (nat_lit 1))]
theorem atom1592Coded_decode : atom1592 = SparsePolynomial.decodeCubic 21 atom1592Coded := by decide +kernel
theorem atom1592Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (38617257772800 : Int) atom1592Coded) := by
  have h := atom1592_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1592Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1593 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1593 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1593 = ((g 11) * (g 14) * (g 14)) := by
  norm_num [atom1593, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1593_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4954771584000 : Int) atom1593) := by
  rw [SparsePolynomial.eval_scale, eval_atom1593]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 11) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1593Coded : CoefficientMerge.Poly := [(nat_lit 5159, Int.ofNat (nat_lit 1))]
theorem atom1593Coded_decode : atom1593 = SparsePolynomial.decodeCubic 21 atom1593Coded := by decide +kernel
theorem atom1593Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (4954771584000 : Int) atom1593Coded) := by
  have h := atom1593_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1593Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1594 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 14, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom1594Coded : CoefficientMerge.Poly := [(nat_lit 5160, Int.ofNat (nat_lit 1))]
theorem atom1594Coded_decode : atom1594 = SparsePolynomial.decodeCubic 21 atom1594Coded := by decide +kernel
theorem atom1594Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8093431584000 : Int) atom1594Coded) := by
  have h := atom1594_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1594Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1595 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 14, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom1595Coded : CoefficientMerge.Poly := [(nat_lit 5161, Int.ofNat (nat_lit 1))]
theorem atom1595Coded_decode : atom1595 = SparsePolynomial.decodeCubic 21 atom1595Coded := by decide +kernel
theorem atom1595Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8260858368000 : Int) atom1595Coded) := by
  have h := atom1595_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1595Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1596 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 14, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1596Coded : CoefficientMerge.Poly := [(nat_lit 5162, Int.ofNat (nat_lit 1))]
theorem atom1596Coded_decode : atom1596 = SparsePolynomial.decodeCubic 21 atom1596Coded := by decide +kernel
theorem atom1596Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35367383520000 : Int) atom1596Coded) := by
  have h := atom1596_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1596Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1597 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 14, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1597Coded : CoefficientMerge.Poly := [(nat_lit 5163, Int.ofNat (nat_lit 1))]
theorem atom1597Coded_decode : atom1597 = SparsePolynomial.decodeCubic 21 atom1597Coded := by decide +kernel
theorem atom1597Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36765453110400 : Int) atom1597Coded) := by
  have h := atom1597_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1597Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1598 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 14, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1598Coded : CoefficientMerge.Poly := [(nat_lit 5164, Int.ofNat (nat_lit 1))]
theorem atom1598Coded_decode : atom1598 = SparsePolynomial.decodeCubic 21 atom1598Coded := by decide +kernel
theorem atom1598Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (37994983488000 : Int) atom1598Coded) := by
  have h := atom1598_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1598Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1599 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 14, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1599Coded : CoefficientMerge.Poly := [(nat_lit 5165, Int.ofNat (nat_lit 1))]
theorem atom1599Coded_decode : atom1599 = SparsePolynomial.decodeCubic 21 atom1599Coded := by decide +kernel
theorem atom1599Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (63945789163200 : Int) atom1599Coded) := by
  have h := atom1599_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1599Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1600 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1600 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1600 = ((g 11) * (g 15) * (g 15)) := by
  norm_num [atom1600, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1600_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11306983564800 : Int) atom1600) := by
  rw [SparsePolynomial.eval_scale, eval_atom1600]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 11) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1600Coded : CoefficientMerge.Poly := [(nat_lit 5181, Int.ofNat (nat_lit 1))]
theorem atom1600Coded_decode : atom1600 = SparsePolynomial.decodeCubic 21 atom1600Coded := by decide +kernel
theorem atom1600Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11306983564800 : Int) atom1600Coded) := by
  have h := atom1600_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1600Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1601 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 15, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom1601Coded : CoefficientMerge.Poly := [(nat_lit 5182, Int.ofNat (nat_lit 1))]
theorem atom1601Coded_decode : atom1601 = SparsePolynomial.decodeCubic 21 atom1601Coded := by decide +kernel
theorem atom1601Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (26897818752000 : Int) atom1601Coded) := by
  have h := atom1601_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1601Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1602 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 15, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1602Coded : CoefficientMerge.Poly := [(nat_lit 5183, Int.ofNat (nat_lit 1))]
theorem atom1602Coded_decode : atom1602 = SparsePolynomial.decodeCubic 21 atom1602Coded := by decide +kernel
theorem atom1602Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (60580379059200 : Int) atom1602Coded) := by
  have h := atom1602_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1602Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1603 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 15, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1603Coded : CoefficientMerge.Poly := [(nat_lit 5184, Int.ofNat (nat_lit 1))]
theorem atom1603Coded_decode : atom1603 = SparsePolynomial.decodeCubic 21 atom1603Coded := by decide +kernel
theorem atom1603Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (65618034048000 : Int) atom1603Coded) := by
  have h := atom1603_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1603Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1604 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 15, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1604Coded : CoefficientMerge.Poly := [(nat_lit 5185, Int.ofNat (nat_lit 1))]
theorem atom1604Coded_decode : atom1604 = SparsePolynomial.decodeCubic 21 atom1604Coded := by decide +kernel
theorem atom1604Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (51049231833600 : Int) atom1604Coded) := by
  have h := atom1604_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1604Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1605 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 15, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1605Coded : CoefficientMerge.Poly := [(nat_lit 5186, Int.ofNat (nat_lit 1))]
theorem atom1605Coded_decode : atom1605 = SparsePolynomial.decodeCubic 21 atom1605Coded := by decide +kernel
theorem atom1605Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (83972064960000 : Int) atom1605Coded) := by
  have h := atom1605_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1605Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1606 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 16, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1606 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1606 = ((g 11) * (g 16) * (g 16)) := by
  norm_num [atom1606, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1606_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11599244213760 : Int) atom1606) := by
  rw [SparsePolynomial.eval_scale, eval_atom1606]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 11) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1606Coded : CoefficientMerge.Poly := [(nat_lit 5203, Int.ofNat (nat_lit 1))]
theorem atom1606Coded_decode : atom1606 = SparsePolynomial.decodeCubic 21 atom1606Coded := by decide +kernel
theorem atom1606Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11599244213760 : Int) atom1606Coded) := by
  have h := atom1606_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1606Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1607 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1607Coded : CoefficientMerge.Poly := [(nat_lit 5204, Int.ofNat (nat_lit 1))]
theorem atom1607Coded_decode : atom1607 = SparsePolynomial.decodeCubic 21 atom1607Coded := by decide +kernel
theorem atom1607Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (54517358246400 : Int) atom1607Coded) := by
  have h := atom1607_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1607Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1608 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 16, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1608Coded : CoefficientMerge.Poly := [(nat_lit 5205, Int.ofNat (nat_lit 1))]
theorem atom1608Coded_decode : atom1608 = SparsePolynomial.decodeCubic 21 atom1608Coded := by decide +kernel
theorem atom1608Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (68922680601600 : Int) atom1608Coded) := by
  have h := atom1608_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1608Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1609 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 16, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1609Coded : CoefficientMerge.Poly := [(nat_lit 5206, Int.ofNat (nat_lit 1))]
theorem atom1609Coded_decode : atom1609 = SparsePolynomial.decodeCubic 21 atom1609Coded := by decide +kernel
theorem atom1609Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (54987390259200 : Int) atom1609Coded) := by
  have h := atom1609_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1609Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1610 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 16, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1610Coded : CoefficientMerge.Poly := [(nat_lit 5207, Int.ofNat (nat_lit 1))]
theorem atom1610Coded_decode : atom1610 = SparsePolynomial.decodeCubic 21 atom1610Coded := by decide +kernel
theorem atom1610Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (76694201740800 : Int) atom1610Coded) := by
  have h := atom1610_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1610Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1611 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1611 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1611 = ((g 11) * (g 17) * (g 17)) := by
  norm_num [atom1611, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1611_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41556232166400 : Int) atom1611) := by
  rw [SparsePolynomial.eval_scale, eval_atom1611]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1611Coded : CoefficientMerge.Poly := [(nat_lit 5225, Int.ofNat (nat_lit 1))]
theorem atom1611Coded_decode : atom1611 = SparsePolynomial.decodeCubic 21 atom1611Coded := by decide +kernel
theorem atom1611Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (41556232166400 : Int) atom1611Coded) := by
  have h := atom1611_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1611Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1612 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 17, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1612Coded : CoefficientMerge.Poly := [(nat_lit 5226, Int.ofNat (nat_lit 1))]
theorem atom1612Coded_decode : atom1612 = SparsePolynomial.decodeCubic 21 atom1612Coded := by decide +kernel
theorem atom1612Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (83144666304000 : Int) atom1612Coded) := by
  have h := atom1612_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1612Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1613 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 17, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1613Coded : CoefficientMerge.Poly := [(nat_lit 5227, Int.ofNat (nat_lit 1))]
theorem atom1613Coded_decode : atom1613 = SparsePolynomial.decodeCubic 21 atom1613Coded := by decide +kernel
theorem atom1613Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (63150637939200 : Int) atom1613Coded) := by
  have h := atom1613_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1613Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1614 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 17, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1614Coded : CoefficientMerge.Poly := [(nat_lit 5228, Int.ofNat (nat_lit 1))]
theorem atom1614Coded_decode : atom1614 = SparsePolynomial.decodeCubic 21 atom1614Coded := by decide +kernel
theorem atom1614Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (71866230105600 : Int) atom1614Coded) := by
  have h := atom1614_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1614Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1615 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 18, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1615 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1615 = ((g 11) * (g 18) * (g 18)) := by
  norm_num [atom1615, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1615_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36462275136000 : Int) atom1615) := by
  rw [SparsePolynomial.eval_scale, eval_atom1615]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 11) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1615Coded : CoefficientMerge.Poly := [(nat_lit 5247, Int.ofNat (nat_lit 1))]
theorem atom1615Coded_decode : atom1615 = SparsePolynomial.decodeCubic 21 atom1615Coded := by decide +kernel
theorem atom1615Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36462275136000 : Int) atom1615Coded) := by
  have h := atom1615_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1615Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block021 : CoefficientMerge.Poly := [(nat_lit 4679, Int.ofNat (nat_lit 12235036884000)), (nat_lit 4680, Int.ofNat (nat_lit 10060008291200)), (nat_lit 4681, Int.ofNat (nat_lit 19067301227520)), (nat_lit 4682, Int.ofNat (nat_lit 30545055374400)), (nat_lit 4696, Int.ofNat (nat_lit 3637196294400)), (nat_lit 4697, Int.ofNat (nat_lit 6880901068800)), (nat_lit 4698, Int.ofNat (nat_lit 8610848568000)), (nat_lit 4699, Int.ofNat (nat_lit 7226753652000)), (nat_lit 4700, Int.ofNat (nat_lit 24723029116800)), (nat_lit 4701, Int.ofNat (nat_lit 25487556040800)), (nat_lit 4702, Int.ofNat (nat_lit 29609621330400)), (nat_lit 4703, Int.ofNat (nat_lit 48203677670400)), (nat_lit 4718, Int.ofNat (nat_lit 7524616377600)), (nat_lit 4719, Int.ofNat (nat_lit 13837762108800)), (nat_lit 4720, Int.ofNat (nat_lit 14444665250400)), (nat_lit 4721, Int.ofNat (nat_lit 39514858588800)), (nat_lit 4722, Int.ofNat (nat_lit 43438294015200)), (nat_lit 4723, Int.ofNat (nat_lit 44668852452000)), (nat_lit 4724, Int.ofNat (nat_lit 70445302603200)), (nat_lit 4740, Int.ofNat (nat_lit 14207114880000)), (nat_lit 4741, Int.ofNat (nat_lit 31648905514800)), (nat_lit 4742, Int.ofNat (nat_lit 63044385868800)), (nat_lit 4743, Int.ofNat (nat_lit 68251193312400)), (nat_lit 4744, Int.ofNat (nat_lit 52704630997200)), (nat_lit 4745, Int.ofNat (nat_lit 84534447690000)), (nat_lit 4762, Int.ofNat (nat_lit 13258427535360)), (nat_lit 4763, Int.ofNat (nat_lit 55380479086800)), (nat_lit 4764, Int.ofNat (nat_lit 67640031660600)), (nat_lit 4765, Int.ofNat (nat_lit 51789484202400)), (nat_lit 4766, Int.ofNat (nat_lit 71505263913300)), (nat_lit 4784, Int.ofNat (nat_lit 41806301644800)), (nat_lit 4785, Int.ofNat (nat_lit 79803065286000)), (nat_lit 4786, Int.ofNat (nat_lit 57575234833200)), (nat_lit 4787, Int.ofNat (nat_lit 64172281244400)), (nat_lit 4806, Int.ofNat (nat_lit 32379144373800)), (nat_lit 4807, Int.ofNat (nat_lit 46613159346600)), (nat_lit 4808, Int.ofNat (nat_lit 56384774100900)), (nat_lit 4828, Int.ofNat (nat_lit 9434482696800)), (nat_lit 4829, Int.ofNat (nat_lit 29846674802700)), (nat_lit 4850, Int.ofNat (nat_lit 16605245065500)), (nat_lit 5093, Int.ofNat (nat_lit 625628505600)), (nat_lit 5097, Int.ofNat (nat_lit 3027061094400)), (nat_lit 5099, Int.ofNat (nat_lit 4622441241600)), (nat_lit 5117, Int.ofNat (nat_lit 427179916800)), (nat_lit 5118, Int.ofNat (nat_lit 2412192625920)), (nat_lit 5120, Int.ofNat (nat_lit 12512392569600)), (nat_lit 5121, Int.ofNat (nat_lit 6764344227200)), (nat_lit 5122, Int.ofNat (nat_lit 11598417976320)), (nat_lit 5123, Int.ofNat (nat_lit 17871729019200)), (nat_lit 5137, Int.ofNat (nat_lit 1585379635200)), (nat_lit 5138, Int.ofNat (nat_lit 2686419532800)), (nat_lit 5139, Int.ofNat (nat_lit 2932238030400)), (nat_lit 5140, Int.ofNat (nat_lit 229178692800)), (nat_lit 5141, Int.ofNat (nat_lit 18882297907200)), (nat_lit 5142, Int.ofNat (nat_lit 16597632038400)), (nat_lit 5143, Int.ofNat (nat_lit 20194842312000)), (nat_lit 5144, Int.ofNat (nat_lit 38617257772800)), (nat_lit 5159, Int.ofNat (nat_lit 4954771584000)), (nat_lit 5160, Int.ofNat (nat_lit 8093431584000)), (nat_lit 5161, Int.ofNat (nat_lit 8260858368000)), (nat_lit 5162, Int.ofNat (nat_lit 35367383520000)), (nat_lit 5163, Int.ofNat (nat_lit 36765453110400)), (nat_lit 5164, Int.ofNat (nat_lit 37994983488000)), (nat_lit 5165, Int.ofNat (nat_lit 63945789163200)), (nat_lit 5181, Int.ofNat (nat_lit 11306983564800)), (nat_lit 5182, Int.ofNat (nat_lit 26897818752000)), (nat_lit 5183, Int.ofNat (nat_lit 60580379059200)), (nat_lit 5184, Int.ofNat (nat_lit 65618034048000)), (nat_lit 5185, Int.ofNat (nat_lit 51049231833600)), (nat_lit 5186, Int.ofNat (nat_lit 83972064960000)), (nat_lit 5203, Int.ofNat (nat_lit 11599244213760)), (nat_lit 5204, Int.ofNat (nat_lit 54517358246400)), (nat_lit 5205, Int.ofNat (nat_lit 68922680601600)), (nat_lit 5206, Int.ofNat (nat_lit 54987390259200)), (nat_lit 5207, Int.ofNat (nat_lit 76694201740800)), (nat_lit 5225, Int.ofNat (nat_lit 41556232166400)), (nat_lit 5226, Int.ofNat (nat_lit 83144666304000)), (nat_lit 5227, Int.ofNat (nat_lit 63150637939200)), (nat_lit 5228, Int.ofNat (nat_lit 71866230105600)), (nat_lit 5247, Int.ofNat (nat_lit 36462275136000))]
def block021_data_flat000 : CoefficientMerge.Poly := [(nat_lit 4679, Int.ofNat (nat_lit 12235036884000))]
theorem block021_data_flat000_step : block021_data_flat000 = (CoefficientMerge.scale (12235036884000 : Int) atom1536Coded) := by decide +kernel
theorem block021_data_flat000_original : block021_data_flat000 = (CoefficientMerge.scale (12235036884000 : Int) atom1536Coded) := by
  rw [block021_data_flat000_step]
def block021_data_flat001 : CoefficientMerge.Poly := [(nat_lit 4680, Int.ofNat (nat_lit 10060008291200))]
theorem block021_data_flat001_step : block021_data_flat001 = (CoefficientMerge.scale (10060008291200 : Int) atom1537Coded) := by decide +kernel
theorem block021_data_flat001_original : block021_data_flat001 = (CoefficientMerge.scale (10060008291200 : Int) atom1537Coded) := by
  rw [block021_data_flat001_step]
def block021_data_flat002 : CoefficientMerge.Poly := [(nat_lit 4679, Int.ofNat (nat_lit 12235036884000)), (nat_lit 4680, Int.ofNat (nat_lit 10060008291200))]
theorem block021_data_flat002_step : block021_data_flat002 = (CoefficientMerge.fastMerge block021_data_flat000 block021_data_flat001) := by decide +kernel
theorem block021_data_flat002_original : block021_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (12235036884000 : Int) atom1536Coded) (CoefficientMerge.scale (10060008291200 : Int) atom1537Coded)) := by
  rw [block021_data_flat002_step, block021_data_flat000_original, block021_data_flat001_original]
def block021_data_flat003 : CoefficientMerge.Poly := [(nat_lit 4681, Int.ofNat (nat_lit 19067301227520))]
theorem block021_data_flat003_step : block021_data_flat003 = (CoefficientMerge.scale (19067301227520 : Int) atom1538Coded) := by decide +kernel
theorem block021_data_flat003_original : block021_data_flat003 = (CoefficientMerge.scale (19067301227520 : Int) atom1538Coded) := by
  rw [block021_data_flat003_step]
def block021_data_flat004 : CoefficientMerge.Poly := [(nat_lit 4682, Int.ofNat (nat_lit 30545055374400))]
theorem block021_data_flat004_step : block021_data_flat004 = (CoefficientMerge.scale (30545055374400 : Int) atom1539Coded) := by decide +kernel
theorem block021_data_flat004_original : block021_data_flat004 = (CoefficientMerge.scale (30545055374400 : Int) atom1539Coded) := by
  rw [block021_data_flat004_step]
def block021_data_flat005 : CoefficientMerge.Poly := [(nat_lit 4696, Int.ofNat (nat_lit 3637196294400))]
theorem block021_data_flat005_step : block021_data_flat005 = (CoefficientMerge.scale (3637196294400 : Int) atom1540Coded) := by decide +kernel
theorem block021_data_flat005_original : block021_data_flat005 = (CoefficientMerge.scale (3637196294400 : Int) atom1540Coded) := by
  rw [block021_data_flat005_step]
def block021_data_flat006 : CoefficientMerge.Poly := [(nat_lit 4682, Int.ofNat (nat_lit 30545055374400)), (nat_lit 4696, Int.ofNat (nat_lit 3637196294400))]
theorem block021_data_flat006_step : block021_data_flat006 = (CoefficientMerge.fastMerge block021_data_flat004 block021_data_flat005) := by decide +kernel
theorem block021_data_flat006_original : block021_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (30545055374400 : Int) atom1539Coded) (CoefficientMerge.scale (3637196294400 : Int) atom1540Coded)) := by
  rw [block021_data_flat006_step, block021_data_flat004_original, block021_data_flat005_original]
def block021_data_flat007 : CoefficientMerge.Poly := [(nat_lit 4681, Int.ofNat (nat_lit 19067301227520)), (nat_lit 4682, Int.ofNat (nat_lit 30545055374400)), (nat_lit 4696, Int.ofNat (nat_lit 3637196294400))]
theorem block021_data_flat007_step : block021_data_flat007 = (CoefficientMerge.fastMerge block021_data_flat003 block021_data_flat006) := by decide +kernel
theorem block021_data_flat007_original : block021_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (19067301227520 : Int) atom1538Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30545055374400 : Int) atom1539Coded) (CoefficientMerge.scale (3637196294400 : Int) atom1540Coded))) := by
  rw [block021_data_flat007_step, block021_data_flat003_original, block021_data_flat006_original]
def block021_data_flat008 : CoefficientMerge.Poly := [(nat_lit 4679, Int.ofNat (nat_lit 12235036884000)), (nat_lit 4680, Int.ofNat (nat_lit 10060008291200)), (nat_lit 4681, Int.ofNat (nat_lit 19067301227520)), (nat_lit 4682, Int.ofNat (nat_lit 30545055374400)), (nat_lit 4696, Int.ofNat (nat_lit 3637196294400))]
theorem block021_data_flat008_step : block021_data_flat008 = (CoefficientMerge.fastMerge block021_data_flat002 block021_data_flat007) := by decide +kernel
theorem block021_data_flat008_original : block021_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12235036884000 : Int) atom1536Coded) (CoefficientMerge.scale (10060008291200 : Int) atom1537Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19067301227520 : Int) atom1538Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30545055374400 : Int) atom1539Coded) (CoefficientMerge.scale (3637196294400 : Int) atom1540Coded)))) := by
  rw [block021_data_flat008_step, block021_data_flat002_original, block021_data_flat007_original]
def block021_data_flat009 : CoefficientMerge.Poly := [(nat_lit 4697, Int.ofNat (nat_lit 6880901068800))]
theorem block021_data_flat009_step : block021_data_flat009 = (CoefficientMerge.scale (6880901068800 : Int) atom1541Coded) := by decide +kernel
theorem block021_data_flat009_original : block021_data_flat009 = (CoefficientMerge.scale (6880901068800 : Int) atom1541Coded) := by
  rw [block021_data_flat009_step]
def block021_data_flat010 : CoefficientMerge.Poly := [(nat_lit 4698, Int.ofNat (nat_lit 8610848568000))]
theorem block021_data_flat010_step : block021_data_flat010 = (CoefficientMerge.scale (8610848568000 : Int) atom1542Coded) := by decide +kernel
theorem block021_data_flat010_original : block021_data_flat010 = (CoefficientMerge.scale (8610848568000 : Int) atom1542Coded) := by
  rw [block021_data_flat010_step]
def block021_data_flat011 : CoefficientMerge.Poly := [(nat_lit 4697, Int.ofNat (nat_lit 6880901068800)), (nat_lit 4698, Int.ofNat (nat_lit 8610848568000))]
theorem block021_data_flat011_step : block021_data_flat011 = (CoefficientMerge.fastMerge block021_data_flat009 block021_data_flat010) := by decide +kernel
theorem block021_data_flat011_original : block021_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6880901068800 : Int) atom1541Coded) (CoefficientMerge.scale (8610848568000 : Int) atom1542Coded)) := by
  rw [block021_data_flat011_step, block021_data_flat009_original, block021_data_flat010_original]
def block021_data_flat012 : CoefficientMerge.Poly := [(nat_lit 4699, Int.ofNat (nat_lit 7226753652000))]
theorem block021_data_flat012_step : block021_data_flat012 = (CoefficientMerge.scale (7226753652000 : Int) atom1543Coded) := by decide +kernel
theorem block021_data_flat012_original : block021_data_flat012 = (CoefficientMerge.scale (7226753652000 : Int) atom1543Coded) := by
  rw [block021_data_flat012_step]
def block021_data_flat013 : CoefficientMerge.Poly := [(nat_lit 4700, Int.ofNat (nat_lit 24723029116800))]
theorem block021_data_flat013_step : block021_data_flat013 = (CoefficientMerge.scale (24723029116800 : Int) atom1544Coded) := by decide +kernel
theorem block021_data_flat013_original : block021_data_flat013 = (CoefficientMerge.scale (24723029116800 : Int) atom1544Coded) := by
  rw [block021_data_flat013_step]
def block021_data_flat014 : CoefficientMerge.Poly := [(nat_lit 4701, Int.ofNat (nat_lit 25487556040800))]
theorem block021_data_flat014_step : block021_data_flat014 = (CoefficientMerge.scale (25487556040800 : Int) atom1545Coded) := by decide +kernel
theorem block021_data_flat014_original : block021_data_flat014 = (CoefficientMerge.scale (25487556040800 : Int) atom1545Coded) := by
  rw [block021_data_flat014_step]
def block021_data_flat015 : CoefficientMerge.Poly := [(nat_lit 4700, Int.ofNat (nat_lit 24723029116800)), (nat_lit 4701, Int.ofNat (nat_lit 25487556040800))]
theorem block021_data_flat015_step : block021_data_flat015 = (CoefficientMerge.fastMerge block021_data_flat013 block021_data_flat014) := by decide +kernel
theorem block021_data_flat015_original : block021_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (24723029116800 : Int) atom1544Coded) (CoefficientMerge.scale (25487556040800 : Int) atom1545Coded)) := by
  rw [block021_data_flat015_step, block021_data_flat013_original, block021_data_flat014_original]
def block021_data_flat016 : CoefficientMerge.Poly := [(nat_lit 4699, Int.ofNat (nat_lit 7226753652000)), (nat_lit 4700, Int.ofNat (nat_lit 24723029116800)), (nat_lit 4701, Int.ofNat (nat_lit 25487556040800))]
theorem block021_data_flat016_step : block021_data_flat016 = (CoefficientMerge.fastMerge block021_data_flat012 block021_data_flat015) := by decide +kernel
theorem block021_data_flat016_original : block021_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7226753652000 : Int) atom1543Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24723029116800 : Int) atom1544Coded) (CoefficientMerge.scale (25487556040800 : Int) atom1545Coded))) := by
  rw [block021_data_flat016_step, block021_data_flat012_original, block021_data_flat015_original]
def block021_data_flat017 : CoefficientMerge.Poly := [(nat_lit 4697, Int.ofNat (nat_lit 6880901068800)), (nat_lit 4698, Int.ofNat (nat_lit 8610848568000)), (nat_lit 4699, Int.ofNat (nat_lit 7226753652000)), (nat_lit 4700, Int.ofNat (nat_lit 24723029116800)), (nat_lit 4701, Int.ofNat (nat_lit 25487556040800))]
theorem block021_data_flat017_step : block021_data_flat017 = (CoefficientMerge.fastMerge block021_data_flat011 block021_data_flat016) := by decide +kernel
theorem block021_data_flat017_original : block021_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6880901068800 : Int) atom1541Coded) (CoefficientMerge.scale (8610848568000 : Int) atom1542Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7226753652000 : Int) atom1543Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24723029116800 : Int) atom1544Coded) (CoefficientMerge.scale (25487556040800 : Int) atom1545Coded)))) := by
  rw [block021_data_flat017_step, block021_data_flat011_original, block021_data_flat016_original]
def block021_data_flat018 : CoefficientMerge.Poly := [(nat_lit 4679, Int.ofNat (nat_lit 12235036884000)), (nat_lit 4680, Int.ofNat (nat_lit 10060008291200)), (nat_lit 4681, Int.ofNat (nat_lit 19067301227520)), (nat_lit 4682, Int.ofNat (nat_lit 30545055374400)), (nat_lit 4696, Int.ofNat (nat_lit 3637196294400)), (nat_lit 4697, Int.ofNat (nat_lit 6880901068800)), (nat_lit 4698, Int.ofNat (nat_lit 8610848568000)), (nat_lit 4699, Int.ofNat (nat_lit 7226753652000)), (nat_lit 4700, Int.ofNat (nat_lit 24723029116800)), (nat_lit 4701, Int.ofNat (nat_lit 25487556040800))]
theorem block021_data_flat018_step : block021_data_flat018 = (CoefficientMerge.fastMerge block021_data_flat008 block021_data_flat017) := by decide +kernel
theorem block021_data_flat018_original : block021_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12235036884000 : Int) atom1536Coded) (CoefficientMerge.scale (10060008291200 : Int) atom1537Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19067301227520 : Int) atom1538Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30545055374400 : Int) atom1539Coded) (CoefficientMerge.scale (3637196294400 : Int) atom1540Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6880901068800 : Int) atom1541Coded) (CoefficientMerge.scale (8610848568000 : Int) atom1542Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7226753652000 : Int) atom1543Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24723029116800 : Int) atom1544Coded) (CoefficientMerge.scale (25487556040800 : Int) atom1545Coded))))) := by
  rw [block021_data_flat018_step, block021_data_flat008_original, block021_data_flat017_original]
def block021_data_flat019 : CoefficientMerge.Poly := [(nat_lit 4702, Int.ofNat (nat_lit 29609621330400))]
theorem block021_data_flat019_step : block021_data_flat019 = (CoefficientMerge.scale (29609621330400 : Int) atom1546Coded) := by decide +kernel
theorem block021_data_flat019_original : block021_data_flat019 = (CoefficientMerge.scale (29609621330400 : Int) atom1546Coded) := by
  rw [block021_data_flat019_step]
def block021_data_flat020 : CoefficientMerge.Poly := [(nat_lit 4703, Int.ofNat (nat_lit 48203677670400))]
theorem block021_data_flat020_step : block021_data_flat020 = (CoefficientMerge.scale (48203677670400 : Int) atom1547Coded) := by decide +kernel
theorem block021_data_flat020_original : block021_data_flat020 = (CoefficientMerge.scale (48203677670400 : Int) atom1547Coded) := by
  rw [block021_data_flat020_step]
def block021_data_flat021 : CoefficientMerge.Poly := [(nat_lit 4702, Int.ofNat (nat_lit 29609621330400)), (nat_lit 4703, Int.ofNat (nat_lit 48203677670400))]
theorem block021_data_flat021_step : block021_data_flat021 = (CoefficientMerge.fastMerge block021_data_flat019 block021_data_flat020) := by decide +kernel
theorem block021_data_flat021_original : block021_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (29609621330400 : Int) atom1546Coded) (CoefficientMerge.scale (48203677670400 : Int) atom1547Coded)) := by
  rw [block021_data_flat021_step, block021_data_flat019_original, block021_data_flat020_original]
def block021_data_flat022 : CoefficientMerge.Poly := [(nat_lit 4718, Int.ofNat (nat_lit 7524616377600))]
theorem block021_data_flat022_step : block021_data_flat022 = (CoefficientMerge.scale (7524616377600 : Int) atom1548Coded) := by decide +kernel
theorem block021_data_flat022_original : block021_data_flat022 = (CoefficientMerge.scale (7524616377600 : Int) atom1548Coded) := by
  rw [block021_data_flat022_step]
def block021_data_flat023 : CoefficientMerge.Poly := [(nat_lit 4719, Int.ofNat (nat_lit 13837762108800))]
theorem block021_data_flat023_step : block021_data_flat023 = (CoefficientMerge.scale (13837762108800 : Int) atom1549Coded) := by decide +kernel
theorem block021_data_flat023_original : block021_data_flat023 = (CoefficientMerge.scale (13837762108800 : Int) atom1549Coded) := by
  rw [block021_data_flat023_step]
def block021_data_flat024 : CoefficientMerge.Poly := [(nat_lit 4720, Int.ofNat (nat_lit 14444665250400))]
theorem block021_data_flat024_step : block021_data_flat024 = (CoefficientMerge.scale (14444665250400 : Int) atom1550Coded) := by decide +kernel
theorem block021_data_flat024_original : block021_data_flat024 = (CoefficientMerge.scale (14444665250400 : Int) atom1550Coded) := by
  rw [block021_data_flat024_step]
def block021_data_flat025 : CoefficientMerge.Poly := [(nat_lit 4719, Int.ofNat (nat_lit 13837762108800)), (nat_lit 4720, Int.ofNat (nat_lit 14444665250400))]
theorem block021_data_flat025_step : block021_data_flat025 = (CoefficientMerge.fastMerge block021_data_flat023 block021_data_flat024) := by decide +kernel
theorem block021_data_flat025_original : block021_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (13837762108800 : Int) atom1549Coded) (CoefficientMerge.scale (14444665250400 : Int) atom1550Coded)) := by
  rw [block021_data_flat025_step, block021_data_flat023_original, block021_data_flat024_original]
def block021_data_flat026 : CoefficientMerge.Poly := [(nat_lit 4718, Int.ofNat (nat_lit 7524616377600)), (nat_lit 4719, Int.ofNat (nat_lit 13837762108800)), (nat_lit 4720, Int.ofNat (nat_lit 14444665250400))]
theorem block021_data_flat026_step : block021_data_flat026 = (CoefficientMerge.fastMerge block021_data_flat022 block021_data_flat025) := by decide +kernel
theorem block021_data_flat026_original : block021_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7524616377600 : Int) atom1548Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13837762108800 : Int) atom1549Coded) (CoefficientMerge.scale (14444665250400 : Int) atom1550Coded))) := by
  rw [block021_data_flat026_step, block021_data_flat022_original, block021_data_flat025_original]
def block021_data_flat027 : CoefficientMerge.Poly := [(nat_lit 4702, Int.ofNat (nat_lit 29609621330400)), (nat_lit 4703, Int.ofNat (nat_lit 48203677670400)), (nat_lit 4718, Int.ofNat (nat_lit 7524616377600)), (nat_lit 4719, Int.ofNat (nat_lit 13837762108800)), (nat_lit 4720, Int.ofNat (nat_lit 14444665250400))]
theorem block021_data_flat027_step : block021_data_flat027 = (CoefficientMerge.fastMerge block021_data_flat021 block021_data_flat026) := by decide +kernel
theorem block021_data_flat027_original : block021_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (29609621330400 : Int) atom1546Coded) (CoefficientMerge.scale (48203677670400 : Int) atom1547Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7524616377600 : Int) atom1548Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13837762108800 : Int) atom1549Coded) (CoefficientMerge.scale (14444665250400 : Int) atom1550Coded)))) := by
  rw [block021_data_flat027_step, block021_data_flat021_original, block021_data_flat026_original]
def block021_data_flat028 : CoefficientMerge.Poly := [(nat_lit 4721, Int.ofNat (nat_lit 39514858588800))]
theorem block021_data_flat028_step : block021_data_flat028 = (CoefficientMerge.scale (39514858588800 : Int) atom1551Coded) := by decide +kernel
theorem block021_data_flat028_original : block021_data_flat028 = (CoefficientMerge.scale (39514858588800 : Int) atom1551Coded) := by
  rw [block021_data_flat028_step]
def block021_data_flat029 : CoefficientMerge.Poly := [(nat_lit 4722, Int.ofNat (nat_lit 43438294015200))]
theorem block021_data_flat029_step : block021_data_flat029 = (CoefficientMerge.scale (43438294015200 : Int) atom1552Coded) := by decide +kernel
theorem block021_data_flat029_original : block021_data_flat029 = (CoefficientMerge.scale (43438294015200 : Int) atom1552Coded) := by
  rw [block021_data_flat029_step]
def block021_data_flat030 : CoefficientMerge.Poly := [(nat_lit 4721, Int.ofNat (nat_lit 39514858588800)), (nat_lit 4722, Int.ofNat (nat_lit 43438294015200))]
theorem block021_data_flat030_step : block021_data_flat030 = (CoefficientMerge.fastMerge block021_data_flat028 block021_data_flat029) := by decide +kernel
theorem block021_data_flat030_original : block021_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (39514858588800 : Int) atom1551Coded) (CoefficientMerge.scale (43438294015200 : Int) atom1552Coded)) := by
  rw [block021_data_flat030_step, block021_data_flat028_original, block021_data_flat029_original]
def block021_data_flat031 : CoefficientMerge.Poly := [(nat_lit 4723, Int.ofNat (nat_lit 44668852452000))]
theorem block021_data_flat031_step : block021_data_flat031 = (CoefficientMerge.scale (44668852452000 : Int) atom1553Coded) := by decide +kernel
theorem block021_data_flat031_original : block021_data_flat031 = (CoefficientMerge.scale (44668852452000 : Int) atom1553Coded) := by
  rw [block021_data_flat031_step]
def block021_data_flat032 : CoefficientMerge.Poly := [(nat_lit 4724, Int.ofNat (nat_lit 70445302603200))]
theorem block021_data_flat032_step : block021_data_flat032 = (CoefficientMerge.scale (70445302603200 : Int) atom1554Coded) := by decide +kernel
theorem block021_data_flat032_original : block021_data_flat032 = (CoefficientMerge.scale (70445302603200 : Int) atom1554Coded) := by
  rw [block021_data_flat032_step]
def block021_data_flat033 : CoefficientMerge.Poly := [(nat_lit 4740, Int.ofNat (nat_lit 14207114880000))]
theorem block021_data_flat033_step : block021_data_flat033 = (CoefficientMerge.scale (14207114880000 : Int) atom1555Coded) := by decide +kernel
theorem block021_data_flat033_original : block021_data_flat033 = (CoefficientMerge.scale (14207114880000 : Int) atom1555Coded) := by
  rw [block021_data_flat033_step]
def block021_data_flat034 : CoefficientMerge.Poly := [(nat_lit 4724, Int.ofNat (nat_lit 70445302603200)), (nat_lit 4740, Int.ofNat (nat_lit 14207114880000))]
theorem block021_data_flat034_step : block021_data_flat034 = (CoefficientMerge.fastMerge block021_data_flat032 block021_data_flat033) := by decide +kernel
theorem block021_data_flat034_original : block021_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (70445302603200 : Int) atom1554Coded) (CoefficientMerge.scale (14207114880000 : Int) atom1555Coded)) := by
  rw [block021_data_flat034_step, block021_data_flat032_original, block021_data_flat033_original]
def block021_data_flat035 : CoefficientMerge.Poly := [(nat_lit 4723, Int.ofNat (nat_lit 44668852452000)), (nat_lit 4724, Int.ofNat (nat_lit 70445302603200)), (nat_lit 4740, Int.ofNat (nat_lit 14207114880000))]
theorem block021_data_flat035_step : block021_data_flat035 = (CoefficientMerge.fastMerge block021_data_flat031 block021_data_flat034) := by decide +kernel
theorem block021_data_flat035_original : block021_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (44668852452000 : Int) atom1553Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70445302603200 : Int) atom1554Coded) (CoefficientMerge.scale (14207114880000 : Int) atom1555Coded))) := by
  rw [block021_data_flat035_step, block021_data_flat031_original, block021_data_flat034_original]
def block021_data_flat036 : CoefficientMerge.Poly := [(nat_lit 4721, Int.ofNat (nat_lit 39514858588800)), (nat_lit 4722, Int.ofNat (nat_lit 43438294015200)), (nat_lit 4723, Int.ofNat (nat_lit 44668852452000)), (nat_lit 4724, Int.ofNat (nat_lit 70445302603200)), (nat_lit 4740, Int.ofNat (nat_lit 14207114880000))]
theorem block021_data_flat036_step : block021_data_flat036 = (CoefficientMerge.fastMerge block021_data_flat030 block021_data_flat035) := by decide +kernel
theorem block021_data_flat036_original : block021_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39514858588800 : Int) atom1551Coded) (CoefficientMerge.scale (43438294015200 : Int) atom1552Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44668852452000 : Int) atom1553Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70445302603200 : Int) atom1554Coded) (CoefficientMerge.scale (14207114880000 : Int) atom1555Coded)))) := by
  rw [block021_data_flat036_step, block021_data_flat030_original, block021_data_flat035_original]
def block021_data_flat037 : CoefficientMerge.Poly := [(nat_lit 4702, Int.ofNat (nat_lit 29609621330400)), (nat_lit 4703, Int.ofNat (nat_lit 48203677670400)), (nat_lit 4718, Int.ofNat (nat_lit 7524616377600)), (nat_lit 4719, Int.ofNat (nat_lit 13837762108800)), (nat_lit 4720, Int.ofNat (nat_lit 14444665250400)), (nat_lit 4721, Int.ofNat (nat_lit 39514858588800)), (nat_lit 4722, Int.ofNat (nat_lit 43438294015200)), (nat_lit 4723, Int.ofNat (nat_lit 44668852452000)), (nat_lit 4724, Int.ofNat (nat_lit 70445302603200)), (nat_lit 4740, Int.ofNat (nat_lit 14207114880000))]
theorem block021_data_flat037_step : block021_data_flat037 = (CoefficientMerge.fastMerge block021_data_flat027 block021_data_flat036) := by decide +kernel
theorem block021_data_flat037_original : block021_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (29609621330400 : Int) atom1546Coded) (CoefficientMerge.scale (48203677670400 : Int) atom1547Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7524616377600 : Int) atom1548Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13837762108800 : Int) atom1549Coded) (CoefficientMerge.scale (14444665250400 : Int) atom1550Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39514858588800 : Int) atom1551Coded) (CoefficientMerge.scale (43438294015200 : Int) atom1552Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44668852452000 : Int) atom1553Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70445302603200 : Int) atom1554Coded) (CoefficientMerge.scale (14207114880000 : Int) atom1555Coded))))) := by
  rw [block021_data_flat037_step, block021_data_flat027_original, block021_data_flat036_original]
def block021_data_flat038 : CoefficientMerge.Poly := [(nat_lit 4679, Int.ofNat (nat_lit 12235036884000)), (nat_lit 4680, Int.ofNat (nat_lit 10060008291200)), (nat_lit 4681, Int.ofNat (nat_lit 19067301227520)), (nat_lit 4682, Int.ofNat (nat_lit 30545055374400)), (nat_lit 4696, Int.ofNat (nat_lit 3637196294400)), (nat_lit 4697, Int.ofNat (nat_lit 6880901068800)), (nat_lit 4698, Int.ofNat (nat_lit 8610848568000)), (nat_lit 4699, Int.ofNat (nat_lit 7226753652000)), (nat_lit 4700, Int.ofNat (nat_lit 24723029116800)), (nat_lit 4701, Int.ofNat (nat_lit 25487556040800)), (nat_lit 4702, Int.ofNat (nat_lit 29609621330400)), (nat_lit 4703, Int.ofNat (nat_lit 48203677670400)), (nat_lit 4718, Int.ofNat (nat_lit 7524616377600)), (nat_lit 4719, Int.ofNat (nat_lit 13837762108800)), (nat_lit 4720, Int.ofNat (nat_lit 14444665250400)), (nat_lit 4721, Int.ofNat (nat_lit 39514858588800)), (nat_lit 4722, Int.ofNat (nat_lit 43438294015200)), (nat_lit 4723, Int.ofNat (nat_lit 44668852452000)), (nat_lit 4724, Int.ofNat (nat_lit 70445302603200)), (nat_lit 4740, Int.ofNat (nat_lit 14207114880000))]
theorem block021_data_flat038_step : block021_data_flat038 = (CoefficientMerge.fastMerge block021_data_flat018 block021_data_flat037) := by decide +kernel
theorem block021_data_flat038_original : block021_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12235036884000 : Int) atom1536Coded) (CoefficientMerge.scale (10060008291200 : Int) atom1537Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19067301227520 : Int) atom1538Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30545055374400 : Int) atom1539Coded) (CoefficientMerge.scale (3637196294400 : Int) atom1540Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6880901068800 : Int) atom1541Coded) (CoefficientMerge.scale (8610848568000 : Int) atom1542Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7226753652000 : Int) atom1543Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24723029116800 : Int) atom1544Coded) (CoefficientMerge.scale (25487556040800 : Int) atom1545Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (29609621330400 : Int) atom1546Coded) (CoefficientMerge.scale (48203677670400 : Int) atom1547Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7524616377600 : Int) atom1548Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13837762108800 : Int) atom1549Coded) (CoefficientMerge.scale (14444665250400 : Int) atom1550Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39514858588800 : Int) atom1551Coded) (CoefficientMerge.scale (43438294015200 : Int) atom1552Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44668852452000 : Int) atom1553Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70445302603200 : Int) atom1554Coded) (CoefficientMerge.scale (14207114880000 : Int) atom1555Coded)))))) := by
  rw [block021_data_flat038_step, block021_data_flat018_original, block021_data_flat037_original]
def block021_data_flat039 : CoefficientMerge.Poly := [(nat_lit 4741, Int.ofNat (nat_lit 31648905514800))]
theorem block021_data_flat039_step : block021_data_flat039 = (CoefficientMerge.scale (31648905514800 : Int) atom1556Coded) := by decide +kernel
theorem block021_data_flat039_original : block021_data_flat039 = (CoefficientMerge.scale (31648905514800 : Int) atom1556Coded) := by
  rw [block021_data_flat039_step]
def block021_data_flat040 : CoefficientMerge.Poly := [(nat_lit 4742, Int.ofNat (nat_lit 63044385868800))]
theorem block021_data_flat040_step : block021_data_flat040 = (CoefficientMerge.scale (63044385868800 : Int) atom1557Coded) := by decide +kernel
theorem block021_data_flat040_original : block021_data_flat040 = (CoefficientMerge.scale (63044385868800 : Int) atom1557Coded) := by
  rw [block021_data_flat040_step]
def block021_data_flat041 : CoefficientMerge.Poly := [(nat_lit 4741, Int.ofNat (nat_lit 31648905514800)), (nat_lit 4742, Int.ofNat (nat_lit 63044385868800))]
theorem block021_data_flat041_step : block021_data_flat041 = (CoefficientMerge.fastMerge block021_data_flat039 block021_data_flat040) := by decide +kernel
theorem block021_data_flat041_original : block021_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (31648905514800 : Int) atom1556Coded) (CoefficientMerge.scale (63044385868800 : Int) atom1557Coded)) := by
  rw [block021_data_flat041_step, block021_data_flat039_original, block021_data_flat040_original]
def block021_data_flat042 : CoefficientMerge.Poly := [(nat_lit 4743, Int.ofNat (nat_lit 68251193312400))]
theorem block021_data_flat042_step : block021_data_flat042 = (CoefficientMerge.scale (68251193312400 : Int) atom1558Coded) := by decide +kernel
theorem block021_data_flat042_original : block021_data_flat042 = (CoefficientMerge.scale (68251193312400 : Int) atom1558Coded) := by
  rw [block021_data_flat042_step]
def block021_data_flat043 : CoefficientMerge.Poly := [(nat_lit 4744, Int.ofNat (nat_lit 52704630997200))]
theorem block021_data_flat043_step : block021_data_flat043 = (CoefficientMerge.scale (52704630997200 : Int) atom1559Coded) := by decide +kernel
theorem block021_data_flat043_original : block021_data_flat043 = (CoefficientMerge.scale (52704630997200 : Int) atom1559Coded) := by
  rw [block021_data_flat043_step]
def block021_data_flat044 : CoefficientMerge.Poly := [(nat_lit 4745, Int.ofNat (nat_lit 84534447690000))]
theorem block021_data_flat044_step : block021_data_flat044 = (CoefficientMerge.scale (84534447690000 : Int) atom1560Coded) := by decide +kernel
theorem block021_data_flat044_original : block021_data_flat044 = (CoefficientMerge.scale (84534447690000 : Int) atom1560Coded) := by
  rw [block021_data_flat044_step]
def block021_data_flat045 : CoefficientMerge.Poly := [(nat_lit 4744, Int.ofNat (nat_lit 52704630997200)), (nat_lit 4745, Int.ofNat (nat_lit 84534447690000))]
theorem block021_data_flat045_step : block021_data_flat045 = (CoefficientMerge.fastMerge block021_data_flat043 block021_data_flat044) := by decide +kernel
theorem block021_data_flat045_original : block021_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (52704630997200 : Int) atom1559Coded) (CoefficientMerge.scale (84534447690000 : Int) atom1560Coded)) := by
  rw [block021_data_flat045_step, block021_data_flat043_original, block021_data_flat044_original]
def block021_data_flat046 : CoefficientMerge.Poly := [(nat_lit 4743, Int.ofNat (nat_lit 68251193312400)), (nat_lit 4744, Int.ofNat (nat_lit 52704630997200)), (nat_lit 4745, Int.ofNat (nat_lit 84534447690000))]
theorem block021_data_flat046_step : block021_data_flat046 = (CoefficientMerge.fastMerge block021_data_flat042 block021_data_flat045) := by decide +kernel
theorem block021_data_flat046_original : block021_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (68251193312400 : Int) atom1558Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52704630997200 : Int) atom1559Coded) (CoefficientMerge.scale (84534447690000 : Int) atom1560Coded))) := by
  rw [block021_data_flat046_step, block021_data_flat042_original, block021_data_flat045_original]
def block021_data_flat047 : CoefficientMerge.Poly := [(nat_lit 4741, Int.ofNat (nat_lit 31648905514800)), (nat_lit 4742, Int.ofNat (nat_lit 63044385868800)), (nat_lit 4743, Int.ofNat (nat_lit 68251193312400)), (nat_lit 4744, Int.ofNat (nat_lit 52704630997200)), (nat_lit 4745, Int.ofNat (nat_lit 84534447690000))]
theorem block021_data_flat047_step : block021_data_flat047 = (CoefficientMerge.fastMerge block021_data_flat041 block021_data_flat046) := by decide +kernel
theorem block021_data_flat047_original : block021_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31648905514800 : Int) atom1556Coded) (CoefficientMerge.scale (63044385868800 : Int) atom1557Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68251193312400 : Int) atom1558Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52704630997200 : Int) atom1559Coded) (CoefficientMerge.scale (84534447690000 : Int) atom1560Coded)))) := by
  rw [block021_data_flat047_step, block021_data_flat041_original, block021_data_flat046_original]
def block021_data_flat048 : CoefficientMerge.Poly := [(nat_lit 4762, Int.ofNat (nat_lit 13258427535360))]
theorem block021_data_flat048_step : block021_data_flat048 = (CoefficientMerge.scale (13258427535360 : Int) atom1561Coded) := by decide +kernel
theorem block021_data_flat048_original : block021_data_flat048 = (CoefficientMerge.scale (13258427535360 : Int) atom1561Coded) := by
  rw [block021_data_flat048_step]
def block021_data_flat049 : CoefficientMerge.Poly := [(nat_lit 4763, Int.ofNat (nat_lit 55380479086800))]
theorem block021_data_flat049_step : block021_data_flat049 = (CoefficientMerge.scale (55380479086800 : Int) atom1562Coded) := by decide +kernel
theorem block021_data_flat049_original : block021_data_flat049 = (CoefficientMerge.scale (55380479086800 : Int) atom1562Coded) := by
  rw [block021_data_flat049_step]
def block021_data_flat050 : CoefficientMerge.Poly := [(nat_lit 4762, Int.ofNat (nat_lit 13258427535360)), (nat_lit 4763, Int.ofNat (nat_lit 55380479086800))]
theorem block021_data_flat050_step : block021_data_flat050 = (CoefficientMerge.fastMerge block021_data_flat048 block021_data_flat049) := by decide +kernel
theorem block021_data_flat050_original : block021_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (13258427535360 : Int) atom1561Coded) (CoefficientMerge.scale (55380479086800 : Int) atom1562Coded)) := by
  rw [block021_data_flat050_step, block021_data_flat048_original, block021_data_flat049_original]
def block021_data_flat051 : CoefficientMerge.Poly := [(nat_lit 4764, Int.ofNat (nat_lit 67640031660600))]
theorem block021_data_flat051_step : block021_data_flat051 = (CoefficientMerge.scale (67640031660600 : Int) atom1563Coded) := by decide +kernel
theorem block021_data_flat051_original : block021_data_flat051 = (CoefficientMerge.scale (67640031660600 : Int) atom1563Coded) := by
  rw [block021_data_flat051_step]
def block021_data_flat052 : CoefficientMerge.Poly := [(nat_lit 4765, Int.ofNat (nat_lit 51789484202400))]
theorem block021_data_flat052_step : block021_data_flat052 = (CoefficientMerge.scale (51789484202400 : Int) atom1564Coded) := by decide +kernel
theorem block021_data_flat052_original : block021_data_flat052 = (CoefficientMerge.scale (51789484202400 : Int) atom1564Coded) := by
  rw [block021_data_flat052_step]
def block021_data_flat053 : CoefficientMerge.Poly := [(nat_lit 4766, Int.ofNat (nat_lit 71505263913300))]
theorem block021_data_flat053_step : block021_data_flat053 = (CoefficientMerge.scale (71505263913300 : Int) atom1565Coded) := by decide +kernel
theorem block021_data_flat053_original : block021_data_flat053 = (CoefficientMerge.scale (71505263913300 : Int) atom1565Coded) := by
  rw [block021_data_flat053_step]
def block021_data_flat054 : CoefficientMerge.Poly := [(nat_lit 4765, Int.ofNat (nat_lit 51789484202400)), (nat_lit 4766, Int.ofNat (nat_lit 71505263913300))]
theorem block021_data_flat054_step : block021_data_flat054 = (CoefficientMerge.fastMerge block021_data_flat052 block021_data_flat053) := by decide +kernel
theorem block021_data_flat054_original : block021_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (51789484202400 : Int) atom1564Coded) (CoefficientMerge.scale (71505263913300 : Int) atom1565Coded)) := by
  rw [block021_data_flat054_step, block021_data_flat052_original, block021_data_flat053_original]
def block021_data_flat055 : CoefficientMerge.Poly := [(nat_lit 4764, Int.ofNat (nat_lit 67640031660600)), (nat_lit 4765, Int.ofNat (nat_lit 51789484202400)), (nat_lit 4766, Int.ofNat (nat_lit 71505263913300))]
theorem block021_data_flat055_step : block021_data_flat055 = (CoefficientMerge.fastMerge block021_data_flat051 block021_data_flat054) := by decide +kernel
theorem block021_data_flat055_original : block021_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (67640031660600 : Int) atom1563Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (51789484202400 : Int) atom1564Coded) (CoefficientMerge.scale (71505263913300 : Int) atom1565Coded))) := by
  rw [block021_data_flat055_step, block021_data_flat051_original, block021_data_flat054_original]
def block021_data_flat056 : CoefficientMerge.Poly := [(nat_lit 4762, Int.ofNat (nat_lit 13258427535360)), (nat_lit 4763, Int.ofNat (nat_lit 55380479086800)), (nat_lit 4764, Int.ofNat (nat_lit 67640031660600)), (nat_lit 4765, Int.ofNat (nat_lit 51789484202400)), (nat_lit 4766, Int.ofNat (nat_lit 71505263913300))]
theorem block021_data_flat056_step : block021_data_flat056 = (CoefficientMerge.fastMerge block021_data_flat050 block021_data_flat055) := by decide +kernel
theorem block021_data_flat056_original : block021_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13258427535360 : Int) atom1561Coded) (CoefficientMerge.scale (55380479086800 : Int) atom1562Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67640031660600 : Int) atom1563Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (51789484202400 : Int) atom1564Coded) (CoefficientMerge.scale (71505263913300 : Int) atom1565Coded)))) := by
  rw [block021_data_flat056_step, block021_data_flat050_original, block021_data_flat055_original]
def block021_data_flat057 : CoefficientMerge.Poly := [(nat_lit 4741, Int.ofNat (nat_lit 31648905514800)), (nat_lit 4742, Int.ofNat (nat_lit 63044385868800)), (nat_lit 4743, Int.ofNat (nat_lit 68251193312400)), (nat_lit 4744, Int.ofNat (nat_lit 52704630997200)), (nat_lit 4745, Int.ofNat (nat_lit 84534447690000)), (nat_lit 4762, Int.ofNat (nat_lit 13258427535360)), (nat_lit 4763, Int.ofNat (nat_lit 55380479086800)), (nat_lit 4764, Int.ofNat (nat_lit 67640031660600)), (nat_lit 4765, Int.ofNat (nat_lit 51789484202400)), (nat_lit 4766, Int.ofNat (nat_lit 71505263913300))]
theorem block021_data_flat057_step : block021_data_flat057 = (CoefficientMerge.fastMerge block021_data_flat047 block021_data_flat056) := by decide +kernel
theorem block021_data_flat057_original : block021_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31648905514800 : Int) atom1556Coded) (CoefficientMerge.scale (63044385868800 : Int) atom1557Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68251193312400 : Int) atom1558Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52704630997200 : Int) atom1559Coded) (CoefficientMerge.scale (84534447690000 : Int) atom1560Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13258427535360 : Int) atom1561Coded) (CoefficientMerge.scale (55380479086800 : Int) atom1562Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67640031660600 : Int) atom1563Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (51789484202400 : Int) atom1564Coded) (CoefficientMerge.scale (71505263913300 : Int) atom1565Coded))))) := by
  rw [block021_data_flat057_step, block021_data_flat047_original, block021_data_flat056_original]
def block021_data_flat058 : CoefficientMerge.Poly := [(nat_lit 4784, Int.ofNat (nat_lit 41806301644800))]
theorem block021_data_flat058_step : block021_data_flat058 = (CoefficientMerge.scale (41806301644800 : Int) atom1566Coded) := by decide +kernel
theorem block021_data_flat058_original : block021_data_flat058 = (CoefficientMerge.scale (41806301644800 : Int) atom1566Coded) := by
  rw [block021_data_flat058_step]
def block021_data_flat059 : CoefficientMerge.Poly := [(nat_lit 4785, Int.ofNat (nat_lit 79803065286000))]
theorem block021_data_flat059_step : block021_data_flat059 = (CoefficientMerge.scale (79803065286000 : Int) atom1567Coded) := by decide +kernel
theorem block021_data_flat059_original : block021_data_flat059 = (CoefficientMerge.scale (79803065286000 : Int) atom1567Coded) := by
  rw [block021_data_flat059_step]
def block021_data_flat060 : CoefficientMerge.Poly := [(nat_lit 4784, Int.ofNat (nat_lit 41806301644800)), (nat_lit 4785, Int.ofNat (nat_lit 79803065286000))]
theorem block021_data_flat060_step : block021_data_flat060 = (CoefficientMerge.fastMerge block021_data_flat058 block021_data_flat059) := by decide +kernel
theorem block021_data_flat060_original : block021_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (41806301644800 : Int) atom1566Coded) (CoefficientMerge.scale (79803065286000 : Int) atom1567Coded)) := by
  rw [block021_data_flat060_step, block021_data_flat058_original, block021_data_flat059_original]
def block021_data_flat061 : CoefficientMerge.Poly := [(nat_lit 4786, Int.ofNat (nat_lit 57575234833200))]
theorem block021_data_flat061_step : block021_data_flat061 = (CoefficientMerge.scale (57575234833200 : Int) atom1568Coded) := by decide +kernel
theorem block021_data_flat061_original : block021_data_flat061 = (CoefficientMerge.scale (57575234833200 : Int) atom1568Coded) := by
  rw [block021_data_flat061_step]
def block021_data_flat062 : CoefficientMerge.Poly := [(nat_lit 4787, Int.ofNat (nat_lit 64172281244400))]
theorem block021_data_flat062_step : block021_data_flat062 = (CoefficientMerge.scale (64172281244400 : Int) atom1569Coded) := by decide +kernel
theorem block021_data_flat062_original : block021_data_flat062 = (CoefficientMerge.scale (64172281244400 : Int) atom1569Coded) := by
  rw [block021_data_flat062_step]
def block021_data_flat063 : CoefficientMerge.Poly := [(nat_lit 4806, Int.ofNat (nat_lit 32379144373800))]
theorem block021_data_flat063_step : block021_data_flat063 = (CoefficientMerge.scale (32379144373800 : Int) atom1570Coded) := by decide +kernel
theorem block021_data_flat063_original : block021_data_flat063 = (CoefficientMerge.scale (32379144373800 : Int) atom1570Coded) := by
  rw [block021_data_flat063_step]
def block021_data_flat064 : CoefficientMerge.Poly := [(nat_lit 4787, Int.ofNat (nat_lit 64172281244400)), (nat_lit 4806, Int.ofNat (nat_lit 32379144373800))]
theorem block021_data_flat064_step : block021_data_flat064 = (CoefficientMerge.fastMerge block021_data_flat062 block021_data_flat063) := by decide +kernel
theorem block021_data_flat064_original : block021_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (64172281244400 : Int) atom1569Coded) (CoefficientMerge.scale (32379144373800 : Int) atom1570Coded)) := by
  rw [block021_data_flat064_step, block021_data_flat062_original, block021_data_flat063_original]
def block021_data_flat065 : CoefficientMerge.Poly := [(nat_lit 4786, Int.ofNat (nat_lit 57575234833200)), (nat_lit 4787, Int.ofNat (nat_lit 64172281244400)), (nat_lit 4806, Int.ofNat (nat_lit 32379144373800))]
theorem block021_data_flat065_step : block021_data_flat065 = (CoefficientMerge.fastMerge block021_data_flat061 block021_data_flat064) := by decide +kernel
theorem block021_data_flat065_original : block021_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (57575234833200 : Int) atom1568Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64172281244400 : Int) atom1569Coded) (CoefficientMerge.scale (32379144373800 : Int) atom1570Coded))) := by
  rw [block021_data_flat065_step, block021_data_flat061_original, block021_data_flat064_original]
def block021_data_flat066 : CoefficientMerge.Poly := [(nat_lit 4784, Int.ofNat (nat_lit 41806301644800)), (nat_lit 4785, Int.ofNat (nat_lit 79803065286000)), (nat_lit 4786, Int.ofNat (nat_lit 57575234833200)), (nat_lit 4787, Int.ofNat (nat_lit 64172281244400)), (nat_lit 4806, Int.ofNat (nat_lit 32379144373800))]
theorem block021_data_flat066_step : block021_data_flat066 = (CoefficientMerge.fastMerge block021_data_flat060 block021_data_flat065) := by decide +kernel
theorem block021_data_flat066_original : block021_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (41806301644800 : Int) atom1566Coded) (CoefficientMerge.scale (79803065286000 : Int) atom1567Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57575234833200 : Int) atom1568Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64172281244400 : Int) atom1569Coded) (CoefficientMerge.scale (32379144373800 : Int) atom1570Coded)))) := by
  rw [block021_data_flat066_step, block021_data_flat060_original, block021_data_flat065_original]
def block021_data_flat067 : CoefficientMerge.Poly := [(nat_lit 4807, Int.ofNat (nat_lit 46613159346600))]
theorem block021_data_flat067_step : block021_data_flat067 = (CoefficientMerge.scale (46613159346600 : Int) atom1571Coded) := by decide +kernel
theorem block021_data_flat067_original : block021_data_flat067 = (CoefficientMerge.scale (46613159346600 : Int) atom1571Coded) := by
  rw [block021_data_flat067_step]
def block021_data_flat068 : CoefficientMerge.Poly := [(nat_lit 4808, Int.ofNat (nat_lit 56384774100900))]
theorem block021_data_flat068_step : block021_data_flat068 = (CoefficientMerge.scale (56384774100900 : Int) atom1572Coded) := by decide +kernel
theorem block021_data_flat068_original : block021_data_flat068 = (CoefficientMerge.scale (56384774100900 : Int) atom1572Coded) := by
  rw [block021_data_flat068_step]
def block021_data_flat069 : CoefficientMerge.Poly := [(nat_lit 4807, Int.ofNat (nat_lit 46613159346600)), (nat_lit 4808, Int.ofNat (nat_lit 56384774100900))]
theorem block021_data_flat069_step : block021_data_flat069 = (CoefficientMerge.fastMerge block021_data_flat067 block021_data_flat068) := by decide +kernel
theorem block021_data_flat069_original : block021_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (46613159346600 : Int) atom1571Coded) (CoefficientMerge.scale (56384774100900 : Int) atom1572Coded)) := by
  rw [block021_data_flat069_step, block021_data_flat067_original, block021_data_flat068_original]
def block021_data_flat070 : CoefficientMerge.Poly := [(nat_lit 4828, Int.ofNat (nat_lit 9434482696800))]
theorem block021_data_flat070_step : block021_data_flat070 = (CoefficientMerge.scale (9434482696800 : Int) atom1573Coded) := by decide +kernel
theorem block021_data_flat070_original : block021_data_flat070 = (CoefficientMerge.scale (9434482696800 : Int) atom1573Coded) := by
  rw [block021_data_flat070_step]
def block021_data_flat071 : CoefficientMerge.Poly := [(nat_lit 4829, Int.ofNat (nat_lit 29846674802700))]
theorem block021_data_flat071_step : block021_data_flat071 = (CoefficientMerge.scale (29846674802700 : Int) atom1574Coded) := by decide +kernel
theorem block021_data_flat071_original : block021_data_flat071 = (CoefficientMerge.scale (29846674802700 : Int) atom1574Coded) := by
  rw [block021_data_flat071_step]
def block021_data_flat072 : CoefficientMerge.Poly := [(nat_lit 4850, Int.ofNat (nat_lit 16605245065500))]
theorem block021_data_flat072_step : block021_data_flat072 = (CoefficientMerge.scale (16605245065500 : Int) atom1575Coded) := by decide +kernel
theorem block021_data_flat072_original : block021_data_flat072 = (CoefficientMerge.scale (16605245065500 : Int) atom1575Coded) := by
  rw [block021_data_flat072_step]
def block021_data_flat073 : CoefficientMerge.Poly := [(nat_lit 4829, Int.ofNat (nat_lit 29846674802700)), (nat_lit 4850, Int.ofNat (nat_lit 16605245065500))]
theorem block021_data_flat073_step : block021_data_flat073 = (CoefficientMerge.fastMerge block021_data_flat071 block021_data_flat072) := by decide +kernel
theorem block021_data_flat073_original : block021_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (29846674802700 : Int) atom1574Coded) (CoefficientMerge.scale (16605245065500 : Int) atom1575Coded)) := by
  rw [block021_data_flat073_step, block021_data_flat071_original, block021_data_flat072_original]
def block021_data_flat074 : CoefficientMerge.Poly := [(nat_lit 4828, Int.ofNat (nat_lit 9434482696800)), (nat_lit 4829, Int.ofNat (nat_lit 29846674802700)), (nat_lit 4850, Int.ofNat (nat_lit 16605245065500))]
theorem block021_data_flat074_step : block021_data_flat074 = (CoefficientMerge.fastMerge block021_data_flat070 block021_data_flat073) := by decide +kernel
theorem block021_data_flat074_original : block021_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (9434482696800 : Int) atom1573Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29846674802700 : Int) atom1574Coded) (CoefficientMerge.scale (16605245065500 : Int) atom1575Coded))) := by
  rw [block021_data_flat074_step, block021_data_flat070_original, block021_data_flat073_original]
def block021_data_flat075 : CoefficientMerge.Poly := [(nat_lit 4807, Int.ofNat (nat_lit 46613159346600)), (nat_lit 4808, Int.ofNat (nat_lit 56384774100900)), (nat_lit 4828, Int.ofNat (nat_lit 9434482696800)), (nat_lit 4829, Int.ofNat (nat_lit 29846674802700)), (nat_lit 4850, Int.ofNat (nat_lit 16605245065500))]
theorem block021_data_flat075_step : block021_data_flat075 = (CoefficientMerge.fastMerge block021_data_flat069 block021_data_flat074) := by decide +kernel
theorem block021_data_flat075_original : block021_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46613159346600 : Int) atom1571Coded) (CoefficientMerge.scale (56384774100900 : Int) atom1572Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9434482696800 : Int) atom1573Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29846674802700 : Int) atom1574Coded) (CoefficientMerge.scale (16605245065500 : Int) atom1575Coded)))) := by
  rw [block021_data_flat075_step, block021_data_flat069_original, block021_data_flat074_original]
def block021_data_flat076 : CoefficientMerge.Poly := [(nat_lit 4784, Int.ofNat (nat_lit 41806301644800)), (nat_lit 4785, Int.ofNat (nat_lit 79803065286000)), (nat_lit 4786, Int.ofNat (nat_lit 57575234833200)), (nat_lit 4787, Int.ofNat (nat_lit 64172281244400)), (nat_lit 4806, Int.ofNat (nat_lit 32379144373800)), (nat_lit 4807, Int.ofNat (nat_lit 46613159346600)), (nat_lit 4808, Int.ofNat (nat_lit 56384774100900)), (nat_lit 4828, Int.ofNat (nat_lit 9434482696800)), (nat_lit 4829, Int.ofNat (nat_lit 29846674802700)), (nat_lit 4850, Int.ofNat (nat_lit 16605245065500))]
theorem block021_data_flat076_step : block021_data_flat076 = (CoefficientMerge.fastMerge block021_data_flat066 block021_data_flat075) := by decide +kernel
theorem block021_data_flat076_original : block021_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (41806301644800 : Int) atom1566Coded) (CoefficientMerge.scale (79803065286000 : Int) atom1567Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57575234833200 : Int) atom1568Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64172281244400 : Int) atom1569Coded) (CoefficientMerge.scale (32379144373800 : Int) atom1570Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46613159346600 : Int) atom1571Coded) (CoefficientMerge.scale (56384774100900 : Int) atom1572Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9434482696800 : Int) atom1573Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29846674802700 : Int) atom1574Coded) (CoefficientMerge.scale (16605245065500 : Int) atom1575Coded))))) := by
  rw [block021_data_flat076_step, block021_data_flat066_original, block021_data_flat075_original]
def block021_data_flat077 : CoefficientMerge.Poly := [(nat_lit 4741, Int.ofNat (nat_lit 31648905514800)), (nat_lit 4742, Int.ofNat (nat_lit 63044385868800)), (nat_lit 4743, Int.ofNat (nat_lit 68251193312400)), (nat_lit 4744, Int.ofNat (nat_lit 52704630997200)), (nat_lit 4745, Int.ofNat (nat_lit 84534447690000)), (nat_lit 4762, Int.ofNat (nat_lit 13258427535360)), (nat_lit 4763, Int.ofNat (nat_lit 55380479086800)), (nat_lit 4764, Int.ofNat (nat_lit 67640031660600)), (nat_lit 4765, Int.ofNat (nat_lit 51789484202400)), (nat_lit 4766, Int.ofNat (nat_lit 71505263913300)), (nat_lit 4784, Int.ofNat (nat_lit 41806301644800)), (nat_lit 4785, Int.ofNat (nat_lit 79803065286000)), (nat_lit 4786, Int.ofNat (nat_lit 57575234833200)), (nat_lit 4787, Int.ofNat (nat_lit 64172281244400)), (nat_lit 4806, Int.ofNat (nat_lit 32379144373800)), (nat_lit 4807, Int.ofNat (nat_lit 46613159346600)), (nat_lit 4808, Int.ofNat (nat_lit 56384774100900)), (nat_lit 4828, Int.ofNat (nat_lit 9434482696800)), (nat_lit 4829, Int.ofNat (nat_lit 29846674802700)), (nat_lit 4850, Int.ofNat (nat_lit 16605245065500))]
theorem block021_data_flat077_step : block021_data_flat077 = (CoefficientMerge.fastMerge block021_data_flat057 block021_data_flat076) := by decide +kernel
theorem block021_data_flat077_original : block021_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31648905514800 : Int) atom1556Coded) (CoefficientMerge.scale (63044385868800 : Int) atom1557Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68251193312400 : Int) atom1558Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52704630997200 : Int) atom1559Coded) (CoefficientMerge.scale (84534447690000 : Int) atom1560Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13258427535360 : Int) atom1561Coded) (CoefficientMerge.scale (55380479086800 : Int) atom1562Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67640031660600 : Int) atom1563Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (51789484202400 : Int) atom1564Coded) (CoefficientMerge.scale (71505263913300 : Int) atom1565Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (41806301644800 : Int) atom1566Coded) (CoefficientMerge.scale (79803065286000 : Int) atom1567Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57575234833200 : Int) atom1568Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64172281244400 : Int) atom1569Coded) (CoefficientMerge.scale (32379144373800 : Int) atom1570Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46613159346600 : Int) atom1571Coded) (CoefficientMerge.scale (56384774100900 : Int) atom1572Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9434482696800 : Int) atom1573Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29846674802700 : Int) atom1574Coded) (CoefficientMerge.scale (16605245065500 : Int) atom1575Coded)))))) := by
  rw [block021_data_flat077_step, block021_data_flat057_original, block021_data_flat076_original]
def block021_data_flat078 : CoefficientMerge.Poly := [(nat_lit 4679, Int.ofNat (nat_lit 12235036884000)), (nat_lit 4680, Int.ofNat (nat_lit 10060008291200)), (nat_lit 4681, Int.ofNat (nat_lit 19067301227520)), (nat_lit 4682, Int.ofNat (nat_lit 30545055374400)), (nat_lit 4696, Int.ofNat (nat_lit 3637196294400)), (nat_lit 4697, Int.ofNat (nat_lit 6880901068800)), (nat_lit 4698, Int.ofNat (nat_lit 8610848568000)), (nat_lit 4699, Int.ofNat (nat_lit 7226753652000)), (nat_lit 4700, Int.ofNat (nat_lit 24723029116800)), (nat_lit 4701, Int.ofNat (nat_lit 25487556040800)), (nat_lit 4702, Int.ofNat (nat_lit 29609621330400)), (nat_lit 4703, Int.ofNat (nat_lit 48203677670400)), (nat_lit 4718, Int.ofNat (nat_lit 7524616377600)), (nat_lit 4719, Int.ofNat (nat_lit 13837762108800)), (nat_lit 4720, Int.ofNat (nat_lit 14444665250400)), (nat_lit 4721, Int.ofNat (nat_lit 39514858588800)), (nat_lit 4722, Int.ofNat (nat_lit 43438294015200)), (nat_lit 4723, Int.ofNat (nat_lit 44668852452000)), (nat_lit 4724, Int.ofNat (nat_lit 70445302603200)), (nat_lit 4740, Int.ofNat (nat_lit 14207114880000)), (nat_lit 4741, Int.ofNat (nat_lit 31648905514800)), (nat_lit 4742, Int.ofNat (nat_lit 63044385868800)), (nat_lit 4743, Int.ofNat (nat_lit 68251193312400)), (nat_lit 4744, Int.ofNat (nat_lit 52704630997200)), (nat_lit 4745, Int.ofNat (nat_lit 84534447690000)), (nat_lit 4762, Int.ofNat (nat_lit 13258427535360)), (nat_lit 4763, Int.ofNat (nat_lit 55380479086800)), (nat_lit 4764, Int.ofNat (nat_lit 67640031660600)), (nat_lit 4765, Int.ofNat (nat_lit 51789484202400)), (nat_lit 4766, Int.ofNat (nat_lit 71505263913300)), (nat_lit 4784, Int.ofNat (nat_lit 41806301644800)), (nat_lit 4785, Int.ofNat (nat_lit 79803065286000)), (nat_lit 4786, Int.ofNat (nat_lit 57575234833200)), (nat_lit 4787, Int.ofNat (nat_lit 64172281244400)), (nat_lit 4806, Int.ofNat (nat_lit 32379144373800)), (nat_lit 4807, Int.ofNat (nat_lit 46613159346600)), (nat_lit 4808, Int.ofNat (nat_lit 56384774100900)), (nat_lit 4828, Int.ofNat (nat_lit 9434482696800)), (nat_lit 4829, Int.ofNat (nat_lit 29846674802700)), (nat_lit 4850, Int.ofNat (nat_lit 16605245065500))]
theorem block021_data_flat078_step : block021_data_flat078 = (CoefficientMerge.fastMerge block021_data_flat038 block021_data_flat077) := by decide +kernel
theorem block021_data_flat078_original : block021_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12235036884000 : Int) atom1536Coded) (CoefficientMerge.scale (10060008291200 : Int) atom1537Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19067301227520 : Int) atom1538Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30545055374400 : Int) atom1539Coded) (CoefficientMerge.scale (3637196294400 : Int) atom1540Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6880901068800 : Int) atom1541Coded) (CoefficientMerge.scale (8610848568000 : Int) atom1542Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7226753652000 : Int) atom1543Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24723029116800 : Int) atom1544Coded) (CoefficientMerge.scale (25487556040800 : Int) atom1545Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (29609621330400 : Int) atom1546Coded) (CoefficientMerge.scale (48203677670400 : Int) atom1547Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7524616377600 : Int) atom1548Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13837762108800 : Int) atom1549Coded) (CoefficientMerge.scale (14444665250400 : Int) atom1550Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39514858588800 : Int) atom1551Coded) (CoefficientMerge.scale (43438294015200 : Int) atom1552Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44668852452000 : Int) atom1553Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70445302603200 : Int) atom1554Coded) (CoefficientMerge.scale (14207114880000 : Int) atom1555Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31648905514800 : Int) atom1556Coded) (CoefficientMerge.scale (63044385868800 : Int) atom1557Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68251193312400 : Int) atom1558Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52704630997200 : Int) atom1559Coded) (CoefficientMerge.scale (84534447690000 : Int) atom1560Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13258427535360 : Int) atom1561Coded) (CoefficientMerge.scale (55380479086800 : Int) atom1562Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67640031660600 : Int) atom1563Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (51789484202400 : Int) atom1564Coded) (CoefficientMerge.scale (71505263913300 : Int) atom1565Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (41806301644800 : Int) atom1566Coded) (CoefficientMerge.scale (79803065286000 : Int) atom1567Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57575234833200 : Int) atom1568Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64172281244400 : Int) atom1569Coded) (CoefficientMerge.scale (32379144373800 : Int) atom1570Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46613159346600 : Int) atom1571Coded) (CoefficientMerge.scale (56384774100900 : Int) atom1572Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9434482696800 : Int) atom1573Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29846674802700 : Int) atom1574Coded) (CoefficientMerge.scale (16605245065500 : Int) atom1575Coded))))))) := by
  rw [block021_data_flat078_step, block021_data_flat038_original, block021_data_flat077_original]
def block021_data_flat079 : CoefficientMerge.Poly := [(nat_lit 5093, Int.ofNat (nat_lit 625628505600))]
theorem block021_data_flat079_step : block021_data_flat079 = (CoefficientMerge.scale (625628505600 : Int) atom1576Coded) := by decide +kernel
theorem block021_data_flat079_original : block021_data_flat079 = (CoefficientMerge.scale (625628505600 : Int) atom1576Coded) := by
  rw [block021_data_flat079_step]
def block021_data_flat080 : CoefficientMerge.Poly := [(nat_lit 5097, Int.ofNat (nat_lit 3027061094400))]
theorem block021_data_flat080_step : block021_data_flat080 = (CoefficientMerge.scale (3027061094400 : Int) atom1577Coded) := by decide +kernel
theorem block021_data_flat080_original : block021_data_flat080 = (CoefficientMerge.scale (3027061094400 : Int) atom1577Coded) := by
  rw [block021_data_flat080_step]
def block021_data_flat081 : CoefficientMerge.Poly := [(nat_lit 5093, Int.ofNat (nat_lit 625628505600)), (nat_lit 5097, Int.ofNat (nat_lit 3027061094400))]
theorem block021_data_flat081_step : block021_data_flat081 = (CoefficientMerge.fastMerge block021_data_flat079 block021_data_flat080) := by decide +kernel
theorem block021_data_flat081_original : block021_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (625628505600 : Int) atom1576Coded) (CoefficientMerge.scale (3027061094400 : Int) atom1577Coded)) := by
  rw [block021_data_flat081_step, block021_data_flat079_original, block021_data_flat080_original]
def block021_data_flat082 : CoefficientMerge.Poly := [(nat_lit 5099, Int.ofNat (nat_lit 4622441241600))]
theorem block021_data_flat082_step : block021_data_flat082 = (CoefficientMerge.scale (4622441241600 : Int) atom1578Coded) := by decide +kernel
theorem block021_data_flat082_original : block021_data_flat082 = (CoefficientMerge.scale (4622441241600 : Int) atom1578Coded) := by
  rw [block021_data_flat082_step]
def block021_data_flat083 : CoefficientMerge.Poly := [(nat_lit 5117, Int.ofNat (nat_lit 427179916800))]
theorem block021_data_flat083_step : block021_data_flat083 = (CoefficientMerge.scale (427179916800 : Int) atom1579Coded) := by decide +kernel
theorem block021_data_flat083_original : block021_data_flat083 = (CoefficientMerge.scale (427179916800 : Int) atom1579Coded) := by
  rw [block021_data_flat083_step]
def block021_data_flat084 : CoefficientMerge.Poly := [(nat_lit 5118, Int.ofNat (nat_lit 2412192625920))]
theorem block021_data_flat084_step : block021_data_flat084 = (CoefficientMerge.scale (2412192625920 : Int) atom1580Coded) := by decide +kernel
theorem block021_data_flat084_original : block021_data_flat084 = (CoefficientMerge.scale (2412192625920 : Int) atom1580Coded) := by
  rw [block021_data_flat084_step]
def block021_data_flat085 : CoefficientMerge.Poly := [(nat_lit 5117, Int.ofNat (nat_lit 427179916800)), (nat_lit 5118, Int.ofNat (nat_lit 2412192625920))]
theorem block021_data_flat085_step : block021_data_flat085 = (CoefficientMerge.fastMerge block021_data_flat083 block021_data_flat084) := by decide +kernel
theorem block021_data_flat085_original : block021_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1579Coded) (CoefficientMerge.scale (2412192625920 : Int) atom1580Coded)) := by
  rw [block021_data_flat085_step, block021_data_flat083_original, block021_data_flat084_original]
def block021_data_flat086 : CoefficientMerge.Poly := [(nat_lit 5099, Int.ofNat (nat_lit 4622441241600)), (nat_lit 5117, Int.ofNat (nat_lit 427179916800)), (nat_lit 5118, Int.ofNat (nat_lit 2412192625920))]
theorem block021_data_flat086_step : block021_data_flat086 = (CoefficientMerge.fastMerge block021_data_flat082 block021_data_flat085) := by decide +kernel
theorem block021_data_flat086_original : block021_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (4622441241600 : Int) atom1578Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1579Coded) (CoefficientMerge.scale (2412192625920 : Int) atom1580Coded))) := by
  rw [block021_data_flat086_step, block021_data_flat082_original, block021_data_flat085_original]
def block021_data_flat087 : CoefficientMerge.Poly := [(nat_lit 5093, Int.ofNat (nat_lit 625628505600)), (nat_lit 5097, Int.ofNat (nat_lit 3027061094400)), (nat_lit 5099, Int.ofNat (nat_lit 4622441241600)), (nat_lit 5117, Int.ofNat (nat_lit 427179916800)), (nat_lit 5118, Int.ofNat (nat_lit 2412192625920))]
theorem block021_data_flat087_step : block021_data_flat087 = (CoefficientMerge.fastMerge block021_data_flat081 block021_data_flat086) := by decide +kernel
theorem block021_data_flat087_original : block021_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (625628505600 : Int) atom1576Coded) (CoefficientMerge.scale (3027061094400 : Int) atom1577Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4622441241600 : Int) atom1578Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1579Coded) (CoefficientMerge.scale (2412192625920 : Int) atom1580Coded)))) := by
  rw [block021_data_flat087_step, block021_data_flat081_original, block021_data_flat086_original]
def block021_data_flat088 : CoefficientMerge.Poly := [(nat_lit 5120, Int.ofNat (nat_lit 12512392569600))]
theorem block021_data_flat088_step : block021_data_flat088 = (CoefficientMerge.scale (12512392569600 : Int) atom1581Coded) := by decide +kernel
theorem block021_data_flat088_original : block021_data_flat088 = (CoefficientMerge.scale (12512392569600 : Int) atom1581Coded) := by
  rw [block021_data_flat088_step]
def block021_data_flat089 : CoefficientMerge.Poly := [(nat_lit 5121, Int.ofNat (nat_lit 6764344227200))]
theorem block021_data_flat089_step : block021_data_flat089 = (CoefficientMerge.scale (6764344227200 : Int) atom1582Coded) := by decide +kernel
theorem block021_data_flat089_original : block021_data_flat089 = (CoefficientMerge.scale (6764344227200 : Int) atom1582Coded) := by
  rw [block021_data_flat089_step]
def block021_data_flat090 : CoefficientMerge.Poly := [(nat_lit 5120, Int.ofNat (nat_lit 12512392569600)), (nat_lit 5121, Int.ofNat (nat_lit 6764344227200))]
theorem block021_data_flat090_step : block021_data_flat090 = (CoefficientMerge.fastMerge block021_data_flat088 block021_data_flat089) := by decide +kernel
theorem block021_data_flat090_original : block021_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (12512392569600 : Int) atom1581Coded) (CoefficientMerge.scale (6764344227200 : Int) atom1582Coded)) := by
  rw [block021_data_flat090_step, block021_data_flat088_original, block021_data_flat089_original]
def block021_data_flat091 : CoefficientMerge.Poly := [(nat_lit 5122, Int.ofNat (nat_lit 11598417976320))]
theorem block021_data_flat091_step : block021_data_flat091 = (CoefficientMerge.scale (11598417976320 : Int) atom1583Coded) := by decide +kernel
theorem block021_data_flat091_original : block021_data_flat091 = (CoefficientMerge.scale (11598417976320 : Int) atom1583Coded) := by
  rw [block021_data_flat091_step]
def block021_data_flat092 : CoefficientMerge.Poly := [(nat_lit 5123, Int.ofNat (nat_lit 17871729019200))]
theorem block021_data_flat092_step : block021_data_flat092 = (CoefficientMerge.scale (17871729019200 : Int) atom1584Coded) := by decide +kernel
theorem block021_data_flat092_original : block021_data_flat092 = (CoefficientMerge.scale (17871729019200 : Int) atom1584Coded) := by
  rw [block021_data_flat092_step]
def block021_data_flat093 : CoefficientMerge.Poly := [(nat_lit 5137, Int.ofNat (nat_lit 1585379635200))]
theorem block021_data_flat093_step : block021_data_flat093 = (CoefficientMerge.scale (1585379635200 : Int) atom1585Coded) := by decide +kernel
theorem block021_data_flat093_original : block021_data_flat093 = (CoefficientMerge.scale (1585379635200 : Int) atom1585Coded) := by
  rw [block021_data_flat093_step]
def block021_data_flat094 : CoefficientMerge.Poly := [(nat_lit 5123, Int.ofNat (nat_lit 17871729019200)), (nat_lit 5137, Int.ofNat (nat_lit 1585379635200))]
theorem block021_data_flat094_step : block021_data_flat094 = (CoefficientMerge.fastMerge block021_data_flat092 block021_data_flat093) := by decide +kernel
theorem block021_data_flat094_original : block021_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (17871729019200 : Int) atom1584Coded) (CoefficientMerge.scale (1585379635200 : Int) atom1585Coded)) := by
  rw [block021_data_flat094_step, block021_data_flat092_original, block021_data_flat093_original]
def block021_data_flat095 : CoefficientMerge.Poly := [(nat_lit 5122, Int.ofNat (nat_lit 11598417976320)), (nat_lit 5123, Int.ofNat (nat_lit 17871729019200)), (nat_lit 5137, Int.ofNat (nat_lit 1585379635200))]
theorem block021_data_flat095_step : block021_data_flat095 = (CoefficientMerge.fastMerge block021_data_flat091 block021_data_flat094) := by decide +kernel
theorem block021_data_flat095_original : block021_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11598417976320 : Int) atom1583Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17871729019200 : Int) atom1584Coded) (CoefficientMerge.scale (1585379635200 : Int) atom1585Coded))) := by
  rw [block021_data_flat095_step, block021_data_flat091_original, block021_data_flat094_original]
def block021_data_flat096 : CoefficientMerge.Poly := [(nat_lit 5120, Int.ofNat (nat_lit 12512392569600)), (nat_lit 5121, Int.ofNat (nat_lit 6764344227200)), (nat_lit 5122, Int.ofNat (nat_lit 11598417976320)), (nat_lit 5123, Int.ofNat (nat_lit 17871729019200)), (nat_lit 5137, Int.ofNat (nat_lit 1585379635200))]
theorem block021_data_flat096_step : block021_data_flat096 = (CoefficientMerge.fastMerge block021_data_flat090 block021_data_flat095) := by decide +kernel
theorem block021_data_flat096_original : block021_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12512392569600 : Int) atom1581Coded) (CoefficientMerge.scale (6764344227200 : Int) atom1582Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11598417976320 : Int) atom1583Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17871729019200 : Int) atom1584Coded) (CoefficientMerge.scale (1585379635200 : Int) atom1585Coded)))) := by
  rw [block021_data_flat096_step, block021_data_flat090_original, block021_data_flat095_original]
def block021_data_flat097 : CoefficientMerge.Poly := [(nat_lit 5093, Int.ofNat (nat_lit 625628505600)), (nat_lit 5097, Int.ofNat (nat_lit 3027061094400)), (nat_lit 5099, Int.ofNat (nat_lit 4622441241600)), (nat_lit 5117, Int.ofNat (nat_lit 427179916800)), (nat_lit 5118, Int.ofNat (nat_lit 2412192625920)), (nat_lit 5120, Int.ofNat (nat_lit 12512392569600)), (nat_lit 5121, Int.ofNat (nat_lit 6764344227200)), (nat_lit 5122, Int.ofNat (nat_lit 11598417976320)), (nat_lit 5123, Int.ofNat (nat_lit 17871729019200)), (nat_lit 5137, Int.ofNat (nat_lit 1585379635200))]
theorem block021_data_flat097_step : block021_data_flat097 = (CoefficientMerge.fastMerge block021_data_flat087 block021_data_flat096) := by decide +kernel
theorem block021_data_flat097_original : block021_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (625628505600 : Int) atom1576Coded) (CoefficientMerge.scale (3027061094400 : Int) atom1577Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4622441241600 : Int) atom1578Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1579Coded) (CoefficientMerge.scale (2412192625920 : Int) atom1580Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12512392569600 : Int) atom1581Coded) (CoefficientMerge.scale (6764344227200 : Int) atom1582Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11598417976320 : Int) atom1583Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17871729019200 : Int) atom1584Coded) (CoefficientMerge.scale (1585379635200 : Int) atom1585Coded))))) := by
  rw [block021_data_flat097_step, block021_data_flat087_original, block021_data_flat096_original]
def block021_data_flat098 : CoefficientMerge.Poly := [(nat_lit 5138, Int.ofNat (nat_lit 2686419532800))]
theorem block021_data_flat098_step : block021_data_flat098 = (CoefficientMerge.scale (2686419532800 : Int) atom1586Coded) := by decide +kernel
theorem block021_data_flat098_original : block021_data_flat098 = (CoefficientMerge.scale (2686419532800 : Int) atom1586Coded) := by
  rw [block021_data_flat098_step]
def block021_data_flat099 : CoefficientMerge.Poly := [(nat_lit 5139, Int.ofNat (nat_lit 2932238030400))]
theorem block021_data_flat099_step : block021_data_flat099 = (CoefficientMerge.scale (2932238030400 : Int) atom1587Coded) := by decide +kernel
theorem block021_data_flat099_original : block021_data_flat099 = (CoefficientMerge.scale (2932238030400 : Int) atom1587Coded) := by
  rw [block021_data_flat099_step]
def block021_data_flat100 : CoefficientMerge.Poly := [(nat_lit 5138, Int.ofNat (nat_lit 2686419532800)), (nat_lit 5139, Int.ofNat (nat_lit 2932238030400))]
theorem block021_data_flat100_step : block021_data_flat100 = (CoefficientMerge.fastMerge block021_data_flat098 block021_data_flat099) := by decide +kernel
theorem block021_data_flat100_original : block021_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2686419532800 : Int) atom1586Coded) (CoefficientMerge.scale (2932238030400 : Int) atom1587Coded)) := by
  rw [block021_data_flat100_step, block021_data_flat098_original, block021_data_flat099_original]
def block021_data_flat101 : CoefficientMerge.Poly := [(nat_lit 5140, Int.ofNat (nat_lit 229178692800))]
theorem block021_data_flat101_step : block021_data_flat101 = (CoefficientMerge.scale (229178692800 : Int) atom1588Coded) := by decide +kernel
theorem block021_data_flat101_original : block021_data_flat101 = (CoefficientMerge.scale (229178692800 : Int) atom1588Coded) := by
  rw [block021_data_flat101_step]
def block021_data_flat102 : CoefficientMerge.Poly := [(nat_lit 5141, Int.ofNat (nat_lit 18882297907200))]
theorem block021_data_flat102_step : block021_data_flat102 = (CoefficientMerge.scale (18882297907200 : Int) atom1589Coded) := by decide +kernel
theorem block021_data_flat102_original : block021_data_flat102 = (CoefficientMerge.scale (18882297907200 : Int) atom1589Coded) := by
  rw [block021_data_flat102_step]
def block021_data_flat103 : CoefficientMerge.Poly := [(nat_lit 5142, Int.ofNat (nat_lit 16597632038400))]
theorem block021_data_flat103_step : block021_data_flat103 = (CoefficientMerge.scale (16597632038400 : Int) atom1590Coded) := by decide +kernel
theorem block021_data_flat103_original : block021_data_flat103 = (CoefficientMerge.scale (16597632038400 : Int) atom1590Coded) := by
  rw [block021_data_flat103_step]
def block021_data_flat104 : CoefficientMerge.Poly := [(nat_lit 5141, Int.ofNat (nat_lit 18882297907200)), (nat_lit 5142, Int.ofNat (nat_lit 16597632038400))]
theorem block021_data_flat104_step : block021_data_flat104 = (CoefficientMerge.fastMerge block021_data_flat102 block021_data_flat103) := by decide +kernel
theorem block021_data_flat104_original : block021_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (18882297907200 : Int) atom1589Coded) (CoefficientMerge.scale (16597632038400 : Int) atom1590Coded)) := by
  rw [block021_data_flat104_step, block021_data_flat102_original, block021_data_flat103_original]
def block021_data_flat105 : CoefficientMerge.Poly := [(nat_lit 5140, Int.ofNat (nat_lit 229178692800)), (nat_lit 5141, Int.ofNat (nat_lit 18882297907200)), (nat_lit 5142, Int.ofNat (nat_lit 16597632038400))]
theorem block021_data_flat105_step : block021_data_flat105 = (CoefficientMerge.fastMerge block021_data_flat101 block021_data_flat104) := by decide +kernel
theorem block021_data_flat105_original : block021_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (229178692800 : Int) atom1588Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18882297907200 : Int) atom1589Coded) (CoefficientMerge.scale (16597632038400 : Int) atom1590Coded))) := by
  rw [block021_data_flat105_step, block021_data_flat101_original, block021_data_flat104_original]
def block021_data_flat106 : CoefficientMerge.Poly := [(nat_lit 5138, Int.ofNat (nat_lit 2686419532800)), (nat_lit 5139, Int.ofNat (nat_lit 2932238030400)), (nat_lit 5140, Int.ofNat (nat_lit 229178692800)), (nat_lit 5141, Int.ofNat (nat_lit 18882297907200)), (nat_lit 5142, Int.ofNat (nat_lit 16597632038400))]
theorem block021_data_flat106_step : block021_data_flat106 = (CoefficientMerge.fastMerge block021_data_flat100 block021_data_flat105) := by decide +kernel
theorem block021_data_flat106_original : block021_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2686419532800 : Int) atom1586Coded) (CoefficientMerge.scale (2932238030400 : Int) atom1587Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229178692800 : Int) atom1588Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18882297907200 : Int) atom1589Coded) (CoefficientMerge.scale (16597632038400 : Int) atom1590Coded)))) := by
  rw [block021_data_flat106_step, block021_data_flat100_original, block021_data_flat105_original]
def block021_data_flat107 : CoefficientMerge.Poly := [(nat_lit 5143, Int.ofNat (nat_lit 20194842312000))]
theorem block021_data_flat107_step : block021_data_flat107 = (CoefficientMerge.scale (20194842312000 : Int) atom1591Coded) := by decide +kernel
theorem block021_data_flat107_original : block021_data_flat107 = (CoefficientMerge.scale (20194842312000 : Int) atom1591Coded) := by
  rw [block021_data_flat107_step]
def block021_data_flat108 : CoefficientMerge.Poly := [(nat_lit 5144, Int.ofNat (nat_lit 38617257772800))]
theorem block021_data_flat108_step : block021_data_flat108 = (CoefficientMerge.scale (38617257772800 : Int) atom1592Coded) := by decide +kernel
theorem block021_data_flat108_original : block021_data_flat108 = (CoefficientMerge.scale (38617257772800 : Int) atom1592Coded) := by
  rw [block021_data_flat108_step]
def block021_data_flat109 : CoefficientMerge.Poly := [(nat_lit 5143, Int.ofNat (nat_lit 20194842312000)), (nat_lit 5144, Int.ofNat (nat_lit 38617257772800))]
theorem block021_data_flat109_step : block021_data_flat109 = (CoefficientMerge.fastMerge block021_data_flat107 block021_data_flat108) := by decide +kernel
theorem block021_data_flat109_original : block021_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (20194842312000 : Int) atom1591Coded) (CoefficientMerge.scale (38617257772800 : Int) atom1592Coded)) := by
  rw [block021_data_flat109_step, block021_data_flat107_original, block021_data_flat108_original]
def block021_data_flat110 : CoefficientMerge.Poly := [(nat_lit 5159, Int.ofNat (nat_lit 4954771584000))]
theorem block021_data_flat110_step : block021_data_flat110 = (CoefficientMerge.scale (4954771584000 : Int) atom1593Coded) := by decide +kernel
theorem block021_data_flat110_original : block021_data_flat110 = (CoefficientMerge.scale (4954771584000 : Int) atom1593Coded) := by
  rw [block021_data_flat110_step]
def block021_data_flat111 : CoefficientMerge.Poly := [(nat_lit 5160, Int.ofNat (nat_lit 8093431584000))]
theorem block021_data_flat111_step : block021_data_flat111 = (CoefficientMerge.scale (8093431584000 : Int) atom1594Coded) := by decide +kernel
theorem block021_data_flat111_original : block021_data_flat111 = (CoefficientMerge.scale (8093431584000 : Int) atom1594Coded) := by
  rw [block021_data_flat111_step]
def block021_data_flat112 : CoefficientMerge.Poly := [(nat_lit 5161, Int.ofNat (nat_lit 8260858368000))]
theorem block021_data_flat112_step : block021_data_flat112 = (CoefficientMerge.scale (8260858368000 : Int) atom1595Coded) := by decide +kernel
theorem block021_data_flat112_original : block021_data_flat112 = (CoefficientMerge.scale (8260858368000 : Int) atom1595Coded) := by
  rw [block021_data_flat112_step]
def block021_data_flat113 : CoefficientMerge.Poly := [(nat_lit 5160, Int.ofNat (nat_lit 8093431584000)), (nat_lit 5161, Int.ofNat (nat_lit 8260858368000))]
theorem block021_data_flat113_step : block021_data_flat113 = (CoefficientMerge.fastMerge block021_data_flat111 block021_data_flat112) := by decide +kernel
theorem block021_data_flat113_original : block021_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8093431584000 : Int) atom1594Coded) (CoefficientMerge.scale (8260858368000 : Int) atom1595Coded)) := by
  rw [block021_data_flat113_step, block021_data_flat111_original, block021_data_flat112_original]
def block021_data_flat114 : CoefficientMerge.Poly := [(nat_lit 5159, Int.ofNat (nat_lit 4954771584000)), (nat_lit 5160, Int.ofNat (nat_lit 8093431584000)), (nat_lit 5161, Int.ofNat (nat_lit 8260858368000))]
theorem block021_data_flat114_step : block021_data_flat114 = (CoefficientMerge.fastMerge block021_data_flat110 block021_data_flat113) := by decide +kernel
theorem block021_data_flat114_original : block021_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (4954771584000 : Int) atom1593Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8093431584000 : Int) atom1594Coded) (CoefficientMerge.scale (8260858368000 : Int) atom1595Coded))) := by
  rw [block021_data_flat114_step, block021_data_flat110_original, block021_data_flat113_original]
def block021_data_flat115 : CoefficientMerge.Poly := [(nat_lit 5143, Int.ofNat (nat_lit 20194842312000)), (nat_lit 5144, Int.ofNat (nat_lit 38617257772800)), (nat_lit 5159, Int.ofNat (nat_lit 4954771584000)), (nat_lit 5160, Int.ofNat (nat_lit 8093431584000)), (nat_lit 5161, Int.ofNat (nat_lit 8260858368000))]
theorem block021_data_flat115_step : block021_data_flat115 = (CoefficientMerge.fastMerge block021_data_flat109 block021_data_flat114) := by decide +kernel
theorem block021_data_flat115_original : block021_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20194842312000 : Int) atom1591Coded) (CoefficientMerge.scale (38617257772800 : Int) atom1592Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4954771584000 : Int) atom1593Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8093431584000 : Int) atom1594Coded) (CoefficientMerge.scale (8260858368000 : Int) atom1595Coded)))) := by
  rw [block021_data_flat115_step, block021_data_flat109_original, block021_data_flat114_original]
def block021_data_flat116 : CoefficientMerge.Poly := [(nat_lit 5138, Int.ofNat (nat_lit 2686419532800)), (nat_lit 5139, Int.ofNat (nat_lit 2932238030400)), (nat_lit 5140, Int.ofNat (nat_lit 229178692800)), (nat_lit 5141, Int.ofNat (nat_lit 18882297907200)), (nat_lit 5142, Int.ofNat (nat_lit 16597632038400)), (nat_lit 5143, Int.ofNat (nat_lit 20194842312000)), (nat_lit 5144, Int.ofNat (nat_lit 38617257772800)), (nat_lit 5159, Int.ofNat (nat_lit 4954771584000)), (nat_lit 5160, Int.ofNat (nat_lit 8093431584000)), (nat_lit 5161, Int.ofNat (nat_lit 8260858368000))]
theorem block021_data_flat116_step : block021_data_flat116 = (CoefficientMerge.fastMerge block021_data_flat106 block021_data_flat115) := by decide +kernel
theorem block021_data_flat116_original : block021_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2686419532800 : Int) atom1586Coded) (CoefficientMerge.scale (2932238030400 : Int) atom1587Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229178692800 : Int) atom1588Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18882297907200 : Int) atom1589Coded) (CoefficientMerge.scale (16597632038400 : Int) atom1590Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20194842312000 : Int) atom1591Coded) (CoefficientMerge.scale (38617257772800 : Int) atom1592Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4954771584000 : Int) atom1593Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8093431584000 : Int) atom1594Coded) (CoefficientMerge.scale (8260858368000 : Int) atom1595Coded))))) := by
  rw [block021_data_flat116_step, block021_data_flat106_original, block021_data_flat115_original]
def block021_data_flat117 : CoefficientMerge.Poly := [(nat_lit 5093, Int.ofNat (nat_lit 625628505600)), (nat_lit 5097, Int.ofNat (nat_lit 3027061094400)), (nat_lit 5099, Int.ofNat (nat_lit 4622441241600)), (nat_lit 5117, Int.ofNat (nat_lit 427179916800)), (nat_lit 5118, Int.ofNat (nat_lit 2412192625920)), (nat_lit 5120, Int.ofNat (nat_lit 12512392569600)), (nat_lit 5121, Int.ofNat (nat_lit 6764344227200)), (nat_lit 5122, Int.ofNat (nat_lit 11598417976320)), (nat_lit 5123, Int.ofNat (nat_lit 17871729019200)), (nat_lit 5137, Int.ofNat (nat_lit 1585379635200)), (nat_lit 5138, Int.ofNat (nat_lit 2686419532800)), (nat_lit 5139, Int.ofNat (nat_lit 2932238030400)), (nat_lit 5140, Int.ofNat (nat_lit 229178692800)), (nat_lit 5141, Int.ofNat (nat_lit 18882297907200)), (nat_lit 5142, Int.ofNat (nat_lit 16597632038400)), (nat_lit 5143, Int.ofNat (nat_lit 20194842312000)), (nat_lit 5144, Int.ofNat (nat_lit 38617257772800)), (nat_lit 5159, Int.ofNat (nat_lit 4954771584000)), (nat_lit 5160, Int.ofNat (nat_lit 8093431584000)), (nat_lit 5161, Int.ofNat (nat_lit 8260858368000))]
theorem block021_data_flat117_step : block021_data_flat117 = (CoefficientMerge.fastMerge block021_data_flat097 block021_data_flat116) := by decide +kernel
theorem block021_data_flat117_original : block021_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (625628505600 : Int) atom1576Coded) (CoefficientMerge.scale (3027061094400 : Int) atom1577Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4622441241600 : Int) atom1578Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1579Coded) (CoefficientMerge.scale (2412192625920 : Int) atom1580Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12512392569600 : Int) atom1581Coded) (CoefficientMerge.scale (6764344227200 : Int) atom1582Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11598417976320 : Int) atom1583Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17871729019200 : Int) atom1584Coded) (CoefficientMerge.scale (1585379635200 : Int) atom1585Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2686419532800 : Int) atom1586Coded) (CoefficientMerge.scale (2932238030400 : Int) atom1587Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229178692800 : Int) atom1588Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18882297907200 : Int) atom1589Coded) (CoefficientMerge.scale (16597632038400 : Int) atom1590Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20194842312000 : Int) atom1591Coded) (CoefficientMerge.scale (38617257772800 : Int) atom1592Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4954771584000 : Int) atom1593Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8093431584000 : Int) atom1594Coded) (CoefficientMerge.scale (8260858368000 : Int) atom1595Coded)))))) := by
  rw [block021_data_flat117_step, block021_data_flat097_original, block021_data_flat116_original]
def block021_data_flat118 : CoefficientMerge.Poly := [(nat_lit 5162, Int.ofNat (nat_lit 35367383520000))]
theorem block021_data_flat118_step : block021_data_flat118 = (CoefficientMerge.scale (35367383520000 : Int) atom1596Coded) := by decide +kernel
theorem block021_data_flat118_original : block021_data_flat118 = (CoefficientMerge.scale (35367383520000 : Int) atom1596Coded) := by
  rw [block021_data_flat118_step]
def block021_data_flat119 : CoefficientMerge.Poly := [(nat_lit 5163, Int.ofNat (nat_lit 36765453110400))]
theorem block021_data_flat119_step : block021_data_flat119 = (CoefficientMerge.scale (36765453110400 : Int) atom1597Coded) := by decide +kernel
theorem block021_data_flat119_original : block021_data_flat119 = (CoefficientMerge.scale (36765453110400 : Int) atom1597Coded) := by
  rw [block021_data_flat119_step]
def block021_data_flat120 : CoefficientMerge.Poly := [(nat_lit 5162, Int.ofNat (nat_lit 35367383520000)), (nat_lit 5163, Int.ofNat (nat_lit 36765453110400))]
theorem block021_data_flat120_step : block021_data_flat120 = (CoefficientMerge.fastMerge block021_data_flat118 block021_data_flat119) := by decide +kernel
theorem block021_data_flat120_original : block021_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (35367383520000 : Int) atom1596Coded) (CoefficientMerge.scale (36765453110400 : Int) atom1597Coded)) := by
  rw [block021_data_flat120_step, block021_data_flat118_original, block021_data_flat119_original]
def block021_data_flat121 : CoefficientMerge.Poly := [(nat_lit 5164, Int.ofNat (nat_lit 37994983488000))]
theorem block021_data_flat121_step : block021_data_flat121 = (CoefficientMerge.scale (37994983488000 : Int) atom1598Coded) := by decide +kernel
theorem block021_data_flat121_original : block021_data_flat121 = (CoefficientMerge.scale (37994983488000 : Int) atom1598Coded) := by
  rw [block021_data_flat121_step]
def block021_data_flat122 : CoefficientMerge.Poly := [(nat_lit 5165, Int.ofNat (nat_lit 63945789163200))]
theorem block021_data_flat122_step : block021_data_flat122 = (CoefficientMerge.scale (63945789163200 : Int) atom1599Coded) := by decide +kernel
theorem block021_data_flat122_original : block021_data_flat122 = (CoefficientMerge.scale (63945789163200 : Int) atom1599Coded) := by
  rw [block021_data_flat122_step]
def block021_data_flat123 : CoefficientMerge.Poly := [(nat_lit 5181, Int.ofNat (nat_lit 11306983564800))]
theorem block021_data_flat123_step : block021_data_flat123 = (CoefficientMerge.scale (11306983564800 : Int) atom1600Coded) := by decide +kernel
theorem block021_data_flat123_original : block021_data_flat123 = (CoefficientMerge.scale (11306983564800 : Int) atom1600Coded) := by
  rw [block021_data_flat123_step]
def block021_data_flat124 : CoefficientMerge.Poly := [(nat_lit 5165, Int.ofNat (nat_lit 63945789163200)), (nat_lit 5181, Int.ofNat (nat_lit 11306983564800))]
theorem block021_data_flat124_step : block021_data_flat124 = (CoefficientMerge.fastMerge block021_data_flat122 block021_data_flat123) := by decide +kernel
theorem block021_data_flat124_original : block021_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (63945789163200 : Int) atom1599Coded) (CoefficientMerge.scale (11306983564800 : Int) atom1600Coded)) := by
  rw [block021_data_flat124_step, block021_data_flat122_original, block021_data_flat123_original]
def block021_data_flat125 : CoefficientMerge.Poly := [(nat_lit 5164, Int.ofNat (nat_lit 37994983488000)), (nat_lit 5165, Int.ofNat (nat_lit 63945789163200)), (nat_lit 5181, Int.ofNat (nat_lit 11306983564800))]
theorem block021_data_flat125_step : block021_data_flat125 = (CoefficientMerge.fastMerge block021_data_flat121 block021_data_flat124) := by decide +kernel
theorem block021_data_flat125_original : block021_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (37994983488000 : Int) atom1598Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (63945789163200 : Int) atom1599Coded) (CoefficientMerge.scale (11306983564800 : Int) atom1600Coded))) := by
  rw [block021_data_flat125_step, block021_data_flat121_original, block021_data_flat124_original]
def block021_data_flat126 : CoefficientMerge.Poly := [(nat_lit 5162, Int.ofNat (nat_lit 35367383520000)), (nat_lit 5163, Int.ofNat (nat_lit 36765453110400)), (nat_lit 5164, Int.ofNat (nat_lit 37994983488000)), (nat_lit 5165, Int.ofNat (nat_lit 63945789163200)), (nat_lit 5181, Int.ofNat (nat_lit 11306983564800))]
theorem block021_data_flat126_step : block021_data_flat126 = (CoefficientMerge.fastMerge block021_data_flat120 block021_data_flat125) := by decide +kernel
theorem block021_data_flat126_original : block021_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35367383520000 : Int) atom1596Coded) (CoefficientMerge.scale (36765453110400 : Int) atom1597Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37994983488000 : Int) atom1598Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (63945789163200 : Int) atom1599Coded) (CoefficientMerge.scale (11306983564800 : Int) atom1600Coded)))) := by
  rw [block021_data_flat126_step, block021_data_flat120_original, block021_data_flat125_original]
def block021_data_flat127 : CoefficientMerge.Poly := [(nat_lit 5182, Int.ofNat (nat_lit 26897818752000))]
theorem block021_data_flat127_step : block021_data_flat127 = (CoefficientMerge.scale (26897818752000 : Int) atom1601Coded) := by decide +kernel
theorem block021_data_flat127_original : block021_data_flat127 = (CoefficientMerge.scale (26897818752000 : Int) atom1601Coded) := by
  rw [block021_data_flat127_step]
def block021_data_flat128 : CoefficientMerge.Poly := [(nat_lit 5183, Int.ofNat (nat_lit 60580379059200))]
theorem block021_data_flat128_step : block021_data_flat128 = (CoefficientMerge.scale (60580379059200 : Int) atom1602Coded) := by decide +kernel
theorem block021_data_flat128_original : block021_data_flat128 = (CoefficientMerge.scale (60580379059200 : Int) atom1602Coded) := by
  rw [block021_data_flat128_step]
def block021_data_flat129 : CoefficientMerge.Poly := [(nat_lit 5182, Int.ofNat (nat_lit 26897818752000)), (nat_lit 5183, Int.ofNat (nat_lit 60580379059200))]
theorem block021_data_flat129_step : block021_data_flat129 = (CoefficientMerge.fastMerge block021_data_flat127 block021_data_flat128) := by decide +kernel
theorem block021_data_flat129_original : block021_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (26897818752000 : Int) atom1601Coded) (CoefficientMerge.scale (60580379059200 : Int) atom1602Coded)) := by
  rw [block021_data_flat129_step, block021_data_flat127_original, block021_data_flat128_original]
def block021_data_flat130 : CoefficientMerge.Poly := [(nat_lit 5184, Int.ofNat (nat_lit 65618034048000))]
theorem block021_data_flat130_step : block021_data_flat130 = (CoefficientMerge.scale (65618034048000 : Int) atom1603Coded) := by decide +kernel
theorem block021_data_flat130_original : block021_data_flat130 = (CoefficientMerge.scale (65618034048000 : Int) atom1603Coded) := by
  rw [block021_data_flat130_step]
def block021_data_flat131 : CoefficientMerge.Poly := [(nat_lit 5185, Int.ofNat (nat_lit 51049231833600))]
theorem block021_data_flat131_step : block021_data_flat131 = (CoefficientMerge.scale (51049231833600 : Int) atom1604Coded) := by decide +kernel
theorem block021_data_flat131_original : block021_data_flat131 = (CoefficientMerge.scale (51049231833600 : Int) atom1604Coded) := by
  rw [block021_data_flat131_step]
def block021_data_flat132 : CoefficientMerge.Poly := [(nat_lit 5186, Int.ofNat (nat_lit 83972064960000))]
theorem block021_data_flat132_step : block021_data_flat132 = (CoefficientMerge.scale (83972064960000 : Int) atom1605Coded) := by decide +kernel
theorem block021_data_flat132_original : block021_data_flat132 = (CoefficientMerge.scale (83972064960000 : Int) atom1605Coded) := by
  rw [block021_data_flat132_step]
def block021_data_flat133 : CoefficientMerge.Poly := [(nat_lit 5185, Int.ofNat (nat_lit 51049231833600)), (nat_lit 5186, Int.ofNat (nat_lit 83972064960000))]
theorem block021_data_flat133_step : block021_data_flat133 = (CoefficientMerge.fastMerge block021_data_flat131 block021_data_flat132) := by decide +kernel
theorem block021_data_flat133_original : block021_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (51049231833600 : Int) atom1604Coded) (CoefficientMerge.scale (83972064960000 : Int) atom1605Coded)) := by
  rw [block021_data_flat133_step, block021_data_flat131_original, block021_data_flat132_original]
def block021_data_flat134 : CoefficientMerge.Poly := [(nat_lit 5184, Int.ofNat (nat_lit 65618034048000)), (nat_lit 5185, Int.ofNat (nat_lit 51049231833600)), (nat_lit 5186, Int.ofNat (nat_lit 83972064960000))]
theorem block021_data_flat134_step : block021_data_flat134 = (CoefficientMerge.fastMerge block021_data_flat130 block021_data_flat133) := by decide +kernel
theorem block021_data_flat134_original : block021_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (65618034048000 : Int) atom1603Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (51049231833600 : Int) atom1604Coded) (CoefficientMerge.scale (83972064960000 : Int) atom1605Coded))) := by
  rw [block021_data_flat134_step, block021_data_flat130_original, block021_data_flat133_original]
def block021_data_flat135 : CoefficientMerge.Poly := [(nat_lit 5182, Int.ofNat (nat_lit 26897818752000)), (nat_lit 5183, Int.ofNat (nat_lit 60580379059200)), (nat_lit 5184, Int.ofNat (nat_lit 65618034048000)), (nat_lit 5185, Int.ofNat (nat_lit 51049231833600)), (nat_lit 5186, Int.ofNat (nat_lit 83972064960000))]
theorem block021_data_flat135_step : block021_data_flat135 = (CoefficientMerge.fastMerge block021_data_flat129 block021_data_flat134) := by decide +kernel
theorem block021_data_flat135_original : block021_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26897818752000 : Int) atom1601Coded) (CoefficientMerge.scale (60580379059200 : Int) atom1602Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65618034048000 : Int) atom1603Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (51049231833600 : Int) atom1604Coded) (CoefficientMerge.scale (83972064960000 : Int) atom1605Coded)))) := by
  rw [block021_data_flat135_step, block021_data_flat129_original, block021_data_flat134_original]
def block021_data_flat136 : CoefficientMerge.Poly := [(nat_lit 5162, Int.ofNat (nat_lit 35367383520000)), (nat_lit 5163, Int.ofNat (nat_lit 36765453110400)), (nat_lit 5164, Int.ofNat (nat_lit 37994983488000)), (nat_lit 5165, Int.ofNat (nat_lit 63945789163200)), (nat_lit 5181, Int.ofNat (nat_lit 11306983564800)), (nat_lit 5182, Int.ofNat (nat_lit 26897818752000)), (nat_lit 5183, Int.ofNat (nat_lit 60580379059200)), (nat_lit 5184, Int.ofNat (nat_lit 65618034048000)), (nat_lit 5185, Int.ofNat (nat_lit 51049231833600)), (nat_lit 5186, Int.ofNat (nat_lit 83972064960000))]
theorem block021_data_flat136_step : block021_data_flat136 = (CoefficientMerge.fastMerge block021_data_flat126 block021_data_flat135) := by decide +kernel
theorem block021_data_flat136_original : block021_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35367383520000 : Int) atom1596Coded) (CoefficientMerge.scale (36765453110400 : Int) atom1597Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37994983488000 : Int) atom1598Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (63945789163200 : Int) atom1599Coded) (CoefficientMerge.scale (11306983564800 : Int) atom1600Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26897818752000 : Int) atom1601Coded) (CoefficientMerge.scale (60580379059200 : Int) atom1602Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65618034048000 : Int) atom1603Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (51049231833600 : Int) atom1604Coded) (CoefficientMerge.scale (83972064960000 : Int) atom1605Coded))))) := by
  rw [block021_data_flat136_step, block021_data_flat126_original, block021_data_flat135_original]
def block021_data_flat137 : CoefficientMerge.Poly := [(nat_lit 5203, Int.ofNat (nat_lit 11599244213760))]
theorem block021_data_flat137_step : block021_data_flat137 = (CoefficientMerge.scale (11599244213760 : Int) atom1606Coded) := by decide +kernel
theorem block021_data_flat137_original : block021_data_flat137 = (CoefficientMerge.scale (11599244213760 : Int) atom1606Coded) := by
  rw [block021_data_flat137_step]
def block021_data_flat138 : CoefficientMerge.Poly := [(nat_lit 5204, Int.ofNat (nat_lit 54517358246400))]
theorem block021_data_flat138_step : block021_data_flat138 = (CoefficientMerge.scale (54517358246400 : Int) atom1607Coded) := by decide +kernel
theorem block021_data_flat138_original : block021_data_flat138 = (CoefficientMerge.scale (54517358246400 : Int) atom1607Coded) := by
  rw [block021_data_flat138_step]
def block021_data_flat139 : CoefficientMerge.Poly := [(nat_lit 5203, Int.ofNat (nat_lit 11599244213760)), (nat_lit 5204, Int.ofNat (nat_lit 54517358246400))]
theorem block021_data_flat139_step : block021_data_flat139 = (CoefficientMerge.fastMerge block021_data_flat137 block021_data_flat138) := by decide +kernel
theorem block021_data_flat139_original : block021_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11599244213760 : Int) atom1606Coded) (CoefficientMerge.scale (54517358246400 : Int) atom1607Coded)) := by
  rw [block021_data_flat139_step, block021_data_flat137_original, block021_data_flat138_original]
def block021_data_flat140 : CoefficientMerge.Poly := [(nat_lit 5205, Int.ofNat (nat_lit 68922680601600))]
theorem block021_data_flat140_step : block021_data_flat140 = (CoefficientMerge.scale (68922680601600 : Int) atom1608Coded) := by decide +kernel
theorem block021_data_flat140_original : block021_data_flat140 = (CoefficientMerge.scale (68922680601600 : Int) atom1608Coded) := by
  rw [block021_data_flat140_step]
def block021_data_flat141 : CoefficientMerge.Poly := [(nat_lit 5206, Int.ofNat (nat_lit 54987390259200))]
theorem block021_data_flat141_step : block021_data_flat141 = (CoefficientMerge.scale (54987390259200 : Int) atom1609Coded) := by decide +kernel
theorem block021_data_flat141_original : block021_data_flat141 = (CoefficientMerge.scale (54987390259200 : Int) atom1609Coded) := by
  rw [block021_data_flat141_step]
def block021_data_flat142 : CoefficientMerge.Poly := [(nat_lit 5207, Int.ofNat (nat_lit 76694201740800))]
theorem block021_data_flat142_step : block021_data_flat142 = (CoefficientMerge.scale (76694201740800 : Int) atom1610Coded) := by decide +kernel
theorem block021_data_flat142_original : block021_data_flat142 = (CoefficientMerge.scale (76694201740800 : Int) atom1610Coded) := by
  rw [block021_data_flat142_step]
def block021_data_flat143 : CoefficientMerge.Poly := [(nat_lit 5206, Int.ofNat (nat_lit 54987390259200)), (nat_lit 5207, Int.ofNat (nat_lit 76694201740800))]
theorem block021_data_flat143_step : block021_data_flat143 = (CoefficientMerge.fastMerge block021_data_flat141 block021_data_flat142) := by decide +kernel
theorem block021_data_flat143_original : block021_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (54987390259200 : Int) atom1609Coded) (CoefficientMerge.scale (76694201740800 : Int) atom1610Coded)) := by
  rw [block021_data_flat143_step, block021_data_flat141_original, block021_data_flat142_original]
def block021_data_flat144 : CoefficientMerge.Poly := [(nat_lit 5205, Int.ofNat (nat_lit 68922680601600)), (nat_lit 5206, Int.ofNat (nat_lit 54987390259200)), (nat_lit 5207, Int.ofNat (nat_lit 76694201740800))]
theorem block021_data_flat144_step : block021_data_flat144 = (CoefficientMerge.fastMerge block021_data_flat140 block021_data_flat143) := by decide +kernel
theorem block021_data_flat144_original : block021_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (68922680601600 : Int) atom1608Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54987390259200 : Int) atom1609Coded) (CoefficientMerge.scale (76694201740800 : Int) atom1610Coded))) := by
  rw [block021_data_flat144_step, block021_data_flat140_original, block021_data_flat143_original]
def block021_data_flat145 : CoefficientMerge.Poly := [(nat_lit 5203, Int.ofNat (nat_lit 11599244213760)), (nat_lit 5204, Int.ofNat (nat_lit 54517358246400)), (nat_lit 5205, Int.ofNat (nat_lit 68922680601600)), (nat_lit 5206, Int.ofNat (nat_lit 54987390259200)), (nat_lit 5207, Int.ofNat (nat_lit 76694201740800))]
theorem block021_data_flat145_step : block021_data_flat145 = (CoefficientMerge.fastMerge block021_data_flat139 block021_data_flat144) := by decide +kernel
theorem block021_data_flat145_original : block021_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11599244213760 : Int) atom1606Coded) (CoefficientMerge.scale (54517358246400 : Int) atom1607Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68922680601600 : Int) atom1608Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54987390259200 : Int) atom1609Coded) (CoefficientMerge.scale (76694201740800 : Int) atom1610Coded)))) := by
  rw [block021_data_flat145_step, block021_data_flat139_original, block021_data_flat144_original]
def block021_data_flat146 : CoefficientMerge.Poly := [(nat_lit 5225, Int.ofNat (nat_lit 41556232166400))]
theorem block021_data_flat146_step : block021_data_flat146 = (CoefficientMerge.scale (41556232166400 : Int) atom1611Coded) := by decide +kernel
theorem block021_data_flat146_original : block021_data_flat146 = (CoefficientMerge.scale (41556232166400 : Int) atom1611Coded) := by
  rw [block021_data_flat146_step]
def block021_data_flat147 : CoefficientMerge.Poly := [(nat_lit 5226, Int.ofNat (nat_lit 83144666304000))]
theorem block021_data_flat147_step : block021_data_flat147 = (CoefficientMerge.scale (83144666304000 : Int) atom1612Coded) := by decide +kernel
theorem block021_data_flat147_original : block021_data_flat147 = (CoefficientMerge.scale (83144666304000 : Int) atom1612Coded) := by
  rw [block021_data_flat147_step]
def block021_data_flat148 : CoefficientMerge.Poly := [(nat_lit 5225, Int.ofNat (nat_lit 41556232166400)), (nat_lit 5226, Int.ofNat (nat_lit 83144666304000))]
theorem block021_data_flat148_step : block021_data_flat148 = (CoefficientMerge.fastMerge block021_data_flat146 block021_data_flat147) := by decide +kernel
theorem block021_data_flat148_original : block021_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (41556232166400 : Int) atom1611Coded) (CoefficientMerge.scale (83144666304000 : Int) atom1612Coded)) := by
  rw [block021_data_flat148_step, block021_data_flat146_original, block021_data_flat147_original]
def block021_data_flat149 : CoefficientMerge.Poly := [(nat_lit 5227, Int.ofNat (nat_lit 63150637939200))]
theorem block021_data_flat149_step : block021_data_flat149 = (CoefficientMerge.scale (63150637939200 : Int) atom1613Coded) := by decide +kernel
theorem block021_data_flat149_original : block021_data_flat149 = (CoefficientMerge.scale (63150637939200 : Int) atom1613Coded) := by
  rw [block021_data_flat149_step]
def block021_data_flat150 : CoefficientMerge.Poly := [(nat_lit 5228, Int.ofNat (nat_lit 71866230105600))]
theorem block021_data_flat150_step : block021_data_flat150 = (CoefficientMerge.scale (71866230105600 : Int) atom1614Coded) := by decide +kernel
theorem block021_data_flat150_original : block021_data_flat150 = (CoefficientMerge.scale (71866230105600 : Int) atom1614Coded) := by
  rw [block021_data_flat150_step]
def block021_data_flat151 : CoefficientMerge.Poly := [(nat_lit 5247, Int.ofNat (nat_lit 36462275136000))]
theorem block021_data_flat151_step : block021_data_flat151 = (CoefficientMerge.scale (36462275136000 : Int) atom1615Coded) := by decide +kernel
theorem block021_data_flat151_original : block021_data_flat151 = (CoefficientMerge.scale (36462275136000 : Int) atom1615Coded) := by
  rw [block021_data_flat151_step]
def block021_data_flat152 : CoefficientMerge.Poly := [(nat_lit 5228, Int.ofNat (nat_lit 71866230105600)), (nat_lit 5247, Int.ofNat (nat_lit 36462275136000))]
theorem block021_data_flat152_step : block021_data_flat152 = (CoefficientMerge.fastMerge block021_data_flat150 block021_data_flat151) := by decide +kernel
theorem block021_data_flat152_original : block021_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (71866230105600 : Int) atom1614Coded) (CoefficientMerge.scale (36462275136000 : Int) atom1615Coded)) := by
  rw [block021_data_flat152_step, block021_data_flat150_original, block021_data_flat151_original]
def block021_data_flat153 : CoefficientMerge.Poly := [(nat_lit 5227, Int.ofNat (nat_lit 63150637939200)), (nat_lit 5228, Int.ofNat (nat_lit 71866230105600)), (nat_lit 5247, Int.ofNat (nat_lit 36462275136000))]
theorem block021_data_flat153_step : block021_data_flat153 = (CoefficientMerge.fastMerge block021_data_flat149 block021_data_flat152) := by decide +kernel
theorem block021_data_flat153_original : block021_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (63150637939200 : Int) atom1613Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (71866230105600 : Int) atom1614Coded) (CoefficientMerge.scale (36462275136000 : Int) atom1615Coded))) := by
  rw [block021_data_flat153_step, block021_data_flat149_original, block021_data_flat152_original]
def block021_data_flat154 : CoefficientMerge.Poly := [(nat_lit 5225, Int.ofNat (nat_lit 41556232166400)), (nat_lit 5226, Int.ofNat (nat_lit 83144666304000)), (nat_lit 5227, Int.ofNat (nat_lit 63150637939200)), (nat_lit 5228, Int.ofNat (nat_lit 71866230105600)), (nat_lit 5247, Int.ofNat (nat_lit 36462275136000))]
theorem block021_data_flat154_step : block021_data_flat154 = (CoefficientMerge.fastMerge block021_data_flat148 block021_data_flat153) := by decide +kernel
theorem block021_data_flat154_original : block021_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (41556232166400 : Int) atom1611Coded) (CoefficientMerge.scale (83144666304000 : Int) atom1612Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (63150637939200 : Int) atom1613Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (71866230105600 : Int) atom1614Coded) (CoefficientMerge.scale (36462275136000 : Int) atom1615Coded)))) := by
  rw [block021_data_flat154_step, block021_data_flat148_original, block021_data_flat153_original]
def block021_data_flat155 : CoefficientMerge.Poly := [(nat_lit 5203, Int.ofNat (nat_lit 11599244213760)), (nat_lit 5204, Int.ofNat (nat_lit 54517358246400)), (nat_lit 5205, Int.ofNat (nat_lit 68922680601600)), (nat_lit 5206, Int.ofNat (nat_lit 54987390259200)), (nat_lit 5207, Int.ofNat (nat_lit 76694201740800)), (nat_lit 5225, Int.ofNat (nat_lit 41556232166400)), (nat_lit 5226, Int.ofNat (nat_lit 83144666304000)), (nat_lit 5227, Int.ofNat (nat_lit 63150637939200)), (nat_lit 5228, Int.ofNat (nat_lit 71866230105600)), (nat_lit 5247, Int.ofNat (nat_lit 36462275136000))]
theorem block021_data_flat155_step : block021_data_flat155 = (CoefficientMerge.fastMerge block021_data_flat145 block021_data_flat154) := by decide +kernel
theorem block021_data_flat155_original : block021_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11599244213760 : Int) atom1606Coded) (CoefficientMerge.scale (54517358246400 : Int) atom1607Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68922680601600 : Int) atom1608Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54987390259200 : Int) atom1609Coded) (CoefficientMerge.scale (76694201740800 : Int) atom1610Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (41556232166400 : Int) atom1611Coded) (CoefficientMerge.scale (83144666304000 : Int) atom1612Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (63150637939200 : Int) atom1613Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (71866230105600 : Int) atom1614Coded) (CoefficientMerge.scale (36462275136000 : Int) atom1615Coded))))) := by
  rw [block021_data_flat155_step, block021_data_flat145_original, block021_data_flat154_original]
def block021_data_flat156 : CoefficientMerge.Poly := [(nat_lit 5162, Int.ofNat (nat_lit 35367383520000)), (nat_lit 5163, Int.ofNat (nat_lit 36765453110400)), (nat_lit 5164, Int.ofNat (nat_lit 37994983488000)), (nat_lit 5165, Int.ofNat (nat_lit 63945789163200)), (nat_lit 5181, Int.ofNat (nat_lit 11306983564800)), (nat_lit 5182, Int.ofNat (nat_lit 26897818752000)), (nat_lit 5183, Int.ofNat (nat_lit 60580379059200)), (nat_lit 5184, Int.ofNat (nat_lit 65618034048000)), (nat_lit 5185, Int.ofNat (nat_lit 51049231833600)), (nat_lit 5186, Int.ofNat (nat_lit 83972064960000)), (nat_lit 5203, Int.ofNat (nat_lit 11599244213760)), (nat_lit 5204, Int.ofNat (nat_lit 54517358246400)), (nat_lit 5205, Int.ofNat (nat_lit 68922680601600)), (nat_lit 5206, Int.ofNat (nat_lit 54987390259200)), (nat_lit 5207, Int.ofNat (nat_lit 76694201740800)), (nat_lit 5225, Int.ofNat (nat_lit 41556232166400)), (nat_lit 5226, Int.ofNat (nat_lit 83144666304000)), (nat_lit 5227, Int.ofNat (nat_lit 63150637939200)), (nat_lit 5228, Int.ofNat (nat_lit 71866230105600)), (nat_lit 5247, Int.ofNat (nat_lit 36462275136000))]
theorem block021_data_flat156_step : block021_data_flat156 = (CoefficientMerge.fastMerge block021_data_flat136 block021_data_flat155) := by decide +kernel
theorem block021_data_flat156_original : block021_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35367383520000 : Int) atom1596Coded) (CoefficientMerge.scale (36765453110400 : Int) atom1597Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37994983488000 : Int) atom1598Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (63945789163200 : Int) atom1599Coded) (CoefficientMerge.scale (11306983564800 : Int) atom1600Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26897818752000 : Int) atom1601Coded) (CoefficientMerge.scale (60580379059200 : Int) atom1602Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65618034048000 : Int) atom1603Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (51049231833600 : Int) atom1604Coded) (CoefficientMerge.scale (83972064960000 : Int) atom1605Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11599244213760 : Int) atom1606Coded) (CoefficientMerge.scale (54517358246400 : Int) atom1607Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68922680601600 : Int) atom1608Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54987390259200 : Int) atom1609Coded) (CoefficientMerge.scale (76694201740800 : Int) atom1610Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (41556232166400 : Int) atom1611Coded) (CoefficientMerge.scale (83144666304000 : Int) atom1612Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (63150637939200 : Int) atom1613Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (71866230105600 : Int) atom1614Coded) (CoefficientMerge.scale (36462275136000 : Int) atom1615Coded)))))) := by
  rw [block021_data_flat156_step, block021_data_flat136_original, block021_data_flat155_original]
def block021_data_flat157 : CoefficientMerge.Poly := [(nat_lit 5093, Int.ofNat (nat_lit 625628505600)), (nat_lit 5097, Int.ofNat (nat_lit 3027061094400)), (nat_lit 5099, Int.ofNat (nat_lit 4622441241600)), (nat_lit 5117, Int.ofNat (nat_lit 427179916800)), (nat_lit 5118, Int.ofNat (nat_lit 2412192625920)), (nat_lit 5120, Int.ofNat (nat_lit 12512392569600)), (nat_lit 5121, Int.ofNat (nat_lit 6764344227200)), (nat_lit 5122, Int.ofNat (nat_lit 11598417976320)), (nat_lit 5123, Int.ofNat (nat_lit 17871729019200)), (nat_lit 5137, Int.ofNat (nat_lit 1585379635200)), (nat_lit 5138, Int.ofNat (nat_lit 2686419532800)), (nat_lit 5139, Int.ofNat (nat_lit 2932238030400)), (nat_lit 5140, Int.ofNat (nat_lit 229178692800)), (nat_lit 5141, Int.ofNat (nat_lit 18882297907200)), (nat_lit 5142, Int.ofNat (nat_lit 16597632038400)), (nat_lit 5143, Int.ofNat (nat_lit 20194842312000)), (nat_lit 5144, Int.ofNat (nat_lit 38617257772800)), (nat_lit 5159, Int.ofNat (nat_lit 4954771584000)), (nat_lit 5160, Int.ofNat (nat_lit 8093431584000)), (nat_lit 5161, Int.ofNat (nat_lit 8260858368000)), (nat_lit 5162, Int.ofNat (nat_lit 35367383520000)), (nat_lit 5163, Int.ofNat (nat_lit 36765453110400)), (nat_lit 5164, Int.ofNat (nat_lit 37994983488000)), (nat_lit 5165, Int.ofNat (nat_lit 63945789163200)), (nat_lit 5181, Int.ofNat (nat_lit 11306983564800)), (nat_lit 5182, Int.ofNat (nat_lit 26897818752000)), (nat_lit 5183, Int.ofNat (nat_lit 60580379059200)), (nat_lit 5184, Int.ofNat (nat_lit 65618034048000)), (nat_lit 5185, Int.ofNat (nat_lit 51049231833600)), (nat_lit 5186, Int.ofNat (nat_lit 83972064960000)), (nat_lit 5203, Int.ofNat (nat_lit 11599244213760)), (nat_lit 5204, Int.ofNat (nat_lit 54517358246400)), (nat_lit 5205, Int.ofNat (nat_lit 68922680601600)), (nat_lit 5206, Int.ofNat (nat_lit 54987390259200)), (nat_lit 5207, Int.ofNat (nat_lit 76694201740800)), (nat_lit 5225, Int.ofNat (nat_lit 41556232166400)), (nat_lit 5226, Int.ofNat (nat_lit 83144666304000)), (nat_lit 5227, Int.ofNat (nat_lit 63150637939200)), (nat_lit 5228, Int.ofNat (nat_lit 71866230105600)), (nat_lit 5247, Int.ofNat (nat_lit 36462275136000))]
theorem block021_data_flat157_step : block021_data_flat157 = (CoefficientMerge.fastMerge block021_data_flat117 block021_data_flat156) := by decide +kernel
theorem block021_data_flat157_original : block021_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (625628505600 : Int) atom1576Coded) (CoefficientMerge.scale (3027061094400 : Int) atom1577Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4622441241600 : Int) atom1578Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1579Coded) (CoefficientMerge.scale (2412192625920 : Int) atom1580Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12512392569600 : Int) atom1581Coded) (CoefficientMerge.scale (6764344227200 : Int) atom1582Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11598417976320 : Int) atom1583Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17871729019200 : Int) atom1584Coded) (CoefficientMerge.scale (1585379635200 : Int) atom1585Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2686419532800 : Int) atom1586Coded) (CoefficientMerge.scale (2932238030400 : Int) atom1587Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229178692800 : Int) atom1588Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18882297907200 : Int) atom1589Coded) (CoefficientMerge.scale (16597632038400 : Int) atom1590Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20194842312000 : Int) atom1591Coded) (CoefficientMerge.scale (38617257772800 : Int) atom1592Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4954771584000 : Int) atom1593Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8093431584000 : Int) atom1594Coded) (CoefficientMerge.scale (8260858368000 : Int) atom1595Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35367383520000 : Int) atom1596Coded) (CoefficientMerge.scale (36765453110400 : Int) atom1597Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37994983488000 : Int) atom1598Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (63945789163200 : Int) atom1599Coded) (CoefficientMerge.scale (11306983564800 : Int) atom1600Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26897818752000 : Int) atom1601Coded) (CoefficientMerge.scale (60580379059200 : Int) atom1602Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65618034048000 : Int) atom1603Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (51049231833600 : Int) atom1604Coded) (CoefficientMerge.scale (83972064960000 : Int) atom1605Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11599244213760 : Int) atom1606Coded) (CoefficientMerge.scale (54517358246400 : Int) atom1607Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68922680601600 : Int) atom1608Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54987390259200 : Int) atom1609Coded) (CoefficientMerge.scale (76694201740800 : Int) atom1610Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (41556232166400 : Int) atom1611Coded) (CoefficientMerge.scale (83144666304000 : Int) atom1612Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (63150637939200 : Int) atom1613Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (71866230105600 : Int) atom1614Coded) (CoefficientMerge.scale (36462275136000 : Int) atom1615Coded))))))) := by
  rw [block021_data_flat157_step, block021_data_flat117_original, block021_data_flat156_original]
def block021_data_flat158 : CoefficientMerge.Poly := [(nat_lit 4679, Int.ofNat (nat_lit 12235036884000)), (nat_lit 4680, Int.ofNat (nat_lit 10060008291200)), (nat_lit 4681, Int.ofNat (nat_lit 19067301227520)), (nat_lit 4682, Int.ofNat (nat_lit 30545055374400)), (nat_lit 4696, Int.ofNat (nat_lit 3637196294400)), (nat_lit 4697, Int.ofNat (nat_lit 6880901068800)), (nat_lit 4698, Int.ofNat (nat_lit 8610848568000)), (nat_lit 4699, Int.ofNat (nat_lit 7226753652000)), (nat_lit 4700, Int.ofNat (nat_lit 24723029116800)), (nat_lit 4701, Int.ofNat (nat_lit 25487556040800)), (nat_lit 4702, Int.ofNat (nat_lit 29609621330400)), (nat_lit 4703, Int.ofNat (nat_lit 48203677670400)), (nat_lit 4718, Int.ofNat (nat_lit 7524616377600)), (nat_lit 4719, Int.ofNat (nat_lit 13837762108800)), (nat_lit 4720, Int.ofNat (nat_lit 14444665250400)), (nat_lit 4721, Int.ofNat (nat_lit 39514858588800)), (nat_lit 4722, Int.ofNat (nat_lit 43438294015200)), (nat_lit 4723, Int.ofNat (nat_lit 44668852452000)), (nat_lit 4724, Int.ofNat (nat_lit 70445302603200)), (nat_lit 4740, Int.ofNat (nat_lit 14207114880000)), (nat_lit 4741, Int.ofNat (nat_lit 31648905514800)), (nat_lit 4742, Int.ofNat (nat_lit 63044385868800)), (nat_lit 4743, Int.ofNat (nat_lit 68251193312400)), (nat_lit 4744, Int.ofNat (nat_lit 52704630997200)), (nat_lit 4745, Int.ofNat (nat_lit 84534447690000)), (nat_lit 4762, Int.ofNat (nat_lit 13258427535360)), (nat_lit 4763, Int.ofNat (nat_lit 55380479086800)), (nat_lit 4764, Int.ofNat (nat_lit 67640031660600)), (nat_lit 4765, Int.ofNat (nat_lit 51789484202400)), (nat_lit 4766, Int.ofNat (nat_lit 71505263913300)), (nat_lit 4784, Int.ofNat (nat_lit 41806301644800)), (nat_lit 4785, Int.ofNat (nat_lit 79803065286000)), (nat_lit 4786, Int.ofNat (nat_lit 57575234833200)), (nat_lit 4787, Int.ofNat (nat_lit 64172281244400)), (nat_lit 4806, Int.ofNat (nat_lit 32379144373800)), (nat_lit 4807, Int.ofNat (nat_lit 46613159346600)), (nat_lit 4808, Int.ofNat (nat_lit 56384774100900)), (nat_lit 4828, Int.ofNat (nat_lit 9434482696800)), (nat_lit 4829, Int.ofNat (nat_lit 29846674802700)), (nat_lit 4850, Int.ofNat (nat_lit 16605245065500)), (nat_lit 5093, Int.ofNat (nat_lit 625628505600)), (nat_lit 5097, Int.ofNat (nat_lit 3027061094400)), (nat_lit 5099, Int.ofNat (nat_lit 4622441241600)), (nat_lit 5117, Int.ofNat (nat_lit 427179916800)), (nat_lit 5118, Int.ofNat (nat_lit 2412192625920)), (nat_lit 5120, Int.ofNat (nat_lit 12512392569600)), (nat_lit 5121, Int.ofNat (nat_lit 6764344227200)), (nat_lit 5122, Int.ofNat (nat_lit 11598417976320)), (nat_lit 5123, Int.ofNat (nat_lit 17871729019200)), (nat_lit 5137, Int.ofNat (nat_lit 1585379635200)), (nat_lit 5138, Int.ofNat (nat_lit 2686419532800)), (nat_lit 5139, Int.ofNat (nat_lit 2932238030400)), (nat_lit 5140, Int.ofNat (nat_lit 229178692800)), (nat_lit 5141, Int.ofNat (nat_lit 18882297907200)), (nat_lit 5142, Int.ofNat (nat_lit 16597632038400)), (nat_lit 5143, Int.ofNat (nat_lit 20194842312000)), (nat_lit 5144, Int.ofNat (nat_lit 38617257772800)), (nat_lit 5159, Int.ofNat (nat_lit 4954771584000)), (nat_lit 5160, Int.ofNat (nat_lit 8093431584000)), (nat_lit 5161, Int.ofNat (nat_lit 8260858368000)), (nat_lit 5162, Int.ofNat (nat_lit 35367383520000)), (nat_lit 5163, Int.ofNat (nat_lit 36765453110400)), (nat_lit 5164, Int.ofNat (nat_lit 37994983488000)), (nat_lit 5165, Int.ofNat (nat_lit 63945789163200)), (nat_lit 5181, Int.ofNat (nat_lit 11306983564800)), (nat_lit 5182, Int.ofNat (nat_lit 26897818752000)), (nat_lit 5183, Int.ofNat (nat_lit 60580379059200)), (nat_lit 5184, Int.ofNat (nat_lit 65618034048000)), (nat_lit 5185, Int.ofNat (nat_lit 51049231833600)), (nat_lit 5186, Int.ofNat (nat_lit 83972064960000)), (nat_lit 5203, Int.ofNat (nat_lit 11599244213760)), (nat_lit 5204, Int.ofNat (nat_lit 54517358246400)), (nat_lit 5205, Int.ofNat (nat_lit 68922680601600)), (nat_lit 5206, Int.ofNat (nat_lit 54987390259200)), (nat_lit 5207, Int.ofNat (nat_lit 76694201740800)), (nat_lit 5225, Int.ofNat (nat_lit 41556232166400)), (nat_lit 5226, Int.ofNat (nat_lit 83144666304000)), (nat_lit 5227, Int.ofNat (nat_lit 63150637939200)), (nat_lit 5228, Int.ofNat (nat_lit 71866230105600)), (nat_lit 5247, Int.ofNat (nat_lit 36462275136000))]
theorem block021_data_flat158_step : block021_data_flat158 = (CoefficientMerge.fastMerge block021_data_flat078 block021_data_flat157) := by decide +kernel
theorem block021_data_flat158_original : block021_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12235036884000 : Int) atom1536Coded) (CoefficientMerge.scale (10060008291200 : Int) atom1537Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19067301227520 : Int) atom1538Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30545055374400 : Int) atom1539Coded) (CoefficientMerge.scale (3637196294400 : Int) atom1540Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6880901068800 : Int) atom1541Coded) (CoefficientMerge.scale (8610848568000 : Int) atom1542Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7226753652000 : Int) atom1543Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24723029116800 : Int) atom1544Coded) (CoefficientMerge.scale (25487556040800 : Int) atom1545Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (29609621330400 : Int) atom1546Coded) (CoefficientMerge.scale (48203677670400 : Int) atom1547Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7524616377600 : Int) atom1548Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13837762108800 : Int) atom1549Coded) (CoefficientMerge.scale (14444665250400 : Int) atom1550Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39514858588800 : Int) atom1551Coded) (CoefficientMerge.scale (43438294015200 : Int) atom1552Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44668852452000 : Int) atom1553Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70445302603200 : Int) atom1554Coded) (CoefficientMerge.scale (14207114880000 : Int) atom1555Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31648905514800 : Int) atom1556Coded) (CoefficientMerge.scale (63044385868800 : Int) atom1557Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68251193312400 : Int) atom1558Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52704630997200 : Int) atom1559Coded) (CoefficientMerge.scale (84534447690000 : Int) atom1560Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13258427535360 : Int) atom1561Coded) (CoefficientMerge.scale (55380479086800 : Int) atom1562Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67640031660600 : Int) atom1563Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (51789484202400 : Int) atom1564Coded) (CoefficientMerge.scale (71505263913300 : Int) atom1565Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (41806301644800 : Int) atom1566Coded) (CoefficientMerge.scale (79803065286000 : Int) atom1567Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57575234833200 : Int) atom1568Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64172281244400 : Int) atom1569Coded) (CoefficientMerge.scale (32379144373800 : Int) atom1570Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46613159346600 : Int) atom1571Coded) (CoefficientMerge.scale (56384774100900 : Int) atom1572Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9434482696800 : Int) atom1573Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29846674802700 : Int) atom1574Coded) (CoefficientMerge.scale (16605245065500 : Int) atom1575Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (625628505600 : Int) atom1576Coded) (CoefficientMerge.scale (3027061094400 : Int) atom1577Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4622441241600 : Int) atom1578Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1579Coded) (CoefficientMerge.scale (2412192625920 : Int) atom1580Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12512392569600 : Int) atom1581Coded) (CoefficientMerge.scale (6764344227200 : Int) atom1582Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11598417976320 : Int) atom1583Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17871729019200 : Int) atom1584Coded) (CoefficientMerge.scale (1585379635200 : Int) atom1585Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2686419532800 : Int) atom1586Coded) (CoefficientMerge.scale (2932238030400 : Int) atom1587Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229178692800 : Int) atom1588Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18882297907200 : Int) atom1589Coded) (CoefficientMerge.scale (16597632038400 : Int) atom1590Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20194842312000 : Int) atom1591Coded) (CoefficientMerge.scale (38617257772800 : Int) atom1592Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4954771584000 : Int) atom1593Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8093431584000 : Int) atom1594Coded) (CoefficientMerge.scale (8260858368000 : Int) atom1595Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35367383520000 : Int) atom1596Coded) (CoefficientMerge.scale (36765453110400 : Int) atom1597Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37994983488000 : Int) atom1598Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (63945789163200 : Int) atom1599Coded) (CoefficientMerge.scale (11306983564800 : Int) atom1600Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26897818752000 : Int) atom1601Coded) (CoefficientMerge.scale (60580379059200 : Int) atom1602Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65618034048000 : Int) atom1603Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (51049231833600 : Int) atom1604Coded) (CoefficientMerge.scale (83972064960000 : Int) atom1605Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11599244213760 : Int) atom1606Coded) (CoefficientMerge.scale (54517358246400 : Int) atom1607Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68922680601600 : Int) atom1608Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54987390259200 : Int) atom1609Coded) (CoefficientMerge.scale (76694201740800 : Int) atom1610Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (41556232166400 : Int) atom1611Coded) (CoefficientMerge.scale (83144666304000 : Int) atom1612Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (63150637939200 : Int) atom1613Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (71866230105600 : Int) atom1614Coded) (CoefficientMerge.scale (36462275136000 : Int) atom1615Coded)))))))) := by
  rw [block021_data_flat158_step, block021_data_flat078_original, block021_data_flat157_original]
def block021_data_flat159 : CoefficientMerge.Poly := [(nat_lit 4679, Int.ofNat (nat_lit 12235036884000)), (nat_lit 4680, Int.ofNat (nat_lit 10060008291200)), (nat_lit 4681, Int.ofNat (nat_lit 19067301227520)), (nat_lit 4682, Int.ofNat (nat_lit 30545055374400)), (nat_lit 4696, Int.ofNat (nat_lit 3637196294400)), (nat_lit 4697, Int.ofNat (nat_lit 6880901068800)), (nat_lit 4698, Int.ofNat (nat_lit 8610848568000)), (nat_lit 4699, Int.ofNat (nat_lit 7226753652000)), (nat_lit 4700, Int.ofNat (nat_lit 24723029116800)), (nat_lit 4701, Int.ofNat (nat_lit 25487556040800)), (nat_lit 4702, Int.ofNat (nat_lit 29609621330400)), (nat_lit 4703, Int.ofNat (nat_lit 48203677670400)), (nat_lit 4718, Int.ofNat (nat_lit 7524616377600)), (nat_lit 4719, Int.ofNat (nat_lit 13837762108800)), (nat_lit 4720, Int.ofNat (nat_lit 14444665250400)), (nat_lit 4721, Int.ofNat (nat_lit 39514858588800)), (nat_lit 4722, Int.ofNat (nat_lit 43438294015200)), (nat_lit 4723, Int.ofNat (nat_lit 44668852452000)), (nat_lit 4724, Int.ofNat (nat_lit 70445302603200)), (nat_lit 4740, Int.ofNat (nat_lit 14207114880000)), (nat_lit 4741, Int.ofNat (nat_lit 31648905514800)), (nat_lit 4742, Int.ofNat (nat_lit 63044385868800)), (nat_lit 4743, Int.ofNat (nat_lit 68251193312400)), (nat_lit 4744, Int.ofNat (nat_lit 52704630997200)), (nat_lit 4745, Int.ofNat (nat_lit 84534447690000)), (nat_lit 4762, Int.ofNat (nat_lit 13258427535360)), (nat_lit 4763, Int.ofNat (nat_lit 55380479086800)), (nat_lit 4764, Int.ofNat (nat_lit 67640031660600)), (nat_lit 4765, Int.ofNat (nat_lit 51789484202400)), (nat_lit 4766, Int.ofNat (nat_lit 71505263913300)), (nat_lit 4784, Int.ofNat (nat_lit 41806301644800)), (nat_lit 4785, Int.ofNat (nat_lit 79803065286000)), (nat_lit 4786, Int.ofNat (nat_lit 57575234833200)), (nat_lit 4787, Int.ofNat (nat_lit 64172281244400)), (nat_lit 4806, Int.ofNat (nat_lit 32379144373800)), (nat_lit 4807, Int.ofNat (nat_lit 46613159346600)), (nat_lit 4808, Int.ofNat (nat_lit 56384774100900)), (nat_lit 4828, Int.ofNat (nat_lit 9434482696800)), (nat_lit 4829, Int.ofNat (nat_lit 29846674802700)), (nat_lit 4850, Int.ofNat (nat_lit 16605245065500)), (nat_lit 5093, Int.ofNat (nat_lit 625628505600)), (nat_lit 5097, Int.ofNat (nat_lit 3027061094400)), (nat_lit 5099, Int.ofNat (nat_lit 4622441241600)), (nat_lit 5117, Int.ofNat (nat_lit 427179916800)), (nat_lit 5118, Int.ofNat (nat_lit 2412192625920)), (nat_lit 5120, Int.ofNat (nat_lit 12512392569600)), (nat_lit 5121, Int.ofNat (nat_lit 6764344227200)), (nat_lit 5122, Int.ofNat (nat_lit 11598417976320)), (nat_lit 5123, Int.ofNat (nat_lit 17871729019200)), (nat_lit 5137, Int.ofNat (nat_lit 1585379635200)), (nat_lit 5138, Int.ofNat (nat_lit 2686419532800)), (nat_lit 5139, Int.ofNat (nat_lit 2932238030400)), (nat_lit 5140, Int.ofNat (nat_lit 229178692800)), (nat_lit 5141, Int.ofNat (nat_lit 18882297907200)), (nat_lit 5142, Int.ofNat (nat_lit 16597632038400)), (nat_lit 5143, Int.ofNat (nat_lit 20194842312000)), (nat_lit 5144, Int.ofNat (nat_lit 38617257772800)), (nat_lit 5159, Int.ofNat (nat_lit 4954771584000)), (nat_lit 5160, Int.ofNat (nat_lit 8093431584000)), (nat_lit 5161, Int.ofNat (nat_lit 8260858368000)), (nat_lit 5162, Int.ofNat (nat_lit 35367383520000)), (nat_lit 5163, Int.ofNat (nat_lit 36765453110400)), (nat_lit 5164, Int.ofNat (nat_lit 37994983488000)), (nat_lit 5165, Int.ofNat (nat_lit 63945789163200)), (nat_lit 5181, Int.ofNat (nat_lit 11306983564800)), (nat_lit 5182, Int.ofNat (nat_lit 26897818752000)), (nat_lit 5183, Int.ofNat (nat_lit 60580379059200)), (nat_lit 5184, Int.ofNat (nat_lit 65618034048000)), (nat_lit 5185, Int.ofNat (nat_lit 51049231833600)), (nat_lit 5186, Int.ofNat (nat_lit 83972064960000)), (nat_lit 5203, Int.ofNat (nat_lit 11599244213760)), (nat_lit 5204, Int.ofNat (nat_lit 54517358246400)), (nat_lit 5205, Int.ofNat (nat_lit 68922680601600)), (nat_lit 5206, Int.ofNat (nat_lit 54987390259200)), (nat_lit 5207, Int.ofNat (nat_lit 76694201740800)), (nat_lit 5225, Int.ofNat (nat_lit 41556232166400)), (nat_lit 5226, Int.ofNat (nat_lit 83144666304000)), (nat_lit 5227, Int.ofNat (nat_lit 63150637939200)), (nat_lit 5228, Int.ofNat (nat_lit 71866230105600)), (nat_lit 5247, Int.ofNat (nat_lit 36462275136000))]
theorem block021_data_flat159_step : block021_data_flat159 = (CoefficientMerge.trim block021_data_flat158) := by decide +kernel
theorem block021_data_flat159_original : block021_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12235036884000 : Int) atom1536Coded) (CoefficientMerge.scale (10060008291200 : Int) atom1537Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19067301227520 : Int) atom1538Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30545055374400 : Int) atom1539Coded) (CoefficientMerge.scale (3637196294400 : Int) atom1540Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6880901068800 : Int) atom1541Coded) (CoefficientMerge.scale (8610848568000 : Int) atom1542Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7226753652000 : Int) atom1543Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24723029116800 : Int) atom1544Coded) (CoefficientMerge.scale (25487556040800 : Int) atom1545Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (29609621330400 : Int) atom1546Coded) (CoefficientMerge.scale (48203677670400 : Int) atom1547Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7524616377600 : Int) atom1548Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13837762108800 : Int) atom1549Coded) (CoefficientMerge.scale (14444665250400 : Int) atom1550Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39514858588800 : Int) atom1551Coded) (CoefficientMerge.scale (43438294015200 : Int) atom1552Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44668852452000 : Int) atom1553Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70445302603200 : Int) atom1554Coded) (CoefficientMerge.scale (14207114880000 : Int) atom1555Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31648905514800 : Int) atom1556Coded) (CoefficientMerge.scale (63044385868800 : Int) atom1557Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68251193312400 : Int) atom1558Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52704630997200 : Int) atom1559Coded) (CoefficientMerge.scale (84534447690000 : Int) atom1560Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13258427535360 : Int) atom1561Coded) (CoefficientMerge.scale (55380479086800 : Int) atom1562Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67640031660600 : Int) atom1563Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (51789484202400 : Int) atom1564Coded) (CoefficientMerge.scale (71505263913300 : Int) atom1565Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (41806301644800 : Int) atom1566Coded) (CoefficientMerge.scale (79803065286000 : Int) atom1567Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57575234833200 : Int) atom1568Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64172281244400 : Int) atom1569Coded) (CoefficientMerge.scale (32379144373800 : Int) atom1570Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46613159346600 : Int) atom1571Coded) (CoefficientMerge.scale (56384774100900 : Int) atom1572Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9434482696800 : Int) atom1573Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29846674802700 : Int) atom1574Coded) (CoefficientMerge.scale (16605245065500 : Int) atom1575Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (625628505600 : Int) atom1576Coded) (CoefficientMerge.scale (3027061094400 : Int) atom1577Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4622441241600 : Int) atom1578Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1579Coded) (CoefficientMerge.scale (2412192625920 : Int) atom1580Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12512392569600 : Int) atom1581Coded) (CoefficientMerge.scale (6764344227200 : Int) atom1582Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11598417976320 : Int) atom1583Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17871729019200 : Int) atom1584Coded) (CoefficientMerge.scale (1585379635200 : Int) atom1585Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2686419532800 : Int) atom1586Coded) (CoefficientMerge.scale (2932238030400 : Int) atom1587Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229178692800 : Int) atom1588Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18882297907200 : Int) atom1589Coded) (CoefficientMerge.scale (16597632038400 : Int) atom1590Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20194842312000 : Int) atom1591Coded) (CoefficientMerge.scale (38617257772800 : Int) atom1592Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4954771584000 : Int) atom1593Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8093431584000 : Int) atom1594Coded) (CoefficientMerge.scale (8260858368000 : Int) atom1595Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35367383520000 : Int) atom1596Coded) (CoefficientMerge.scale (36765453110400 : Int) atom1597Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37994983488000 : Int) atom1598Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (63945789163200 : Int) atom1599Coded) (CoefficientMerge.scale (11306983564800 : Int) atom1600Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26897818752000 : Int) atom1601Coded) (CoefficientMerge.scale (60580379059200 : Int) atom1602Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65618034048000 : Int) atom1603Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (51049231833600 : Int) atom1604Coded) (CoefficientMerge.scale (83972064960000 : Int) atom1605Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11599244213760 : Int) atom1606Coded) (CoefficientMerge.scale (54517358246400 : Int) atom1607Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68922680601600 : Int) atom1608Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54987390259200 : Int) atom1609Coded) (CoefficientMerge.scale (76694201740800 : Int) atom1610Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (41556232166400 : Int) atom1611Coded) (CoefficientMerge.scale (83144666304000 : Int) atom1612Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (63150637939200 : Int) atom1613Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (71866230105600 : Int) atom1614Coded) (CoefficientMerge.scale (36462275136000 : Int) atom1615Coded))))))))) := by
  rw [block021_data_flat159_step, block021_data_flat158_original]
theorem block021_data : block021 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12235036884000 : Int) atom1536Coded) (CoefficientMerge.scale (10060008291200 : Int) atom1537Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19067301227520 : Int) atom1538Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30545055374400 : Int) atom1539Coded) (CoefficientMerge.scale (3637196294400 : Int) atom1540Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6880901068800 : Int) atom1541Coded) (CoefficientMerge.scale (8610848568000 : Int) atom1542Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7226753652000 : Int) atom1543Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24723029116800 : Int) atom1544Coded) (CoefficientMerge.scale (25487556040800 : Int) atom1545Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (29609621330400 : Int) atom1546Coded) (CoefficientMerge.scale (48203677670400 : Int) atom1547Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7524616377600 : Int) atom1548Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13837762108800 : Int) atom1549Coded) (CoefficientMerge.scale (14444665250400 : Int) atom1550Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39514858588800 : Int) atom1551Coded) (CoefficientMerge.scale (43438294015200 : Int) atom1552Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44668852452000 : Int) atom1553Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70445302603200 : Int) atom1554Coded) (CoefficientMerge.scale (14207114880000 : Int) atom1555Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31648905514800 : Int) atom1556Coded) (CoefficientMerge.scale (63044385868800 : Int) atom1557Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68251193312400 : Int) atom1558Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52704630997200 : Int) atom1559Coded) (CoefficientMerge.scale (84534447690000 : Int) atom1560Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13258427535360 : Int) atom1561Coded) (CoefficientMerge.scale (55380479086800 : Int) atom1562Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67640031660600 : Int) atom1563Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (51789484202400 : Int) atom1564Coded) (CoefficientMerge.scale (71505263913300 : Int) atom1565Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (41806301644800 : Int) atom1566Coded) (CoefficientMerge.scale (79803065286000 : Int) atom1567Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57575234833200 : Int) atom1568Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64172281244400 : Int) atom1569Coded) (CoefficientMerge.scale (32379144373800 : Int) atom1570Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46613159346600 : Int) atom1571Coded) (CoefficientMerge.scale (56384774100900 : Int) atom1572Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9434482696800 : Int) atom1573Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29846674802700 : Int) atom1574Coded) (CoefficientMerge.scale (16605245065500 : Int) atom1575Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (625628505600 : Int) atom1576Coded) (CoefficientMerge.scale (3027061094400 : Int) atom1577Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4622441241600 : Int) atom1578Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1579Coded) (CoefficientMerge.scale (2412192625920 : Int) atom1580Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12512392569600 : Int) atom1581Coded) (CoefficientMerge.scale (6764344227200 : Int) atom1582Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11598417976320 : Int) atom1583Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17871729019200 : Int) atom1584Coded) (CoefficientMerge.scale (1585379635200 : Int) atom1585Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2686419532800 : Int) atom1586Coded) (CoefficientMerge.scale (2932238030400 : Int) atom1587Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229178692800 : Int) atom1588Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18882297907200 : Int) atom1589Coded) (CoefficientMerge.scale (16597632038400 : Int) atom1590Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20194842312000 : Int) atom1591Coded) (CoefficientMerge.scale (38617257772800 : Int) atom1592Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4954771584000 : Int) atom1593Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8093431584000 : Int) atom1594Coded) (CoefficientMerge.scale (8260858368000 : Int) atom1595Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35367383520000 : Int) atom1596Coded) (CoefficientMerge.scale (36765453110400 : Int) atom1597Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37994983488000 : Int) atom1598Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (63945789163200 : Int) atom1599Coded) (CoefficientMerge.scale (11306983564800 : Int) atom1600Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26897818752000 : Int) atom1601Coded) (CoefficientMerge.scale (60580379059200 : Int) atom1602Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65618034048000 : Int) atom1603Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (51049231833600 : Int) atom1604Coded) (CoefficientMerge.scale (83972064960000 : Int) atom1605Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11599244213760 : Int) atom1606Coded) (CoefficientMerge.scale (54517358246400 : Int) atom1607Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68922680601600 : Int) atom1608Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54987390259200 : Int) atom1609Coded) (CoefficientMerge.scale (76694201740800 : Int) atom1610Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (41556232166400 : Int) atom1611Coded) (CoefficientMerge.scale (83144666304000 : Int) atom1612Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (63150637939200 : Int) atom1613Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (71866230105600 : Int) atom1614Coded) (CoefficientMerge.scale (36462275136000 : Int) atom1615Coded)))))))) := by
  have h : block021 = block021_data_flat159 := by decide +kernel
  exact h.trans block021_data_flat159_original
theorem block021_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) block021 := by
  rw [block021_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1536Coded_nonneg g hg hA hB) (atom1537Coded_nonneg g hg hA hB)) (add_nonneg (atom1538Coded_nonneg g hg hA hB) (add_nonneg (atom1539Coded_nonneg g hg hA hB) (atom1540Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1541Coded_nonneg g hg hA hB) (atom1542Coded_nonneg g hg hA hB)) (add_nonneg (atom1543Coded_nonneg g hg hA hB) (add_nonneg (atom1544Coded_nonneg g hg hA hB) (atom1545Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1546Coded_nonneg g hg hA hB) (atom1547Coded_nonneg g hg hA hB)) (add_nonneg (atom1548Coded_nonneg g hg hA hB) (add_nonneg (atom1549Coded_nonneg g hg hA hB) (atom1550Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1551Coded_nonneg g hg hA hB) (atom1552Coded_nonneg g hg hA hB)) (add_nonneg (atom1553Coded_nonneg g hg hA hB) (add_nonneg (atom1554Coded_nonneg g hg hA hB) (atom1555Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1556Coded_nonneg g hg hA hB) (atom1557Coded_nonneg g hg hA hB)) (add_nonneg (atom1558Coded_nonneg g hg hA hB) (add_nonneg (atom1559Coded_nonneg g hg hA hB) (atom1560Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1561Coded_nonneg g hg hA hB) (atom1562Coded_nonneg g hg hA hB)) (add_nonneg (atom1563Coded_nonneg g hg hA hB) (add_nonneg (atom1564Coded_nonneg g hg hA hB) (atom1565Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1566Coded_nonneg g hg hA hB) (atom1567Coded_nonneg g hg hA hB)) (add_nonneg (atom1568Coded_nonneg g hg hA hB) (add_nonneg (atom1569Coded_nonneg g hg hA hB) (atom1570Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1571Coded_nonneg g hg hA hB) (atom1572Coded_nonneg g hg hA hB)) (add_nonneg (atom1573Coded_nonneg g hg hA hB) (add_nonneg (atom1574Coded_nonneg g hg hA hB) (atom1575Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1576Coded_nonneg g hg hA hB) (atom1577Coded_nonneg g hg hA hB)) (add_nonneg (atom1578Coded_nonneg g hg hA hB) (add_nonneg (atom1579Coded_nonneg g hg hA hB) (atom1580Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1581Coded_nonneg g hg hA hB) (atom1582Coded_nonneg g hg hA hB)) (add_nonneg (atom1583Coded_nonneg g hg hA hB) (add_nonneg (atom1584Coded_nonneg g hg hA hB) (atom1585Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1586Coded_nonneg g hg hA hB) (atom1587Coded_nonneg g hg hA hB)) (add_nonneg (atom1588Coded_nonneg g hg hA hB) (add_nonneg (atom1589Coded_nonneg g hg hA hB) (atom1590Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1591Coded_nonneg g hg hA hB) (atom1592Coded_nonneg g hg hA hB)) (add_nonneg (atom1593Coded_nonneg g hg hA hB) (add_nonneg (atom1594Coded_nonneg g hg hA hB) (atom1595Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1596Coded_nonneg g hg hA hB) (atom1597Coded_nonneg g hg hA hB)) (add_nonneg (atom1598Coded_nonneg g hg hA hB) (add_nonneg (atom1599Coded_nonneg g hg hA hB) (atom1600Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1601Coded_nonneg g hg hA hB) (atom1602Coded_nonneg g hg hA hB)) (add_nonneg (atom1603Coded_nonneg g hg hA hB) (add_nonneg (atom1604Coded_nonneg g hg hA hB) (atom1605Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1606Coded_nonneg g hg hA hB) (atom1607Coded_nonneg g hg hA hB)) (add_nonneg (atom1608Coded_nonneg g hg hA hB) (add_nonneg (atom1609Coded_nonneg g hg hA hB) (atom1610Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1611Coded_nonneg g hg hA hB) (atom1612Coded_nonneg g hg hA hB)) (add_nonneg (atom1613Coded_nonneg g hg hA hB) (add_nonneg (atom1614Coded_nonneg g hg hA hB) (atom1615Coded_nonneg g hg hA hB))))))))

end APPT.Finite21
