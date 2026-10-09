import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom1329 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1329 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1329 = ((g 4) * (g 8) * (g 14)) := by
  norm_num [atom1329, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1329_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (95552995507200 : Int) atom1329) := by
  rw [SparsePolynomial.eval_scale, eval_atom1329]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1329Coded : CoefficientMerge.Poly := [(nat_lit 2510, Int.ofNat (nat_lit 1))]
theorem atom1329Coded_decode : atom1329 = SparsePolynomial.decodeCubic 24 atom1329Coded := by decide +kernel
theorem atom1329Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (95552995507200 : Int) atom1329Coded) := by
  have h := atom1329_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1329Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1330 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1330 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1330 = ((g 4) * (g 8) * (g 15)) := by
  norm_num [atom1330, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1330_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (99003939148800 : Int) atom1330) := by
  rw [SparsePolynomial.eval_scale, eval_atom1330]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1330Coded : CoefficientMerge.Poly := [(nat_lit 2511, Int.ofNat (nat_lit 1))]
theorem atom1330Coded_decode : atom1330 = SparsePolynomial.decodeCubic 24 atom1330Coded := by decide +kernel
theorem atom1330Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (99003939148800 : Int) atom1330Coded) := by
  have h := atom1330_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1330Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1331 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1331 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1331 = ((g 4) * (g 8) * (g 16)) := by
  norm_num [atom1331, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1331_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (90632372544000 : Int) atom1331) := by
  rw [SparsePolynomial.eval_scale, eval_atom1331]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1331Coded : CoefficientMerge.Poly := [(nat_lit 2512, Int.ofNat (nat_lit 1))]
theorem atom1331Coded_decode : atom1331 = SparsePolynomial.decodeCubic 24 atom1331Coded := by decide +kernel
theorem atom1331Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (90632372544000 : Int) atom1331Coded) := by
  have h := atom1331_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1331Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1332 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1332 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1332 = ((g 4) * (g 8) * (g 17)) := by
  norm_num [atom1332, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1332_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (96840978393600 : Int) atom1332) := by
  rw [SparsePolynomial.eval_scale, eval_atom1332]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1332Coded : CoefficientMerge.Poly := [(nat_lit 2513, Int.ofNat (nat_lit 1))]
theorem atom1332Coded_decode : atom1332 = SparsePolynomial.decodeCubic 24 atom1332Coded := by decide +kernel
theorem atom1332Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (96840978393600 : Int) atom1332Coded) := by
  have h := atom1332_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1332Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1333 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1333 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1333 = ((g 4) * (g 8) * (g 18)) := by
  norm_num [atom1333, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1333_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (137461084992000 : Int) atom1333) := by
  rw [SparsePolynomial.eval_scale, eval_atom1333]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 8) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1333Coded : CoefficientMerge.Poly := [(nat_lit 2514, Int.ofNat (nat_lit 1))]
theorem atom1333Coded_decode : atom1333 = SparsePolynomial.decodeCubic 24 atom1333Coded := by decide +kernel
theorem atom1333Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (137461084992000 : Int) atom1333Coded) := by
  have h := atom1333_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1333Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1334 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1334 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1334 = ((g 4) * (g 8) * (g 19)) := by
  norm_num [atom1334, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1334_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (157970956046400 : Int) atom1334) := by
  rw [SparsePolynomial.eval_scale, eval_atom1334]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 8) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1334Coded : CoefficientMerge.Poly := [(nat_lit 2515, Int.ofNat (nat_lit 1))]
theorem atom1334Coded_decode : atom1334 = SparsePolynomial.decodeCubic 24 atom1334Coded := by decide +kernel
theorem atom1334Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (157970956046400 : Int) atom1334Coded) := by
  have h := atom1334_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1334Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1335 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1335 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1335 = ((g 4) * (g 8) * (g 20)) := by
  norm_num [atom1335, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1335_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (196654739198400 : Int) atom1335) := by
  rw [SparsePolynomial.eval_scale, eval_atom1335]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 8) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1335Coded : CoefficientMerge.Poly := [(nat_lit 2516, Int.ofNat (nat_lit 1))]
theorem atom1335Coded_decode : atom1335 = SparsePolynomial.decodeCubic 24 atom1335Coded := by decide +kernel
theorem atom1335Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (196654739198400 : Int) atom1335Coded) := by
  have h := atom1335_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1335Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1336 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1336 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1336 = ((g 4) * (g 8) * (g 21)) := by
  norm_num [atom1336, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1336_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (267813699652800 : Int) atom1336) := by
  rw [SparsePolynomial.eval_scale, eval_atom1336]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 4) * (g 8) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1336Coded : CoefficientMerge.Poly := [(nat_lit 2517, Int.ofNat (nat_lit 1))]
theorem atom1336Coded_decode : atom1336 = SparsePolynomial.decodeCubic 24 atom1336Coded := by decide +kernel
theorem atom1336Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (267813699652800 : Int) atom1336Coded) := by
  have h := atom1336_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1336Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1337 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1337 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1337 = ((g 4) * (g 8) * (g 22)) := by
  norm_num [atom1337, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1337_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (338972660107200 : Int) atom1337) := by
  rw [SparsePolynomial.eval_scale, eval_atom1337]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 4) * (g 8) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1337Coded : CoefficientMerge.Poly := [(nat_lit 2518, Int.ofNat (nat_lit 1))]
theorem atom1337Coded_decode : atom1337 = SparsePolynomial.decodeCubic 24 atom1337Coded := by decide +kernel
theorem atom1337Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (338972660107200 : Int) atom1337Coded) := by
  have h := atom1337_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1337Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1338 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1338 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1338 = ((g 4) * (g 8) * (g 23)) := by
  norm_num [atom1338, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1338_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (410131620561600 : Int) atom1338) := by
  rw [SparsePolynomial.eval_scale, eval_atom1338]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 4) * (g 8) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1338Coded : CoefficientMerge.Poly := [(nat_lit 2519, Int.ofNat (nat_lit 1))]
theorem atom1338Coded_decode : atom1338 = SparsePolynomial.decodeCubic 24 atom1338Coded := by decide +kernel
theorem atom1338Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (410131620561600 : Int) atom1338Coded) := by
  have h := atom1338_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1338Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1339 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom1339 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1339 = ((g 4) * (g 9) * (g 9)) := by
  norm_num [atom1339, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1339_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (69667045180128 : Int) atom1339) := by
  rw [SparsePolynomial.eval_scale, eval_atom1339]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1339Coded : CoefficientMerge.Poly := [(nat_lit 2529, Int.ofNat (nat_lit 1))]
theorem atom1339Coded_decode : atom1339 = SparsePolynomial.decodeCubic 24 atom1339Coded := by decide +kernel
theorem atom1339Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (69667045180128 : Int) atom1339Coded) := by
  have h := atom1339_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1339Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1340 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1340 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1340 = ((g 4) * (g 9) * (g 10)) := by
  norm_num [atom1340, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1340_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (129230222210496 : Int) atom1340) := by
  rw [SparsePolynomial.eval_scale, eval_atom1340]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1340Coded : CoefficientMerge.Poly := [(nat_lit 2530, Int.ofNat (nat_lit 1))]
theorem atom1340Coded_decode : atom1340 = SparsePolynomial.decodeCubic 24 atom1340Coded := by decide +kernel
theorem atom1340Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (129230222210496 : Int) atom1340Coded) := by
  have h := atom1340_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1340Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1341 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1341 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1341 = ((g 4) * (g 9) * (g 11)) := by
  norm_num [atom1341, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1341_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (123772944236832 : Int) atom1341) := by
  rw [SparsePolynomial.eval_scale, eval_atom1341]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1341Coded : CoefficientMerge.Poly := [(nat_lit 2531, Int.ofNat (nat_lit 1))]
theorem atom1341Coded_decode : atom1341 = SparsePolynomial.decodeCubic 24 atom1341Coded := by decide +kernel
theorem atom1341Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (123772944236832 : Int) atom1341Coded) := by
  have h := atom1341_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1341Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1342 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1342 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1342 = ((g 4) * (g 9) * (g 12)) := by
  norm_num [atom1342, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1342_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (151694926460352 : Int) atom1342) := by
  rw [SparsePolynomial.eval_scale, eval_atom1342]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1342Coded : CoefficientMerge.Poly := [(nat_lit 2532, Int.ofNat (nat_lit 1))]
theorem atom1342Coded_decode : atom1342 = SparsePolynomial.decodeCubic 24 atom1342Coded := by decide +kernel
theorem atom1342Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (151694926460352 : Int) atom1342Coded) := by
  have h := atom1342_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1342Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1343 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1343 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1343 = ((g 4) * (g 9) * (g 13)) := by
  norm_num [atom1343, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1343_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (139950755353728 : Int) atom1343) := by
  rw [SparsePolynomial.eval_scale, eval_atom1343]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1343Coded : CoefficientMerge.Poly := [(nat_lit 2533, Int.ofNat (nat_lit 1))]
theorem atom1343Coded_decode : atom1343 = SparsePolynomial.decodeCubic 24 atom1343Coded := by decide +kernel
theorem atom1343Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (139950755353728 : Int) atom1343Coded) := by
  have h := atom1343_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1343Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1344 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1344 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1344 = ((g 4) * (g 9) * (g 14)) := by
  norm_num [atom1344, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1344_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (127615362006528 : Int) atom1344) := by
  rw [SparsePolynomial.eval_scale, eval_atom1344]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1344Coded : CoefficientMerge.Poly := [(nat_lit 2534, Int.ofNat (nat_lit 1))]
theorem atom1344Coded_decode : atom1344 = SparsePolynomial.decodeCubic 24 atom1344Coded := by decide +kernel
theorem atom1344Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (127615362006528 : Int) atom1344Coded) := by
  have h := atom1344_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1344Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1345 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1345 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1345 = ((g 4) * (g 9) * (g 15)) := by
  norm_num [atom1345, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1345_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (130066975254528 : Int) atom1345) := by
  rw [SparsePolynomial.eval_scale, eval_atom1345]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1345Coded : CoefficientMerge.Poly := [(nat_lit 2535, Int.ofNat (nat_lit 1))]
theorem atom1345Coded_decode : atom1345 = SparsePolynomial.decodeCubic 24 atom1345Coded := by decide +kernel
theorem atom1345Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (130066975254528 : Int) atom1345Coded) := by
  have h := atom1345_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1345Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1346 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1346 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1346 = ((g 4) * (g 9) * (g 16)) := by
  norm_num [atom1346, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1346_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (120696078256128 : Int) atom1346) := by
  rw [SparsePolynomial.eval_scale, eval_atom1346]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1346Coded : CoefficientMerge.Poly := [(nat_lit 2536, Int.ofNat (nat_lit 1))]
theorem atom1346Coded_decode : atom1346 = SparsePolynomial.decodeCubic 24 atom1346Coded := by decide +kernel
theorem atom1346Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (120696078256128 : Int) atom1346Coded) := by
  have h := atom1346_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1346Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1347 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1347 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1347 = ((g 4) * (g 9) * (g 17)) := by
  norm_num [atom1347, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1347_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (125905353712128 : Int) atom1347) := by
  rw [SparsePolynomial.eval_scale, eval_atom1347]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1347Coded : CoefficientMerge.Poly := [(nat_lit 2537, Int.ofNat (nat_lit 1))]
theorem atom1347Coded_decode : atom1347 = SparsePolynomial.decodeCubic 24 atom1347Coded := by decide +kernel
theorem atom1347Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (125905353712128 : Int) atom1347Coded) := by
  have h := atom1347_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1347Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1348 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1348 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1348 = ((g 4) * (g 9) * (g 18)) := by
  norm_num [atom1348, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1348_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (167729597747712 : Int) atom1348) := by
  rw [SparsePolynomial.eval_scale, eval_atom1348]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 9) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1348Coded : CoefficientMerge.Poly := [(nat_lit 2538, Int.ofNat (nat_lit 1))]
theorem atom1348Coded_decode : atom1348 = SparsePolynomial.decodeCubic 24 atom1348Coded := by decide +kernel
theorem atom1348Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (167729597747712 : Int) atom1348Coded) := by
  have h := atom1348_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1348Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1349 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1349 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1349 = ((g 4) * (g 9) * (g 19)) := by
  norm_num [atom1349, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1349_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (191647074070080 : Int) atom1349) := by
  rw [SparsePolynomial.eval_scale, eval_atom1349]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 9) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1349Coded : CoefficientMerge.Poly := [(nat_lit 2539, Int.ofNat (nat_lit 1))]
theorem atom1349Coded_decode : atom1349 = SparsePolynomial.decodeCubic 24 atom1349Coded := by decide +kernel
theorem atom1349Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (191647074070080 : Int) atom1349Coded) := by
  have h := atom1349_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1349Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1350 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1350 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1350 = ((g 4) * (g 9) * (g 20)) := by
  norm_num [atom1350, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1350_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (233738462490048 : Int) atom1350) := by
  rw [SparsePolynomial.eval_scale, eval_atom1350]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 9) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1350Coded : CoefficientMerge.Poly := [(nat_lit 2540, Int.ofNat (nat_lit 1))]
theorem atom1350Coded_decode : atom1350 = SparsePolynomial.decodeCubic 24 atom1350Coded := by decide +kernel
theorem atom1350Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (233738462490048 : Int) atom1350Coded) := by
  have h := atom1350_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1350Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1351 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1351 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1351 = ((g 4) * (g 9) * (g 21)) := by
  norm_num [atom1351, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1351_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (312711963873984 : Int) atom1351) := by
  rw [SparsePolynomial.eval_scale, eval_atom1351]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 4) * (g 9) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1351Coded : CoefficientMerge.Poly := [(nat_lit 2541, Int.ofNat (nat_lit 1))]
theorem atom1351Coded_decode : atom1351 = SparsePolynomial.decodeCubic 24 atom1351Coded := by decide +kernel
theorem atom1351Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (312711963873984 : Int) atom1351Coded) := by
  have h := atom1351_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1351Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1352 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1352 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1352 = ((g 4) * (g 9) * (g 22)) := by
  norm_num [atom1352, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1352_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (391685465257920 : Int) atom1352) := by
  rw [SparsePolynomial.eval_scale, eval_atom1352]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 4) * (g 9) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1352Coded : CoefficientMerge.Poly := [(nat_lit 2542, Int.ofNat (nat_lit 1))]
theorem atom1352Coded_decode : atom1352 = SparsePolynomial.decodeCubic 24 atom1352Coded := by decide +kernel
theorem atom1352Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (391685465257920 : Int) atom1352Coded) := by
  have h := atom1352_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1352Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1353 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1353 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1353 = ((g 4) * (g 9) * (g 23)) := by
  norm_num [atom1353, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1353_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (470658966641856 : Int) atom1353) := by
  rw [SparsePolynomial.eval_scale, eval_atom1353]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 4) * (g 9) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1353Coded : CoefficientMerge.Poly := [(nat_lit 2543, Int.ofNat (nat_lit 1))]
theorem atom1353Coded_decode : atom1353 = SparsePolynomial.decodeCubic 24 atom1353Coded := by decide +kernel
theorem atom1353Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (470658966641856 : Int) atom1353Coded) := by
  have h := atom1353_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1353Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1354 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1354 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1354 = ((g 4) * (g 10) * (g 10)) := by
  norm_num [atom1354, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1354_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (94497216108768 : Int) atom1354) := by
  rw [SparsePolynomial.eval_scale, eval_atom1354]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1354Coded : CoefficientMerge.Poly := [(nat_lit 2554, Int.ofNat (nat_lit 1))]
theorem atom1354Coded_decode : atom1354 = SparsePolynomial.decodeCubic 24 atom1354Coded := by decide +kernel
theorem atom1354Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (94497216108768 : Int) atom1354Coded) := by
  have h := atom1354_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1354Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1355 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1355 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1355 = ((g 4) * (g 10) * (g 11)) := by
  norm_num [atom1355, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1355_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (188725167351072 : Int) atom1355) := by
  rw [SparsePolynomial.eval_scale, eval_atom1355]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1355Coded : CoefficientMerge.Poly := [(nat_lit 2555, Int.ofNat (nat_lit 1))]
theorem atom1355Coded_decode : atom1355 = SparsePolynomial.decodeCubic 24 atom1355Coded := by decide +kernel
theorem atom1355Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (188725167351072 : Int) atom1355Coded) := by
  have h := atom1355_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1355Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1356 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1356 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1356 = ((g 4) * (g 10) * (g 12)) := by
  norm_num [atom1356, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1356_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (211544185862592 : Int) atom1356) := by
  rw [SparsePolynomial.eval_scale, eval_atom1356]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1356Coded : CoefficientMerge.Poly := [(nat_lit 2556, Int.ofNat (nat_lit 1))]
theorem atom1356Coded_decode : atom1356 = SparsePolynomial.decodeCubic 24 atom1356Coded := by decide +kernel
theorem atom1356Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (211544185862592 : Int) atom1356Coded) := by
  have h := atom1356_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1356Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1357 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1357 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1357 = ((g 4) * (g 10) * (g 13)) := by
  norm_num [atom1357, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1357_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (200863132195968 : Int) atom1357) := by
  rw [SparsePolynomial.eval_scale, eval_atom1357]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1357Coded : CoefficientMerge.Poly := [(nat_lit 2557, Int.ofNat (nat_lit 1))]
theorem atom1357Coded_decode : atom1357 = SparsePolynomial.decodeCubic 24 atom1357Coded := by decide +kernel
theorem atom1357Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (200863132195968 : Int) atom1357Coded) := by
  have h := atom1357_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1357Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1358 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1358 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1358 = ((g 4) * (g 10) * (g 14)) := by
  norm_num [atom1358, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1358_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (186507815712768 : Int) atom1358) := by
  rw [SparsePolynomial.eval_scale, eval_atom1358]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1358Coded : CoefficientMerge.Poly := [(nat_lit 2558, Int.ofNat (nat_lit 1))]
theorem atom1358Coded_decode : atom1358 = SparsePolynomial.decodeCubic 24 atom1358Coded := by decide +kernel
theorem atom1358Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (186507815712768 : Int) atom1358Coded) := by
  have h := atom1358_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1358Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1359 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1359 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1359 = ((g 4) * (g 10) * (g 15)) := by
  norm_num [atom1359, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1359_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (186939505824768 : Int) atom1359) := by
  rw [SparsePolynomial.eval_scale, eval_atom1359]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1359Coded : CoefficientMerge.Poly := [(nat_lit 2559, Int.ofNat (nat_lit 1))]
theorem atom1359Coded_decode : atom1359 = SparsePolynomial.decodeCubic 24 atom1359Coded := by decide +kernel
theorem atom1359Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (186939505824768 : Int) atom1359Coded) := by
  have h := atom1359_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1359Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1360 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1360 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1360 = ((g 4) * (g 10) * (g 16)) := by
  norm_num [atom1360, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1360_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (175548685690368 : Int) atom1360) := by
  rw [SparsePolynomial.eval_scale, eval_atom1360]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1360Coded : CoefficientMerge.Poly := [(nat_lit 2560, Int.ofNat (nat_lit 1))]
theorem atom1360Coded_decode : atom1360 = SparsePolynomial.decodeCubic 24 atom1360Coded := by decide +kernel
theorem atom1360Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (175548685690368 : Int) atom1360Coded) := by
  have h := atom1360_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1360Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1361 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1361 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1361 = ((g 4) * (g 10) * (g 17)) := by
  norm_num [atom1361, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1361_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (178738038010368 : Int) atom1361) := by
  rw [SparsePolynomial.eval_scale, eval_atom1361]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1361Coded : CoefficientMerge.Poly := [(nat_lit 2561, Int.ofNat (nat_lit 1))]
theorem atom1361Coded_decode : atom1361 = SparsePolynomial.decodeCubic 24 atom1361Coded := by decide +kernel
theorem atom1361Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (178738038010368 : Int) atom1361Coded) := by
  have h := atom1361_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1361Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1362 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1362 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1362 = ((g 4) * (g 10) * (g 18)) := by
  norm_num [atom1362, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1362_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (217275122921472 : Int) atom1362) := by
  rw [SparsePolynomial.eval_scale, eval_atom1362]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1362Coded : CoefficientMerge.Poly := [(nat_lit 2562, Int.ofNat (nat_lit 1))]
theorem atom1362Coded_decode : atom1362 = SparsePolynomial.decodeCubic 24 atom1362Coded := by decide +kernel
theorem atom1362Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (217275122921472 : Int) atom1362Coded) := by
  have h := atom1362_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1362Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1363 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1363 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1363 = ((g 4) * (g 10) * (g 19)) := by
  norm_num [atom1363, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1363_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (236638204130880 : Int) atom1363) := by
  rw [SparsePolynomial.eval_scale, eval_atom1363]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1363Coded : CoefficientMerge.Poly := [(nat_lit 2563, Int.ofNat (nat_lit 1))]
theorem atom1363Coded_decode : atom1363 = SparsePolynomial.decodeCubic 24 atom1363Coded := by decide +kernel
theorem atom1363Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (236638204130880 : Int) atom1363Coded) := by
  have h := atom1363_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1363Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1364 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1364 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1364 = ((g 4) * (g 10) * (g 20)) := by
  norm_num [atom1364, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1364_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (274175197437888 : Int) atom1364) := by
  rw [SparsePolynomial.eval_scale, eval_atom1364]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 10) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1364Coded : CoefficientMerge.Poly := [(nat_lit 2564, Int.ofNat (nat_lit 1))]
theorem atom1364Coded_decode : atom1364 = SparsePolynomial.decodeCubic 24 atom1364Coded := by decide +kernel
theorem atom1364Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (274175197437888 : Int) atom1364Coded) := by
  have h := atom1364_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1364Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1365 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1365 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1365 = ((g 4) * (g 10) * (g 21)) := by
  norm_num [atom1365, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1365_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (346059831731904 : Int) atom1365) := by
  rw [SparsePolynomial.eval_scale, eval_atom1365]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 4) * (g 10) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1365Coded : CoefficientMerge.Poly := [(nat_lit 2565, Int.ofNat (nat_lit 1))]
theorem atom1365Coded_decode : atom1365 = SparsePolynomial.decodeCubic 24 atom1365Coded := by decide +kernel
theorem atom1365Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (346059831731904 : Int) atom1365Coded) := by
  have h := atom1365_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1365Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1366 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1366 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1366 = ((g 4) * (g 10) * (g 22)) := by
  norm_num [atom1366, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1366_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (417944466025920 : Int) atom1366) := by
  rw [SparsePolynomial.eval_scale, eval_atom1366]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 4) * (g 10) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1366Coded : CoefficientMerge.Poly := [(nat_lit 2566, Int.ofNat (nat_lit 1))]
theorem atom1366Coded_decode : atom1366 = SparsePolynomial.decodeCubic 24 atom1366Coded := by decide +kernel
theorem atom1366Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (417944466025920 : Int) atom1366Coded) := by
  have h := atom1366_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1366Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1367 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1367 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1367 = ((g 4) * (g 10) * (g 23)) := by
  norm_num [atom1367, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1367_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (489829100319936 : Int) atom1367) := by
  rw [SparsePolynomial.eval_scale, eval_atom1367]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 4) * (g 10) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1367Coded : CoefficientMerge.Poly := [(nat_lit 2567, Int.ofNat (nat_lit 1))]
theorem atom1367Coded_decode : atom1367 = SparsePolynomial.decodeCubic 24 atom1367Coded := by decide +kernel
theorem atom1367Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (489829100319936 : Int) atom1367Coded) := by
  have h := atom1367_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1367Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1368 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1368 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1368 = ((g 4) * (g 11) * (g 11)) := by
  norm_num [atom1368, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1368_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (135328071472704 : Int) atom1368) := by
  rw [SparsePolynomial.eval_scale, eval_atom1368]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1368Coded : CoefficientMerge.Poly := [(nat_lit 2579, Int.ofNat (nat_lit 1))]
theorem atom1368Coded_decode : atom1368 = SparsePolynomial.decodeCubic 24 atom1368Coded := by decide +kernel
theorem atom1368Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (135328071472704 : Int) atom1368Coded) := by
  have h := atom1368_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1368Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1369 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1369 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1369 = ((g 4) * (g 11) * (g 12)) := by
  norm_num [atom1369, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1369_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (270656674504128 : Int) atom1369) := by
  rw [SparsePolynomial.eval_scale, eval_atom1369]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1369Coded : CoefficientMerge.Poly := [(nat_lit 2580, Int.ofNat (nat_lit 1))]
theorem atom1369Coded_decode : atom1369 = SparsePolynomial.decodeCubic 24 atom1369Coded := by decide +kernel
theorem atom1369Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (270656674504128 : Int) atom1369Coded) := by
  have h := atom1369_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1369Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1370 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1370 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1370 = ((g 4) * (g 11) * (g 13)) := by
  norm_num [atom1370, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1370_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (253852064383104 : Int) atom1370) := by
  rw [SparsePolynomial.eval_scale, eval_atom1370]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1370Coded : CoefficientMerge.Poly := [(nat_lit 2581, Int.ofNat (nat_lit 1))]
theorem atom1370Coded_decode : atom1370 = SparsePolynomial.decodeCubic 24 atom1370Coded := by decide +kernel
theorem atom1370Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (253852064383104 : Int) atom1370Coded) := by
  have h := atom1370_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1370Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1371 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1371 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1371 = ((g 4) * (g 11) * (g 14)) := by
  norm_num [atom1371, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1371_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (233373191445504 : Int) atom1371) := by
  rw [SparsePolynomial.eval_scale, eval_atom1371]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1371Coded : CoefficientMerge.Poly := [(nat_lit 2582, Int.ofNat (nat_lit 1))]
theorem atom1371Coded_decode : atom1371 = SparsePolynomial.decodeCubic 24 atom1371Coded := by decide +kernel
theorem atom1371Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (233373191445504 : Int) atom1371Coded) := by
  have h := atom1371_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1371Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1372 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1372 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1372 = ((g 4) * (g 11) * (g 15)) := by
  norm_num [atom1372, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1372_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (227681325103104 : Int) atom1372) := by
  rw [SparsePolynomial.eval_scale, eval_atom1372]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1372Coded : CoefficientMerge.Poly := [(nat_lit 2583, Int.ofNat (nat_lit 1))]
theorem atom1372Coded_decode : atom1372 = SparsePolynomial.decodeCubic 24 atom1372Coded := by decide +kernel
theorem atom1372Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (227681325103104 : Int) atom1372Coded) := by
  have h := atom1372_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1372Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1373 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1373 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1373 = ((g 4) * (g 11) * (g 16)) := by
  norm_num [atom1373, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1373_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (213249989090304 : Int) atom1373) := by
  rw [SparsePolynomial.eval_scale, eval_atom1373]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1373Coded : CoefficientMerge.Poly := [(nat_lit 2584, Int.ofNat (nat_lit 1))]
theorem atom1373Coded_decode : atom1373 = SparsePolynomial.decodeCubic 24 atom1373Coded := by decide +kernel
theorem atom1373Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (213249989090304 : Int) atom1373Coded) := by
  have h := atom1373_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1373Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1374 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1374 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1374 = ((g 4) * (g 11) * (g 17)) := by
  norm_num [atom1374, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1374_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (213398825531904 : Int) atom1374) := by
  rw [SparsePolynomial.eval_scale, eval_atom1374]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1374Coded : CoefficientMerge.Poly := [(nat_lit 2585, Int.ofNat (nat_lit 1))]
theorem atom1374Coded_decode : atom1374 = SparsePolynomial.decodeCubic 24 atom1374Coded := by decide +kernel
theorem atom1374Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (213398825531904 : Int) atom1374Coded) := by
  have h := atom1374_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1374Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1375 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1375 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1375 = ((g 4) * (g 11) * (g 18)) := by
  norm_num [atom1375, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1375_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (261028728595008 : Int) atom1375) := by
  rw [SparsePolynomial.eval_scale, eval_atom1375]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1375Coded : CoefficientMerge.Poly := [(nat_lit 2586, Int.ofNat (nat_lit 1))]
theorem atom1375Coded_decode : atom1375 = SparsePolynomial.decodeCubic 24 atom1375Coded := by decide +kernel
theorem atom1375Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (261028728595008 : Int) atom1375Coded) := by
  have h := atom1375_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1375Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1376 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1376 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1376 = ((g 4) * (g 11) * (g 19)) := by
  norm_num [atom1376, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1376_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (266731717631040 : Int) atom1376) := by
  rw [SparsePolynomial.eval_scale, eval_atom1376]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1376Coded : CoefficientMerge.Poly := [(nat_lit 2587, Int.ofNat (nat_lit 1))]
theorem atom1376Coded_decode : atom1376 = SparsePolynomial.decodeCubic 24 atom1376Coded := by decide +kernel
theorem atom1376Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (266731717631040 : Int) atom1376Coded) := by
  have h := atom1376_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1376Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1377 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1377 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1377 = ((g 4) * (g 11) * (g 20)) := by
  norm_num [atom1377, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1377_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (312525412535808 : Int) atom1377) := by
  rw [SparsePolynomial.eval_scale, eval_atom1377]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1377Coded : CoefficientMerge.Poly := [(nat_lit 2588, Int.ofNat (nat_lit 1))]
theorem atom1377Coded_decode : atom1377 = SparsePolynomial.decodeCubic 24 atom1377Coded := by decide +kernel
theorem atom1377Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (312525412535808 : Int) atom1377Coded) := by
  have h := atom1377_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1377Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1378 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1378 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1378 = ((g 4) * (g 11) * (g 21)) := by
  norm_num [atom1378, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1378_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (373099828946112 : Int) atom1378) := by
  rw [SparsePolynomial.eval_scale, eval_atom1378]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 4) * (g 11) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1378Coded : CoefficientMerge.Poly := [(nat_lit 2589, Int.ofNat (nat_lit 1))]
theorem atom1378Coded_decode : atom1378 = SparsePolynomial.decodeCubic 24 atom1378Coded := by decide +kernel
theorem atom1378Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (373099828946112 : Int) atom1378Coded) := by
  have h := atom1378_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1378Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1379 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1379 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1379 = ((g 4) * (g 11) * (g 22)) := by
  norm_num [atom1379, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1379_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (443962291008960 : Int) atom1379) := by
  rw [SparsePolynomial.eval_scale, eval_atom1379]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 4) * (g 11) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1379Coded : CoefficientMerge.Poly := [(nat_lit 2590, Int.ofNat (nat_lit 1))]
theorem atom1379Coded_decode : atom1379 = SparsePolynomial.decodeCubic 24 atom1379Coded := by decide +kernel
theorem atom1379Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (443962291008960 : Int) atom1379Coded) := by
  have h := atom1379_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1379Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1380 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1380 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1380 = ((g 4) * (g 11) * (g 23)) := by
  norm_num [atom1380, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1380_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (514824753071808 : Int) atom1380) := by
  rw [SparsePolynomial.eval_scale, eval_atom1380]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 4) * (g 11) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1380Coded : CoefficientMerge.Poly := [(nat_lit 2591, Int.ofNat (nat_lit 1))]
theorem atom1380Coded_decode : atom1380 = SparsePolynomial.decodeCubic 24 atom1380Coded := by decide +kernel
theorem atom1380Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (514824753071808 : Int) atom1380Coded) := by
  have h := atom1380_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1380Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1381 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1381 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1381 = ((g 4) * (g 12) * (g 12)) := by
  norm_num [atom1381, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1381_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (176428723261824 : Int) atom1381) := by
  rw [SparsePolynomial.eval_scale, eval_atom1381]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1381Coded : CoefficientMerge.Poly := [(nat_lit 2604, Int.ofNat (nat_lit 1))]
theorem atom1381Coded_decode : atom1381 = SparsePolynomial.decodeCubic 24 atom1381Coded := by decide +kernel
theorem atom1381Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (176428723261824 : Int) atom1381Coded) := by
  have h := atom1381_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1381Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1382 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1382 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1382 = ((g 4) * (g 12) * (g 13)) := by
  norm_num [atom1382, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1382_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (323260875805824 : Int) atom1382) := by
  rw [SparsePolynomial.eval_scale, eval_atom1382]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1382Coded : CoefficientMerge.Poly := [(nat_lit 2605, Int.ofNat (nat_lit 1))]
theorem atom1382Coded_decode : atom1382 = SparsePolynomial.decodeCubic 24 atom1382Coded := by decide +kernel
theorem atom1382Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (323260875805824 : Int) atom1382Coded) := by
  have h := atom1382_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1382Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1383 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1383 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1383 = ((g 4) * (g 12) * (g 14)) := by
  norm_num [atom1383, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1383_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (301803934823424 : Int) atom1383) := by
  rw [SparsePolynomial.eval_scale, eval_atom1383]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1383Coded : CoefficientMerge.Poly := [(nat_lit 2606, Int.ofNat (nat_lit 1))]
theorem atom1383Coded_decode : atom1383 = SparsePolynomial.decodeCubic 24 atom1383Coded := by decide +kernel
theorem atom1383Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (301803934823424 : Int) atom1383Coded) := by
  have h := atom1383_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1383Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1384 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 12, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1384 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1384 = ((g 4) * (g 12) * (g 15)) := by
  norm_num [atom1384, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1384_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (295134000436224 : Int) atom1384) := by
  rw [SparsePolynomial.eval_scale, eval_atom1384]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1384Coded : CoefficientMerge.Poly := [(nat_lit 2607, Int.ofNat (nat_lit 1))]
theorem atom1384Coded_decode : atom1384 = SparsePolynomial.decodeCubic 24 atom1384Coded := by decide +kernel
theorem atom1384Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (295134000436224 : Int) atom1384Coded) := by
  have h := atom1384_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1384Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1385 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 12, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1385 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1385 = ((g 4) * (g 12) * (g 16)) := by
  norm_num [atom1385, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1385_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (276641555802624 : Int) atom1385) := by
  rw [SparsePolynomial.eval_scale, eval_atom1385]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1385Coded : CoefficientMerge.Poly := [(nat_lit 2608, Int.ofNat (nat_lit 1))]
theorem atom1385Coded_decode : atom1385 = SparsePolynomial.decodeCubic 24 atom1385Coded := by decide +kernel
theorem atom1385Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (276641555802624 : Int) atom1385Coded) := by
  have h := atom1385_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1385Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1386 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 12, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1386 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1386 = ((g 4) * (g 12) * (g 17)) := by
  norm_num [atom1386, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1386_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (272729283623424 : Int) atom1386) := by
  rw [SparsePolynomial.eval_scale, eval_atom1386]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1386Coded : CoefficientMerge.Poly := [(nat_lit 2609, Int.ofNat (nat_lit 1))]
theorem atom1386Coded_decode : atom1386 = SparsePolynomial.decodeCubic 24 atom1386Coded := by decide +kernel
theorem atom1386Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (272729283623424 : Int) atom1386Coded) := by
  have h := atom1386_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1386Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1387 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 12, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1387 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1387 = ((g 4) * (g 12) * (g 18)) := by
  norm_num [atom1387, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1387_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (341962264626048 : Int) atom1387) := by
  rw [SparsePolynomial.eval_scale, eval_atom1387]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1387Coded : CoefficientMerge.Poly := [(nat_lit 2610, Int.ofNat (nat_lit 1))]
theorem atom1387Coded_decode : atom1387 = SparsePolynomial.decodeCubic 24 atom1387Coded := by decide +kernel
theorem atom1387Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (341962264626048 : Int) atom1387Coded) := by
  have h := atom1387_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1387Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1388 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 12, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1388 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1388 = ((g 4) * (g 12) * (g 19)) := by
  norm_num [atom1388, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1388_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (308703594162240 : Int) atom1388) := by
  rw [SparsePolynomial.eval_scale, eval_atom1388]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1388Coded : CoefficientMerge.Poly := [(nat_lit 2611, Int.ofNat (nat_lit 1))]
theorem atom1388Coded_decode : atom1388 = SparsePolynomial.decodeCubic 24 atom1388Coded := by decide +kernel
theorem atom1388Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (308703594162240 : Int) atom1388Coded) := by
  have h := atom1388_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1388Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1389 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 12, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1389 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1389 = ((g 4) * (g 12) * (g 20)) := by
  norm_num [atom1389, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1389_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (403664875990848 : Int) atom1389) := by
  rw [SparsePolynomial.eval_scale, eval_atom1389]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1389Coded : CoefficientMerge.Poly := [(nat_lit 2612, Int.ofNat (nat_lit 1))]
theorem atom1389Coded_decode : atom1389 = SparsePolynomial.decodeCubic 24 atom1389Coded := by decide +kernel
theorem atom1389Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (403664875990848 : Int) atom1389Coded) := by
  have h := atom1389_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1389Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1390 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 12, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1390 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1390 = ((g 4) * (g 12) * (g 21)) := by
  norm_num [atom1390, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1390_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (388476759598272 : Int) atom1390) := by
  rw [SparsePolynomial.eval_scale, eval_atom1390]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 4) * (g 12) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1390Coded : CoefficientMerge.Poly := [(nat_lit 2613, Int.ofNat (nat_lit 1))]
theorem atom1390Coded_decode : atom1390 = SparsePolynomial.decodeCubic 24 atom1390Coded := by decide +kernel
theorem atom1390Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (388476759598272 : Int) atom1390Coded) := by
  have h := atom1390_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1390Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1391 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 12, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1391 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1391 = ((g 4) * (g 12) * (g 22)) := by
  norm_num [atom1391, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1391_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (442962960615360 : Int) atom1391) := by
  rw [SparsePolynomial.eval_scale, eval_atom1391]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 4) * (g 12) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1391Coded : CoefficientMerge.Poly := [(nat_lit 2614, Int.ofNat (nat_lit 1))]
theorem atom1391Coded_decode : atom1391 = SparsePolynomial.decodeCubic 24 atom1391Coded := by decide +kernel
theorem atom1391Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (442962960615360 : Int) atom1391Coded) := by
  have h := atom1391_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1391Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1392 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 12, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1392 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1392 = ((g 4) * (g 12) * (g 23)) := by
  norm_num [atom1392, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1392_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (497449161632448 : Int) atom1392) := by
  rw [SparsePolynomial.eval_scale, eval_atom1392]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 4) * (g 12) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1392Coded : CoefficientMerge.Poly := [(nat_lit 2615, Int.ofNat (nat_lit 1))]
theorem atom1392Coded_decode : atom1392 = SparsePolynomial.decodeCubic 24 atom1392Coded := by decide +kernel
theorem atom1392Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (497449161632448 : Int) atom1392Coded) := by
  have h := atom1392_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1392Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1393 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1393 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1393 = ((g 4) * (g 13) * (g 13)) := by
  norm_num [atom1393, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1393_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (187932272774400 : Int) atom1393) := by
  rw [SparsePolynomial.eval_scale, eval_atom1393]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1393Coded : CoefficientMerge.Poly := [(nat_lit 2629, Int.ofNat (nat_lit 1))]
theorem atom1393Coded_decode : atom1393 = SparsePolynomial.decodeCubic 24 atom1393Coded := by decide +kernel
theorem atom1393Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (187932272774400 : Int) atom1393Coded) := by
  have h := atom1393_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1393Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1394 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1394 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1394 = ((g 4) * (g 13) * (g 14)) := by
  norm_num [atom1394, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1394_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (336999056486400 : Int) atom1394) := by
  rw [SparsePolynomial.eval_scale, eval_atom1394]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1394Coded : CoefficientMerge.Poly := [(nat_lit 2630, Int.ofNat (nat_lit 1))]
theorem atom1394Coded_decode : atom1394 = SparsePolynomial.decodeCubic 24 atom1394Coded := by decide +kernel
theorem atom1394Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (336999056486400 : Int) atom1394Coded) := by
  have h := atom1394_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1394Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1395 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 13, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1395 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1395 = ((g 4) * (g 13) * (g 15)) := by
  norm_num [atom1395, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1395_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (322164380160000 : Int) atom1395) := by
  rw [SparsePolynomial.eval_scale, eval_atom1395]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1395Coded : CoefficientMerge.Poly := [(nat_lit 2631, Int.ofNat (nat_lit 1))]
theorem atom1395Coded_decode : atom1395 = SparsePolynomial.decodeCubic 24 atom1395Coded := by decide +kernel
theorem atom1395Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (322164380160000 : Int) atom1395Coded) := by
  have h := atom1395_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1395Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1396 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 13, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1396 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1396 = ((g 4) * (g 13) * (g 16)) := by
  norm_num [atom1396, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1396_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (298590234163200 : Int) atom1396) := by
  rw [SparsePolynomial.eval_scale, eval_atom1396]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1396Coded : CoefficientMerge.Poly := [(nat_lit 2632, Int.ofNat (nat_lit 1))]
theorem atom1396Coded_decode : atom1396 = SparsePolynomial.decodeCubic 24 atom1396Coded := by decide +kernel
theorem atom1396Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (298590234163200 : Int) atom1396Coded) := by
  have h := atom1396_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1396Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1397 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 13, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1397 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1397 = ((g 4) * (g 13) * (g 17)) := by
  norm_num [atom1397, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1397_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (289596260620800 : Int) atom1397) := by
  rw [SparsePolynomial.eval_scale, eval_atom1397]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1397Coded : CoefficientMerge.Poly := [(nat_lit 2633, Int.ofNat (nat_lit 1))]
theorem atom1397Coded_decode : atom1397 = SparsePolynomial.decodeCubic 24 atom1397Coded := by decide +kernel
theorem atom1397Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (289596260620800 : Int) atom1397Coded) := by
  have h := atom1397_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1397Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1398 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 13, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1398 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1398 = ((g 4) * (g 13) * (g 18)) := by
  norm_num [atom1398, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1398_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (349729575148800 : Int) atom1398) := by
  rw [SparsePolynomial.eval_scale, eval_atom1398]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1398Coded : CoefficientMerge.Poly := [(nat_lit 2634, Int.ofNat (nat_lit 1))]
theorem atom1398Coded_decode : atom1398 = SparsePolynomial.decodeCubic 24 atom1398Coded := by decide +kernel
theorem atom1398Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (349729575148800 : Int) atom1398Coded) := by
  have h := atom1398_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1398Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1399 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 13, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1399 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1399 = ((g 4) * (g 13) * (g 19)) := by
  norm_num [atom1399, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1399_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (320595613934400 : Int) atom1399) := by
  rw [SparsePolynomial.eval_scale, eval_atom1399]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1399Coded : CoefficientMerge.Poly := [(nat_lit 2635, Int.ofNat (nat_lit 1))]
theorem atom1399Coded_decode : atom1399 = SparsePolynomial.decodeCubic 24 atom1399Coded := by decide +kernel
theorem atom1399Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (320595613934400 : Int) atom1399Coded) := by
  have h := atom1399_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1399Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1400 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 13, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1400 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1400 = ((g 4) * (g 13) * (g 20)) := by
  norm_num [atom1400, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1400_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (421638113937600 : Int) atom1400) := by
  rw [SparsePolynomial.eval_scale, eval_atom1400]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1400Coded : CoefficientMerge.Poly := [(nat_lit 2636, Int.ofNat (nat_lit 1))]
theorem atom1400Coded_decode : atom1400 = SparsePolynomial.decodeCubic 24 atom1400Coded := by decide +kernel
theorem atom1400Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (421638113937600 : Int) atom1400Coded) := by
  have h := atom1400_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1400Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1401 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 13, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1401 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1401 = ((g 4) * (g 13) * (g 21)) := by
  norm_num [atom1401, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1401_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (400582267646400 : Int) atom1401) := by
  rw [SparsePolynomial.eval_scale, eval_atom1401]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 4) * (g 13) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1401Coded : CoefficientMerge.Poly := [(nat_lit 2637, Int.ofNat (nat_lit 1))]
theorem atom1401Coded_decode : atom1401 = SparsePolynomial.decodeCubic 24 atom1401Coded := by decide +kernel
theorem atom1401Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (400582267646400 : Int) atom1401Coded) := by
  have h := atom1401_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1401Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1402 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 13, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1402 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1402 = ((g 4) * (g 13) * (g 22)) := by
  norm_num [atom1402, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1402_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (456904694635200 : Int) atom1402) := by
  rw [SparsePolynomial.eval_scale, eval_atom1402]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 4) * (g 13) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1402Coded : CoefficientMerge.Poly := [(nat_lit 2638, Int.ofNat (nat_lit 1))]
theorem atom1402Coded_decode : atom1402 = SparsePolynomial.decodeCubic 24 atom1402Coded := by decide +kernel
theorem atom1402Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (456904694635200 : Int) atom1402Coded) := by
  have h := atom1402_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1402Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1403 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 13, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1403 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1403 = ((g 4) * (g 13) * (g 23)) := by
  norm_num [atom1403, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1403_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (513227121624000 : Int) atom1403) := by
  rw [SparsePolynomial.eval_scale, eval_atom1403]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 4) * (g 13) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1403Coded : CoefficientMerge.Poly := [(nat_lit 2639, Int.ofNat (nat_lit 1))]
theorem atom1403Coded_decode : atom1403 = SparsePolynomial.decodeCubic 24 atom1403Coded := by decide +kernel
theorem atom1403Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (513227121624000 : Int) atom1403Coded) := by
  have h := atom1403_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1403Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1404 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1404 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1404 = ((g 4) * (g 14) * (g 14)) := by
  norm_num [atom1404, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1404_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (190166903942400 : Int) atom1404) := by
  rw [SparsePolynomial.eval_scale, eval_atom1404]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1404Coded : CoefficientMerge.Poly := [(nat_lit 2654, Int.ofNat (nat_lit 1))]
theorem atom1404Coded_decode : atom1404 = SparsePolynomial.decodeCubic 24 atom1404Coded := by decide +kernel
theorem atom1404Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (190166903942400 : Int) atom1404Coded) := by
  have h := atom1404_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1404Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1405 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 14, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1405 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1405 = ((g 4) * (g 14) * (g 15)) := by
  norm_num [atom1405, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1405_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (354261980217600 : Int) atom1405) := by
  rw [SparsePolynomial.eval_scale, eval_atom1405]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1405Coded : CoefficientMerge.Poly := [(nat_lit 2655, Int.ofNat (nat_lit 1))]
theorem atom1405Coded_decode : atom1405 = SparsePolynomial.decodeCubic 24 atom1405Coded := by decide +kernel
theorem atom1405Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (354261980217600 : Int) atom1405Coded) := by
  have h := atom1405_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1405Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1406 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 14, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1406 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1406 = ((g 4) * (g 14) * (g 16)) := by
  norm_num [atom1406, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1406_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (324585540115200 : Int) atom1406) := by
  rw [SparsePolynomial.eval_scale, eval_atom1406]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1406Coded : CoefficientMerge.Poly := [(nat_lit 2656, Int.ofNat (nat_lit 1))]
theorem atom1406Coded_decode : atom1406 = SparsePolynomial.decodeCubic 24 atom1406Coded := by decide +kernel
theorem atom1406Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (324585540115200 : Int) atom1406Coded) := by
  have h := atom1406_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1406Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1407 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 14, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1407 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1407 = ((g 4) * (g 14) * (g 17)) := by
  norm_num [atom1407, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1407_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (309489272467200 : Int) atom1407) := by
  rw [SparsePolynomial.eval_scale, eval_atom1407]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1407Coded : CoefficientMerge.Poly := [(nat_lit 2657, Int.ofNat (nat_lit 1))]
theorem atom1407Coded_decode : atom1407 = SparsePolynomial.decodeCubic 24 atom1407Coded := by decide +kernel
theorem atom1407Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (309489272467200 : Int) atom1407Coded) := by
  have h := atom1407_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1407Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1408 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 14, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1408 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1408 = ((g 4) * (g 14) * (g 18)) := by
  norm_num [atom1408, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1408_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (350148360038400 : Int) atom1408) := by
  rw [SparsePolynomial.eval_scale, eval_atom1408]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1408Coded : CoefficientMerge.Poly := [(nat_lit 2658, Int.ofNat (nat_lit 1))]
theorem atom1408Coded_decode : atom1408 = SparsePolynomial.decodeCubic 24 atom1408Coded := by decide +kernel
theorem atom1408Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (350148360038400 : Int) atom1408Coded) := by
  have h := atom1408_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1408Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block019 : CoefficientMerge.Poly := [(nat_lit 2510, Int.ofNat (nat_lit 95552995507200)), (nat_lit 2511, Int.ofNat (nat_lit 99003939148800)), (nat_lit 2512, Int.ofNat (nat_lit 90632372544000)), (nat_lit 2513, Int.ofNat (nat_lit 96840978393600)), (nat_lit 2514, Int.ofNat (nat_lit 137461084992000)), (nat_lit 2515, Int.ofNat (nat_lit 157970956046400)), (nat_lit 2516, Int.ofNat (nat_lit 196654739198400)), (nat_lit 2517, Int.ofNat (nat_lit 267813699652800)), (nat_lit 2518, Int.ofNat (nat_lit 338972660107200)), (nat_lit 2519, Int.ofNat (nat_lit 410131620561600)), (nat_lit 2529, Int.ofNat (nat_lit 69667045180128)), (nat_lit 2530, Int.ofNat (nat_lit 129230222210496)), (nat_lit 2531, Int.ofNat (nat_lit 123772944236832)), (nat_lit 2532, Int.ofNat (nat_lit 151694926460352)), (nat_lit 2533, Int.ofNat (nat_lit 139950755353728)), (nat_lit 2534, Int.ofNat (nat_lit 127615362006528)), (nat_lit 2535, Int.ofNat (nat_lit 130066975254528)), (nat_lit 2536, Int.ofNat (nat_lit 120696078256128)), (nat_lit 2537, Int.ofNat (nat_lit 125905353712128)), (nat_lit 2538, Int.ofNat (nat_lit 167729597747712)), (nat_lit 2539, Int.ofNat (nat_lit 191647074070080)), (nat_lit 2540, Int.ofNat (nat_lit 233738462490048)), (nat_lit 2541, Int.ofNat (nat_lit 312711963873984)), (nat_lit 2542, Int.ofNat (nat_lit 391685465257920)), (nat_lit 2543, Int.ofNat (nat_lit 470658966641856)), (nat_lit 2554, Int.ofNat (nat_lit 94497216108768)), (nat_lit 2555, Int.ofNat (nat_lit 188725167351072)), (nat_lit 2556, Int.ofNat (nat_lit 211544185862592)), (nat_lit 2557, Int.ofNat (nat_lit 200863132195968)), (nat_lit 2558, Int.ofNat (nat_lit 186507815712768)), (nat_lit 2559, Int.ofNat (nat_lit 186939505824768)), (nat_lit 2560, Int.ofNat (nat_lit 175548685690368)), (nat_lit 2561, Int.ofNat (nat_lit 178738038010368)), (nat_lit 2562, Int.ofNat (nat_lit 217275122921472)), (nat_lit 2563, Int.ofNat (nat_lit 236638204130880)), (nat_lit 2564, Int.ofNat (nat_lit 274175197437888)), (nat_lit 2565, Int.ofNat (nat_lit 346059831731904)), (nat_lit 2566, Int.ofNat (nat_lit 417944466025920)), (nat_lit 2567, Int.ofNat (nat_lit 489829100319936)), (nat_lit 2579, Int.ofNat (nat_lit 135328071472704)), (nat_lit 2580, Int.ofNat (nat_lit 270656674504128)), (nat_lit 2581, Int.ofNat (nat_lit 253852064383104)), (nat_lit 2582, Int.ofNat (nat_lit 233373191445504)), (nat_lit 2583, Int.ofNat (nat_lit 227681325103104)), (nat_lit 2584, Int.ofNat (nat_lit 213249989090304)), (nat_lit 2585, Int.ofNat (nat_lit 213398825531904)), (nat_lit 2586, Int.ofNat (nat_lit 261028728595008)), (nat_lit 2587, Int.ofNat (nat_lit 266731717631040)), (nat_lit 2588, Int.ofNat (nat_lit 312525412535808)), (nat_lit 2589, Int.ofNat (nat_lit 373099828946112)), (nat_lit 2590, Int.ofNat (nat_lit 443962291008960)), (nat_lit 2591, Int.ofNat (nat_lit 514824753071808)), (nat_lit 2604, Int.ofNat (nat_lit 176428723261824)), (nat_lit 2605, Int.ofNat (nat_lit 323260875805824)), (nat_lit 2606, Int.ofNat (nat_lit 301803934823424)), (nat_lit 2607, Int.ofNat (nat_lit 295134000436224)), (nat_lit 2608, Int.ofNat (nat_lit 276641555802624)), (nat_lit 2609, Int.ofNat (nat_lit 272729283623424)), (nat_lit 2610, Int.ofNat (nat_lit 341962264626048)), (nat_lit 2611, Int.ofNat (nat_lit 308703594162240)), (nat_lit 2612, Int.ofNat (nat_lit 403664875990848)), (nat_lit 2613, Int.ofNat (nat_lit 388476759598272)), (nat_lit 2614, Int.ofNat (nat_lit 442962960615360)), (nat_lit 2615, Int.ofNat (nat_lit 497449161632448)), (nat_lit 2629, Int.ofNat (nat_lit 187932272774400)), (nat_lit 2630, Int.ofNat (nat_lit 336999056486400)), (nat_lit 2631, Int.ofNat (nat_lit 322164380160000)), (nat_lit 2632, Int.ofNat (nat_lit 298590234163200)), (nat_lit 2633, Int.ofNat (nat_lit 289596260620800)), (nat_lit 2634, Int.ofNat (nat_lit 349729575148800)), (nat_lit 2635, Int.ofNat (nat_lit 320595613934400)), (nat_lit 2636, Int.ofNat (nat_lit 421638113937600)), (nat_lit 2637, Int.ofNat (nat_lit 400582267646400)), (nat_lit 2638, Int.ofNat (nat_lit 456904694635200)), (nat_lit 2639, Int.ofNat (nat_lit 513227121624000)), (nat_lit 2654, Int.ofNat (nat_lit 190166903942400)), (nat_lit 2655, Int.ofNat (nat_lit 354261980217600)), (nat_lit 2656, Int.ofNat (nat_lit 324585540115200)), (nat_lit 2657, Int.ofNat (nat_lit 309489272467200)), (nat_lit 2658, Int.ofNat (nat_lit 350148360038400))]
theorem block019_data : block019 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (95552995507200 : Int) atom1329Coded) (CoefficientMerge.scale (99003939148800 : Int) atom1330Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (90632372544000 : Int) atom1331Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (96840978393600 : Int) atom1332Coded) (CoefficientMerge.scale (137461084992000 : Int) atom1333Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (157970956046400 : Int) atom1334Coded) (CoefficientMerge.scale (196654739198400 : Int) atom1335Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (267813699652800 : Int) atom1336Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (338972660107200 : Int) atom1337Coded) (CoefficientMerge.scale (410131620561600 : Int) atom1338Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (69667045180128 : Int) atom1339Coded) (CoefficientMerge.scale (129230222210496 : Int) atom1340Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (123772944236832 : Int) atom1341Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (151694926460352 : Int) atom1342Coded) (CoefficientMerge.scale (139950755353728 : Int) atom1343Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (127615362006528 : Int) atom1344Coded) (CoefficientMerge.scale (130066975254528 : Int) atom1345Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (120696078256128 : Int) atom1346Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (125905353712128 : Int) atom1347Coded) (CoefficientMerge.scale (167729597747712 : Int) atom1348Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (191647074070080 : Int) atom1349Coded) (CoefficientMerge.scale (233738462490048 : Int) atom1350Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (312711963873984 : Int) atom1351Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (391685465257920 : Int) atom1352Coded) (CoefficientMerge.scale (470658966641856 : Int) atom1353Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (94497216108768 : Int) atom1354Coded) (CoefficientMerge.scale (188725167351072 : Int) atom1355Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (211544185862592 : Int) atom1356Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (200863132195968 : Int) atom1357Coded) (CoefficientMerge.scale (186507815712768 : Int) atom1358Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (186939505824768 : Int) atom1359Coded) (CoefficientMerge.scale (175548685690368 : Int) atom1360Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (178738038010368 : Int) atom1361Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (217275122921472 : Int) atom1362Coded) (CoefficientMerge.scale (236638204130880 : Int) atom1363Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (274175197437888 : Int) atom1364Coded) (CoefficientMerge.scale (346059831731904 : Int) atom1365Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (417944466025920 : Int) atom1366Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (489829100319936 : Int) atom1367Coded) (CoefficientMerge.scale (135328071472704 : Int) atom1368Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (270656674504128 : Int) atom1369Coded) (CoefficientMerge.scale (253852064383104 : Int) atom1370Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (233373191445504 : Int) atom1371Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (227681325103104 : Int) atom1372Coded) (CoefficientMerge.scale (213249989090304 : Int) atom1373Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (213398825531904 : Int) atom1374Coded) (CoefficientMerge.scale (261028728595008 : Int) atom1375Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (266731717631040 : Int) atom1376Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (312525412535808 : Int) atom1377Coded) (CoefficientMerge.scale (373099828946112 : Int) atom1378Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (443962291008960 : Int) atom1379Coded) (CoefficientMerge.scale (514824753071808 : Int) atom1380Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (176428723261824 : Int) atom1381Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (323260875805824 : Int) atom1382Coded) (CoefficientMerge.scale (301803934823424 : Int) atom1383Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (295134000436224 : Int) atom1384Coded) (CoefficientMerge.scale (276641555802624 : Int) atom1385Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (272729283623424 : Int) atom1386Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (341962264626048 : Int) atom1387Coded) (CoefficientMerge.scale (308703594162240 : Int) atom1388Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (403664875990848 : Int) atom1389Coded) (CoefficientMerge.scale (388476759598272 : Int) atom1390Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (442962960615360 : Int) atom1391Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (497449161632448 : Int) atom1392Coded) (CoefficientMerge.scale (187932272774400 : Int) atom1393Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (336999056486400 : Int) atom1394Coded) (CoefficientMerge.scale (322164380160000 : Int) atom1395Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (298590234163200 : Int) atom1396Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (289596260620800 : Int) atom1397Coded) (CoefficientMerge.scale (349729575148800 : Int) atom1398Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (320595613934400 : Int) atom1399Coded) (CoefficientMerge.scale (421638113937600 : Int) atom1400Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (400582267646400 : Int) atom1401Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (456904694635200 : Int) atom1402Coded) (CoefficientMerge.scale (513227121624000 : Int) atom1403Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (190166903942400 : Int) atom1404Coded) (CoefficientMerge.scale (354261980217600 : Int) atom1405Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (324585540115200 : Int) atom1406Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (309489272467200 : Int) atom1407Coded) (CoefficientMerge.scale (350148360038400 : Int) atom1408Coded)))))))) := by decide +kernel
theorem block019_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block019 := by
  rw [block019_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1329Coded_nonneg g hg hA hB) (atom1330Coded_nonneg g hg hA hB)) (add_nonneg (atom1331Coded_nonneg g hg hA hB) (add_nonneg (atom1332Coded_nonneg g hg hA hB) (atom1333Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1334Coded_nonneg g hg hA hB) (atom1335Coded_nonneg g hg hA hB)) (add_nonneg (atom1336Coded_nonneg g hg hA hB) (add_nonneg (atom1337Coded_nonneg g hg hA hB) (atom1338Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1339Coded_nonneg g hg hA hB) (atom1340Coded_nonneg g hg hA hB)) (add_nonneg (atom1341Coded_nonneg g hg hA hB) (add_nonneg (atom1342Coded_nonneg g hg hA hB) (atom1343Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1344Coded_nonneg g hg hA hB) (atom1345Coded_nonneg g hg hA hB)) (add_nonneg (atom1346Coded_nonneg g hg hA hB) (add_nonneg (atom1347Coded_nonneg g hg hA hB) (atom1348Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1349Coded_nonneg g hg hA hB) (atom1350Coded_nonneg g hg hA hB)) (add_nonneg (atom1351Coded_nonneg g hg hA hB) (add_nonneg (atom1352Coded_nonneg g hg hA hB) (atom1353Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1354Coded_nonneg g hg hA hB) (atom1355Coded_nonneg g hg hA hB)) (add_nonneg (atom1356Coded_nonneg g hg hA hB) (add_nonneg (atom1357Coded_nonneg g hg hA hB) (atom1358Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1359Coded_nonneg g hg hA hB) (atom1360Coded_nonneg g hg hA hB)) (add_nonneg (atom1361Coded_nonneg g hg hA hB) (add_nonneg (atom1362Coded_nonneg g hg hA hB) (atom1363Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1364Coded_nonneg g hg hA hB) (atom1365Coded_nonneg g hg hA hB)) (add_nonneg (atom1366Coded_nonneg g hg hA hB) (add_nonneg (atom1367Coded_nonneg g hg hA hB) (atom1368Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1369Coded_nonneg g hg hA hB) (atom1370Coded_nonneg g hg hA hB)) (add_nonneg (atom1371Coded_nonneg g hg hA hB) (add_nonneg (atom1372Coded_nonneg g hg hA hB) (atom1373Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1374Coded_nonneg g hg hA hB) (atom1375Coded_nonneg g hg hA hB)) (add_nonneg (atom1376Coded_nonneg g hg hA hB) (add_nonneg (atom1377Coded_nonneg g hg hA hB) (atom1378Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1379Coded_nonneg g hg hA hB) (atom1380Coded_nonneg g hg hA hB)) (add_nonneg (atom1381Coded_nonneg g hg hA hB) (add_nonneg (atom1382Coded_nonneg g hg hA hB) (atom1383Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1384Coded_nonneg g hg hA hB) (atom1385Coded_nonneg g hg hA hB)) (add_nonneg (atom1386Coded_nonneg g hg hA hB) (add_nonneg (atom1387Coded_nonneg g hg hA hB) (atom1388Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1389Coded_nonneg g hg hA hB) (atom1390Coded_nonneg g hg hA hB)) (add_nonneg (atom1391Coded_nonneg g hg hA hB) (add_nonneg (atom1392Coded_nonneg g hg hA hB) (atom1393Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1394Coded_nonneg g hg hA hB) (atom1395Coded_nonneg g hg hA hB)) (add_nonneg (atom1396Coded_nonneg g hg hA hB) (add_nonneg (atom1397Coded_nonneg g hg hA hB) (atom1398Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1399Coded_nonneg g hg hA hB) (atom1400Coded_nonneg g hg hA hB)) (add_nonneg (atom1401Coded_nonneg g hg hA hB) (add_nonneg (atom1402Coded_nonneg g hg hA hB) (atom1403Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1404Coded_nonneg g hg hA hB) (atom1405Coded_nonneg g hg hA hB)) (add_nonneg (atom1406Coded_nonneg g hg hA hB) (add_nonneg (atom1407Coded_nonneg g hg hA hB) (atom1408Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
