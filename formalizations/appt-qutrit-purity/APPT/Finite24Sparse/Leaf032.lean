import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom2369 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 16, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2369 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2369 = ((g 13) * (g 16) * (g 21)) := by
  norm_num [atom2369, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2369_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (268132862289600 : Int) atom2369) := by
  rw [SparsePolynomial.eval_scale, eval_atom2369]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 13) * (g 16) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2369Coded : CoefficientMerge.Poly := [(nat_lit 7893, Int.ofNat (nat_lit 1))]
theorem atom2369Coded_decode : atom2369 = SparsePolynomial.decodeCubic 24 atom2369Coded := by decide +kernel
theorem atom2369Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (268132862289600 : Int) atom2369Coded) := by
  have h := atom2369_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2369Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2370 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 16, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2370 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2370 = ((g 13) * (g 16) * (g 22)) := by
  norm_num [atom2370, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2370_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (255013789363200 : Int) atom2370) := by
  rw [SparsePolynomial.eval_scale, eval_atom2370]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 13) * (g 16) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2370Coded : CoefficientMerge.Poly := [(nat_lit 7894, Int.ofNat (nat_lit 1))]
theorem atom2370Coded_decode : atom2370 = SparsePolynomial.decodeCubic 24 atom2370Coded := by decide +kernel
theorem atom2370Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (255013789363200 : Int) atom2370Coded) := by
  have h := atom2370_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2370Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2371 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 16, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2371 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2371 = ((g 13) * (g 16) * (g 23)) := by
  norm_num [atom2371, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2371_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (456770220228000 : Int) atom2371) := by
  rw [SparsePolynomial.eval_scale, eval_atom2371]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 13) * (g 16) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2371Coded : CoefficientMerge.Poly := [(nat_lit 7895, Int.ofNat (nat_lit 1))]
theorem atom2371Coded_decode : atom2371 = SparsePolynomial.decodeCubic 24 atom2371Coded := by decide +kernel
theorem atom2371Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (456770220228000 : Int) atom2371Coded) := by
  have h := atom2371_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2371Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2372 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom2372 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2372 = ((g 13) * (g 17) * (g 17)) := by
  norm_num [atom2372, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2372_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41470439472000 : Int) atom2372) := by
  rw [SparsePolynomial.eval_scale, eval_atom2372]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 13) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2372Coded : CoefficientMerge.Poly := [(nat_lit 7913, Int.ofNat (nat_lit 1))]
theorem atom2372Coded_decode : atom2372 = SparsePolynomial.decodeCubic 24 atom2372Coded := by decide +kernel
theorem atom2372Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (41470439472000 : Int) atom2372Coded) := by
  have h := atom2372_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2372Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2373 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 17, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2373 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2373 = ((g 13) * (g 17) * (g 18)) := by
  norm_num [atom2373, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2373_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (130081695004800 : Int) atom2373) := by
  rw [SparsePolynomial.eval_scale, eval_atom2373]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 13) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2373Coded : CoefficientMerge.Poly := [(nat_lit 7914, Int.ofNat (nat_lit 1))]
theorem atom2373Coded_decode : atom2373 = SparsePolynomial.decodeCubic 24 atom2373Coded := by decide +kernel
theorem atom2373Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (130081695004800 : Int) atom2373Coded) := by
  have h := atom2373_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2373Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2374 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 17, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2374 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2374 = ((g 13) * (g 17) * (g 19)) := by
  norm_num [atom2374, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2374_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (144679235500800 : Int) atom2374) := by
  rw [SparsePolynomial.eval_scale, eval_atom2374]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 13) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2374Coded : CoefficientMerge.Poly := [(nat_lit 7915, Int.ofNat (nat_lit 1))]
theorem atom2374Coded_decode : atom2374 = SparsePolynomial.decodeCubic 24 atom2374Coded := by decide +kernel
theorem atom2374Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (144679235500800 : Int) atom2374Coded) := by
  have h := atom2374_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2374Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2375 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 17, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2375 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2375 = ((g 13) * (g 17) * (g 20)) := by
  norm_num [atom2375, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2375_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (412121123568000 : Int) atom2375) := by
  rw [SparsePolynomial.eval_scale, eval_atom2375]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2375Coded : CoefficientMerge.Poly := [(nat_lit 7916, Int.ofNat (nat_lit 1))]
theorem atom2375Coded_decode : atom2375 = SparsePolynomial.decodeCubic 24 atom2375Coded := by decide +kernel
theorem atom2375Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (412121123568000 : Int) atom2375Coded) := by
  have h := atom2375_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2375Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2376 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 17, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2376 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2376 = ((g 13) * (g 17) * (g 21)) := by
  norm_num [atom2376, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2376_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (420077150539200 : Int) atom2376) := by
  rw [SparsePolynomial.eval_scale, eval_atom2376]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 13) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2376Coded : CoefficientMerge.Poly := [(nat_lit 7917, Int.ofNat (nat_lit 1))]
theorem atom2376Coded_decode : atom2376 = SparsePolynomial.decodeCubic 24 atom2376Coded := by decide +kernel
theorem atom2376Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (420077150539200 : Int) atom2376Coded) := by
  have h := atom2376_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2376Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2377 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 17, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2377 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2377 = ((g 13) * (g 17) * (g 22)) := by
  norm_num [atom2377, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2377_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (432690996326400 : Int) atom2377) := by
  rw [SparsePolynomial.eval_scale, eval_atom2377]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 13) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2377Coded : CoefficientMerge.Poly := [(nat_lit 7918, Int.ofNat (nat_lit 1))]
theorem atom2377Coded_decode : atom2377 = SparsePolynomial.decodeCubic 24 atom2377Coded := by decide +kernel
theorem atom2377Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (432690996326400 : Int) atom2377Coded) := by
  have h := atom2377_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2377Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2378 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 17, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2378 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2378 = ((g 13) * (g 17) * (g 23)) := by
  norm_num [atom2378, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2378_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (655019877204000 : Int) atom2378) := by
  rw [SparsePolynomial.eval_scale, eval_atom2378]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 13) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2378Coded : CoefficientMerge.Poly := [(nat_lit 7919, Int.ofNat (nat_lit 1))]
theorem atom2378Coded_decode : atom2378 = SparsePolynomial.decodeCubic 24 atom2378Coded := by decide +kernel
theorem atom2378Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (655019877204000 : Int) atom2378Coded) := by
  have h := atom2378_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2378Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2379 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 18, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2379 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2379 = ((g 13) * (g 18) * (g 18)) := by
  norm_num [atom2379, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2379_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (122580671875200 : Int) atom2379) := by
  rw [SparsePolynomial.eval_scale, eval_atom2379]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 13) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2379Coded : CoefficientMerge.Poly := [(nat_lit 7938, Int.ofNat (nat_lit 1))]
theorem atom2379Coded_decode : atom2379 = SparsePolynomial.decodeCubic 24 atom2379Coded := by decide +kernel
theorem atom2379Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (122580671875200 : Int) atom2379Coded) := by
  have h := atom2379_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2379Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2380 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 18, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2380 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2380 = ((g 13) * (g 18) * (g 19)) := by
  norm_num [atom2380, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2380_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (282393592588800 : Int) atom2380) := by
  rw [SparsePolynomial.eval_scale, eval_atom2380]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 13) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2380Coded : CoefficientMerge.Poly := [(nat_lit 7939, Int.ofNat (nat_lit 1))]
theorem atom2380Coded_decode : atom2380 = SparsePolynomial.decodeCubic 24 atom2380Coded := by decide +kernel
theorem atom2380Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (282393592588800 : Int) atom2380Coded) := by
  have h := atom2380_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2380Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2381 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 18, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2381 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2381 = ((g 13) * (g 18) * (g 20)) := by
  norm_num [atom2381, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2381_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (586889813664000 : Int) atom2381) := by
  rw [SparsePolynomial.eval_scale, eval_atom2381]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2381Coded : CoefficientMerge.Poly := [(nat_lit 7940, Int.ofNat (nat_lit 1))]
theorem atom2381Coded_decode : atom2381 = SparsePolynomial.decodeCubic 24 atom2381Coded := by decide +kernel
theorem atom2381Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (586889813664000 : Int) atom2381Coded) := by
  have h := atom2381_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2381Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2382 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 18, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2382 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2382 = ((g 13) * (g 18) * (g 21)) := by
  norm_num [atom2382, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2382_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (616912250169600 : Int) atom2382) := by
  rw [SparsePolynomial.eval_scale, eval_atom2382]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 13) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2382Coded : CoefficientMerge.Poly := [(nat_lit 7941, Int.ofNat (nat_lit 1))]
theorem atom2382Coded_decode : atom2382 = SparsePolynomial.decodeCubic 24 atom2382Coded := by decide +kernel
theorem atom2382Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (616912250169600 : Int) atom2382Coded) := by
  have h := atom2382_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2382Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2383 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 18, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2383 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2383 = ((g 13) * (g 18) * (g 22)) := by
  norm_num [atom2383, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2383_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (497465235388800 : Int) atom2383) := by
  rw [SparsePolynomial.eval_scale, eval_atom2383]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 13) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2383Coded : CoefficientMerge.Poly := [(nat_lit 7942, Int.ofNat (nat_lit 1))]
theorem atom2383Coded_decode : atom2383 = SparsePolynomial.decodeCubic 24 atom2383Coded := by decide +kernel
theorem atom2383Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (497465235388800 : Int) atom2383Coded) := by
  have h := atom2383_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2383Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2384 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 18, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2384 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2384 = ((g 13) * (g 18) * (g 23)) := by
  norm_num [atom2384, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2384_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (765835096118400 : Int) atom2384) := by
  rw [SparsePolynomial.eval_scale, eval_atom2384]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 13) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2384Coded : CoefficientMerge.Poly := [(nat_lit 7943, Int.ofNat (nat_lit 1))]
theorem atom2384Coded_decode : atom2384 = SparsePolynomial.decodeCubic 24 atom2384Coded := by decide +kernel
theorem atom2384Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (765835096118400 : Int) atom2384Coded) := by
  have h := atom2384_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2384Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2385 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 19, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2385 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2385 = ((g 13) * (g 19) * (g 19)) := by
  norm_num [atom2385, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2385_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (119238230643840 : Int) atom2385) := by
  rw [SparsePolynomial.eval_scale, eval_atom2385]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 13) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2385Coded : CoefficientMerge.Poly := [(nat_lit 7963, Int.ofNat (nat_lit 1))]
theorem atom2385Coded_decode : atom2385 = SparsePolynomial.decodeCubic 24 atom2385Coded := by decide +kernel
theorem atom2385Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (119238230643840 : Int) atom2385Coded) := by
  have h := atom2385_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2385Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2386 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 19, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2386 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2386 = ((g 13) * (g 19) * (g 20)) := by
  norm_num [atom2386, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2386_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (537665600102400 : Int) atom2386) := by
  rw [SparsePolynomial.eval_scale, eval_atom2386]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2386Coded : CoefficientMerge.Poly := [(nat_lit 7964, Int.ofNat (nat_lit 1))]
theorem atom2386Coded_decode : atom2386 = SparsePolynomial.decodeCubic 24 atom2386Coded := by decide +kernel
theorem atom2386Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (537665600102400 : Int) atom2386Coded) := by
  have h := atom2386_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2386Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2387 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 19, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2387 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2387 = ((g 13) * (g 19) * (g 21)) := by
  norm_num [atom2387, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2387_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (648792328060800 : Int) atom2387) := by
  rw [SparsePolynomial.eval_scale, eval_atom2387]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 13) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2387Coded : CoefficientMerge.Poly := [(nat_lit 7965, Int.ofNat (nat_lit 1))]
theorem atom2387Coded_decode : atom2387 = SparsePolynomial.decodeCubic 24 atom2387Coded := by decide +kernel
theorem atom2387Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (648792328060800 : Int) atom2387Coded) := by
  have h := atom2387_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2387Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2388 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 19, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2388 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2388 = ((g 13) * (g 19) * (g 22)) := by
  norm_num [atom2388, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2388_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (516707405222400 : Int) atom2388) := by
  rw [SparsePolynomial.eval_scale, eval_atom2388]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 13) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2388Coded : CoefficientMerge.Poly := [(nat_lit 7966, Int.ofNat (nat_lit 1))]
theorem atom2388Coded_decode : atom2388 = SparsePolynomial.decodeCubic 24 atom2388Coded := by decide +kernel
theorem atom2388Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (516707405222400 : Int) atom2388Coded) := by
  have h := atom2388_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2388Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2389 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 19, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2389 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2389 = ((g 13) * (g 19) * (g 23)) := by
  norm_num [atom2389, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2389_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (684584938699200 : Int) atom2389) := by
  rw [SparsePolynomial.eval_scale, eval_atom2389]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 13) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2389Coded : CoefficientMerge.Poly := [(nat_lit 7967, Int.ofNat (nat_lit 1))]
theorem atom2389Coded_decode : atom2389 = SparsePolynomial.decodeCubic 24 atom2389Coded := by decide +kernel
theorem atom2389Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (684584938699200 : Int) atom2389Coded) := by
  have h := atom2389_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2389Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2390 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 20, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2390 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2390 = ((g 13) * (g 20) * (g 20)) := by
  norm_num [atom2390, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2390_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (392272304054400 : Int) atom2390) := by
  rw [SparsePolynomial.eval_scale, eval_atom2390]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2390Coded : CoefficientMerge.Poly := [(nat_lit 7988, Int.ofNat (nat_lit 1))]
theorem atom2390Coded_decode : atom2390 = SparsePolynomial.decodeCubic 24 atom2390Coded := by decide +kernel
theorem atom2390Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (392272304054400 : Int) atom2390Coded) := by
  have h := atom2390_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2390Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2391 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 20, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2391 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2391 = ((g 13) * (g 20) * (g 21)) := by
  norm_num [atom2391, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2391_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (772722742176000 : Int) atom2391) := by
  rw [SparsePolynomial.eval_scale, eval_atom2391]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 13) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2391Coded : CoefficientMerge.Poly := [(nat_lit 7989, Int.ofNat (nat_lit 1))]
theorem atom2391Coded_decode : atom2391 = SparsePolynomial.decodeCubic 24 atom2391Coded := by decide +kernel
theorem atom2391Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (772722742176000 : Int) atom2391Coded) := by
  have h := atom2391_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2391Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2392 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 20, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2392 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2392 = ((g 13) * (g 20) * (g 22)) := by
  norm_num [atom2392, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2392_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (564667693430400 : Int) atom2392) := by
  rw [SparsePolynomial.eval_scale, eval_atom2392]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 13) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2392Coded : CoefficientMerge.Poly := [(nat_lit 7990, Int.ofNat (nat_lit 1))]
theorem atom2392Coded_decode : atom2392 = SparsePolynomial.decodeCubic 24 atom2392Coded := by decide +kernel
theorem atom2392Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (564667693430400 : Int) atom2392Coded) := by
  have h := atom2392_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2392Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2393 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 20, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2393 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2393 = ((g 13) * (g 20) * (g 23)) := by
  norm_num [atom2393, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2393_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (540935936956800 : Int) atom2393) := by
  rw [SparsePolynomial.eval_scale, eval_atom2393]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 13) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2393Coded : CoefficientMerge.Poly := [(nat_lit 7991, Int.ofNat (nat_lit 1))]
theorem atom2393Coded_decode : atom2393 = SparsePolynomial.decodeCubic 24 atom2393Coded := by decide +kernel
theorem atom2393Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (540935936956800 : Int) atom2393Coded) := by
  have h := atom2393_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2393Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2394 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 21, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2394 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2394 = ((g 13) * (g 21) * (g 21)) := by
  norm_num [atom2394, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2394_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (337287870057600 : Int) atom2394) := by
  rw [SparsePolynomial.eval_scale, eval_atom2394]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 13) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2394Coded : CoefficientMerge.Poly := [(nat_lit 8013, Int.ofNat (nat_lit 1))]
theorem atom2394Coded_decode : atom2394 = SparsePolynomial.decodeCubic 24 atom2394Coded := by decide +kernel
theorem atom2394Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (337287870057600 : Int) atom2394Coded) := by
  have h := atom2394_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2394Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2395 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 21, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2395 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2395 = ((g 13) * (g 21) * (g 22)) := by
  norm_num [atom2395, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2395_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (504358789233600 : Int) atom2395) := by
  rw [SparsePolynomial.eval_scale, eval_atom2395]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 13) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2395Coded : CoefficientMerge.Poly := [(nat_lit 8014, Int.ofNat (nat_lit 1))]
theorem atom2395Coded_decode : atom2395 = SparsePolynomial.decodeCubic 24 atom2395Coded := by decide +kernel
theorem atom2395Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (504358789233600 : Int) atom2395Coded) := by
  have h := atom2395_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2395Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2396 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 21, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2396 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2396 = ((g 13) * (g 21) * (g 23)) := by
  norm_num [atom2396, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2396_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (508847144097600 : Int) atom2396) := by
  rw [SparsePolynomial.eval_scale, eval_atom2396]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 13) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2396Coded : CoefficientMerge.Poly := [(nat_lit 8015, Int.ofNat (nat_lit 1))]
theorem atom2396Coded_decode : atom2396 = SparsePolynomial.decodeCubic 24 atom2396Coded := by decide +kernel
theorem atom2396Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (508847144097600 : Int) atom2396Coded) := by
  have h := atom2396_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2396Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2397 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 22, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2397 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2397 = ((g 13) * (g 22) * (g 22)) := by
  norm_num [atom2397, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2397_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (121844922595200 : Int) atom2397) := by
  rw [SparsePolynomial.eval_scale, eval_atom2397]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 13) * (g 22) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2397Coded : CoefficientMerge.Poly := [(nat_lit 8038, Int.ofNat (nat_lit 1))]
theorem atom2397Coded_decode : atom2397 = SparsePolynomial.decodeCubic 24 atom2397Coded := by decide +kernel
theorem atom2397Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (121844922595200 : Int) atom2397Coded) := by
  have h := atom2397_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2397Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2398 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 22, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2398 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2398 = ((g 13) * (g 22) * (g 23)) := by
  norm_num [atom2398, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2398_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (265838402340000 : Int) atom2398) := by
  rw [SparsePolynomial.eval_scale, eval_atom2398]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 13) * (g 22) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2398Coded : CoefficientMerge.Poly := [(nat_lit 8039, Int.ofNat (nat_lit 1))]
theorem atom2398Coded_decode : atom2398 = SparsePolynomial.decodeCubic 24 atom2398Coded := by decide +kernel
theorem atom2398Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (265838402340000 : Int) atom2398Coded) := by
  have h := atom2398_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2398Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2399 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 23, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2399 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2399 = ((g 13) * (g 23) * (g 23)) := by
  norm_num [atom2399, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2399_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (109034705656800 : Int) atom2399) := by
  rw [SparsePolynomial.eval_scale, eval_atom2399]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 13) * (g 23) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2399Coded : CoefficientMerge.Poly := [(nat_lit 8063, Int.ofNat (nat_lit 1))]
theorem atom2399Coded_decode : atom2399 = SparsePolynomial.decodeCubic 24 atom2399Coded := by decide +kernel
theorem atom2399Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (109034705656800 : Int) atom2399Coded) := by
  have h := atom2399_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2399Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2400 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom2400 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2400 = ((g 14) * (g 14) * (g 14)) := by
  norm_num [atom2400, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2400_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2739299270400 : Int) atom2400) := by
  rw [SparsePolynomial.eval_scale, eval_atom2400]
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 14) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2400Coded : CoefficientMerge.Poly := [(nat_lit 8414, Int.ofNat (nat_lit 1))]
theorem atom2400Coded_decode : atom2400 = SparsePolynomial.decodeCubic 24 atom2400Coded := by decide +kernel
theorem atom2400Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (2739299270400 : Int) atom2400Coded) := by
  have h := atom2400_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2400Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2401 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 14, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2401 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2401 = ((g 14) * (g 14) * (g 18)) := by
  norm_num [atom2401, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2401_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20400780708000 : Int) atom2401) := by
  rw [SparsePolynomial.eval_scale, eval_atom2401]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 14) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2401Coded : CoefficientMerge.Poly := [(nat_lit 8418, Int.ofNat (nat_lit 1))]
theorem atom2401Coded_decode : atom2401 = SparsePolynomial.decodeCubic 24 atom2401Coded := by decide +kernel
theorem atom2401Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (20400780708000 : Int) atom2401Coded) := by
  have h := atom2401_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2401Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2402 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 14, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2402 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2402 = ((g 14) * (g 14) * (g 20)) := by
  norm_num [atom2402, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2402_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52121547324000 : Int) atom2402) := by
  rw [SparsePolynomial.eval_scale, eval_atom2402]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 14) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2402Coded : CoefficientMerge.Poly := [(nat_lit 8420, Int.ofNat (nat_lit 1))]
theorem atom2402Coded_decode : atom2402 = SparsePolynomial.decodeCubic 24 atom2402Coded := by decide +kernel
theorem atom2402Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (52121547324000 : Int) atom2402Coded) := by
  have h := atom2402_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2402Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2403 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 14, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2403 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2403 = ((g 14) * (g 14) * (g 21)) := by
  norm_num [atom2403, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2403_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12579780074400 : Int) atom2403) := by
  rw [SparsePolynomial.eval_scale, eval_atom2403]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 14) * (g 14) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2403Coded : CoefficientMerge.Poly := [(nat_lit 8421, Int.ofNat (nat_lit 1))]
theorem atom2403Coded_decode : atom2403 = SparsePolynomial.decodeCubic 24 atom2403Coded := by decide +kernel
theorem atom2403Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (12579780074400 : Int) atom2403Coded) := by
  have h := atom2403_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2403Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2404 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom2404 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2404 = ((g 14) * (g 15) * (g 15)) := by
  norm_num [atom2404, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2404_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5134857235200 : Int) atom2404) := by
  rw [SparsePolynomial.eval_scale, eval_atom2404]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 14) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2404Coded : CoefficientMerge.Poly := [(nat_lit 8439, Int.ofNat (nat_lit 1))]
theorem atom2404Coded_decode : atom2404 = SparsePolynomial.decodeCubic 24 atom2404Coded := by decide +kernel
theorem atom2404Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (5134857235200 : Int) atom2404Coded) := by
  have h := atom2404_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2404Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2405 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 15, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom2405 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2405 = ((g 14) * (g 15) * (g 17)) := by
  norm_num [atom2405, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2405_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3083040576000 : Int) atom2405) := by
  rw [SparsePolynomial.eval_scale, eval_atom2405]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 14) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2405Coded : CoefficientMerge.Poly := [(nat_lit 8441, Int.ofNat (nat_lit 1))]
theorem atom2405Coded_decode : atom2405 = SparsePolynomial.decodeCubic 24 atom2405Coded := by decide +kernel
theorem atom2405Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3083040576000 : Int) atom2405Coded) := by
  have h := atom2405_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2405Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2406 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 15, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2406 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2406 = ((g 14) * (g 15) * (g 18)) := by
  norm_num [atom2406, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2406_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39376524972960 : Int) atom2406) := by
  rw [SparsePolynomial.eval_scale, eval_atom2406]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 14) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2406Coded : CoefficientMerge.Poly := [(nat_lit 8442, Int.ofNat (nat_lit 1))]
theorem atom2406Coded_decode : atom2406 = SparsePolynomial.decodeCubic 24 atom2406Coded := by decide +kernel
theorem atom2406Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (39376524972960 : Int) atom2406Coded) := by
  have h := atom2406_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2406Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2407 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 15, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2407 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2407 = ((g 14) * (g 15) * (g 20)) := by
  norm_num [atom2407, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2407_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (174486042511200 : Int) atom2407) := by
  rw [SparsePolynomial.eval_scale, eval_atom2407]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 14) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2407Coded : CoefficientMerge.Poly := [(nat_lit 8444, Int.ofNat (nat_lit 1))]
theorem atom2407Coded_decode : atom2407 = SparsePolynomial.decodeCubic 24 atom2407Coded := by decide +kernel
theorem atom2407Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (174486042511200 : Int) atom2407Coded) := by
  have h := atom2407_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2407Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2408 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 15, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2408 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2408 = ((g 14) * (g 15) * (g 21)) := by
  norm_num [atom2408, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2408_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (128607934240800 : Int) atom2408) := by
  rw [SparsePolynomial.eval_scale, eval_atom2408]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 14) * (g 15) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2408Coded : CoefficientMerge.Poly := [(nat_lit 8445, Int.ofNat (nat_lit 1))]
theorem atom2408Coded_decode : atom2408 = SparsePolynomial.decodeCubic 24 atom2408Coded := by decide +kernel
theorem atom2408Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (128607934240800 : Int) atom2408Coded) := by
  have h := atom2408_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2408Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2409 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 15, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2409 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2409 = ((g 14) * (g 15) * (g 22)) := by
  norm_num [atom2409, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2409_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (96386479580160 : Int) atom2409) := by
  rw [SparsePolynomial.eval_scale, eval_atom2409]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 14) * (g 15) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2409Coded : CoefficientMerge.Poly := [(nat_lit 8446, Int.ofNat (nat_lit 1))]
theorem atom2409Coded_decode : atom2409 = SparsePolynomial.decodeCubic 24 atom2409Coded := by decide +kernel
theorem atom2409Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (96386479580160 : Int) atom2409Coded) := by
  have h := atom2409_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2409Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2410 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 15, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2410 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2410 = ((g 14) * (g 15) * (g 23)) := by
  norm_num [atom2410, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2410_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (153439015262400 : Int) atom2410) := by
  rw [SparsePolynomial.eval_scale, eval_atom2410]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 14) * (g 15) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2410Coded : CoefficientMerge.Poly := [(nat_lit 8447, Int.ofNat (nat_lit 1))]
theorem atom2410Coded_decode : atom2410 = SparsePolynomial.decodeCubic 24 atom2410Coded := by decide +kernel
theorem atom2410Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (153439015262400 : Int) atom2410Coded) := by
  have h := atom2410_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2410Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2411 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 16, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom2411 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2411 = ((g 14) * (g 16) * (g 16)) := by
  norm_num [atom2411, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2411_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11300938387200 : Int) atom2411) := by
  rw [SparsePolynomial.eval_scale, eval_atom2411]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 14) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2411Coded : CoefficientMerge.Poly := [(nat_lit 8464, Int.ofNat (nat_lit 1))]
theorem atom2411Coded_decode : atom2411 = SparsePolynomial.decodeCubic 24 atom2411Coded := by decide +kernel
theorem atom2411Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (11300938387200 : Int) atom2411Coded) := by
  have h := atom2411_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2411Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2412 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom2412 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2412 = ((g 14) * (g 16) * (g 17)) := by
  norm_num [atom2412, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2412_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24664324608000 : Int) atom2412) := by
  rw [SparsePolynomial.eval_scale, eval_atom2412]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 14) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2412Coded : CoefficientMerge.Poly := [(nat_lit 8465, Int.ofNat (nat_lit 1))]
theorem atom2412Coded_decode : atom2412 = SparsePolynomial.decodeCubic 24 atom2412Coded := by decide +kernel
theorem atom2412Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (24664324608000 : Int) atom2412Coded) := by
  have h := atom2412_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2412Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2413 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 16, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2413 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2413 = ((g 14) * (g 16) * (g 18)) := by
  norm_num [atom2413, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2413_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27029092436640 : Int) atom2413) := by
  rw [SparsePolynomial.eval_scale, eval_atom2413]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 14) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2413Coded : CoefficientMerge.Poly := [(nat_lit 8466, Int.ofNat (nat_lit 1))]
theorem atom2413Coded_decode : atom2413 = SparsePolynomial.decodeCubic 24 atom2413Coded := by decide +kernel
theorem atom2413Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (27029092436640 : Int) atom2413Coded) := by
  have h := atom2413_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2413Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2414 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 16, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2414 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2414 = ((g 14) * (g 16) * (g 20)) := by
  norm_num [atom2414, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2414_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (215567799804000 : Int) atom2414) := by
  rw [SparsePolynomial.eval_scale, eval_atom2414]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 14) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2414Coded : CoefficientMerge.Poly := [(nat_lit 8468, Int.ofNat (nat_lit 1))]
theorem atom2414Coded_decode : atom2414 = SparsePolynomial.decodeCubic 24 atom2414Coded := by decide +kernel
theorem atom2414Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (215567799804000 : Int) atom2414Coded) := by
  have h := atom2414_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2414Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2415 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 16, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2415 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2415 = ((g 14) * (g 16) * (g 21)) := by
  norm_num [atom2415, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2415_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (197885015748000 : Int) atom2415) := by
  rw [SparsePolynomial.eval_scale, eval_atom2415]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 14) * (g 16) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2415Coded : CoefficientMerge.Poly := [(nat_lit 8469, Int.ofNat (nat_lit 1))]
theorem atom2415Coded_decode : atom2415 = SparsePolynomial.decodeCubic 24 atom2415Coded := by decide +kernel
theorem atom2415Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (197885015748000 : Int) atom2415Coded) := by
  have h := atom2415_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2415Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2416 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 16, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2416 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2416 = ((g 14) * (g 16) * (g 22)) := by
  norm_num [atom2416, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2416_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (164800213079040 : Int) atom2416) := by
  rw [SparsePolynomial.eval_scale, eval_atom2416]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 14) * (g 16) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2416Coded : CoefficientMerge.Poly := [(nat_lit 8470, Int.ofNat (nat_lit 1))]
theorem atom2416Coded_decode : atom2416 = SparsePolynomial.decodeCubic 24 atom2416Coded := by decide +kernel
theorem atom2416Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (164800213079040 : Int) atom2416Coded) := by
  have h := atom2416_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2416Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2417 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 16, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2417 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2417 = ((g 14) * (g 16) * (g 23)) := by
  norm_num [atom2417, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2417_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (363241134547200 : Int) atom2417) := by
  rw [SparsePolynomial.eval_scale, eval_atom2417]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 14) * (g 16) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2417Coded : CoefficientMerge.Poly := [(nat_lit 8471, Int.ofNat (nat_lit 1))]
theorem atom2417Coded_decode : atom2417 = SparsePolynomial.decodeCubic 24 atom2417Coded := by decide +kernel
theorem atom2417Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (363241134547200 : Int) atom2417Coded) := by
  have h := atom2417_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2417Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2418 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom2418 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2418 = ((g 14) * (g 17) * (g 17)) := by
  norm_num [atom2418, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2418_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25008065913600 : Int) atom2418) := by
  rw [SparsePolynomial.eval_scale, eval_atom2418]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 14) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2418Coded : CoefficientMerge.Poly := [(nat_lit 8489, Int.ofNat (nat_lit 1))]
theorem atom2418Coded_decode : atom2418 = SparsePolynomial.decodeCubic 24 atom2418Coded := by decide +kernel
theorem atom2418Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (25008065913600 : Int) atom2418Coded) := by
  have h := atom2418_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2418Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2419 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 17, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2419 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2419 = ((g 14) * (g 17) * (g 18)) := by
  norm_num [atom2419, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2419_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (71475157353600 : Int) atom2419) := by
  rw [SparsePolynomial.eval_scale, eval_atom2419]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 14) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2419Coded : CoefficientMerge.Poly := [(nat_lit 8490, Int.ofNat (nat_lit 1))]
theorem atom2419Coded_decode : atom2419 = SparsePolynomial.decodeCubic 24 atom2419Coded := by decide +kernel
theorem atom2419Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (71475157353600 : Int) atom2419Coded) := by
  have h := atom2419_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2419Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2420 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 17, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2420 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2420 = ((g 14) * (g 17) * (g 19)) := by
  norm_num [atom2420, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2420_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (89689459860000 : Int) atom2420) := by
  rw [SparsePolynomial.eval_scale, eval_atom2420]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 14) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2420Coded : CoefficientMerge.Poly := [(nat_lit 8491, Int.ofNat (nat_lit 1))]
theorem atom2420Coded_decode : atom2420 = SparsePolynomial.decodeCubic 24 atom2420Coded := by decide +kernel
theorem atom2420Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (89689459860000 : Int) atom2420Coded) := by
  have h := atom2420_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2420Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2421 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 17, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2421 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2421 = ((g 14) * (g 17) * (g 20)) := by
  norm_num [atom2421, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2421_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (351305386185600 : Int) atom2421) := by
  rw [SparsePolynomial.eval_scale, eval_atom2421]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 14) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2421Coded : CoefficientMerge.Poly := [(nat_lit 8492, Int.ofNat (nat_lit 1))]
theorem atom2421Coded_decode : atom2421 = SparsePolynomial.decodeCubic 24 atom2421Coded := by decide +kernel
theorem atom2421Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (351305386185600 : Int) atom2421Coded) := by
  have h := atom2421_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2421Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2422 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 17, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2422 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2422 = ((g 14) * (g 17) * (g 21)) := by
  norm_num [atom2422, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2422_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (364301110958400 : Int) atom2422) := by
  rw [SparsePolynomial.eval_scale, eval_atom2422]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 14) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2422Coded : CoefficientMerge.Poly := [(nat_lit 8493, Int.ofNat (nat_lit 1))]
theorem atom2422Coded_decode : atom2422 = SparsePolynomial.decodeCubic 24 atom2422Coded := by decide +kernel
theorem atom2422Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (364301110958400 : Int) atom2422Coded) := by
  have h := atom2422_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2422Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2423 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 17, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2423 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2423 = ((g 14) * (g 17) * (g 22)) := by
  norm_num [atom2423, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2423_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (361575865778400 : Int) atom2423) := by
  rw [SparsePolynomial.eval_scale, eval_atom2423]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 14) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2423Coded : CoefficientMerge.Poly := [(nat_lit 8494, Int.ofNat (nat_lit 1))]
theorem atom2423Coded_decode : atom2423 = SparsePolynomial.decodeCubic 24 atom2423Coded := by decide +kernel
theorem atom2423Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (361575865778400 : Int) atom2423Coded) := by
  have h := atom2423_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2423Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2424 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 17, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2424 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2424 = ((g 14) * (g 17) * (g 23)) := by
  norm_num [atom2424, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2424_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (584217584596800 : Int) atom2424) := by
  rw [SparsePolynomial.eval_scale, eval_atom2424]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 14) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2424Coded : CoefficientMerge.Poly := [(nat_lit 8495, Int.ofNat (nat_lit 1))]
theorem atom2424Coded_decode : atom2424 = SparsePolynomial.decodeCubic 24 atom2424Coded := by decide +kernel
theorem atom2424Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (584217584596800 : Int) atom2424Coded) := by
  have h := atom2424_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2424Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2425 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 18, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2425 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2425 = ((g 14) * (g 18) * (g 18)) := by
  norm_num [atom2425, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2425_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (89642062540800 : Int) atom2425) := by
  rw [SparsePolynomial.eval_scale, eval_atom2425]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 14) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2425Coded : CoefficientMerge.Poly := [(nat_lit 8514, Int.ofNat (nat_lit 1))]
theorem atom2425Coded_decode : atom2425 = SparsePolynomial.decodeCubic 24 atom2425Coded := by decide +kernel
theorem atom2425Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (89642062540800 : Int) atom2425Coded) := by
  have h := atom2425_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2425Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2426 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 18, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2426 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2426 = ((g 14) * (g 18) * (g 19)) := by
  norm_num [atom2426, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2426_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (231081643069200 : Int) atom2426) := by
  rw [SparsePolynomial.eval_scale, eval_atom2426]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 14) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2426Coded : CoefficientMerge.Poly := [(nat_lit 8515, Int.ofNat (nat_lit 1))]
theorem atom2426Coded_decode : atom2426 = SparsePolynomial.decodeCubic 24 atom2426Coded := by decide +kernel
theorem atom2426Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (231081643069200 : Int) atom2426Coded) := by
  have h := atom2426_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2426Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2427 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 18, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2427 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2427 = ((g 14) * (g 18) * (g 20)) := by
  norm_num [atom2427, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2427_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (545421771417600 : Int) atom2427) := by
  rw [SparsePolynomial.eval_scale, eval_atom2427]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 14) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2427Coded : CoefficientMerge.Poly := [(nat_lit 8516, Int.ofNat (nat_lit 1))]
theorem atom2427Coded_decode : atom2427 = SparsePolynomial.decodeCubic 24 atom2427Coded := by decide +kernel
theorem atom2427Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (545421771417600 : Int) atom2427Coded) := by
  have h := atom2427_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2427Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2428 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 18, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2428 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2428 = ((g 14) * (g 18) * (g 21)) := by
  norm_num [atom2428, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2428_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (587648796134400 : Int) atom2428) := by
  rw [SparsePolynomial.eval_scale, eval_atom2428]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 14) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2428Coded : CoefficientMerge.Poly := [(nat_lit 8517, Int.ofNat (nat_lit 1))]
theorem atom2428Coded_decode : atom2428 = SparsePolynomial.decodeCubic 24 atom2428Coded := by decide +kernel
theorem atom2428Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (587648796134400 : Int) atom2428Coded) := by
  have h := atom2428_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2428Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2429 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 18, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2429 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2429 = ((g 14) * (g 18) * (g 22)) := by
  norm_num [atom2429, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2429_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (482552368527600 : Int) atom2429) := by
  rw [SparsePolynomial.eval_scale, eval_atom2429]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 14) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2429Coded : CoefficientMerge.Poly := [(nat_lit 8518, Int.ofNat (nat_lit 1))]
theorem atom2429Coded_decode : atom2429 = SparsePolynomial.decodeCubic 24 atom2429Coded := by decide +kernel
theorem atom2429Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (482552368527600 : Int) atom2429Coded) := by
  have h := atom2429_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2429Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2430 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 18, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2430 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2430 = ((g 14) * (g 18) * (g 23)) := by
  norm_num [atom2430, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2430_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (759227313121200 : Int) atom2430) := by
  rw [SparsePolynomial.eval_scale, eval_atom2430]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 14) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2430Coded : CoefficientMerge.Poly := [(nat_lit 8519, Int.ofNat (nat_lit 1))]
theorem atom2430Coded_decode : atom2430 = SparsePolynomial.decodeCubic 24 atom2430Coded := by decide +kernel
theorem atom2430Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (759227313121200 : Int) atom2430Coded) := by
  have h := atom2430_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2430Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2431 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 19, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2431 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2431 = ((g 14) * (g 19) * (g 19)) := by
  norm_num [atom2431, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2431_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (95421168944640 : Int) atom2431) := by
  rw [SparsePolynomial.eval_scale, eval_atom2431]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 14) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2431Coded : CoefficientMerge.Poly := [(nat_lit 8539, Int.ofNat (nat_lit 1))]
theorem atom2431Coded_decode : atom2431 = SparsePolynomial.decodeCubic 24 atom2431Coded := by decide +kernel
theorem atom2431Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (95421168944640 : Int) atom2431Coded) := by
  have h := atom2431_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2431Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2432 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 19, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2432 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2432 = ((g 14) * (g 19) * (g 20)) := by
  norm_num [atom2432, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2432_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (500895976719600 : Int) atom2432) := by
  rw [SparsePolynomial.eval_scale, eval_atom2432]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 14) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2432Coded : CoefficientMerge.Poly := [(nat_lit 8540, Int.ofNat (nat_lit 1))]
theorem atom2432Coded_decode : atom2432 = SparsePolynomial.decodeCubic 24 atom2432Coded := by decide +kernel
theorem atom2432Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (500895976719600 : Int) atom2432Coded) := by
  have h := atom2432_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2432Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2433 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 19, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2433 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2433 = ((g 14) * (g 19) * (g 21)) := by
  norm_num [atom2433, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2433_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (624067545162600 : Int) atom2433) := by
  rw [SparsePolynomial.eval_scale, eval_atom2433]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 14) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2433Coded : CoefficientMerge.Poly := [(nat_lit 8541, Int.ofNat (nat_lit 1))]
theorem atom2433Coded_decode : atom2433 = SparsePolynomial.decodeCubic 24 atom2433Coded := by decide +kernel
theorem atom2433Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (624067545162600 : Int) atom2433Coded) := by
  have h := atom2433_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2433Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2434 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 19, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2434 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2434 = ((g 14) * (g 19) * (g 22)) := by
  norm_num [atom2434, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2434_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (528698249503200 : Int) atom2434) := by
  rw [SparsePolynomial.eval_scale, eval_atom2434]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 14) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2434Coded : CoefficientMerge.Poly := [(nat_lit 8542, Int.ofNat (nat_lit 1))]
theorem atom2434Coded_decode : atom2434 = SparsePolynomial.decodeCubic 24 atom2434Coded := by decide +kernel
theorem atom2434Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (528698249503200 : Int) atom2434Coded) := by
  have h := atom2434_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2434Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2435 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 19, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2435 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2435 = ((g 14) * (g 19) * (g 23)) := by
  norm_num [atom2435, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2435_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (709210793699100 : Int) atom2435) := by
  rw [SparsePolynomial.eval_scale, eval_atom2435]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 14) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2435Coded : CoefficientMerge.Poly := [(nat_lit 8543, Int.ofNat (nat_lit 1))]
theorem atom2435Coded_decode : atom2435 = SparsePolynomial.decodeCubic 24 atom2435Coded := by decide +kernel
theorem atom2435Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (709210793699100 : Int) atom2435Coded) := by
  have h := atom2435_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2435Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2436 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 20, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2436 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2436 = ((g 14) * (g 20) * (g 20)) := by
  norm_num [atom2436, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2436_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (378597382732800 : Int) atom2436) := by
  rw [SparsePolynomial.eval_scale, eval_atom2436]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 14) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2436Coded : CoefficientMerge.Poly := [(nat_lit 8564, Int.ofNat (nat_lit 1))]
theorem atom2436Coded_decode : atom2436 = SparsePolynomial.decodeCubic 24 atom2436Coded := by decide +kernel
theorem atom2436Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (378597382732800 : Int) atom2436Coded) := by
  have h := atom2436_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2436Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2437 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 20, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2437 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2437 = ((g 14) * (g 20) * (g 21)) := by
  norm_num [atom2437, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2437_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (759618673228800 : Int) atom2437) := by
  rw [SparsePolynomial.eval_scale, eval_atom2437]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 14) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2437Coded : CoefficientMerge.Poly := [(nat_lit 8565, Int.ofNat (nat_lit 1))]
theorem atom2437Coded_decode : atom2437 = SparsePolynomial.decodeCubic 24 atom2437Coded := by decide +kernel
theorem atom2437Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (759618673228800 : Int) atom2437Coded) := by
  have h := atom2437_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2437Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2438 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 20, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2438 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2438 = ((g 14) * (g 20) * (g 22)) := by
  norm_num [atom2438, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2438_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (613004972605200 : Int) atom2438) := by
  rw [SparsePolynomial.eval_scale, eval_atom2438]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 14) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2438Coded : CoefficientMerge.Poly := [(nat_lit 8566, Int.ofNat (nat_lit 1))]
theorem atom2438Coded_decode : atom2438 = SparsePolynomial.decodeCubic 24 atom2438Coded := by decide +kernel
theorem atom2438Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (613004972605200 : Int) atom2438Coded) := by
  have h := atom2438_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2438Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2439 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 20, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2439 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2439 = ((g 14) * (g 20) * (g 23)) := by
  norm_num [atom2439, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2439_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (656760067563600 : Int) atom2439) := by
  rw [SparsePolynomial.eval_scale, eval_atom2439]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 14) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2439Coded : CoefficientMerge.Poly := [(nat_lit 8567, Int.ofNat (nat_lit 1))]
theorem atom2439Coded_decode : atom2439 = SparsePolynomial.decodeCubic 24 atom2439Coded := by decide +kernel
theorem atom2439Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (656760067563600 : Int) atom2439Coded) := by
  have h := atom2439_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2439Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2440 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 21, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2440 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2440 = ((g 14) * (g 21) * (g 21)) := by
  norm_num [atom2440, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2440_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (334775681856000 : Int) atom2440) := by
  rw [SparsePolynomial.eval_scale, eval_atom2440]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 14) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2440Coded : CoefficientMerge.Poly := [(nat_lit 8589, Int.ofNat (nat_lit 1))]
theorem atom2440Coded_decode : atom2440 = SparsePolynomial.decodeCubic 24 atom2440Coded := by decide +kernel
theorem atom2440Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (334775681856000 : Int) atom2440Coded) := by
  have h := atom2440_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2440Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2441 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 21, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2441 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2441 = ((g 14) * (g 21) * (g 22)) := by
  norm_num [atom2441, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2441_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (573058747560600 : Int) atom2441) := by
  rw [SparsePolynomial.eval_scale, eval_atom2441]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 14) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2441Coded : CoefficientMerge.Poly := [(nat_lit 8590, Int.ofNat (nat_lit 1))]
theorem atom2441Coded_decode : atom2441 = SparsePolynomial.decodeCubic 24 atom2441Coded := by decide +kernel
theorem atom2441Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (573058747560600 : Int) atom2441Coded) := by
  have h := atom2441_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2441Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2442 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 21, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2442 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2442 = ((g 14) * (g 21) * (g 23)) := by
  norm_num [atom2442, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2442_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (648004298772600 : Int) atom2442) := by
  rw [SparsePolynomial.eval_scale, eval_atom2442]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 14) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2442Coded : CoefficientMerge.Poly := [(nat_lit 8591, Int.ofNat (nat_lit 1))]
theorem atom2442Coded_decode : atom2442 = SparsePolynomial.decodeCubic 24 atom2442Coded := by decide +kernel
theorem atom2442Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (648004298772600 : Int) atom2442Coded) := by
  have h := atom2442_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2442Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2443 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 22, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2443 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2443 = ((g 14) * (g 22) * (g 22)) := by
  norm_num [atom2443, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2443_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (188901029066400 : Int) atom2443) := by
  rw [SparsePolynomial.eval_scale, eval_atom2443]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 14) * (g 22) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2443Coded : CoefficientMerge.Poly := [(nat_lit 8614, Int.ofNat (nat_lit 1))]
theorem atom2443Coded_decode : atom2443 = SparsePolynomial.decodeCubic 24 atom2443Coded := by decide +kernel
theorem atom2443Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (188901029066400 : Int) atom2443Coded) := by
  have h := atom2443_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2443Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2444 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 22, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2444 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2444 = ((g 14) * (g 22) * (g 23)) := by
  norm_num [atom2444, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2444_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (479009353479300 : Int) atom2444) := by
  rw [SparsePolynomial.eval_scale, eval_atom2444]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 14) * (g 22) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2444Coded : CoefficientMerge.Poly := [(nat_lit 8615, Int.ofNat (nat_lit 1))]
theorem atom2444Coded_decode : atom2444 = SparsePolynomial.decodeCubic 24 atom2444Coded := by decide +kernel
theorem atom2444Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (479009353479300 : Int) atom2444Coded) := by
  have h := atom2444_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2444Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2445 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 23, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2445 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2445 = ((g 14) * (g 23) * (g 23)) := by
  norm_num [atom2445, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2445_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (253041385835700 : Int) atom2445) := by
  rw [SparsePolynomial.eval_scale, eval_atom2445]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 14) * (g 23) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2445Coded : CoefficientMerge.Poly := [(nat_lit 8639, Int.ofNat (nat_lit 1))]
theorem atom2445Coded_decode : atom2445 = SparsePolynomial.decodeCubic 24 atom2445Coded := by decide +kernel
theorem atom2445Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (253041385835700 : Int) atom2445Coded) := by
  have h := atom2445_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2445Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2446 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom2446 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2446 = ((g 15) * (g 15) * (g 15)) := by
  norm_num [atom2446, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2446_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4450918348800 : Int) atom2446) := by
  rw [SparsePolynomial.eval_scale, eval_atom2446]
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 15) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2446Coded : CoefficientMerge.Poly := [(nat_lit 9015, Int.ofNat (nat_lit 1))]
theorem atom2446Coded_decode : atom2446 = SparsePolynomial.decodeCubic 24 atom2446Coded := by decide +kernel
theorem atom2446Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (4450918348800 : Int) atom2446Coded) := by
  have h := atom2446_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2446Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2447 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 15, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2447 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2447 = ((g 15) * (g 15) * (g 18)) := by
  norm_num [atom2447, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2447_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24318972518400 : Int) atom2447) := by
  rw [SparsePolynomial.eval_scale, eval_atom2447]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 15) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2447Coded : CoefficientMerge.Poly := [(nat_lit 9018, Int.ofNat (nat_lit 1))]
theorem atom2447Coded_decode : atom2447 = SparsePolynomial.decodeCubic 24 atom2447Coded := by decide +kernel
theorem atom2447Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (24318972518400 : Int) atom2447Coded) := by
  have h := atom2447_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2447Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2448 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 15, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2448 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2448 = ((g 15) * (g 15) * (g 20)) := by
  norm_num [atom2448, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2448_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (89482272768000 : Int) atom2448) := by
  rw [SparsePolynomial.eval_scale, eval_atom2448]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 15) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2448Coded : CoefficientMerge.Poly := [(nat_lit 9020, Int.ofNat (nat_lit 1))]
theorem atom2448Coded_decode : atom2448 = SparsePolynomial.decodeCubic 24 atom2448Coded := by decide +kernel
theorem atom2448Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (89482272768000 : Int) atom2448Coded) := by
  have h := atom2448_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2448Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block032 : CoefficientMerge.Poly := [(nat_lit 7893, Int.ofNat (nat_lit 268132862289600)), (nat_lit 7894, Int.ofNat (nat_lit 255013789363200)), (nat_lit 7895, Int.ofNat (nat_lit 456770220228000)), (nat_lit 7913, Int.ofNat (nat_lit 41470439472000)), (nat_lit 7914, Int.ofNat (nat_lit 130081695004800)), (nat_lit 7915, Int.ofNat (nat_lit 144679235500800)), (nat_lit 7916, Int.ofNat (nat_lit 412121123568000)), (nat_lit 7917, Int.ofNat (nat_lit 420077150539200)), (nat_lit 7918, Int.ofNat (nat_lit 432690996326400)), (nat_lit 7919, Int.ofNat (nat_lit 655019877204000)), (nat_lit 7938, Int.ofNat (nat_lit 122580671875200)), (nat_lit 7939, Int.ofNat (nat_lit 282393592588800)), (nat_lit 7940, Int.ofNat (nat_lit 586889813664000)), (nat_lit 7941, Int.ofNat (nat_lit 616912250169600)), (nat_lit 7942, Int.ofNat (nat_lit 497465235388800)), (nat_lit 7943, Int.ofNat (nat_lit 765835096118400)), (nat_lit 7963, Int.ofNat (nat_lit 119238230643840)), (nat_lit 7964, Int.ofNat (nat_lit 537665600102400)), (nat_lit 7965, Int.ofNat (nat_lit 648792328060800)), (nat_lit 7966, Int.ofNat (nat_lit 516707405222400)), (nat_lit 7967, Int.ofNat (nat_lit 684584938699200)), (nat_lit 7988, Int.ofNat (nat_lit 392272304054400)), (nat_lit 7989, Int.ofNat (nat_lit 772722742176000)), (nat_lit 7990, Int.ofNat (nat_lit 564667693430400)), (nat_lit 7991, Int.ofNat (nat_lit 540935936956800)), (nat_lit 8013, Int.ofNat (nat_lit 337287870057600)), (nat_lit 8014, Int.ofNat (nat_lit 504358789233600)), (nat_lit 8015, Int.ofNat (nat_lit 508847144097600)), (nat_lit 8038, Int.ofNat (nat_lit 121844922595200)), (nat_lit 8039, Int.ofNat (nat_lit 265838402340000)), (nat_lit 8063, Int.ofNat (nat_lit 109034705656800)), (nat_lit 8414, Int.ofNat (nat_lit 2739299270400)), (nat_lit 8418, Int.ofNat (nat_lit 20400780708000)), (nat_lit 8420, Int.ofNat (nat_lit 52121547324000)), (nat_lit 8421, Int.ofNat (nat_lit 12579780074400)), (nat_lit 8439, Int.ofNat (nat_lit 5134857235200)), (nat_lit 8441, Int.ofNat (nat_lit 3083040576000)), (nat_lit 8442, Int.ofNat (nat_lit 39376524972960)), (nat_lit 8444, Int.ofNat (nat_lit 174486042511200)), (nat_lit 8445, Int.ofNat (nat_lit 128607934240800)), (nat_lit 8446, Int.ofNat (nat_lit 96386479580160)), (nat_lit 8447, Int.ofNat (nat_lit 153439015262400)), (nat_lit 8464, Int.ofNat (nat_lit 11300938387200)), (nat_lit 8465, Int.ofNat (nat_lit 24664324608000)), (nat_lit 8466, Int.ofNat (nat_lit 27029092436640)), (nat_lit 8468, Int.ofNat (nat_lit 215567799804000)), (nat_lit 8469, Int.ofNat (nat_lit 197885015748000)), (nat_lit 8470, Int.ofNat (nat_lit 164800213079040)), (nat_lit 8471, Int.ofNat (nat_lit 363241134547200)), (nat_lit 8489, Int.ofNat (nat_lit 25008065913600)), (nat_lit 8490, Int.ofNat (nat_lit 71475157353600)), (nat_lit 8491, Int.ofNat (nat_lit 89689459860000)), (nat_lit 8492, Int.ofNat (nat_lit 351305386185600)), (nat_lit 8493, Int.ofNat (nat_lit 364301110958400)), (nat_lit 8494, Int.ofNat (nat_lit 361575865778400)), (nat_lit 8495, Int.ofNat (nat_lit 584217584596800)), (nat_lit 8514, Int.ofNat (nat_lit 89642062540800)), (nat_lit 8515, Int.ofNat (nat_lit 231081643069200)), (nat_lit 8516, Int.ofNat (nat_lit 545421771417600)), (nat_lit 8517, Int.ofNat (nat_lit 587648796134400)), (nat_lit 8518, Int.ofNat (nat_lit 482552368527600)), (nat_lit 8519, Int.ofNat (nat_lit 759227313121200)), (nat_lit 8539, Int.ofNat (nat_lit 95421168944640)), (nat_lit 8540, Int.ofNat (nat_lit 500895976719600)), (nat_lit 8541, Int.ofNat (nat_lit 624067545162600)), (nat_lit 8542, Int.ofNat (nat_lit 528698249503200)), (nat_lit 8543, Int.ofNat (nat_lit 709210793699100)), (nat_lit 8564, Int.ofNat (nat_lit 378597382732800)), (nat_lit 8565, Int.ofNat (nat_lit 759618673228800)), (nat_lit 8566, Int.ofNat (nat_lit 613004972605200)), (nat_lit 8567, Int.ofNat (nat_lit 656760067563600)), (nat_lit 8589, Int.ofNat (nat_lit 334775681856000)), (nat_lit 8590, Int.ofNat (nat_lit 573058747560600)), (nat_lit 8591, Int.ofNat (nat_lit 648004298772600)), (nat_lit 8614, Int.ofNat (nat_lit 188901029066400)), (nat_lit 8615, Int.ofNat (nat_lit 479009353479300)), (nat_lit 8639, Int.ofNat (nat_lit 253041385835700)), (nat_lit 9015, Int.ofNat (nat_lit 4450918348800)), (nat_lit 9018, Int.ofNat (nat_lit 24318972518400)), (nat_lit 9020, Int.ofNat (nat_lit 89482272768000))]
theorem block032_data : block032 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (268132862289600 : Int) atom2369Coded) (CoefficientMerge.scale (255013789363200 : Int) atom2370Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (456770220228000 : Int) atom2371Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41470439472000 : Int) atom2372Coded) (CoefficientMerge.scale (130081695004800 : Int) atom2373Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (144679235500800 : Int) atom2374Coded) (CoefficientMerge.scale (412121123568000 : Int) atom2375Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (420077150539200 : Int) atom2376Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (432690996326400 : Int) atom2377Coded) (CoefficientMerge.scale (655019877204000 : Int) atom2378Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (122580671875200 : Int) atom2379Coded) (CoefficientMerge.scale (282393592588800 : Int) atom2380Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (586889813664000 : Int) atom2381Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (616912250169600 : Int) atom2382Coded) (CoefficientMerge.scale (497465235388800 : Int) atom2383Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (765835096118400 : Int) atom2384Coded) (CoefficientMerge.scale (119238230643840 : Int) atom2385Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (537665600102400 : Int) atom2386Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (648792328060800 : Int) atom2387Coded) (CoefficientMerge.scale (516707405222400 : Int) atom2388Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (684584938699200 : Int) atom2389Coded) (CoefficientMerge.scale (392272304054400 : Int) atom2390Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (772722742176000 : Int) atom2391Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (564667693430400 : Int) atom2392Coded) (CoefficientMerge.scale (540935936956800 : Int) atom2393Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (337287870057600 : Int) atom2394Coded) (CoefficientMerge.scale (504358789233600 : Int) atom2395Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (508847144097600 : Int) atom2396Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (121844922595200 : Int) atom2397Coded) (CoefficientMerge.scale (265838402340000 : Int) atom2398Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (109034705656800 : Int) atom2399Coded) (CoefficientMerge.scale (2739299270400 : Int) atom2400Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20400780708000 : Int) atom2401Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52121547324000 : Int) atom2402Coded) (CoefficientMerge.scale (12579780074400 : Int) atom2403Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5134857235200 : Int) atom2404Coded) (CoefficientMerge.scale (3083040576000 : Int) atom2405Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39376524972960 : Int) atom2406Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (174486042511200 : Int) atom2407Coded) (CoefficientMerge.scale (128607934240800 : Int) atom2408Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (96386479580160 : Int) atom2409Coded) (CoefficientMerge.scale (153439015262400 : Int) atom2410Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11300938387200 : Int) atom2411Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24664324608000 : Int) atom2412Coded) (CoefficientMerge.scale (27029092436640 : Int) atom2413Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (215567799804000 : Int) atom2414Coded) (CoefficientMerge.scale (197885015748000 : Int) atom2415Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (164800213079040 : Int) atom2416Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (363241134547200 : Int) atom2417Coded) (CoefficientMerge.scale (25008065913600 : Int) atom2418Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (71475157353600 : Int) atom2419Coded) (CoefficientMerge.scale (89689459860000 : Int) atom2420Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (351305386185600 : Int) atom2421Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (364301110958400 : Int) atom2422Coded) (CoefficientMerge.scale (361575865778400 : Int) atom2423Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (584217584596800 : Int) atom2424Coded) (CoefficientMerge.scale (89642062540800 : Int) atom2425Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (231081643069200 : Int) atom2426Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (545421771417600 : Int) atom2427Coded) (CoefficientMerge.scale (587648796134400 : Int) atom2428Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (482552368527600 : Int) atom2429Coded) (CoefficientMerge.scale (759227313121200 : Int) atom2430Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (95421168944640 : Int) atom2431Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (500895976719600 : Int) atom2432Coded) (CoefficientMerge.scale (624067545162600 : Int) atom2433Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (528698249503200 : Int) atom2434Coded) (CoefficientMerge.scale (709210793699100 : Int) atom2435Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (378597382732800 : Int) atom2436Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (759618673228800 : Int) atom2437Coded) (CoefficientMerge.scale (613004972605200 : Int) atom2438Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (656760067563600 : Int) atom2439Coded) (CoefficientMerge.scale (334775681856000 : Int) atom2440Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (573058747560600 : Int) atom2441Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (648004298772600 : Int) atom2442Coded) (CoefficientMerge.scale (188901029066400 : Int) atom2443Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (479009353479300 : Int) atom2444Coded) (CoefficientMerge.scale (253041385835700 : Int) atom2445Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4450918348800 : Int) atom2446Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24318972518400 : Int) atom2447Coded) (CoefficientMerge.scale (89482272768000 : Int) atom2448Coded)))))))) := by decide +kernel
theorem block032_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block032 := by
  rw [block032_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2369Coded_nonneg g hg hA hB) (atom2370Coded_nonneg g hg hA hB)) (add_nonneg (atom2371Coded_nonneg g hg hA hB) (add_nonneg (atom2372Coded_nonneg g hg hA hB) (atom2373Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2374Coded_nonneg g hg hA hB) (atom2375Coded_nonneg g hg hA hB)) (add_nonneg (atom2376Coded_nonneg g hg hA hB) (add_nonneg (atom2377Coded_nonneg g hg hA hB) (atom2378Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2379Coded_nonneg g hg hA hB) (atom2380Coded_nonneg g hg hA hB)) (add_nonneg (atom2381Coded_nonneg g hg hA hB) (add_nonneg (atom2382Coded_nonneg g hg hA hB) (atom2383Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2384Coded_nonneg g hg hA hB) (atom2385Coded_nonneg g hg hA hB)) (add_nonneg (atom2386Coded_nonneg g hg hA hB) (add_nonneg (atom2387Coded_nonneg g hg hA hB) (atom2388Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2389Coded_nonneg g hg hA hB) (atom2390Coded_nonneg g hg hA hB)) (add_nonneg (atom2391Coded_nonneg g hg hA hB) (add_nonneg (atom2392Coded_nonneg g hg hA hB) (atom2393Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2394Coded_nonneg g hg hA hB) (atom2395Coded_nonneg g hg hA hB)) (add_nonneg (atom2396Coded_nonneg g hg hA hB) (add_nonneg (atom2397Coded_nonneg g hg hA hB) (atom2398Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2399Coded_nonneg g hg hA hB) (atom2400Coded_nonneg g hg hA hB)) (add_nonneg (atom2401Coded_nonneg g hg hA hB) (add_nonneg (atom2402Coded_nonneg g hg hA hB) (atom2403Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2404Coded_nonneg g hg hA hB) (atom2405Coded_nonneg g hg hA hB)) (add_nonneg (atom2406Coded_nonneg g hg hA hB) (add_nonneg (atom2407Coded_nonneg g hg hA hB) (atom2408Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2409Coded_nonneg g hg hA hB) (atom2410Coded_nonneg g hg hA hB)) (add_nonneg (atom2411Coded_nonneg g hg hA hB) (add_nonneg (atom2412Coded_nonneg g hg hA hB) (atom2413Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2414Coded_nonneg g hg hA hB) (atom2415Coded_nonneg g hg hA hB)) (add_nonneg (atom2416Coded_nonneg g hg hA hB) (add_nonneg (atom2417Coded_nonneg g hg hA hB) (atom2418Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2419Coded_nonneg g hg hA hB) (atom2420Coded_nonneg g hg hA hB)) (add_nonneg (atom2421Coded_nonneg g hg hA hB) (add_nonneg (atom2422Coded_nonneg g hg hA hB) (atom2423Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2424Coded_nonneg g hg hA hB) (atom2425Coded_nonneg g hg hA hB)) (add_nonneg (atom2426Coded_nonneg g hg hA hB) (add_nonneg (atom2427Coded_nonneg g hg hA hB) (atom2428Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2429Coded_nonneg g hg hA hB) (atom2430Coded_nonneg g hg hA hB)) (add_nonneg (atom2431Coded_nonneg g hg hA hB) (add_nonneg (atom2432Coded_nonneg g hg hA hB) (atom2433Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2434Coded_nonneg g hg hA hB) (atom2435Coded_nonneg g hg hA hB)) (add_nonneg (atom2436Coded_nonneg g hg hA hB) (add_nonneg (atom2437Coded_nonneg g hg hA hB) (atom2438Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2439Coded_nonneg g hg hA hB) (atom2440Coded_nonneg g hg hA hB)) (add_nonneg (atom2441Coded_nonneg g hg hA hB) (add_nonneg (atom2442Coded_nonneg g hg hA hB) (atom2443Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2444Coded_nonneg g hg hA hB) (atom2445Coded_nonneg g hg hA hB)) (add_nonneg (atom2446Coded_nonneg g hg hA hB) (add_nonneg (atom2447Coded_nonneg g hg hA hB) (atom2448Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
