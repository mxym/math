import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom1249 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 20, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1249 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1249 = ((g 3) * (g 20) * (g 21)) := by
  norm_num [atom1249, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1249_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (519056458905600 : Int) atom1249) := by
  rw [SparsePolynomial.eval_scale, eval_atom1249]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1249Coded : CoefficientMerge.Poly := [(nat_lit 2229, Int.ofNat (nat_lit 1))]
theorem atom1249Coded_decode : atom1249 = SparsePolynomial.decodeCubic 24 atom1249Coded := by decide +kernel
theorem atom1249Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (519056458905600 : Int) atom1249Coded) := by
  have h := atom1249_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1249Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1250 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 20, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1250 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1250 = ((g 3) * (g 20) * (g 22)) := by
  norm_num [atom1250, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1250_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (358976744985600 : Int) atom1250) := by
  rw [SparsePolynomial.eval_scale, eval_atom1250]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1250Coded : CoefficientMerge.Poly := [(nat_lit 2230, Int.ofNat (nat_lit 1))]
theorem atom1250Coded_decode : atom1250 = SparsePolynomial.decodeCubic 24 atom1250Coded := by decide +kernel
theorem atom1250Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (358976744985600 : Int) atom1250Coded) := by
  have h := atom1250_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1250Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1251 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 20, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1251 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1251 = ((g 3) * (g 20) * (g 23)) := by
  norm_num [atom1251, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1251_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (415551344947200 : Int) atom1251) := by
  rw [SparsePolynomial.eval_scale, eval_atom1251]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1251Coded : CoefficientMerge.Poly := [(nat_lit 2231, Int.ofNat (nat_lit 1))]
theorem atom1251Coded_decode : atom1251 = SparsePolynomial.decodeCubic 24 atom1251Coded := by decide +kernel
theorem atom1251Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (415551344947200 : Int) atom1251Coded) := by
  have h := atom1251_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1251Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1252 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 21, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1252 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1252 = ((g 3) * (g 21) * (g 21)) := by
  norm_num [atom1252, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1252_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (149899559040000 : Int) atom1252) := by
  rw [SparsePolynomial.eval_scale, eval_atom1252]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1252Coded : CoefficientMerge.Poly := [(nat_lit 2253, Int.ofNat (nat_lit 1))]
theorem atom1252Coded_decode : atom1252 = SparsePolynomial.decodeCubic 24 atom1252Coded := by decide +kernel
theorem atom1252Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (149899559040000 : Int) atom1252Coded) := by
  have h := atom1252_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1252Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1253 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 21, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1253 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1253 = ((g 3) * (g 21) * (g 22)) := by
  norm_num [atom1253, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1253_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (193568557593600 : Int) atom1253) := by
  rw [SparsePolynomial.eval_scale, eval_atom1253]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1253Coded : CoefficientMerge.Poly := [(nat_lit 2254, Int.ofNat (nat_lit 1))]
theorem atom1253Coded_decode : atom1253 = SparsePolynomial.decodeCubic 24 atom1253Coded := by decide +kernel
theorem atom1253Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (193568557593600 : Int) atom1253Coded) := by
  have h := atom1253_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1253Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1254 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 21, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1254 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1254 = ((g 3) * (g 21) * (g 23)) := by
  norm_num [atom1254, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1254_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (256657812364800 : Int) atom1254) := by
  rw [SparsePolynomial.eval_scale, eval_atom1254]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1254Coded : CoefficientMerge.Poly := [(nat_lit 2255, Int.ofNat (nat_lit 1))]
theorem atom1254Coded_decode : atom1254 = SparsePolynomial.decodeCubic 24 atom1254Coded := by decide +kernel
theorem atom1254Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (256657812364800 : Int) atom1254Coded) := by
  have h := atom1254_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1254Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1255 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 22, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1255 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1255 = ((g 3) * (g 22) * (g 23)) := by
  norm_num [atom1255, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1255_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65611984132800 : Int) atom1255) := by
  rw [SparsePolynomial.eval_scale, eval_atom1255]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 22) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1255Coded : CoefficientMerge.Poly := [(nat_lit 2279, Int.ofNat (nat_lit 1))]
theorem atom1255Coded_decode : atom1255 = SparsePolynomial.decodeCubic 24 atom1255Coded := by decide +kernel
theorem atom1255Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (65611984132800 : Int) atom1255Coded) := by
  have h := atom1255_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1255Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1256 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 23, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1256 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1256 = ((g 3) * (g 23) * (g 23)) := by
  norm_num [atom1256, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1256_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (81519845299200 : Int) atom1256) := by
  rw [SparsePolynomial.eval_scale, eval_atom1256]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 23) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1256Coded : CoefficientMerge.Poly := [(nat_lit 2303, Int.ofNat (nat_lit 1))]
theorem atom1256Coded_decode : atom1256 = SparsePolynomial.decodeCubic 24 atom1256Coded := by decide +kernel
theorem atom1256Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (81519845299200 : Int) atom1256Coded) := by
  have h := atom1256_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1256Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1257 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 4, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom1257 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1257 = ((g 4) * (g 4) * (g 4)) := by
  norm_num [atom1257, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1257_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19145134310400 : Int) atom1257) := by
  rw [SparsePolynomial.eval_scale, eval_atom1257]
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 4) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1257Coded : CoefficientMerge.Poly := [(nat_lit 2404, Int.ofNat (nat_lit 1))]
theorem atom1257Coded_decode : atom1257 = SparsePolynomial.decodeCubic 24 atom1257Coded := by decide +kernel
theorem atom1257Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (19145134310400 : Int) atom1257Coded) := by
  have h := atom1257_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1257Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1258 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 4, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom1258 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1258 = ((g 4) * (g 4) * (g 5)) := by
  norm_num [atom1258, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1258_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33284636169696 : Int) atom1258) := by
  rw [SparsePolynomial.eval_scale, eval_atom1258]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 4) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1258Coded : CoefficientMerge.Poly := [(nat_lit 2405, Int.ofNat (nat_lit 1))]
theorem atom1258Coded_decode : atom1258 = SparsePolynomial.decodeCubic 24 atom1258Coded := by decide +kernel
theorem atom1258Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (33284636169696 : Int) atom1258Coded) := by
  have h := atom1258_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1258Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1259 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 4, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom1259 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1259 = ((g 4) * (g 4) * (g 6)) := by
  norm_num [atom1259, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1259_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12426232089600 : Int) atom1259) := by
  rw [SparsePolynomial.eval_scale, eval_atom1259]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 4) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1259Coded : CoefficientMerge.Poly := [(nat_lit 2406, Int.ofNat (nat_lit 1))]
theorem atom1259Coded_decode : atom1259 = SparsePolynomial.decodeCubic 24 atom1259Coded := by decide +kernel
theorem atom1259Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (12426232089600 : Int) atom1259Coded) := by
  have h := atom1259_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1259Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1260 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 4, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom1260 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1260 = ((g 4) * (g 4) * (g 7)) := by
  norm_num [atom1260, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1260_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7216956633600 : Int) atom1260) := by
  rw [SparsePolynomial.eval_scale, eval_atom1260]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1260Coded : CoefficientMerge.Poly := [(nat_lit 2407, Int.ofNat (nat_lit 1))]
theorem atom1260Coded_decode : atom1260 = SparsePolynomial.decodeCubic 24 atom1260Coded := by decide +kernel
theorem atom1260Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (7216956633600 : Int) atom1260Coded) := by
  have h := atom1260_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1260Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1261 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 4, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom1261 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1261 = ((g 4) * (g 4) * (g 8)) := by
  norm_num [atom1261, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1261_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2007681177600 : Int) atom1261) := by
  rw [SparsePolynomial.eval_scale, eval_atom1261]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1261Coded : CoefficientMerge.Poly := [(nat_lit 2408, Int.ofNat (nat_lit 1))]
theorem atom1261Coded_decode : atom1261 = SparsePolynomial.decodeCubic 24 atom1261Coded := by decide +kernel
theorem atom1261Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (2007681177600 : Int) atom1261Coded) := by
  have h := atom1261_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1261Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1262 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 4, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom1262 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1262 = ((g 4) * (g 4) * (g 9)) := by
  norm_num [atom1262, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1262_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2810186767728 : Int) atom1262) := by
  rw [SparsePolynomial.eval_scale, eval_atom1262]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1262Coded : CoefficientMerge.Poly := [(nat_lit 2409, Int.ofNat (nat_lit 1))]
theorem atom1262Coded_decode : atom1262 = SparsePolynomial.decodeCubic 24 atom1262Coded := by decide +kernel
theorem atom1262Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (2810186767728 : Int) atom1262Coded) := by
  have h := atom1262_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1262Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1263 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 4, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1263 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1263 = ((g 4) * (g 4) * (g 10)) := by
  norm_num [atom1263, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1263_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15244408345968 : Int) atom1263) := by
  rw [SparsePolynomial.eval_scale, eval_atom1263]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1263Coded : CoefficientMerge.Poly := [(nat_lit 2410, Int.ofNat (nat_lit 1))]
theorem atom1263Coded_decode : atom1263 = SparsePolynomial.decodeCubic 24 atom1263Coded := by decide +kernel
theorem atom1263Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (15244408345968 : Int) atom1263Coded) := by
  have h := atom1263_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1263Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1264 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 4, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1264 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1264 = ((g 4) * (g 4) * (g 11)) := by
  norm_num [atom1264, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1264_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26040202684704 : Int) atom1264) := by
  rw [SparsePolynomial.eval_scale, eval_atom1264]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1264Coded : CoefficientMerge.Poly := [(nat_lit 2411, Int.ofNat (nat_lit 1))]
theorem atom1264Coded_decode : atom1264 = SparsePolynomial.decodeCubic 24 atom1264Coded := by decide +kernel
theorem atom1264Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (26040202684704 : Int) atom1264Coded) := by
  have h := atom1264_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1264Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1265 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 4, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1265 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1265 = ((g 4) * (g 4) * (g 12)) := by
  norm_num [atom1265, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1265_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48752909452224 : Int) atom1265) := by
  rw [SparsePolynomial.eval_scale, eval_atom1265]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1265Coded : CoefficientMerge.Poly := [(nat_lit 2412, Int.ofNat (nat_lit 1))]
theorem atom1265Coded_decode : atom1265 = SparsePolynomial.decodeCubic 24 atom1265Coded := by decide +kernel
theorem atom1265Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (48752909452224 : Int) atom1265Coded) := by
  have h := atom1265_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1265Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1266 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 4, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1266 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1266 = ((g 4) * (g 4) * (g 13)) := by
  norm_num [atom1266, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1266_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34882503465600 : Int) atom1266) := by
  rw [SparsePolynomial.eval_scale, eval_atom1266]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 4) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1266Coded : CoefficientMerge.Poly := [(nat_lit 2413, Int.ofNat (nat_lit 1))]
theorem atom1266Coded_decode : atom1266 = SparsePolynomial.decodeCubic 24 atom1266Coded := by decide +kernel
theorem atom1266Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (34882503465600 : Int) atom1266Coded) := by
  have h := atom1266_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1266Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1267 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 4, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1267 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1267 = ((g 4) * (g 4) * (g 14)) := by
  norm_num [atom1267, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1267_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17337834662400 : Int) atom1267) := by
  rw [SparsePolynomial.eval_scale, eval_atom1267]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1267Coded : CoefficientMerge.Poly := [(nat_lit 2414, Int.ofNat (nat_lit 1))]
theorem atom1267Coded_decode : atom1267 = SparsePolynomial.decodeCubic 24 atom1267Coded := by decide +kernel
theorem atom1267Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (17337834662400 : Int) atom1267Coded) := by
  have h := atom1267_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1267Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1268 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 4, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1268 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1268 = ((g 4) * (g 4) * (g 15)) := by
  norm_num [atom1268, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1268_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14580172454400 : Int) atom1268) := by
  rw [SparsePolynomial.eval_scale, eval_atom1268]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 4) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1268Coded : CoefficientMerge.Poly := [(nat_lit 2415, Int.ofNat (nat_lit 1))]
theorem atom1268Coded_decode : atom1268 = SparsePolynomial.decodeCubic 24 atom1268Coded := by decide +kernel
theorem atom1268Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (14580172454400 : Int) atom1268Coded) := by
  have h := atom1268_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1268Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1269 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 4, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1269 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1269 = ((g 4) * (g 4) * (g 18)) := by
  norm_num [atom1269, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1269_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18173912097600 : Int) atom1269) := by
  rw [SparsePolynomial.eval_scale, eval_atom1269]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 4) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1269Coded : CoefficientMerge.Poly := [(nat_lit 2418, Int.ofNat (nat_lit 1))]
theorem atom1269Coded_decode : atom1269 = SparsePolynomial.decodeCubic 24 atom1269Coded := by decide +kernel
theorem atom1269Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (18173912097600 : Int) atom1269Coded) := by
  have h := atom1269_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1269Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1270 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom1270 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1270 = ((g 4) * (g 5) * (g 5)) := by
  norm_num [atom1270, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1270_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37193995228896 : Int) atom1270) := by
  rw [SparsePolynomial.eval_scale, eval_atom1270]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 4) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1270Coded : CoefficientMerge.Poly := [(nat_lit 2429, Int.ofNat (nat_lit 1))]
theorem atom1270Coded_decode : atom1270 = SparsePolynomial.decodeCubic 24 atom1270Coded := by decide +kernel
theorem atom1270Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (37193995228896 : Int) atom1270Coded) := by
  have h := atom1270_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1270Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1271 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom1271 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1271 = ((g 4) * (g 5) * (g 6)) := by
  norm_num [atom1271, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1271_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29044448275392 : Int) atom1271) := by
  rw [SparsePolynomial.eval_scale, eval_atom1271]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 4) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1271Coded : CoefficientMerge.Poly := [(nat_lit 2430, Int.ofNat (nat_lit 1))]
theorem atom1271Coded_decode : atom1271 = SparsePolynomial.decodeCubic 24 atom1271Coded := by decide +kernel
theorem atom1271Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (29044448275392 : Int) atom1271Coded) := by
  have h := atom1271_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1271Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1272 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom1272 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1272 = ((g 4) * (g 5) * (g 7)) := by
  norm_num [atom1272, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1272_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2242076371392 : Int) atom1272) := by
  rw [SparsePolynomial.eval_scale, eval_atom1272]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1272Coded : CoefficientMerge.Poly := [(nat_lit 2431, Int.ofNat (nat_lit 1))]
theorem atom1272Coded_decode : atom1272 = SparsePolynomial.decodeCubic 24 atom1272Coded := by decide +kernel
theorem atom1272Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (2242076371392 : Int) atom1272Coded) := by
  have h := atom1272_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1272Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1273 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom1273 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1273 = ((g 4) * (g 5) * (g 9)) := by
  norm_num [atom1273, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1273_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3077576911728 : Int) atom1273) := by
  rw [SparsePolynomial.eval_scale, eval_atom1273]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1273Coded : CoefficientMerge.Poly := [(nat_lit 2433, Int.ofNat (nat_lit 1))]
theorem atom1273Coded_decode : atom1273 = SparsePolynomial.decodeCubic 24 atom1273Coded := by decide +kernel
theorem atom1273Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3077576911728 : Int) atom1273Coded) := by
  have h := atom1273_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1273Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1274 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1274 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1274 = ((g 4) * (g 5) * (g 10)) := by
  norm_num [atom1274, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1274_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12869199875664 : Int) atom1274) := by
  rw [SparsePolynomial.eval_scale, eval_atom1274]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1274Coded : CoefficientMerge.Poly := [(nat_lit 2434, Int.ofNat (nat_lit 1))]
theorem atom1274Coded_decode : atom1274 = SparsePolynomial.decodeCubic 24 atom1274Coded := by decide +kernel
theorem atom1274Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (12869199875664 : Int) atom1274Coded) := by
  have h := atom1274_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1274Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1275 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1275 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1275 = ((g 4) * (g 5) * (g 11)) := by
  norm_num [atom1275, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1275_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29390633404704 : Int) atom1275) := by
  rw [SparsePolynomial.eval_scale, eval_atom1275]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1275Coded : CoefficientMerge.Poly := [(nat_lit 2435, Int.ofNat (nat_lit 1))]
theorem atom1275Coded_decode : atom1275 = SparsePolynomial.decodeCubic 24 atom1275Coded := by decide +kernel
theorem atom1275Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (29390633404704 : Int) atom1275Coded) := by
  have h := atom1275_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1275Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1276 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1276 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1276 = ((g 4) * (g 5) * (g 12)) := by
  norm_num [atom1276, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1276_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (79919010651744 : Int) atom1276) := by
  rw [SparsePolynomial.eval_scale, eval_atom1276]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1276Coded : CoefficientMerge.Poly := [(nat_lit 2436, Int.ofNat (nat_lit 1))]
theorem atom1276Coded_decode : atom1276 = SparsePolynomial.decodeCubic 24 atom1276Coded := by decide +kernel
theorem atom1276Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (79919010651744 : Int) atom1276Coded) := by
  have h := atom1276_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1276Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1277 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1277 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1277 = ((g 4) * (g 5) * (g 13)) := by
  norm_num [atom1277, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1277_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (57281162390496 : Int) atom1277) := by
  rw [SparsePolynomial.eval_scale, eval_atom1277]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1277Coded : CoefficientMerge.Poly := [(nat_lit 2437, Int.ofNat (nat_lit 1))]
theorem atom1277Coded_decode : atom1277 = SparsePolynomial.decodeCubic 24 atom1277Coded := by decide +kernel
theorem atom1277Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (57281162390496 : Int) atom1277Coded) := by
  have h := atom1277_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1277Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1278 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1278 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1278 = ((g 4) * (g 5) * (g 14)) := by
  norm_num [atom1278, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1278_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27294788496096 : Int) atom1278) := by
  rw [SparsePolynomial.eval_scale, eval_atom1278]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1278Coded : CoefficientMerge.Poly := [(nat_lit 2438, Int.ofNat (nat_lit 1))]
theorem atom1278Coded_decode : atom1278 = SparsePolynomial.decodeCubic 24 atom1278Coded := by decide +kernel
theorem atom1278Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (27294788496096 : Int) atom1278Coded) := by
  have h := atom1278_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1278Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1279 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1279 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1279 = ((g 4) * (g 5) * (g 15)) := by
  norm_num [atom1279, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1279_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27620166864096 : Int) atom1279) := by
  rw [SparsePolynomial.eval_scale, eval_atom1279]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 5) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1279Coded : CoefficientMerge.Poly := [(nat_lit 2439, Int.ofNat (nat_lit 1))]
theorem atom1279Coded_decode : atom1279 = SparsePolynomial.decodeCubic 24 atom1279Coded := by decide +kernel
theorem atom1279Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (27620166864096 : Int) atom1279Coded) := by
  have h := atom1279_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1279Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1280 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1280 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1280 = ((g 4) * (g 5) * (g 16)) := by
  norm_num [atom1280, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1280_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16123034985696 : Int) atom1280) := by
  rw [SparsePolynomial.eval_scale, eval_atom1280]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 5) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1280Coded : CoefficientMerge.Poly := [(nat_lit 2440, Int.ofNat (nat_lit 1))]
theorem atom1280Coded_decode : atom1280 = SparsePolynomial.decodeCubic 24 atom1280Coded := by decide +kernel
theorem atom1280Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (16123034985696 : Int) atom1280Coded) := by
  have h := atom1280_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1280Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1281 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1281 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1281 = ((g 4) * (g 5) * (g 17)) := by
  norm_num [atom1281, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1281_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19206075561696 : Int) atom1281) := by
  rw [SparsePolynomial.eval_scale, eval_atom1281]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 5) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1281Coded : CoefficientMerge.Poly := [(nat_lit 2441, Int.ofNat (nat_lit 1))]
theorem atom1281Coded_decode : atom1281 = SparsePolynomial.decodeCubic 24 atom1281Coded := by decide +kernel
theorem atom1281Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (19206075561696 : Int) atom1281Coded) := by
  have h := atom1281_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1281Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1282 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1282 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1282 = ((g 4) * (g 5) * (g 18)) := by
  norm_num [atom1282, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1282_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49319508264048 : Int) atom1282) := by
  rw [SparsePolynomial.eval_scale, eval_atom1282]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 5) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1282Coded : CoefficientMerge.Poly := [(nat_lit 2442, Int.ofNat (nat_lit 1))]
theorem atom1282Coded_decode : atom1282 = SparsePolynomial.decodeCubic 24 atom1282Coded := by decide +kernel
theorem atom1282Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (49319508264048 : Int) atom1282Coded) := by
  have h := atom1282_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1282Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1283 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1283 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1283 = ((g 4) * (g 5) * (g 19)) := by
  norm_num [atom1283, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1283_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36196508174400 : Int) atom1283) := by
  rw [SparsePolynomial.eval_scale, eval_atom1283]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 5) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1283Coded : CoefficientMerge.Poly := [(nat_lit 2443, Int.ofNat (nat_lit 1))]
theorem atom1283Coded_decode : atom1283 = SparsePolynomial.decodeCubic 24 atom1283Coded := by decide +kernel
theorem atom1283Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (36196508174400 : Int) atom1283Coded) := by
  have h := atom1283_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1283Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1284 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1284 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1284 = ((g 4) * (g 5) * (g 20)) := by
  norm_num [atom1284, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1284_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47956822204752 : Int) atom1284) := by
  rw [SparsePolynomial.eval_scale, eval_atom1284]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 5) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1284Coded : CoefficientMerge.Poly := [(nat_lit 2444, Int.ofNat (nat_lit 1))]
theorem atom1284Coded_decode : atom1284 = SparsePolynomial.decodeCubic 24 atom1284Coded := by decide +kernel
theorem atom1284Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (47956822204752 : Int) atom1284Coded) := by
  have h := atom1284_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1284Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1285 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1285 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1285 = ((g 4) * (g 5) * (g 21)) := by
  norm_num [atom1285, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1285_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (74969085851928 : Int) atom1285) := by
  rw [SparsePolynomial.eval_scale, eval_atom1285]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 4) * (g 5) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1285Coded : CoefficientMerge.Poly := [(nat_lit 2445, Int.ofNat (nat_lit 1))]
theorem atom1285Coded_decode : atom1285 = SparsePolynomial.decodeCubic 24 atom1285Coded := by decide +kernel
theorem atom1285Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (74969085851928 : Int) atom1285Coded) := by
  have h := atom1285_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1285Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1286 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1286 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1286 = ((g 4) * (g 5) * (g 22)) := by
  norm_num [atom1286, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1286_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (101981349499104 : Int) atom1286) := by
  rw [SparsePolynomial.eval_scale, eval_atom1286]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 4) * (g 5) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1286Coded : CoefficientMerge.Poly := [(nat_lit 2446, Int.ofNat (nat_lit 1))]
theorem atom1286Coded_decode : atom1286 = SparsePolynomial.decodeCubic 24 atom1286Coded := by decide +kernel
theorem atom1286Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (101981349499104 : Int) atom1286Coded) := by
  have h := atom1286_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1286Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1287 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1287 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1287 = ((g 4) * (g 5) * (g 23)) := by
  norm_num [atom1287, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1287_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (130089392506692 : Int) atom1287) := by
  rw [SparsePolynomial.eval_scale, eval_atom1287]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 4) * (g 5) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1287Coded : CoefficientMerge.Poly := [(nat_lit 2447, Int.ofNat (nat_lit 1))]
theorem atom1287Coded_decode : atom1287 = SparsePolynomial.decodeCubic 24 atom1287Coded := by decide +kernel
theorem atom1287Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (130089392506692 : Int) atom1287Coded) := by
  have h := atom1287_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1287Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1288 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom1288 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1288 = ((g 4) * (g 6) * (g 6)) := by
  norm_num [atom1288, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1288_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25323457420800 : Int) atom1288) := by
  rw [SparsePolynomial.eval_scale, eval_atom1288]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 4) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1288Coded : CoefficientMerge.Poly := [(nat_lit 2454, Int.ofNat (nat_lit 1))]
theorem atom1288Coded_decode : atom1288 = SparsePolynomial.decodeCubic 24 atom1288Coded := by decide +kernel
theorem atom1288Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (25323457420800 : Int) atom1288Coded) := by
  have h := atom1288_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1288Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1289 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom1289 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1289 = ((g 4) * (g 6) * (g 7)) := by
  norm_num [atom1289, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1289_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22823950195200 : Int) atom1289) := by
  rw [SparsePolynomial.eval_scale, eval_atom1289]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1289Coded : CoefficientMerge.Poly := [(nat_lit 2455, Int.ofNat (nat_lit 1))]
theorem atom1289Coded_decode : atom1289 = SparsePolynomial.decodeCubic 24 atom1289Coded := by decide +kernel
theorem atom1289Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (22823950195200 : Int) atom1289Coded) := by
  have h := atom1289_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1289Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1290 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom1290 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1290 = ((g 4) * (g 6) * (g 8)) := by
  norm_num [atom1290, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1290_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (850493952000 : Int) atom1290) := by
  rw [SparsePolynomial.eval_scale, eval_atom1290]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1290Coded : CoefficientMerge.Poly := [(nat_lit 2456, Int.ofNat (nat_lit 1))]
theorem atom1290Coded_decode : atom1290 = SparsePolynomial.decodeCubic 24 atom1290Coded := by decide +kernel
theorem atom1290Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (850493952000 : Int) atom1290Coded) := by
  have h := atom1290_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1290Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1291 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom1291 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1291 = ((g 4) * (g 6) * (g 9)) := by
  norm_num [atom1291, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1291_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4523416630128 : Int) atom1291) := by
  rw [SparsePolynomial.eval_scale, eval_atom1291]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1291Coded : CoefficientMerge.Poly := [(nat_lit 2457, Int.ofNat (nat_lit 1))]
theorem atom1291Coded_decode : atom1291 = SparsePolynomial.decodeCubic 24 atom1291Coded := by decide +kernel
theorem atom1291Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (4523416630128 : Int) atom1291Coded) := by
  have h := atom1291_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1291Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1292 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1292 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1292 = ((g 4) * (g 6) * (g 10)) := by
  norm_num [atom1292, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1292_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24745725232272 : Int) atom1292) := by
  rw [SparsePolynomial.eval_scale, eval_atom1292]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1292Coded : CoefficientMerge.Poly := [(nat_lit 2458, Int.ofNat (nat_lit 1))]
theorem atom1292Coded_decode : atom1292 = SparsePolynomial.decodeCubic 24 atom1292Coded := by decide +kernel
theorem atom1292Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (24745725232272 : Int) atom1292Coded) := by
  have h := atom1292_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1292Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1293 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1293 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1293 = ((g 4) * (g 6) * (g 11)) := by
  norm_num [atom1293, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1293_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34961368790304 : Int) atom1293) := by
  rw [SparsePolynomial.eval_scale, eval_atom1293]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1293Coded : CoefficientMerge.Poly := [(nat_lit 2459, Int.ofNat (nat_lit 1))]
theorem atom1293Coded_decode : atom1293 = SparsePolynomial.decodeCubic 24 atom1293Coded := by decide +kernel
theorem atom1293Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (34961368790304 : Int) atom1293Coded) := by
  have h := atom1293_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1293Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1294 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1294 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1294 = ((g 4) * (g 6) * (g 12)) := by
  norm_num [atom1294, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1294_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (60757116133824 : Int) atom1294) := by
  rw [SparsePolynomial.eval_scale, eval_atom1294]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1294Coded : CoefficientMerge.Poly := [(nat_lit 2460, Int.ofNat (nat_lit 1))]
theorem atom1294Coded_decode : atom1294 = SparsePolynomial.decodeCubic 24 atom1294Coded := by decide +kernel
theorem atom1294Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (60757116133824 : Int) atom1294Coded) := by
  have h := atom1294_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1294Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1295 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1295 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1295 = ((g 4) * (g 6) * (g 13)) := by
  norm_num [atom1295, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1295_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52032198556800 : Int) atom1295) := by
  rw [SparsePolynomial.eval_scale, eval_atom1295]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1295Coded : CoefficientMerge.Poly := [(nat_lit 2461, Int.ofNat (nat_lit 1))]
theorem atom1295Coded_decode : atom1295 = SparsePolynomial.decodeCubic 24 atom1295Coded := by decide +kernel
theorem atom1295Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (52032198556800 : Int) atom1295Coded) := by
  have h := atom1295_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1295Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1296 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1296 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1296 = ((g 4) * (g 6) * (g 14)) := by
  norm_num [atom1296, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1296_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39633018163200 : Int) atom1296) := by
  rw [SparsePolynomial.eval_scale, eval_atom1296]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1296Coded : CoefficientMerge.Poly := [(nat_lit 2462, Int.ofNat (nat_lit 1))]
theorem atom1296Coded_decode : atom1296 = SparsePolynomial.decodeCubic 24 atom1296Coded := by decide +kernel
theorem atom1296Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (39633018163200 : Int) atom1296Coded) := by
  have h := atom1296_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1296Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1297 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1297 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1297 = ((g 4) * (g 6) * (g 15)) := by
  norm_num [atom1297, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1297_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42020844364800 : Int) atom1297) := by
  rw [SparsePolynomial.eval_scale, eval_atom1297]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1297Coded : CoefficientMerge.Poly := [(nat_lit 2463, Int.ofNat (nat_lit 1))]
theorem atom1297Coded_decode : atom1297 = SparsePolynomial.decodeCubic 24 atom1297Coded := by decide +kernel
theorem atom1297Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (42020844364800 : Int) atom1297Coded) := by
  have h := atom1297_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1297Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1298 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1298 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1298 = ((g 4) * (g 6) * (g 16)) := by
  norm_num [atom1298, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1298_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32586160320000 : Int) atom1298) := by
  rw [SparsePolynomial.eval_scale, eval_atom1298]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 6) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1298Coded : CoefficientMerge.Poly := [(nat_lit 2464, Int.ofNat (nat_lit 1))]
theorem atom1298Coded_decode : atom1298 = SparsePolynomial.decodeCubic 24 atom1298Coded := by decide +kernel
theorem atom1298Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (32586160320000 : Int) atom1298Coded) := by
  have h := atom1298_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1298Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1299 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1299 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1299 = ((g 4) * (g 6) * (g 17)) := by
  norm_num [atom1299, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1299_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37731648729600 : Int) atom1299) := by
  rw [SparsePolynomial.eval_scale, eval_atom1299]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1299Coded : CoefficientMerge.Poly := [(nat_lit 2465, Int.ofNat (nat_lit 1))]
theorem atom1299Coded_decode : atom1299 = SparsePolynomial.decodeCubic 24 atom1299Coded := by decide +kernel
theorem atom1299Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (37731648729600 : Int) atom1299Coded) := by
  have h := atom1299_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1299Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1300 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1300 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1300 = ((g 4) * (g 6) * (g 18)) := by
  norm_num [atom1300, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1300_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (71505279014400 : Int) atom1300) := by
  rw [SparsePolynomial.eval_scale, eval_atom1300]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 6) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1300Coded : CoefficientMerge.Poly := [(nat_lit 2466, Int.ofNat (nat_lit 1))]
theorem atom1300Coded_decode : atom1300 = SparsePolynomial.decodeCubic 24 atom1300Coded := by decide +kernel
theorem atom1300Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (71505279014400 : Int) atom1300Coded) := by
  have h := atom1300_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1300Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1301 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1301 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1301 = ((g 4) * (g 6) * (g 19)) := by
  norm_num [atom1301, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1301_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (79385314881600 : Int) atom1301) := by
  rw [SparsePolynomial.eval_scale, eval_atom1301]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 6) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1301Coded : CoefficientMerge.Poly := [(nat_lit 2467, Int.ofNat (nat_lit 1))]
theorem atom1301Coded_decode : atom1301 = SparsePolynomial.decodeCubic 24 atom1301Coded := by decide +kernel
theorem atom1301Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (79385314881600 : Int) atom1301Coded) := by
  have h := atom1301_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1301Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1302 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1302 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1302 = ((g 4) * (g 6) * (g 20)) := by
  norm_num [atom1302, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1302_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (105439262846400 : Int) atom1302) := by
  rw [SparsePolynomial.eval_scale, eval_atom1302]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 6) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1302Coded : CoefficientMerge.Poly := [(nat_lit 2468, Int.ofNat (nat_lit 1))]
theorem atom1302Coded_decode : atom1302 = SparsePolynomial.decodeCubic 24 atom1302Coded := by decide +kernel
theorem atom1302Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (105439262846400 : Int) atom1302Coded) := by
  have h := atom1302_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1302Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1303 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1303 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1303 = ((g 4) * (g 6) * (g 21)) := by
  norm_num [atom1303, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1303_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (152401670366400 : Int) atom1303) := by
  rw [SparsePolynomial.eval_scale, eval_atom1303]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 4) * (g 6) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1303Coded : CoefficientMerge.Poly := [(nat_lit 2469, Int.ofNat (nat_lit 1))]
theorem atom1303Coded_decode : atom1303 = SparsePolynomial.decodeCubic 24 atom1303Coded := by decide +kernel
theorem atom1303Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (152401670366400 : Int) atom1303Coded) := by
  have h := atom1303_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1303Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1304 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1304 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1304 = ((g 4) * (g 6) * (g 22)) := by
  norm_num [atom1304, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1304_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (199364077886400 : Int) atom1304) := by
  rw [SparsePolynomial.eval_scale, eval_atom1304]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 4) * (g 6) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1304Coded : CoefficientMerge.Poly := [(nat_lit 2470, Int.ofNat (nat_lit 1))]
theorem atom1304Coded_decode : atom1304 = SparsePolynomial.decodeCubic 24 atom1304Coded := by decide +kernel
theorem atom1304Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (199364077886400 : Int) atom1304Coded) := by
  have h := atom1304_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1304Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1305 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1305 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1305 = ((g 4) * (g 6) * (g 23)) := by
  norm_num [atom1305, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1305_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (246326485406400 : Int) atom1305) := by
  rw [SparsePolynomial.eval_scale, eval_atom1305]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 4) * (g 6) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1305Coded : CoefficientMerge.Poly := [(nat_lit 2471, Int.ofNat (nat_lit 1))]
theorem atom1305Coded_decode : atom1305 = SparsePolynomial.decodeCubic 24 atom1305Coded := by decide +kernel
theorem atom1305Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (246326485406400 : Int) atom1305Coded) := by
  have h := atom1305_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1305Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1306 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom1306 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1306 = ((g 4) * (g 7) * (g 7)) := by
  norm_num [atom1306, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1306_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28330898534400 : Int) atom1306) := by
  rw [SparsePolynomial.eval_scale, eval_atom1306]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1306Coded : CoefficientMerge.Poly := [(nat_lit 2479, Int.ofNat (nat_lit 1))]
theorem atom1306Coded_decode : atom1306 = SparsePolynomial.decodeCubic 24 atom1306Coded := by decide +kernel
theorem atom1306Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (28330898534400 : Int) atom1306Coded) := by
  have h := atom1306_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1306Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1307 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom1307 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1307 = ((g 4) * (g 7) * (g 8)) := by
  norm_num [atom1307, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1307_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41917539417600 : Int) atom1307) := by
  rw [SparsePolynomial.eval_scale, eval_atom1307]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1307Coded : CoefficientMerge.Poly := [(nat_lit 2480, Int.ofNat (nat_lit 1))]
theorem atom1307Coded_decode : atom1307 = SparsePolynomial.decodeCubic 24 atom1307Coded := by decide +kernel
theorem atom1307Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (41917539417600 : Int) atom1307Coded) := by
  have h := atom1307_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1307Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1308 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom1308 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1308 = ((g 4) * (g 7) * (g 9)) := by
  norm_num [atom1308, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1308_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30177621698928 : Int) atom1308) := by
  rw [SparsePolynomial.eval_scale, eval_atom1308]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1308Coded : CoefficientMerge.Poly := [(nat_lit 2481, Int.ofNat (nat_lit 1))]
theorem atom1308Coded_decode : atom1308 = SparsePolynomial.decodeCubic 24 atom1308Coded := by decide +kernel
theorem atom1308Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (30177621698928 : Int) atom1308Coded) := by
  have h := atom1308_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1308Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1309 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1309 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1309 = ((g 4) * (g 7) * (g 10)) := by
  norm_num [atom1309, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1309_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49379337558672 : Int) atom1309) := by
  rw [SparsePolynomial.eval_scale, eval_atom1309]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1309Coded : CoefficientMerge.Poly := [(nat_lit 2482, Int.ofNat (nat_lit 1))]
theorem atom1309Coded_decode : atom1309 = SparsePolynomial.decodeCubic 24 atom1309Coded := by decide +kernel
theorem atom1309Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (49379337558672 : Int) atom1309Coded) := by
  have h := atom1309_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1309Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1310 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1310 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1310 = ((g 4) * (g 7) * (g 11)) := by
  norm_num [atom1310, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1310_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (62699284041504 : Int) atom1310) := by
  rw [SparsePolynomial.eval_scale, eval_atom1310]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1310Coded : CoefficientMerge.Poly := [(nat_lit 2483, Int.ofNat (nat_lit 1))]
theorem atom1310Coded_decode : atom1310 = SparsePolynomial.decodeCubic 24 atom1310Coded := by decide +kernel
theorem atom1310Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (62699284041504 : Int) atom1310Coded) := by
  have h := atom1310_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1310Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1311 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1311 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1311 = ((g 4) * (g 7) * (g 12)) := by
  norm_num [atom1311, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1311_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (91599334309824 : Int) atom1311) := by
  rw [SparsePolynomial.eval_scale, eval_atom1311]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1311Coded : CoefficientMerge.Poly := [(nat_lit 2484, Int.ofNat (nat_lit 1))]
theorem atom1311Coded_decode : atom1311 = SparsePolynomial.decodeCubic 24 atom1311Coded := by decide +kernel
theorem atom1311Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (91599334309824 : Int) atom1311Coded) := by
  have h := atom1311_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1311Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1312 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1312 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1312 = ((g 4) * (g 7) * (g 13)) := by
  norm_num [atom1312, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1312_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (83916271824000 : Int) atom1312) := by
  rw [SparsePolynomial.eval_scale, eval_atom1312]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1312Coded : CoefficientMerge.Poly := [(nat_lit 2485, Int.ofNat (nat_lit 1))]
theorem atom1312Coded_decode : atom1312 = SparsePolynomial.decodeCubic 24 atom1312Coded := by decide +kernel
theorem atom1312Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (83916271824000 : Int) atom1312Coded) := by
  have h := atom1312_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1312Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1313 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1313 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1313 = ((g 4) * (g 7) * (g 14)) := by
  norm_num [atom1313, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1313_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (72558946521600 : Int) atom1313) := by
  rw [SparsePolynomial.eval_scale, eval_atom1313]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1313Coded : CoefficientMerge.Poly := [(nat_lit 2486, Int.ofNat (nat_lit 1))]
theorem atom1313Coded_decode : atom1313 = SparsePolynomial.decodeCubic 24 atom1313Coded := by decide +kernel
theorem atom1313Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (72558946521600 : Int) atom1313Coded) := by
  have h := atom1313_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1313Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1314 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1314 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1314 = ((g 4) * (g 7) * (g 15)) := by
  norm_num [atom1314, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1314_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (75988627814400 : Int) atom1314) := by
  rw [SparsePolynomial.eval_scale, eval_atom1314]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1314Coded : CoefficientMerge.Poly := [(nat_lit 2487, Int.ofNat (nat_lit 1))]
theorem atom1314Coded_decode : atom1314 = SparsePolynomial.decodeCubic 24 atom1314Coded := by decide +kernel
theorem atom1314Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (75988627814400 : Int) atom1314Coded) := by
  have h := atom1314_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1314Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1315 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1315 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1315 = ((g 4) * (g 7) * (g 16)) := by
  norm_num [atom1315, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1315_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (67595798860800 : Int) atom1315) := by
  rw [SparsePolynomial.eval_scale, eval_atom1315]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1315Coded : CoefficientMerge.Poly := [(nat_lit 2488, Int.ofNat (nat_lit 1))]
theorem atom1315Coded_decode : atom1315 = SparsePolynomial.decodeCubic 24 atom1315Coded := by decide +kernel
theorem atom1315Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (67595798860800 : Int) atom1315Coded) := by
  have h := atom1315_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1315Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1316 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1316 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1316 = ((g 4) * (g 7) * (g 17)) := by
  norm_num [atom1316, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1316_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (73783142361600 : Int) atom1316) := by
  rw [SparsePolynomial.eval_scale, eval_atom1316]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1316Coded : CoefficientMerge.Poly := [(nat_lit 2489, Int.ofNat (nat_lit 1))]
theorem atom1316Coded_decode : atom1316 = SparsePolynomial.decodeCubic 24 atom1316Coded := by decide +kernel
theorem atom1316Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (73783142361600 : Int) atom1316Coded) := by
  have h := atom1316_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1316Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1317 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1317 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1317 = ((g 4) * (g 7) * (g 18)) := by
  norm_num [atom1317, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1317_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (110928036172800 : Int) atom1317) := by
  rw [SparsePolynomial.eval_scale, eval_atom1317]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 7) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1317Coded : CoefficientMerge.Poly := [(nat_lit 2490, Int.ofNat (nat_lit 1))]
theorem atom1317Coded_decode : atom1317 = SparsePolynomial.decodeCubic 24 atom1317Coded := by decide +kernel
theorem atom1317Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (110928036172800 : Int) atom1317Coded) := by
  have h := atom1317_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1317Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1318 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1318 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1318 = ((g 4) * (g 7) * (g 19)) := by
  norm_num [atom1318, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1318_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (124508744001600 : Int) atom1318) := by
  rw [SparsePolynomial.eval_scale, eval_atom1318]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 7) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1318Coded : CoefficientMerge.Poly := [(nat_lit 2491, Int.ofNat (nat_lit 1))]
theorem atom1318Coded_decode : atom1318 = SparsePolynomial.decodeCubic 24 atom1318Coded := by decide +kernel
theorem atom1318Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (124508744001600 : Int) atom1318Coded) := by
  have h := atom1318_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1318Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1319 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1319 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1319 = ((g 4) * (g 7) * (g 20)) := by
  norm_num [atom1319, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1319_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (156263363928000 : Int) atom1319) := by
  rw [SparsePolynomial.eval_scale, eval_atom1319]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 7) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1319Coded : CoefficientMerge.Poly := [(nat_lit 2492, Int.ofNat (nat_lit 1))]
theorem atom1319Coded_decode : atom1319 = SparsePolynomial.decodeCubic 24 atom1319Coded := by decide +kernel
theorem atom1319Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (156263363928000 : Int) atom1319Coded) := by
  have h := atom1319_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1319Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1320 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1320 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1320 = ((g 4) * (g 7) * (g 21)) := by
  norm_num [atom1320, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1320_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (213585260280000 : Int) atom1320) := by
  rw [SparsePolynomial.eval_scale, eval_atom1320]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 4) * (g 7) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1320Coded : CoefficientMerge.Poly := [(nat_lit 2493, Int.ofNat (nat_lit 1))]
theorem atom1320Coded_decode : atom1320 = SparsePolynomial.decodeCubic 24 atom1320Coded := by decide +kernel
theorem atom1320Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (213585260280000 : Int) atom1320Coded) := by
  have h := atom1320_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1320Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1321 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1321 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1321 = ((g 4) * (g 7) * (g 22)) := by
  norm_num [atom1321, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1321_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (270907156632000 : Int) atom1321) := by
  rw [SparsePolynomial.eval_scale, eval_atom1321]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 4) * (g 7) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1321Coded : CoefficientMerge.Poly := [(nat_lit 2494, Int.ofNat (nat_lit 1))]
theorem atom1321Coded_decode : atom1321 = SparsePolynomial.decodeCubic 24 atom1321Coded := by decide +kernel
theorem atom1321Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (270907156632000 : Int) atom1321Coded) := by
  have h := atom1321_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1321Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1322 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1322 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1322 = ((g 4) * (g 7) * (g 23)) := by
  norm_num [atom1322, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1322_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (328229052984000 : Int) atom1322) := by
  rw [SparsePolynomial.eval_scale, eval_atom1322]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 4) * (g 7) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1322Coded : CoefficientMerge.Poly := [(nat_lit 2495, Int.ofNat (nat_lit 1))]
theorem atom1322Coded_decode : atom1322 = SparsePolynomial.decodeCubic 24 atom1322Coded := by decide +kernel
theorem atom1322Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (328229052984000 : Int) atom1322Coded) := by
  have h := atom1322_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1322Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1323 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom1323 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1323 = ((g 4) * (g 8) * (g 8)) := by
  norm_num [atom1323, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1323_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (45437639385600 : Int) atom1323) := by
  rw [SparsePolynomial.eval_scale, eval_atom1323]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1323Coded : CoefficientMerge.Poly := [(nat_lit 2504, Int.ofNat (nat_lit 1))]
theorem atom1323Coded_decode : atom1323 = SparsePolynomial.decodeCubic 24 atom1323Coded := by decide +kernel
theorem atom1323Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (45437639385600 : Int) atom1323Coded) := by
  have h := atom1323_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1323Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1324 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom1324 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1324 = ((g 4) * (g 8) * (g 9)) := by
  norm_num [atom1324, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1324_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (80170645487328 : Int) atom1324) := by
  rw [SparsePolynomial.eval_scale, eval_atom1324]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1324Coded : CoefficientMerge.Poly := [(nat_lit 2505, Int.ofNat (nat_lit 1))]
theorem atom1324Coded_decode : atom1324 = SparsePolynomial.decodeCubic 24 atom1324Coded := by decide +kernel
theorem atom1324Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (80170645487328 : Int) atom1324Coded) := by
  have h := atom1324_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1324Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1325 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1325 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1325 = ((g 4) * (g 8) * (g 10)) := by
  norm_num [atom1325, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1325_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (71128035587664 : Int) atom1325) := by
  rw [SparsePolynomial.eval_scale, eval_atom1325]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1325Coded : CoefficientMerge.Poly := [(nat_lit 2506, Int.ofNat (nat_lit 1))]
theorem atom1325Coded_decode : atom1325 = SparsePolynomial.decodeCubic 24 atom1325Coded := by decide +kernel
theorem atom1325Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (71128035587664 : Int) atom1325Coded) := by
  have h := atom1325_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1325Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1326 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1326 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1326 = ((g 4) * (g 8) * (g 11)) := by
  norm_num [atom1326, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1326_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (88712586556704 : Int) atom1326) := by
  rw [SparsePolynomial.eval_scale, eval_atom1326]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1326Coded : CoefficientMerge.Poly := [(nat_lit 2507, Int.ofNat (nat_lit 1))]
theorem atom1326Coded_decode : atom1326 = SparsePolynomial.decodeCubic 24 atom1326Coded := by decide +kernel
theorem atom1326Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (88712586556704 : Int) atom1326Coded) := by
  have h := atom1326_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1326Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1327 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1327 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1327 = ((g 4) * (g 8) * (g 12)) := by
  norm_num [atom1327, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1327_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (114550858597824 : Int) atom1327) := by
  rw [SparsePolynomial.eval_scale, eval_atom1327]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1327Coded : CoefficientMerge.Poly := [(nat_lit 2508, Int.ofNat (nat_lit 1))]
theorem atom1327Coded_decode : atom1327 = SparsePolynomial.decodeCubic 24 atom1327Coded := by decide +kernel
theorem atom1327Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (114550858597824 : Int) atom1327Coded) := by
  have h := atom1327_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1327Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1328 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1328 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1328 = ((g 4) * (g 8) * (g 13)) := by
  norm_num [atom1328, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1328_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (106889058460800 : Int) atom1328) := by
  rw [SparsePolynomial.eval_scale, eval_atom1328]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1328Coded : CoefficientMerge.Poly := [(nat_lit 2509, Int.ofNat (nat_lit 1))]
theorem atom1328Coded_decode : atom1328 = SparsePolynomial.decodeCubic 24 atom1328Coded := by decide +kernel
theorem atom1328Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (106889058460800 : Int) atom1328Coded) := by
  have h := atom1328_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1328Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block018 : CoefficientMerge.Poly := [(nat_lit 2229, Int.ofNat (nat_lit 519056458905600)), (nat_lit 2230, Int.ofNat (nat_lit 358976744985600)), (nat_lit 2231, Int.ofNat (nat_lit 415551344947200)), (nat_lit 2253, Int.ofNat (nat_lit 149899559040000)), (nat_lit 2254, Int.ofNat (nat_lit 193568557593600)), (nat_lit 2255, Int.ofNat (nat_lit 256657812364800)), (nat_lit 2279, Int.ofNat (nat_lit 65611984132800)), (nat_lit 2303, Int.ofNat (nat_lit 81519845299200)), (nat_lit 2404, Int.ofNat (nat_lit 19145134310400)), (nat_lit 2405, Int.ofNat (nat_lit 33284636169696)), (nat_lit 2406, Int.ofNat (nat_lit 12426232089600)), (nat_lit 2407, Int.ofNat (nat_lit 7216956633600)), (nat_lit 2408, Int.ofNat (nat_lit 2007681177600)), (nat_lit 2409, Int.ofNat (nat_lit 2810186767728)), (nat_lit 2410, Int.ofNat (nat_lit 15244408345968)), (nat_lit 2411, Int.ofNat (nat_lit 26040202684704)), (nat_lit 2412, Int.ofNat (nat_lit 48752909452224)), (nat_lit 2413, Int.ofNat (nat_lit 34882503465600)), (nat_lit 2414, Int.ofNat (nat_lit 17337834662400)), (nat_lit 2415, Int.ofNat (nat_lit 14580172454400)), (nat_lit 2418, Int.ofNat (nat_lit 18173912097600)), (nat_lit 2429, Int.ofNat (nat_lit 37193995228896)), (nat_lit 2430, Int.ofNat (nat_lit 29044448275392)), (nat_lit 2431, Int.ofNat (nat_lit 2242076371392)), (nat_lit 2433, Int.ofNat (nat_lit 3077576911728)), (nat_lit 2434, Int.ofNat (nat_lit 12869199875664)), (nat_lit 2435, Int.ofNat (nat_lit 29390633404704)), (nat_lit 2436, Int.ofNat (nat_lit 79919010651744)), (nat_lit 2437, Int.ofNat (nat_lit 57281162390496)), (nat_lit 2438, Int.ofNat (nat_lit 27294788496096)), (nat_lit 2439, Int.ofNat (nat_lit 27620166864096)), (nat_lit 2440, Int.ofNat (nat_lit 16123034985696)), (nat_lit 2441, Int.ofNat (nat_lit 19206075561696)), (nat_lit 2442, Int.ofNat (nat_lit 49319508264048)), (nat_lit 2443, Int.ofNat (nat_lit 36196508174400)), (nat_lit 2444, Int.ofNat (nat_lit 47956822204752)), (nat_lit 2445, Int.ofNat (nat_lit 74969085851928)), (nat_lit 2446, Int.ofNat (nat_lit 101981349499104)), (nat_lit 2447, Int.ofNat (nat_lit 130089392506692)), (nat_lit 2454, Int.ofNat (nat_lit 25323457420800)), (nat_lit 2455, Int.ofNat (nat_lit 22823950195200)), (nat_lit 2456, Int.ofNat (nat_lit 850493952000)), (nat_lit 2457, Int.ofNat (nat_lit 4523416630128)), (nat_lit 2458, Int.ofNat (nat_lit 24745725232272)), (nat_lit 2459, Int.ofNat (nat_lit 34961368790304)), (nat_lit 2460, Int.ofNat (nat_lit 60757116133824)), (nat_lit 2461, Int.ofNat (nat_lit 52032198556800)), (nat_lit 2462, Int.ofNat (nat_lit 39633018163200)), (nat_lit 2463, Int.ofNat (nat_lit 42020844364800)), (nat_lit 2464, Int.ofNat (nat_lit 32586160320000)), (nat_lit 2465, Int.ofNat (nat_lit 37731648729600)), (nat_lit 2466, Int.ofNat (nat_lit 71505279014400)), (nat_lit 2467, Int.ofNat (nat_lit 79385314881600)), (nat_lit 2468, Int.ofNat (nat_lit 105439262846400)), (nat_lit 2469, Int.ofNat (nat_lit 152401670366400)), (nat_lit 2470, Int.ofNat (nat_lit 199364077886400)), (nat_lit 2471, Int.ofNat (nat_lit 246326485406400)), (nat_lit 2479, Int.ofNat (nat_lit 28330898534400)), (nat_lit 2480, Int.ofNat (nat_lit 41917539417600)), (nat_lit 2481, Int.ofNat (nat_lit 30177621698928)), (nat_lit 2482, Int.ofNat (nat_lit 49379337558672)), (nat_lit 2483, Int.ofNat (nat_lit 62699284041504)), (nat_lit 2484, Int.ofNat (nat_lit 91599334309824)), (nat_lit 2485, Int.ofNat (nat_lit 83916271824000)), (nat_lit 2486, Int.ofNat (nat_lit 72558946521600)), (nat_lit 2487, Int.ofNat (nat_lit 75988627814400)), (nat_lit 2488, Int.ofNat (nat_lit 67595798860800)), (nat_lit 2489, Int.ofNat (nat_lit 73783142361600)), (nat_lit 2490, Int.ofNat (nat_lit 110928036172800)), (nat_lit 2491, Int.ofNat (nat_lit 124508744001600)), (nat_lit 2492, Int.ofNat (nat_lit 156263363928000)), (nat_lit 2493, Int.ofNat (nat_lit 213585260280000)), (nat_lit 2494, Int.ofNat (nat_lit 270907156632000)), (nat_lit 2495, Int.ofNat (nat_lit 328229052984000)), (nat_lit 2504, Int.ofNat (nat_lit 45437639385600)), (nat_lit 2505, Int.ofNat (nat_lit 80170645487328)), (nat_lit 2506, Int.ofNat (nat_lit 71128035587664)), (nat_lit 2507, Int.ofNat (nat_lit 88712586556704)), (nat_lit 2508, Int.ofNat (nat_lit 114550858597824)), (nat_lit 2509, Int.ofNat (nat_lit 106889058460800))]
theorem block018_data : block018 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (519056458905600 : Int) atom1249Coded) (CoefficientMerge.scale (358976744985600 : Int) atom1250Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (415551344947200 : Int) atom1251Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (149899559040000 : Int) atom1252Coded) (CoefficientMerge.scale (193568557593600 : Int) atom1253Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (256657812364800 : Int) atom1254Coded) (CoefficientMerge.scale (65611984132800 : Int) atom1255Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (81519845299200 : Int) atom1256Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19145134310400 : Int) atom1257Coded) (CoefficientMerge.scale (33284636169696 : Int) atom1258Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12426232089600 : Int) atom1259Coded) (CoefficientMerge.scale (7216956633600 : Int) atom1260Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2007681177600 : Int) atom1261Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2810186767728 : Int) atom1262Coded) (CoefficientMerge.scale (15244408345968 : Int) atom1263Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26040202684704 : Int) atom1264Coded) (CoefficientMerge.scale (48752909452224 : Int) atom1265Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34882503465600 : Int) atom1266Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17337834662400 : Int) atom1267Coded) (CoefficientMerge.scale (14580172454400 : Int) atom1268Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (18173912097600 : Int) atom1269Coded) (CoefficientMerge.scale (37193995228896 : Int) atom1270Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29044448275392 : Int) atom1271Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2242076371392 : Int) atom1272Coded) (CoefficientMerge.scale (3077576911728 : Int) atom1273Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12869199875664 : Int) atom1274Coded) (CoefficientMerge.scale (29390633404704 : Int) atom1275Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (79919010651744 : Int) atom1276Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57281162390496 : Int) atom1277Coded) (CoefficientMerge.scale (27294788496096 : Int) atom1278Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (27620166864096 : Int) atom1279Coded) (CoefficientMerge.scale (16123034985696 : Int) atom1280Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19206075561696 : Int) atom1281Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49319508264048 : Int) atom1282Coded) (CoefficientMerge.scale (36196508174400 : Int) atom1283Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (47956822204752 : Int) atom1284Coded) (CoefficientMerge.scale (74969085851928 : Int) atom1285Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101981349499104 : Int) atom1286Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (130089392506692 : Int) atom1287Coded) (CoefficientMerge.scale (25323457420800 : Int) atom1288Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22823950195200 : Int) atom1289Coded) (CoefficientMerge.scale (850493952000 : Int) atom1290Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4523416630128 : Int) atom1291Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24745725232272 : Int) atom1292Coded) (CoefficientMerge.scale (34961368790304 : Int) atom1293Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (60757116133824 : Int) atom1294Coded) (CoefficientMerge.scale (52032198556800 : Int) atom1295Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39633018163200 : Int) atom1296Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42020844364800 : Int) atom1297Coded) (CoefficientMerge.scale (32586160320000 : Int) atom1298Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37731648729600 : Int) atom1299Coded) (CoefficientMerge.scale (71505279014400 : Int) atom1300Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (79385314881600 : Int) atom1301Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (105439262846400 : Int) atom1302Coded) (CoefficientMerge.scale (152401670366400 : Int) atom1303Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (199364077886400 : Int) atom1304Coded) (CoefficientMerge.scale (246326485406400 : Int) atom1305Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28330898534400 : Int) atom1306Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41917539417600 : Int) atom1307Coded) (CoefficientMerge.scale (30177621698928 : Int) atom1308Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (49379337558672 : Int) atom1309Coded) (CoefficientMerge.scale (62699284041504 : Int) atom1310Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (91599334309824 : Int) atom1311Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83916271824000 : Int) atom1312Coded) (CoefficientMerge.scale (72558946521600 : Int) atom1313Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (75988627814400 : Int) atom1314Coded) (CoefficientMerge.scale (67595798860800 : Int) atom1315Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73783142361600 : Int) atom1316Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110928036172800 : Int) atom1317Coded) (CoefficientMerge.scale (124508744001600 : Int) atom1318Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (156263363928000 : Int) atom1319Coded) (CoefficientMerge.scale (213585260280000 : Int) atom1320Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (270907156632000 : Int) atom1321Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (328229052984000 : Int) atom1322Coded) (CoefficientMerge.scale (45437639385600 : Int) atom1323Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (80170645487328 : Int) atom1324Coded) (CoefficientMerge.scale (71128035587664 : Int) atom1325Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (88712586556704 : Int) atom1326Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (114550858597824 : Int) atom1327Coded) (CoefficientMerge.scale (106889058460800 : Int) atom1328Coded)))))))) := by decide +kernel
theorem block018_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block018 := by
  rw [block018_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1249Coded_nonneg g hg hA hB) (atom1250Coded_nonneg g hg hA hB)) (add_nonneg (atom1251Coded_nonneg g hg hA hB) (add_nonneg (atom1252Coded_nonneg g hg hA hB) (atom1253Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1254Coded_nonneg g hg hA hB) (atom1255Coded_nonneg g hg hA hB)) (add_nonneg (atom1256Coded_nonneg g hg hA hB) (add_nonneg (atom1257Coded_nonneg g hg hA hB) (atom1258Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1259Coded_nonneg g hg hA hB) (atom1260Coded_nonneg g hg hA hB)) (add_nonneg (atom1261Coded_nonneg g hg hA hB) (add_nonneg (atom1262Coded_nonneg g hg hA hB) (atom1263Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1264Coded_nonneg g hg hA hB) (atom1265Coded_nonneg g hg hA hB)) (add_nonneg (atom1266Coded_nonneg g hg hA hB) (add_nonneg (atom1267Coded_nonneg g hg hA hB) (atom1268Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1269Coded_nonneg g hg hA hB) (atom1270Coded_nonneg g hg hA hB)) (add_nonneg (atom1271Coded_nonneg g hg hA hB) (add_nonneg (atom1272Coded_nonneg g hg hA hB) (atom1273Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1274Coded_nonneg g hg hA hB) (atom1275Coded_nonneg g hg hA hB)) (add_nonneg (atom1276Coded_nonneg g hg hA hB) (add_nonneg (atom1277Coded_nonneg g hg hA hB) (atom1278Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1279Coded_nonneg g hg hA hB) (atom1280Coded_nonneg g hg hA hB)) (add_nonneg (atom1281Coded_nonneg g hg hA hB) (add_nonneg (atom1282Coded_nonneg g hg hA hB) (atom1283Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1284Coded_nonneg g hg hA hB) (atom1285Coded_nonneg g hg hA hB)) (add_nonneg (atom1286Coded_nonneg g hg hA hB) (add_nonneg (atom1287Coded_nonneg g hg hA hB) (atom1288Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1289Coded_nonneg g hg hA hB) (atom1290Coded_nonneg g hg hA hB)) (add_nonneg (atom1291Coded_nonneg g hg hA hB) (add_nonneg (atom1292Coded_nonneg g hg hA hB) (atom1293Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1294Coded_nonneg g hg hA hB) (atom1295Coded_nonneg g hg hA hB)) (add_nonneg (atom1296Coded_nonneg g hg hA hB) (add_nonneg (atom1297Coded_nonneg g hg hA hB) (atom1298Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1299Coded_nonneg g hg hA hB) (atom1300Coded_nonneg g hg hA hB)) (add_nonneg (atom1301Coded_nonneg g hg hA hB) (add_nonneg (atom1302Coded_nonneg g hg hA hB) (atom1303Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1304Coded_nonneg g hg hA hB) (atom1305Coded_nonneg g hg hA hB)) (add_nonneg (atom1306Coded_nonneg g hg hA hB) (add_nonneg (atom1307Coded_nonneg g hg hA hB) (atom1308Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1309Coded_nonneg g hg hA hB) (atom1310Coded_nonneg g hg hA hB)) (add_nonneg (atom1311Coded_nonneg g hg hA hB) (add_nonneg (atom1312Coded_nonneg g hg hA hB) (atom1313Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1314Coded_nonneg g hg hA hB) (atom1315Coded_nonneg g hg hA hB)) (add_nonneg (atom1316Coded_nonneg g hg hA hB) (add_nonneg (atom1317Coded_nonneg g hg hA hB) (atom1318Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1319Coded_nonneg g hg hA hB) (atom1320Coded_nonneg g hg hA hB)) (add_nonneg (atom1321Coded_nonneg g hg hA hB) (add_nonneg (atom1322Coded_nonneg g hg hA hB) (atom1323Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1324Coded_nonneg g hg hA hB) (atom1325Coded_nonneg g hg hA hB)) (add_nonneg (atom1326Coded_nonneg g hg hA hB) (add_nonneg (atom1327Coded_nonneg g hg hA hB) (atom1328Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
