-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom0976 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0976 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0976 = ((g 4) * (g 7) * (g 20)) := by
  norm_num [atom0976, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0976_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37738841800608 : Int) atom0976) := by
  rw [SparsePolynomial.eval_scale, eval_atom0976]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 7) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0976Coded : CoefficientMerge.Poly := [(nat_lit 1931, Int.ofNat (nat_lit 1))]
theorem atom0976Coded_decode : atom0976 = SparsePolynomial.decodeCubic 21 atom0976Coded := by decide +kernel
theorem atom0976Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (37738841800608 : Int) atom0976Coded) := by
  have h := atom0976_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0976Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0977 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0977 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0977 = ((g 4) * (g 8) * (g 8)) := by
  norm_num [atom0977, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0977_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8316316713600 : Int) atom0977) := by
  rw [SparsePolynomial.eval_scale, eval_atom0977]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0977Coded : CoefficientMerge.Poly := [(nat_lit 1940, Int.ofNat (nat_lit 1))]
theorem atom0977Coded_decode : atom0977 = SparsePolynomial.decodeCubic 21 atom0977Coded := by decide +kernel
theorem atom0977Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8316316713600 : Int) atom0977Coded) := by
  have h := atom0977_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0977Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0978 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0978 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0978 = ((g 4) * (g 8) * (g 9)) := by
  norm_num [atom0978, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0978_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14616092937600 : Int) atom0978) := by
  rw [SparsePolynomial.eval_scale, eval_atom0978]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0978Coded : CoefficientMerge.Poly := [(nat_lit 1941, Int.ofNat (nat_lit 1))]
theorem atom0978Coded_decode : atom0978 = SparsePolynomial.decodeCubic 21 atom0978Coded := by decide +kernel
theorem atom0978Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14616092937600 : Int) atom0978Coded) := by
  have h := atom0978_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0978Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0979 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0979 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0979 = ((g 4) * (g 8) * (g 10)) := by
  norm_num [atom0979, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0979_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14686645276800 : Int) atom0979) := by
  rw [SparsePolynomial.eval_scale, eval_atom0979]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0979Coded : CoefficientMerge.Poly := [(nat_lit 1942, Int.ofNat (nat_lit 1))]
theorem atom0979Coded_decode : atom0979 = SparsePolynomial.decodeCubic 21 atom0979Coded := by decide +kernel
theorem atom0979Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14686645276800 : Int) atom0979Coded) := by
  have h := atom0979_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0979Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0980 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0980 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0980 = ((g 4) * (g 8) * (g 11)) := by
  norm_num [atom0980, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0980_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14704288099200 : Int) atom0980) := by
  rw [SparsePolynomial.eval_scale, eval_atom0980]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0980Coded : CoefficientMerge.Poly := [(nat_lit 1943, Int.ofNat (nat_lit 1))]
theorem atom0980Coded_decode : atom0980 = SparsePolynomial.decodeCubic 21 atom0980Coded := by decide +kernel
theorem atom0980Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14704288099200 : Int) atom0980Coded) := by
  have h := atom0980_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0980Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0981 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0981 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0981 = ((g 4) * (g 8) * (g 12)) := by
  norm_num [atom0981, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0981_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13399306704000 : Int) atom0981) := by
  rw [SparsePolynomial.eval_scale, eval_atom0981]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0981Coded : CoefficientMerge.Poly := [(nat_lit 1944, Int.ofNat (nat_lit 1))]
theorem atom0981Coded_decode : atom0981 = SparsePolynomial.decodeCubic 21 atom0981Coded := by decide +kernel
theorem atom0981Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13399306704000 : Int) atom0981Coded) := by
  have h := atom0981_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0981Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0982 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0982 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0982 = ((g 4) * (g 8) * (g 13)) := by
  norm_num [atom0982, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0982_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14099031273600 : Int) atom0982) := by
  rw [SparsePolynomial.eval_scale, eval_atom0982]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0982Coded : CoefficientMerge.Poly := [(nat_lit 1945, Int.ofNat (nat_lit 1))]
theorem atom0982Coded_decode : atom0982 = SparsePolynomial.decodeCubic 21 atom0982Coded := by decide +kernel
theorem atom0982Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14099031273600 : Int) atom0982Coded) := by
  have h := atom0982_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0982Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0983 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0983 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0983 = ((g 4) * (g 8) * (g 14)) := by
  norm_num [atom0983, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0983_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14798755843200 : Int) atom0983) := by
  rw [SparsePolynomial.eval_scale, eval_atom0983]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0983Coded : CoefficientMerge.Poly := [(nat_lit 1946, Int.ofNat (nat_lit 1))]
theorem atom0983Coded_decode : atom0983 = SparsePolynomial.decodeCubic 21 atom0983Coded := by decide +kernel
theorem atom0983Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14798755843200 : Int) atom0983Coded) := by
  have h := atom0983_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0983Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0984 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0984 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0984 = ((g 4) * (g 8) * (g 15)) := by
  norm_num [atom0984, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0984_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23245546060800 : Int) atom0984) := by
  rw [SparsePolynomial.eval_scale, eval_atom0984]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0984Coded : CoefficientMerge.Poly := [(nat_lit 1947, Int.ofNat (nat_lit 1))]
theorem atom0984Coded_decode : atom0984 = SparsePolynomial.decodeCubic 21 atom0984Coded := by decide +kernel
theorem atom0984Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23245546060800 : Int) atom0984Coded) := by
  have h := atom0984_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0984Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0985 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0985 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0985 = ((g 4) * (g 8) * (g 16)) := by
  norm_num [atom0985, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0985_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20719776344400 : Int) atom0985) := by
  rw [SparsePolynomial.eval_scale, eval_atom0985]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0985Coded : CoefficientMerge.Poly := [(nat_lit 1948, Int.ofNat (nat_lit 1))]
theorem atom0985Coded_decode : atom0985 = SparsePolynomial.decodeCubic 21 atom0985Coded := by decide +kernel
theorem atom0985Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20719776344400 : Int) atom0985Coded) := by
  have h := atom0985_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0985Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0986 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0986 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0986 = ((g 4) * (g 8) * (g 17)) := by
  norm_num [atom0986, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0986_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26086557772800 : Int) atom0986) := by
  rw [SparsePolynomial.eval_scale, eval_atom0986]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0986Coded : CoefficientMerge.Poly := [(nat_lit 1949, Int.ofNat (nat_lit 1))]
theorem atom0986Coded_decode : atom0986 = SparsePolynomial.decodeCubic 21 atom0986Coded := by decide +kernel
theorem atom0986Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (26086557772800 : Int) atom0986Coded) := by
  have h := atom0986_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0986Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0987 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0987 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0987 = ((g 4) * (g 8) * (g 18)) := by
  norm_num [atom0987, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0987_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31162368207600 : Int) atom0987) := by
  rw [SparsePolynomial.eval_scale, eval_atom0987]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 8) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0987Coded : CoefficientMerge.Poly := [(nat_lit 1950, Int.ofNat (nat_lit 1))]
theorem atom0987Coded_decode : atom0987 = SparsePolynomial.decodeCubic 21 atom0987Coded := by decide +kernel
theorem atom0987Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31162368207600 : Int) atom0987Coded) := by
  have h := atom0987_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0987Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0988 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0988 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0988 = ((g 4) * (g 8) * (g 19)) := by
  norm_num [atom0988, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0988_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37890854593200 : Int) atom0988) := by
  rw [SparsePolynomial.eval_scale, eval_atom0988]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 8) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0988Coded : CoefficientMerge.Poly := [(nat_lit 1951, Int.ofNat (nat_lit 1))]
theorem atom0988Coded_decode : atom0988 = SparsePolynomial.decodeCubic 21 atom0988Coded := by decide +kernel
theorem atom0988Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (37890854593200 : Int) atom0988Coded) := by
  have h := atom0988_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0988Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0989 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0989 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0989 = ((g 4) * (g 8) * (g 20)) := by
  norm_num [atom0989, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0989_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44619340978800 : Int) atom0989) := by
  rw [SparsePolynomial.eval_scale, eval_atom0989]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 8) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0989Coded : CoefficientMerge.Poly := [(nat_lit 1952, Int.ofNat (nat_lit 1))]
theorem atom0989Coded_decode : atom0989 = SparsePolynomial.decodeCubic 21 atom0989Coded := by decide +kernel
theorem atom0989Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (44619340978800 : Int) atom0989Coded) := by
  have h := atom0989_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0989Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0990 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0990 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0990 = ((g 4) * (g 9) * (g 9)) := by
  norm_num [atom0990, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0990_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10739741241600 : Int) atom0990) := by
  rw [SparsePolynomial.eval_scale, eval_atom0990]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0990Coded : CoefficientMerge.Poly := [(nat_lit 1962, Int.ofNat (nat_lit 1))]
theorem atom0990Coded_decode : atom0990 = SparsePolynomial.decodeCubic 21 atom0990Coded := by decide +kernel
theorem atom0990Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10739741241600 : Int) atom0990Coded) := by
  have h := atom0990_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0990Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0991 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0991 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0991 = ((g 4) * (g 9) * (g 10)) := by
  norm_num [atom0991, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0991_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19770762816000 : Int) atom0991) := by
  rw [SparsePolynomial.eval_scale, eval_atom0991]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0991Coded : CoefficientMerge.Poly := [(nat_lit 1963, Int.ofNat (nat_lit 1))]
theorem atom0991Coded_decode : atom0991 = SparsePolynomial.decodeCubic 21 atom0991Coded := by decide +kernel
theorem atom0991Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19770762816000 : Int) atom0991Coded) := by
  have h := atom0991_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0991Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0992 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0992 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0992 = ((g 4) * (g 9) * (g 11)) := by
  norm_num [atom0992, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0992_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19283908089600 : Int) atom0992) := by
  rw [SparsePolynomial.eval_scale, eval_atom0992]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0992Coded : CoefficientMerge.Poly := [(nat_lit 1964, Int.ofNat (nat_lit 1))]
theorem atom0992Coded_decode : atom0992 = SparsePolynomial.decodeCubic 21 atom0992Coded := by decide +kernel
theorem atom0992Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19283908089600 : Int) atom0992Coded) := by
  have h := atom0992_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0992Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0993 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0993 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0993 = ((g 4) * (g 9) * (g 12)) := by
  norm_num [atom0993, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0993_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18160623129600 : Int) atom0993) := by
  rw [SparsePolynomial.eval_scale, eval_atom0993]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0993Coded : CoefficientMerge.Poly := [(nat_lit 1965, Int.ofNat (nat_lit 1))]
theorem atom0993Coded_decode : atom0993 = SparsePolynomial.decodeCubic 21 atom0993Coded := by decide +kernel
theorem atom0993Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18160623129600 : Int) atom0993Coded) := by
  have h := atom0993_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0993Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0994 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0994 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0994 = ((g 4) * (g 9) * (g 13)) := by
  norm_num [atom0994, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0994_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18614864217600 : Int) atom0994) := by
  rw [SparsePolynomial.eval_scale, eval_atom0994]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0994Coded : CoefficientMerge.Poly := [(nat_lit 1966, Int.ofNat (nat_lit 1))]
theorem atom0994Coded_decode : atom0994 = SparsePolynomial.decodeCubic 21 atom0994Coded := by decide +kernel
theorem atom0994Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18614864217600 : Int) atom0994Coded) := by
  have h := atom0994_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0994Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0995 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0995 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0995 = ((g 4) * (g 9) * (g 14)) := by
  norm_num [atom0995, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0995_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19069105305600 : Int) atom0995) := by
  rw [SparsePolynomial.eval_scale, eval_atom0995]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0995Coded : CoefficientMerge.Poly := [(nat_lit 1967, Int.ofNat (nat_lit 1))]
theorem atom0995Coded_decode : atom0995 = SparsePolynomial.decodeCubic 21 atom0995Coded := by decide +kernel
theorem atom0995Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19069105305600 : Int) atom0995Coded) := by
  have h := atom0995_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0995Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0996 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0996 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0996 = ((g 4) * (g 9) * (g 15)) := by
  norm_num [atom0996, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0996_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27327917030400 : Int) atom0996) := by
  rw [SparsePolynomial.eval_scale, eval_atom0996]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0996Coded : CoefficientMerge.Poly := [(nat_lit 1968, Int.ofNat (nat_lit 1))]
theorem atom0996Coded_decode : atom0996 = SparsePolynomial.decodeCubic 21 atom0996Coded := by decide +kernel
theorem atom0996Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27327917030400 : Int) atom0996Coded) := by
  have h := atom0996_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0996Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0997 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0997 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0997 = ((g 4) * (g 9) * (g 16)) := by
  norm_num [atom0997, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0997_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24967957392000 : Int) atom0997) := by
  rw [SparsePolynomial.eval_scale, eval_atom0997]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0997Coded : CoefficientMerge.Poly := [(nat_lit 1969, Int.ofNat (nat_lit 1))]
theorem atom0997Coded_decode : atom0997 = SparsePolynomial.decodeCubic 21 atom0997Coded := by decide +kernel
theorem atom0997Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24967957392000 : Int) atom0997Coded) := by
  have h := atom0997_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0997Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0998 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0998 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0998 = ((g 4) * (g 9) * (g 17)) := by
  norm_num [atom0998, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0998_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31850587238400 : Int) atom0998) := by
  rw [SparsePolynomial.eval_scale, eval_atom0998]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0998Coded : CoefficientMerge.Poly := [(nat_lit 1970, Int.ofNat (nat_lit 1))]
theorem atom0998Coded_decode : atom0998 = SparsePolynomial.decodeCubic 21 atom0998Coded := by decide +kernel
theorem atom0998Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31850587238400 : Int) atom0998Coded) := by
  have h := atom0998_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0998Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0999 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0999 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0999 = ((g 4) * (g 9) * (g 18)) := by
  norm_num [atom0999, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0999_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35857179388800 : Int) atom0999) := by
  rw [SparsePolynomial.eval_scale, eval_atom0999]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 9) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0999Coded : CoefficientMerge.Poly := [(nat_lit 1971, Int.ofNat (nat_lit 1))]
theorem atom0999Coded_decode : atom0999 = SparsePolynomial.decodeCubic 21 atom0999Coded := by decide +kernel
theorem atom0999Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35857179388800 : Int) atom0999Coded) := by
  have h := atom0999_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0999Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1000 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1000 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1000 = ((g 4) * (g 9) * (g 19)) := by
  norm_num [atom1000, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1000_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42965247024000 : Int) atom1000) := by
  rw [SparsePolynomial.eval_scale, eval_atom1000]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 9) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1000Coded : CoefficientMerge.Poly := [(nat_lit 1972, Int.ofNat (nat_lit 1))]
theorem atom1000Coded_decode : atom1000 = SparsePolynomial.decodeCubic 21 atom1000Coded := by decide +kernel
theorem atom1000Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (42965247024000 : Int) atom1000Coded) := by
  have h := atom1000_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1000Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1001 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1001 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1001 = ((g 4) * (g 9) * (g 20)) := by
  norm_num [atom1001, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1001_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (50073314659200 : Int) atom1001) := by
  rw [SparsePolynomial.eval_scale, eval_atom1001]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 9) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1001Coded : CoefficientMerge.Poly := [(nat_lit 1973, Int.ofNat (nat_lit 1))]
theorem atom1001Coded_decode : atom1001 = SparsePolynomial.decodeCubic 21 atom1001Coded := by decide +kernel
theorem atom1001Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (50073314659200 : Int) atom1001Coded) := by
  have h := atom1001_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1001Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1002 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1002 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1002 = ((g 4) * (g 10) * (g 10)) := by
  norm_num [atom1002, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1002_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13470986592000 : Int) atom1002) := by
  rw [SparsePolynomial.eval_scale, eval_atom1002]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1002Coded : CoefficientMerge.Poly := [(nat_lit 1984, Int.ofNat (nat_lit 1))]
theorem atom1002Coded_decode : atom1002 = SparsePolynomial.decodeCubic 21 atom1002Coded := by decide +kernel
theorem atom1002Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13470986592000 : Int) atom1002Coded) := by
  have h := atom1002_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1002Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1003 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1003 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1003 = ((g 4) * (g 10) * (g 11)) := by
  norm_num [atom1003, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1003_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25277957510400 : Int) atom1003) := by
  rw [SparsePolynomial.eval_scale, eval_atom1003]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1003Coded : CoefficientMerge.Poly := [(nat_lit 1985, Int.ofNat (nat_lit 1))]
theorem atom1003Coded_decode : atom1003 = SparsePolynomial.decodeCubic 21 atom1003Coded := by decide +kernel
theorem atom1003Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25277957510400 : Int) atom1003Coded) := by
  have h := atom1003_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1003Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1004 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1004 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1004 = ((g 4) * (g 10) * (g 12)) := by
  norm_num [atom1004, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1004_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23313843302400 : Int) atom1004) := by
  rw [SparsePolynomial.eval_scale, eval_atom1004]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1004Coded : CoefficientMerge.Poly := [(nat_lit 1986, Int.ofNat (nat_lit 1))]
theorem atom1004Coded_decode : atom1004 = SparsePolynomial.decodeCubic 21 atom1004Coded := by decide +kernel
theorem atom1004Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23313843302400 : Int) atom1004Coded) := by
  have h := atom1004_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1004Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1005 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1005 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1005 = ((g 4) * (g 10) * (g 13)) := by
  norm_num [atom1005, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1005_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23354435059200 : Int) atom1005) := by
  rw [SparsePolynomial.eval_scale, eval_atom1005]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1005Coded : CoefficientMerge.Poly := [(nat_lit 1987, Int.ofNat (nat_lit 1))]
theorem atom1005Coded_decode : atom1005 = SparsePolynomial.decodeCubic 21 atom1005Coded := by decide +kernel
theorem atom1005Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23354435059200 : Int) atom1005Coded) := by
  have h := atom1005_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1005Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1006 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1006 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1006 = ((g 4) * (g 10) * (g 14)) := by
  norm_num [atom1006, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1006_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23395026816000 : Int) atom1006) := by
  rw [SparsePolynomial.eval_scale, eval_atom1006]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1006Coded : CoefficientMerge.Poly := [(nat_lit 1988, Int.ofNat (nat_lit 1))]
theorem atom1006Coded_decode : atom1006 = SparsePolynomial.decodeCubic 21 atom1006Coded := by decide +kernel
theorem atom1006Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23395026816000 : Int) atom1006Coded) := by
  have h := atom1006_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1006Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1007 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1007 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1007 = ((g 4) * (g 10) * (g 15)) := by
  norm_num [atom1007, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1007_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31410288000000 : Int) atom1007) := by
  rw [SparsePolynomial.eval_scale, eval_atom1007]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1007Coded : CoefficientMerge.Poly := [(nat_lit 1989, Int.ofNat (nat_lit 1))]
theorem atom1007Coded_decode : atom1007 = SparsePolynomial.decodeCubic 21 atom1007Coded := by decide +kernel
theorem atom1007Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31410288000000 : Int) atom1007Coded) := by
  have h := atom1007_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1007Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1008 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1008 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1008 = ((g 4) * (g 10) * (g 16)) := by
  norm_num [atom1008, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1008_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28735500628800 : Int) atom1008) := by
  rw [SparsePolynomial.eval_scale, eval_atom1008]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1008Coded : CoefficientMerge.Poly := [(nat_lit 1990, Int.ofNat (nat_lit 1))]
theorem atom1008Coded_decode : atom1008 = SparsePolynomial.decodeCubic 21 atom1008Coded := by decide +kernel
theorem atom1008Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (28735500628800 : Int) atom1008Coded) := by
  have h := atom1008_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1008Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1009 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1009 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1009 = ((g 4) * (g 10) * (g 17)) := by
  norm_num [atom1009, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1009_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37614616704000 : Int) atom1009) := by
  rw [SparsePolynomial.eval_scale, eval_atom1009]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1009Coded : CoefficientMerge.Poly := [(nat_lit 1991, Int.ofNat (nat_lit 1))]
theorem atom1009Coded_decode : atom1009 = SparsePolynomial.decodeCubic 21 atom1009Coded := by decide +kernel
theorem atom1009Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (37614616704000 : Int) atom1009Coded) := by
  have h := atom1009_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1009Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1010 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1010 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1010 = ((g 4) * (g 10) * (g 18)) := by
  norm_num [atom1010, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1010_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39335264740800 : Int) atom1010) := by
  rw [SparsePolynomial.eval_scale, eval_atom1010]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1010Coded : CoefficientMerge.Poly := [(nat_lit 1992, Int.ofNat (nat_lit 1))]
theorem atom1010Coded_decode : atom1010 = SparsePolynomial.decodeCubic 21 atom1010Coded := by decide +kernel
theorem atom1010Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39335264740800 : Int) atom1010Coded) := by
  have h := atom1010_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1010Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1011 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1011 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1011 = ((g 4) * (g 10) * (g 19)) := by
  norm_num [atom1011, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1011_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46388243563200 : Int) atom1011) := by
  rw [SparsePolynomial.eval_scale, eval_atom1011]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1011Coded : CoefficientMerge.Poly := [(nat_lit 1993, Int.ofNat (nat_lit 1))]
theorem atom1011Coded_decode : atom1011 = SparsePolynomial.decodeCubic 21 atom1011Coded := by decide +kernel
theorem atom1011Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (46388243563200 : Int) atom1011Coded) := by
  have h := atom1011_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1011Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1012 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1012 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1012 = ((g 4) * (g 10) * (g 20)) := by
  norm_num [atom1012, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1012_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53441222385600 : Int) atom1012) := by
  rw [SparsePolynomial.eval_scale, eval_atom1012]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 10) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1012Coded : CoefficientMerge.Poly := [(nat_lit 1994, Int.ofNat (nat_lit 1))]
theorem atom1012Coded_decode : atom1012 = SparsePolynomial.decodeCubic 21 atom1012Coded := by decide +kernel
theorem atom1012Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (53441222385600 : Int) atom1012Coded) := by
  have h := atom1012_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1012Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1013 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1013 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1013 = ((g 4) * (g 11) * (g 11)) := by
  norm_num [atom1013, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1013_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16246935936000 : Int) atom1013) := by
  rw [SparsePolynomial.eval_scale, eval_atom1013]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1013Coded : CoefficientMerge.Poly := [(nat_lit 2006, Int.ofNat (nat_lit 1))]
theorem atom1013Coded_decode : atom1013 = SparsePolynomial.decodeCubic 21 atom1013Coded := by decide +kernel
theorem atom1013Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16246935936000 : Int) atom1013Coded) := by
  have h := atom1013_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1013Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1014 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1014 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1014 = ((g 4) * (g 11) * (g 12)) := by
  norm_num [atom1014, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1014_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28498236883200 : Int) atom1014) := by
  rw [SparsePolynomial.eval_scale, eval_atom1014]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1014Coded : CoefficientMerge.Poly := [(nat_lit 2007, Int.ofNat (nat_lit 1))]
theorem atom1014Coded_decode : atom1014 = SparsePolynomial.decodeCubic 21 atom1014Coded := by decide +kernel
theorem atom1014Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (28498236883200 : Int) atom1014Coded) := by
  have h := atom1014_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1014Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1015 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1015 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1015 = ((g 4) * (g 11) * (g 13)) := by
  norm_num [atom1015, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1015_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27957013459200 : Int) atom1015) := by
  rw [SparsePolynomial.eval_scale, eval_atom1015]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1015Coded : CoefficientMerge.Poly := [(nat_lit 2008, Int.ofNat (nat_lit 1))]
theorem atom1015Coded_decode : atom1015 = SparsePolynomial.decodeCubic 21 atom1015Coded := by decide +kernel
theorem atom1015Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27957013459200 : Int) atom1015Coded) := by
  have h := atom1015_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1015Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1016 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1016 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1016 = ((g 4) * (g 11) * (g 14)) := by
  norm_num [atom1016, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1016_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27415790035200 : Int) atom1016) := by
  rw [SparsePolynomial.eval_scale, eval_atom1016]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1016Coded : CoefficientMerge.Poly := [(nat_lit 2009, Int.ofNat (nat_lit 1))]
theorem atom1016Coded_decode : atom1016 = SparsePolynomial.decodeCubic 21 atom1016Coded := by decide +kernel
theorem atom1016Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27415790035200 : Int) atom1016Coded) := by
  have h := atom1016_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1016Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1017 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1017 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1017 = ((g 4) * (g 11) * (g 15)) := by
  norm_num [atom1017, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1017_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34868811801600 : Int) atom1017) := by
  rw [SparsePolynomial.eval_scale, eval_atom1017]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1017Coded : CoefficientMerge.Poly := [(nat_lit 2010, Int.ofNat (nat_lit 1))]
theorem atom1017Coded_decode : atom1017 = SparsePolynomial.decodeCubic 21 atom1017Coded := by decide +kernel
theorem atom1017Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (34868811801600 : Int) atom1017Coded) := by
  have h := atom1017_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1017Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1018 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1018 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1018 = ((g 4) * (g 11) * (g 16)) := by
  norm_num [atom1018, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1018_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31796949592800 : Int) atom1018) := by
  rw [SparsePolynomial.eval_scale, eval_atom1018]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1018Coded : CoefficientMerge.Poly := [(nat_lit 2011, Int.ofNat (nat_lit 1))]
theorem atom1018Coded_decode : atom1018 = SparsePolynomial.decodeCubic 21 atom1018Coded := by decide +kernel
theorem atom1018Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31796949592800 : Int) atom1018Coded) := by
  have h := atom1018_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1018Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1019 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1019 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1019 = ((g 4) * (g 11) * (g 17)) := by
  norm_num [atom1019, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1019_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42754799001600 : Int) atom1019) := by
  rw [SparsePolynomial.eval_scale, eval_atom1019]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1019Coded : CoefficientMerge.Poly := [(nat_lit 2012, Int.ofNat (nat_lit 1))]
theorem atom1019Coded_decode : atom1019 = SparsePolynomial.decodeCubic 21 atom1019Coded := by decide +kernel
theorem atom1019Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (42754799001600 : Int) atom1019Coded) := by
  have h := atom1019_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1019Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1020 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1020 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1020 = ((g 4) * (g 11) * (g 18)) := by
  norm_num [atom1020, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1020_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41641715556000 : Int) atom1020) := by
  rw [SparsePolynomial.eval_scale, eval_atom1020]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1020Coded : CoefficientMerge.Poly := [(nat_lit 2013, Int.ofNat (nat_lit 1))]
theorem atom1020Coded_decode : atom1020 = SparsePolynomial.decodeCubic 21 atom1020Coded := by decide +kernel
theorem atom1020Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (41641715556000 : Int) atom1020Coded) := by
  have h := atom1020_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1020Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1021 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1021 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1021 = ((g 4) * (g 11) * (g 19)) := by
  norm_num [atom1021, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1021_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48385300672800 : Int) atom1021) := by
  rw [SparsePolynomial.eval_scale, eval_atom1021]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1021Coded : CoefficientMerge.Poly := [(nat_lit 2014, Int.ofNat (nat_lit 1))]
theorem atom1021Coded_decode : atom1021 = SparsePolynomial.decodeCubic 21 atom1021Coded := by decide +kernel
theorem atom1021Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (48385300672800 : Int) atom1021Coded) := by
  have h := atom1021_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1021Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1022 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1022 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1022 = ((g 4) * (g 11) * (g 20)) := by
  norm_num [atom1022, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1022_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (55128885789600 : Int) atom1022) := by
  rw [SparsePolynomial.eval_scale, eval_atom1022]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1022Coded : CoefficientMerge.Poly := [(nat_lit 2015, Int.ofNat (nat_lit 1))]
theorem atom1022Coded_decode : atom1022 = SparsePolynomial.decodeCubic 21 atom1022Coded := by decide +kernel
theorem atom1022Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (55128885789600 : Int) atom1022Coded) := by
  have h := atom1022_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1022Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1023 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1023 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1023 = ((g 4) * (g 12) * (g 12)) := by
  norm_num [atom1023, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1023_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17118445881600 : Int) atom1023) := by
  rw [SparsePolynomial.eval_scale, eval_atom1023]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1023Coded : CoefficientMerge.Poly := [(nat_lit 2028, Int.ofNat (nat_lit 1))]
theorem atom1023Coded_decode : atom1023 = SparsePolynomial.decodeCubic 21 atom1023Coded := by decide +kernel
theorem atom1023Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17118445881600 : Int) atom1023Coded) := by
  have h := atom1023_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1023Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1024 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1024 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1024 = ((g 4) * (g 12) * (g 13)) := by
  norm_num [atom1024, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1024_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32518507392000 : Int) atom1024) := by
  rw [SparsePolynomial.eval_scale, eval_atom1024]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1024Coded : CoefficientMerge.Poly := [(nat_lit 2029, Int.ofNat (nat_lit 1))]
theorem atom1024Coded_decode : atom1024 = SparsePolynomial.decodeCubic 21 atom1024Coded := by decide +kernel
theorem atom1024Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32518507392000 : Int) atom1024Coded) := by
  have h := atom1024_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1024Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1025 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1025 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1025 = ((g 4) * (g 12) * (g 14)) := by
  norm_num [atom1025, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1025_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31227302937600 : Int) atom1025) := by
  rw [SparsePolynomial.eval_scale, eval_atom1025]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1025Coded : CoefficientMerge.Poly := [(nat_lit 2030, Int.ofNat (nat_lit 1))]
theorem atom1025Coded_decode : atom1025 = SparsePolynomial.decodeCubic 21 atom1025Coded := by decide +kernel
theorem atom1025Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31227302937600 : Int) atom1025Coded) := by
  have h := atom1025_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1025Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1026 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 12, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1026 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1026 = ((g 4) * (g 12) * (g 15)) := by
  norm_num [atom1026, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1026_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34633735248000 : Int) atom1026) := by
  rw [SparsePolynomial.eval_scale, eval_atom1026]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1026Coded : CoefficientMerge.Poly := [(nat_lit 2031, Int.ofNat (nat_lit 1))]
theorem atom1026Coded_decode : atom1026 = SparsePolynomial.decodeCubic 21 atom1026Coded := by decide +kernel
theorem atom1026Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (34633735248000 : Int) atom1026Coded) := by
  have h := atom1026_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1026Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1027 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 12, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1027 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1027 = ((g 4) * (g 12) * (g 16)) := by
  norm_num [atom1027, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1027_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33705364364000 : Int) atom1027) := by
  rw [SparsePolynomial.eval_scale, eval_atom1027]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1027Coded : CoefficientMerge.Poly := [(nat_lit 2032, Int.ofNat (nat_lit 1))]
theorem atom1027Coded_decode : atom1027 = SparsePolynomial.decodeCubic 21 atom1027Coded := by decide +kernel
theorem atom1027Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (33705364364000 : Int) atom1027Coded) := by
  have h := atom1027_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1027Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1028 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 12, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1028 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1028 = ((g 4) * (g 12) * (g 17)) := by
  norm_num [atom1028, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1028_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43390369097600 : Int) atom1028) := by
  rw [SparsePolynomial.eval_scale, eval_atom1028]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1028Coded : CoefficientMerge.Poly := [(nat_lit 2033, Int.ofNat (nat_lit 1))]
theorem atom1028Coded_decode : atom1028 = SparsePolynomial.decodeCubic 21 atom1028Coded := by decide +kernel
theorem atom1028Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (43390369097600 : Int) atom1028Coded) := by
  have h := atom1028_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1028Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1029 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 12, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1029 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1029 = ((g 4) * (g 12) * (g 18)) := by
  norm_num [atom1029, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1029_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42915361938400 : Int) atom1029) := by
  rw [SparsePolynomial.eval_scale, eval_atom1029]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1029Coded : CoefficientMerge.Poly := [(nat_lit 2034, Int.ofNat (nat_lit 1))]
theorem atom1029Coded_decode : atom1029 = SparsePolynomial.decodeCubic 21 atom1029Coded := by decide +kernel
theorem atom1029Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (42915361938400 : Int) atom1029Coded) := by
  have h := atom1029_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1029Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1030 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 12, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1030 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1030 = ((g 4) * (g 12) * (g 19)) := by
  norm_num [atom1030, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1030_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48592346426400 : Int) atom1030) := by
  rw [SparsePolynomial.eval_scale, eval_atom1030]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1030Coded : CoefficientMerge.Poly := [(nat_lit 2035, Int.ofNat (nat_lit 1))]
theorem atom1030Coded_decode : atom1030 = SparsePolynomial.decodeCubic 21 atom1030Coded := by decide +kernel
theorem atom1030Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (48592346426400 : Int) atom1030Coded) := by
  have h := atom1030_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1030Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1031 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 12, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1031 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1031 = ((g 4) * (g 12) * (g 20)) := by
  norm_num [atom1031, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1031_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (55028408400000 : Int) atom1031) := by
  rw [SparsePolynomial.eval_scale, eval_atom1031]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1031Coded : CoefficientMerge.Poly := [(nat_lit 2036, Int.ofNat (nat_lit 1))]
theorem atom1031Coded_decode : atom1031 = SparsePolynomial.decodeCubic 21 atom1031Coded := by decide +kernel
theorem atom1031Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (55028408400000 : Int) atom1031Coded) := by
  have h := atom1031_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1031Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1032 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1032 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1032 = ((g 4) * (g 13) * (g 13)) := by
  norm_num [atom1032, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1032_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19975700563200 : Int) atom1032) := by
  rw [SparsePolynomial.eval_scale, eval_atom1032]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1032Coded : CoefficientMerge.Poly := [(nat_lit 2050, Int.ofNat (nat_lit 1))]
theorem atom1032Coded_decode : atom1032 = SparsePolynomial.decodeCubic 21 atom1032Coded := by decide +kernel
theorem atom1032Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19975700563200 : Int) atom1032Coded) := by
  have h := atom1032_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1032Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1033 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1033 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1033 = ((g 4) * (g 13) * (g 14)) := by
  norm_num [atom1033, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1033_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36571516070400 : Int) atom1033) := by
  rw [SparsePolynomial.eval_scale, eval_atom1033]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1033Coded : CoefficientMerge.Poly := [(nat_lit 2051, Int.ofNat (nat_lit 1))]
theorem atom1033Coded_decode : atom1033 = SparsePolynomial.decodeCubic 21 atom1033Coded := by decide +kernel
theorem atom1033Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36571516070400 : Int) atom1033Coded) := by
  have h := atom1033_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1033Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1034 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 13, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1034 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1034 = ((g 4) * (g 13) * (g 15)) := by
  norm_num [atom1034, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1034_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38601069393600 : Int) atom1034) := by
  rw [SparsePolynomial.eval_scale, eval_atom1034]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1034Coded : CoefficientMerge.Poly := [(nat_lit 2052, Int.ofNat (nat_lit 1))]
theorem atom1034Coded_decode : atom1034 = SparsePolynomial.decodeCubic 21 atom1034Coded := by decide +kernel
theorem atom1034Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (38601069393600 : Int) atom1034Coded) := by
  have h := atom1034_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1034Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1035 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 13, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1035 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1035 = ((g 4) * (g 13) * (g 16)) := by
  norm_num [atom1035, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1035_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36159816938400 : Int) atom1035) := by
  rw [SparsePolynomial.eval_scale, eval_atom1035]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1035Coded : CoefficientMerge.Poly := [(nat_lit 2053, Int.ofNat (nat_lit 1))]
theorem atom1035Coded_decode : atom1035 = SparsePolynomial.decodeCubic 21 atom1035Coded := by decide +kernel
theorem atom1035Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36159816938400 : Int) atom1035Coded) := by
  have h := atom1035_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1035Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1036 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 13, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1036 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1036 = ((g 4) * (g 13) * (g 17)) := by
  norm_num [atom1036, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1036_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47594873289600 : Int) atom1036) := by
  rw [SparsePolynomial.eval_scale, eval_atom1036]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1036Coded : CoefficientMerge.Poly := [(nat_lit 2054, Int.ofNat (nat_lit 1))]
theorem atom1036Coded_decode : atom1036 = SparsePolynomial.decodeCubic 21 atom1036Coded := by decide +kernel
theorem atom1036Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (47594873289600 : Int) atom1036Coded) := by
  have h := atom1036_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1036Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1037 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 13, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1037 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1037 = ((g 4) * (g 13) * (g 18)) := by
  norm_num [atom1037, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1037_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47799330616800 : Int) atom1037) := by
  rw [SparsePolynomial.eval_scale, eval_atom1037]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1037Coded : CoefficientMerge.Poly := [(nat_lit 2055, Int.ofNat (nat_lit 1))]
theorem atom1037Coded_decode : atom1037 = SparsePolynomial.decodeCubic 21 atom1037Coded := by decide +kernel
theorem atom1037Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (47799330616800 : Int) atom1037Coded) := by
  have h := atom1037_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1037Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1038 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 13, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1038 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1038 = ((g 4) * (g 13) * (g 19)) := by
  norm_num [atom1038, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1038_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46286873474400 : Int) atom1038) := by
  rw [SparsePolynomial.eval_scale, eval_atom1038]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1038Coded : CoefficientMerge.Poly := [(nat_lit 2056, Int.ofNat (nat_lit 1))]
theorem atom1038Coded_decode : atom1038 = SparsePolynomial.decodeCubic 21 atom1038Coded := by decide +kernel
theorem atom1038Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (46286873474400 : Int) atom1038Coded) := by
  have h := atom1038_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1038Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1039 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 13, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1039 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1039 = ((g 4) * (g 13) * (g 20)) := by
  norm_num [atom1039, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1039_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (58138510147200 : Int) atom1039) := by
  rw [SparsePolynomial.eval_scale, eval_atom1039]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1039Coded : CoefficientMerge.Poly := [(nat_lit 2057, Int.ofNat (nat_lit 1))]
theorem atom1039Coded_decode : atom1039 = SparsePolynomial.decodeCubic 21 atom1039Coded := by decide +kernel
theorem atom1039Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (58138510147200 : Int) atom1039Coded) := by
  have h := atom1039_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1039Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1040 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1040 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1040 = ((g 4) * (g 14) * (g 14)) := by
  norm_num [atom1040, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1040_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23439806611200 : Int) atom1040) := by
  rw [SparsePolynomial.eval_scale, eval_atom1040]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1040Coded : CoefficientMerge.Poly := [(nat_lit 2072, Int.ofNat (nat_lit 1))]
theorem atom1040Coded_decode : atom1040 = SparsePolynomial.decodeCubic 21 atom1040Coded := by decide +kernel
theorem atom1040Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23439806611200 : Int) atom1040Coded) := by
  have h := atom1040_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1040Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1041 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 14, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1041 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1041 = ((g 4) * (g 14) * (g 15)) := by
  norm_num [atom1041, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1041_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42456561436800 : Int) atom1041) := by
  rw [SparsePolynomial.eval_scale, eval_atom1041]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1041Coded : CoefficientMerge.Poly := [(nat_lit 2073, Int.ofNat (nat_lit 1))]
theorem atom1041Coded_decode : atom1041 = SparsePolynomial.decodeCubic 21 atom1041Coded := by decide +kernel
theorem atom1041Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (42456561436800 : Int) atom1041Coded) := by
  have h := atom1041_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1041Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1042 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 14, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1042 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1042 = ((g 4) * (g 14) * (g 16)) := by
  norm_num [atom1042, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1042_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38495120076000 : Int) atom1042) := by
  rw [SparsePolynomial.eval_scale, eval_atom1042]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1042Coded : CoefficientMerge.Poly := [(nat_lit 2074, Int.ofNat (nat_lit 1))]
theorem atom1042Coded_decode : atom1042 = SparsePolynomial.decodeCubic 21 atom1042Coded := by decide +kernel
theorem atom1042Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (38495120076000 : Int) atom1042Coded) := by
  have h := atom1042_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1042Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1043 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 14, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1043 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1043 = ((g 4) * (g 14) * (g 17)) := by
  norm_num [atom1043, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1043_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53992907337600 : Int) atom1043) := by
  rw [SparsePolynomial.eval_scale, eval_atom1043]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1043Coded : CoefficientMerge.Poly := [(nat_lit 2075, Int.ofNat (nat_lit 1))]
theorem atom1043Coded_decode : atom1043 = SparsePolynomial.decodeCubic 21 atom1043Coded := by decide +kernel
theorem atom1043Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (53992907337600 : Int) atom1043Coded) := by
  have h := atom1043_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1043Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1044 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 14, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1044 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1044 = ((g 4) * (g 14) * (g 18)) := by
  norm_num [atom1044, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1044_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (55096182136800 : Int) atom1044) := by
  rw [SparsePolynomial.eval_scale, eval_atom1044]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1044Coded : CoefficientMerge.Poly := [(nat_lit 2076, Int.ofNat (nat_lit 1))]
theorem atom1044Coded_decode : atom1044 = SparsePolynomial.decodeCubic 21 atom1044Coded := by decide +kernel
theorem atom1044Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (55096182136800 : Int) atom1044Coded) := by
  have h := atom1044_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1044Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1045 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 14, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1045 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1045 = ((g 4) * (g 14) * (g 19)) := by
  norm_num [atom1045, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1045_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48432127111200 : Int) atom1045) := by
  rw [SparsePolynomial.eval_scale, eval_atom1045]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1045Coded : CoefficientMerge.Poly := [(nat_lit 2077, Int.ofNat (nat_lit 1))]
theorem atom1045Coded_decode : atom1045 = SparsePolynomial.decodeCubic 21 atom1045Coded := by decide +kernel
theorem atom1045Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (48432127111200 : Int) atom1045Coded) := by
  have h := atom1045_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1045Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1046 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 14, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1046 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1046 = ((g 4) * (g 14) * (g 20)) := by
  norm_num [atom1046, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1046_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65831614531200 : Int) atom1046) := by
  rw [SparsePolynomial.eval_scale, eval_atom1046]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1046Coded : CoefficientMerge.Poly := [(nat_lit 2078, Int.ofNat (nat_lit 1))]
theorem atom1046Coded_decode : atom1046 = SparsePolynomial.decodeCubic 21 atom1046Coded := by decide +kernel
theorem atom1046Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (65831614531200 : Int) atom1046Coded) := by
  have h := atom1046_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1046Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1047 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1047 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1047 = ((g 4) * (g 15) * (g 15)) := by
  norm_num [atom1047, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1047_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27544406400000 : Int) atom1047) := by
  rw [SparsePolynomial.eval_scale, eval_atom1047]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1047Coded : CoefficientMerge.Poly := [(nat_lit 2094, Int.ofNat (nat_lit 1))]
theorem atom1047Coded_decode : atom1047 = SparsePolynomial.decodeCubic 21 atom1047Coded := by decide +kernel
theorem atom1047Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27544406400000 : Int) atom1047Coded) := by
  have h := atom1047_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1047Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1048 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 15, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1048 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1048 = ((g 4) * (g 15) * (g 16)) := by
  norm_num [atom1048, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1048_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49565736486000 : Int) atom1048) := by
  rw [SparsePolynomial.eval_scale, eval_atom1048]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1048Coded : CoefficientMerge.Poly := [(nat_lit 2095, Int.ofNat (nat_lit 1))]
theorem atom1048Coded_decode : atom1048 = SparsePolynomial.decodeCubic 21 atom1048Coded := by decide +kernel
theorem atom1048Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (49565736486000 : Int) atom1048Coded) := by
  have h := atom1048_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1048Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1049 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 15, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1049 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1049 = ((g 4) * (g 15) * (g 17)) := by
  norm_num [atom1049, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1049_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (69701433984000 : Int) atom1049) := by
  rw [SparsePolynomial.eval_scale, eval_atom1049]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1049Coded : CoefficientMerge.Poly := [(nat_lit 2096, Int.ofNat (nat_lit 1))]
theorem atom1049Coded_decode : atom1049 = SparsePolynomial.decodeCubic 21 atom1049Coded := by decide +kernel
theorem atom1049Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (69701433984000 : Int) atom1049Coded) := by
  have h := atom1049_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1049Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1050 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 15, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1050 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1050 = ((g 4) * (g 15) * (g 18)) := by
  norm_num [atom1050, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1050_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (67506930565200 : Int) atom1050) := by
  rw [SparsePolynomial.eval_scale, eval_atom1050]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1050Coded : CoefficientMerge.Poly := [(nat_lit 2097, Int.ofNat (nat_lit 1))]
theorem atom1050Coded_decode : atom1050 = SparsePolynomial.decodeCubic 21 atom1050Coded := by decide +kernel
theorem atom1050Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (67506930565200 : Int) atom1050Coded) := by
  have h := atom1050_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1050Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1051 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 15, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1051 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1051 = ((g 4) * (g 15) * (g 19)) := by
  norm_num [atom1051, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1051_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46776865338000 : Int) atom1051) := by
  rw [SparsePolynomial.eval_scale, eval_atom1051]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1051Coded : CoefficientMerge.Poly := [(nat_lit 2098, Int.ofNat (nat_lit 1))]
theorem atom1051Coded_decode : atom1051 = SparsePolynomial.decodeCubic 21 atom1051Coded := by decide +kernel
theorem atom1051Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (46776865338000 : Int) atom1051Coded) := by
  have h := atom1051_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1051Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1052 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 15, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1052 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1052 = ((g 4) * (g 15) * (g 20)) := by
  norm_num [atom1052, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1052_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (68668144750800 : Int) atom1052) := by
  rw [SparsePolynomial.eval_scale, eval_atom1052]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1052Coded : CoefficientMerge.Poly := [(nat_lit 2099, Int.ofNat (nat_lit 1))]
theorem atom1052Coded_decode : atom1052 = SparsePolynomial.decodeCubic 21 atom1052Coded := by decide +kernel
theorem atom1052Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (68668144750800 : Int) atom1052Coded) := by
  have h := atom1052_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1052Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1053 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 16, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1053 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1053 = ((g 4) * (g 16) * (g 16)) := by
  norm_num [atom1053, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1053_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19150031093760 : Int) atom1053) := by
  rw [SparsePolynomial.eval_scale, eval_atom1053]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1053Coded : CoefficientMerge.Poly := [(nat_lit 2116, Int.ofNat (nat_lit 1))]
theorem atom1053Coded_decode : atom1053 = SparsePolynomial.decodeCubic 21 atom1053Coded := by decide +kernel
theorem atom1053Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19150031093760 : Int) atom1053Coded) := by
  have h := atom1053_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1053Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1054 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1054 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1054 = ((g 4) * (g 16) * (g 17)) := by
  norm_num [atom1054, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1054_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (54894908250000 : Int) atom1054) := by
  rw [SparsePolynomial.eval_scale, eval_atom1054]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1054Coded : CoefficientMerge.Poly := [(nat_lit 2117, Int.ofNat (nat_lit 1))]
theorem atom1054Coded_decode : atom1054 = SparsePolynomial.decodeCubic 21 atom1054Coded := by decide +kernel
theorem atom1054Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (54894908250000 : Int) atom1054Coded) := by
  have h := atom1054_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1054Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1055 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 16, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1055 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1055 = ((g 4) * (g 16) * (g 18)) := by
  norm_num [atom1055, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1055_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (55511190567000 : Int) atom1055) := by
  rw [SparsePolynomial.eval_scale, eval_atom1055]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1055Coded : CoefficientMerge.Poly := [(nat_lit 2118, Int.ofNat (nat_lit 1))]
theorem atom1055Coded_decode : atom1055 = SparsePolynomial.decodeCubic 21 atom1055Coded := by decide +kernel
theorem atom1055Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (55511190567000 : Int) atom1055Coded) := by
  have h := atom1055_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1055Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block014 : CoefficientMerge.Poly := [(nat_lit 1931, Int.ofNat (nat_lit 37738841800608)), (nat_lit 1940, Int.ofNat (nat_lit 8316316713600)), (nat_lit 1941, Int.ofNat (nat_lit 14616092937600)), (nat_lit 1942, Int.ofNat (nat_lit 14686645276800)), (nat_lit 1943, Int.ofNat (nat_lit 14704288099200)), (nat_lit 1944, Int.ofNat (nat_lit 13399306704000)), (nat_lit 1945, Int.ofNat (nat_lit 14099031273600)), (nat_lit 1946, Int.ofNat (nat_lit 14798755843200)), (nat_lit 1947, Int.ofNat (nat_lit 23245546060800)), (nat_lit 1948, Int.ofNat (nat_lit 20719776344400)), (nat_lit 1949, Int.ofNat (nat_lit 26086557772800)), (nat_lit 1950, Int.ofNat (nat_lit 31162368207600)), (nat_lit 1951, Int.ofNat (nat_lit 37890854593200)), (nat_lit 1952, Int.ofNat (nat_lit 44619340978800)), (nat_lit 1962, Int.ofNat (nat_lit 10739741241600)), (nat_lit 1963, Int.ofNat (nat_lit 19770762816000)), (nat_lit 1964, Int.ofNat (nat_lit 19283908089600)), (nat_lit 1965, Int.ofNat (nat_lit 18160623129600)), (nat_lit 1966, Int.ofNat (nat_lit 18614864217600)), (nat_lit 1967, Int.ofNat (nat_lit 19069105305600)), (nat_lit 1968, Int.ofNat (nat_lit 27327917030400)), (nat_lit 1969, Int.ofNat (nat_lit 24967957392000)), (nat_lit 1970, Int.ofNat (nat_lit 31850587238400)), (nat_lit 1971, Int.ofNat (nat_lit 35857179388800)), (nat_lit 1972, Int.ofNat (nat_lit 42965247024000)), (nat_lit 1973, Int.ofNat (nat_lit 50073314659200)), (nat_lit 1984, Int.ofNat (nat_lit 13470986592000)), (nat_lit 1985, Int.ofNat (nat_lit 25277957510400)), (nat_lit 1986, Int.ofNat (nat_lit 23313843302400)), (nat_lit 1987, Int.ofNat (nat_lit 23354435059200)), (nat_lit 1988, Int.ofNat (nat_lit 23395026816000)), (nat_lit 1989, Int.ofNat (nat_lit 31410288000000)), (nat_lit 1990, Int.ofNat (nat_lit 28735500628800)), (nat_lit 1991, Int.ofNat (nat_lit 37614616704000)), (nat_lit 1992, Int.ofNat (nat_lit 39335264740800)), (nat_lit 1993, Int.ofNat (nat_lit 46388243563200)), (nat_lit 1994, Int.ofNat (nat_lit 53441222385600)), (nat_lit 2006, Int.ofNat (nat_lit 16246935936000)), (nat_lit 2007, Int.ofNat (nat_lit 28498236883200)), (nat_lit 2008, Int.ofNat (nat_lit 27957013459200)), (nat_lit 2009, Int.ofNat (nat_lit 27415790035200)), (nat_lit 2010, Int.ofNat (nat_lit 34868811801600)), (nat_lit 2011, Int.ofNat (nat_lit 31796949592800)), (nat_lit 2012, Int.ofNat (nat_lit 42754799001600)), (nat_lit 2013, Int.ofNat (nat_lit 41641715556000)), (nat_lit 2014, Int.ofNat (nat_lit 48385300672800)), (nat_lit 2015, Int.ofNat (nat_lit 55128885789600)), (nat_lit 2028, Int.ofNat (nat_lit 17118445881600)), (nat_lit 2029, Int.ofNat (nat_lit 32518507392000)), (nat_lit 2030, Int.ofNat (nat_lit 31227302937600)), (nat_lit 2031, Int.ofNat (nat_lit 34633735248000)), (nat_lit 2032, Int.ofNat (nat_lit 33705364364000)), (nat_lit 2033, Int.ofNat (nat_lit 43390369097600)), (nat_lit 2034, Int.ofNat (nat_lit 42915361938400)), (nat_lit 2035, Int.ofNat (nat_lit 48592346426400)), (nat_lit 2036, Int.ofNat (nat_lit 55028408400000)), (nat_lit 2050, Int.ofNat (nat_lit 19975700563200)), (nat_lit 2051, Int.ofNat (nat_lit 36571516070400)), (nat_lit 2052, Int.ofNat (nat_lit 38601069393600)), (nat_lit 2053, Int.ofNat (nat_lit 36159816938400)), (nat_lit 2054, Int.ofNat (nat_lit 47594873289600)), (nat_lit 2055, Int.ofNat (nat_lit 47799330616800)), (nat_lit 2056, Int.ofNat (nat_lit 46286873474400)), (nat_lit 2057, Int.ofNat (nat_lit 58138510147200)), (nat_lit 2072, Int.ofNat (nat_lit 23439806611200)), (nat_lit 2073, Int.ofNat (nat_lit 42456561436800)), (nat_lit 2074, Int.ofNat (nat_lit 38495120076000)), (nat_lit 2075, Int.ofNat (nat_lit 53992907337600)), (nat_lit 2076, Int.ofNat (nat_lit 55096182136800)), (nat_lit 2077, Int.ofNat (nat_lit 48432127111200)), (nat_lit 2078, Int.ofNat (nat_lit 65831614531200)), (nat_lit 2094, Int.ofNat (nat_lit 27544406400000)), (nat_lit 2095, Int.ofNat (nat_lit 49565736486000)), (nat_lit 2096, Int.ofNat (nat_lit 69701433984000)), (nat_lit 2097, Int.ofNat (nat_lit 67506930565200)), (nat_lit 2098, Int.ofNat (nat_lit 46776865338000)), (nat_lit 2099, Int.ofNat (nat_lit 68668144750800)), (nat_lit 2116, Int.ofNat (nat_lit 19150031093760)), (nat_lit 2117, Int.ofNat (nat_lit 54894908250000)), (nat_lit 2118, Int.ofNat (nat_lit 55511190567000))]
def block014_data_flat000 : CoefficientMerge.Poly := [(nat_lit 1931, Int.ofNat (nat_lit 37738841800608))]
theorem block014_data_flat000_step : block014_data_flat000 = (CoefficientMerge.scale (37738841800608 : Int) atom0976Coded) := by decide +kernel
theorem block014_data_flat000_original : block014_data_flat000 = (CoefficientMerge.scale (37738841800608 : Int) atom0976Coded) := by
  rw [block014_data_flat000_step]
def block014_data_flat001 : CoefficientMerge.Poly := [(nat_lit 1940, Int.ofNat (nat_lit 8316316713600))]
theorem block014_data_flat001_step : block014_data_flat001 = (CoefficientMerge.scale (8316316713600 : Int) atom0977Coded) := by decide +kernel
theorem block014_data_flat001_original : block014_data_flat001 = (CoefficientMerge.scale (8316316713600 : Int) atom0977Coded) := by
  rw [block014_data_flat001_step]
def block014_data_flat002 : CoefficientMerge.Poly := [(nat_lit 1931, Int.ofNat (nat_lit 37738841800608)), (nat_lit 1940, Int.ofNat (nat_lit 8316316713600))]
theorem block014_data_flat002_step : block014_data_flat002 = (CoefficientMerge.fastMerge block014_data_flat000 block014_data_flat001) := by decide +kernel
theorem block014_data_flat002_original : block014_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (37738841800608 : Int) atom0976Coded) (CoefficientMerge.scale (8316316713600 : Int) atom0977Coded)) := by
  rw [block014_data_flat002_step, block014_data_flat000_original, block014_data_flat001_original]
def block014_data_flat003 : CoefficientMerge.Poly := [(nat_lit 1941, Int.ofNat (nat_lit 14616092937600))]
theorem block014_data_flat003_step : block014_data_flat003 = (CoefficientMerge.scale (14616092937600 : Int) atom0978Coded) := by decide +kernel
theorem block014_data_flat003_original : block014_data_flat003 = (CoefficientMerge.scale (14616092937600 : Int) atom0978Coded) := by
  rw [block014_data_flat003_step]
def block014_data_flat004 : CoefficientMerge.Poly := [(nat_lit 1942, Int.ofNat (nat_lit 14686645276800))]
theorem block014_data_flat004_step : block014_data_flat004 = (CoefficientMerge.scale (14686645276800 : Int) atom0979Coded) := by decide +kernel
theorem block014_data_flat004_original : block014_data_flat004 = (CoefficientMerge.scale (14686645276800 : Int) atom0979Coded) := by
  rw [block014_data_flat004_step]
def block014_data_flat005 : CoefficientMerge.Poly := [(nat_lit 1943, Int.ofNat (nat_lit 14704288099200))]
theorem block014_data_flat005_step : block014_data_flat005 = (CoefficientMerge.scale (14704288099200 : Int) atom0980Coded) := by decide +kernel
theorem block014_data_flat005_original : block014_data_flat005 = (CoefficientMerge.scale (14704288099200 : Int) atom0980Coded) := by
  rw [block014_data_flat005_step]
def block014_data_flat006 : CoefficientMerge.Poly := [(nat_lit 1942, Int.ofNat (nat_lit 14686645276800)), (nat_lit 1943, Int.ofNat (nat_lit 14704288099200))]
theorem block014_data_flat006_step : block014_data_flat006 = (CoefficientMerge.fastMerge block014_data_flat004 block014_data_flat005) := by decide +kernel
theorem block014_data_flat006_original : block014_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (14686645276800 : Int) atom0979Coded) (CoefficientMerge.scale (14704288099200 : Int) atom0980Coded)) := by
  rw [block014_data_flat006_step, block014_data_flat004_original, block014_data_flat005_original]
def block014_data_flat007 : CoefficientMerge.Poly := [(nat_lit 1941, Int.ofNat (nat_lit 14616092937600)), (nat_lit 1942, Int.ofNat (nat_lit 14686645276800)), (nat_lit 1943, Int.ofNat (nat_lit 14704288099200))]
theorem block014_data_flat007_step : block014_data_flat007 = (CoefficientMerge.fastMerge block014_data_flat003 block014_data_flat006) := by decide +kernel
theorem block014_data_flat007_original : block014_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (14616092937600 : Int) atom0978Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14686645276800 : Int) atom0979Coded) (CoefficientMerge.scale (14704288099200 : Int) atom0980Coded))) := by
  rw [block014_data_flat007_step, block014_data_flat003_original, block014_data_flat006_original]
def block014_data_flat008 : CoefficientMerge.Poly := [(nat_lit 1931, Int.ofNat (nat_lit 37738841800608)), (nat_lit 1940, Int.ofNat (nat_lit 8316316713600)), (nat_lit 1941, Int.ofNat (nat_lit 14616092937600)), (nat_lit 1942, Int.ofNat (nat_lit 14686645276800)), (nat_lit 1943, Int.ofNat (nat_lit 14704288099200))]
theorem block014_data_flat008_step : block014_data_flat008 = (CoefficientMerge.fastMerge block014_data_flat002 block014_data_flat007) := by decide +kernel
theorem block014_data_flat008_original : block014_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37738841800608 : Int) atom0976Coded) (CoefficientMerge.scale (8316316713600 : Int) atom0977Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14616092937600 : Int) atom0978Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14686645276800 : Int) atom0979Coded) (CoefficientMerge.scale (14704288099200 : Int) atom0980Coded)))) := by
  rw [block014_data_flat008_step, block014_data_flat002_original, block014_data_flat007_original]
def block014_data_flat009 : CoefficientMerge.Poly := [(nat_lit 1944, Int.ofNat (nat_lit 13399306704000))]
theorem block014_data_flat009_step : block014_data_flat009 = (CoefficientMerge.scale (13399306704000 : Int) atom0981Coded) := by decide +kernel
theorem block014_data_flat009_original : block014_data_flat009 = (CoefficientMerge.scale (13399306704000 : Int) atom0981Coded) := by
  rw [block014_data_flat009_step]
def block014_data_flat010 : CoefficientMerge.Poly := [(nat_lit 1945, Int.ofNat (nat_lit 14099031273600))]
theorem block014_data_flat010_step : block014_data_flat010 = (CoefficientMerge.scale (14099031273600 : Int) atom0982Coded) := by decide +kernel
theorem block014_data_flat010_original : block014_data_flat010 = (CoefficientMerge.scale (14099031273600 : Int) atom0982Coded) := by
  rw [block014_data_flat010_step]
def block014_data_flat011 : CoefficientMerge.Poly := [(nat_lit 1944, Int.ofNat (nat_lit 13399306704000)), (nat_lit 1945, Int.ofNat (nat_lit 14099031273600))]
theorem block014_data_flat011_step : block014_data_flat011 = (CoefficientMerge.fastMerge block014_data_flat009 block014_data_flat010) := by decide +kernel
theorem block014_data_flat011_original : block014_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (13399306704000 : Int) atom0981Coded) (CoefficientMerge.scale (14099031273600 : Int) atom0982Coded)) := by
  rw [block014_data_flat011_step, block014_data_flat009_original, block014_data_flat010_original]
def block014_data_flat012 : CoefficientMerge.Poly := [(nat_lit 1946, Int.ofNat (nat_lit 14798755843200))]
theorem block014_data_flat012_step : block014_data_flat012 = (CoefficientMerge.scale (14798755843200 : Int) atom0983Coded) := by decide +kernel
theorem block014_data_flat012_original : block014_data_flat012 = (CoefficientMerge.scale (14798755843200 : Int) atom0983Coded) := by
  rw [block014_data_flat012_step]
def block014_data_flat013 : CoefficientMerge.Poly := [(nat_lit 1947, Int.ofNat (nat_lit 23245546060800))]
theorem block014_data_flat013_step : block014_data_flat013 = (CoefficientMerge.scale (23245546060800 : Int) atom0984Coded) := by decide +kernel
theorem block014_data_flat013_original : block014_data_flat013 = (CoefficientMerge.scale (23245546060800 : Int) atom0984Coded) := by
  rw [block014_data_flat013_step]
def block014_data_flat014 : CoefficientMerge.Poly := [(nat_lit 1948, Int.ofNat (nat_lit 20719776344400))]
theorem block014_data_flat014_step : block014_data_flat014 = (CoefficientMerge.scale (20719776344400 : Int) atom0985Coded) := by decide +kernel
theorem block014_data_flat014_original : block014_data_flat014 = (CoefficientMerge.scale (20719776344400 : Int) atom0985Coded) := by
  rw [block014_data_flat014_step]
def block014_data_flat015 : CoefficientMerge.Poly := [(nat_lit 1947, Int.ofNat (nat_lit 23245546060800)), (nat_lit 1948, Int.ofNat (nat_lit 20719776344400))]
theorem block014_data_flat015_step : block014_data_flat015 = (CoefficientMerge.fastMerge block014_data_flat013 block014_data_flat014) := by decide +kernel
theorem block014_data_flat015_original : block014_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (23245546060800 : Int) atom0984Coded) (CoefficientMerge.scale (20719776344400 : Int) atom0985Coded)) := by
  rw [block014_data_flat015_step, block014_data_flat013_original, block014_data_flat014_original]
def block014_data_flat016 : CoefficientMerge.Poly := [(nat_lit 1946, Int.ofNat (nat_lit 14798755843200)), (nat_lit 1947, Int.ofNat (nat_lit 23245546060800)), (nat_lit 1948, Int.ofNat (nat_lit 20719776344400))]
theorem block014_data_flat016_step : block014_data_flat016 = (CoefficientMerge.fastMerge block014_data_flat012 block014_data_flat015) := by decide +kernel
theorem block014_data_flat016_original : block014_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (14798755843200 : Int) atom0983Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23245546060800 : Int) atom0984Coded) (CoefficientMerge.scale (20719776344400 : Int) atom0985Coded))) := by
  rw [block014_data_flat016_step, block014_data_flat012_original, block014_data_flat015_original]
def block014_data_flat017 : CoefficientMerge.Poly := [(nat_lit 1944, Int.ofNat (nat_lit 13399306704000)), (nat_lit 1945, Int.ofNat (nat_lit 14099031273600)), (nat_lit 1946, Int.ofNat (nat_lit 14798755843200)), (nat_lit 1947, Int.ofNat (nat_lit 23245546060800)), (nat_lit 1948, Int.ofNat (nat_lit 20719776344400))]
theorem block014_data_flat017_step : block014_data_flat017 = (CoefficientMerge.fastMerge block014_data_flat011 block014_data_flat016) := by decide +kernel
theorem block014_data_flat017_original : block014_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13399306704000 : Int) atom0981Coded) (CoefficientMerge.scale (14099031273600 : Int) atom0982Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14798755843200 : Int) atom0983Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23245546060800 : Int) atom0984Coded) (CoefficientMerge.scale (20719776344400 : Int) atom0985Coded)))) := by
  rw [block014_data_flat017_step, block014_data_flat011_original, block014_data_flat016_original]
def block014_data_flat018 : CoefficientMerge.Poly := [(nat_lit 1931, Int.ofNat (nat_lit 37738841800608)), (nat_lit 1940, Int.ofNat (nat_lit 8316316713600)), (nat_lit 1941, Int.ofNat (nat_lit 14616092937600)), (nat_lit 1942, Int.ofNat (nat_lit 14686645276800)), (nat_lit 1943, Int.ofNat (nat_lit 14704288099200)), (nat_lit 1944, Int.ofNat (nat_lit 13399306704000)), (nat_lit 1945, Int.ofNat (nat_lit 14099031273600)), (nat_lit 1946, Int.ofNat (nat_lit 14798755843200)), (nat_lit 1947, Int.ofNat (nat_lit 23245546060800)), (nat_lit 1948, Int.ofNat (nat_lit 20719776344400))]
theorem block014_data_flat018_step : block014_data_flat018 = (CoefficientMerge.fastMerge block014_data_flat008 block014_data_flat017) := by decide +kernel
theorem block014_data_flat018_original : block014_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37738841800608 : Int) atom0976Coded) (CoefficientMerge.scale (8316316713600 : Int) atom0977Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14616092937600 : Int) atom0978Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14686645276800 : Int) atom0979Coded) (CoefficientMerge.scale (14704288099200 : Int) atom0980Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13399306704000 : Int) atom0981Coded) (CoefficientMerge.scale (14099031273600 : Int) atom0982Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14798755843200 : Int) atom0983Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23245546060800 : Int) atom0984Coded) (CoefficientMerge.scale (20719776344400 : Int) atom0985Coded))))) := by
  rw [block014_data_flat018_step, block014_data_flat008_original, block014_data_flat017_original]
def block014_data_flat019 : CoefficientMerge.Poly := [(nat_lit 1949, Int.ofNat (nat_lit 26086557772800))]
theorem block014_data_flat019_step : block014_data_flat019 = (CoefficientMerge.scale (26086557772800 : Int) atom0986Coded) := by decide +kernel
theorem block014_data_flat019_original : block014_data_flat019 = (CoefficientMerge.scale (26086557772800 : Int) atom0986Coded) := by
  rw [block014_data_flat019_step]
def block014_data_flat020 : CoefficientMerge.Poly := [(nat_lit 1950, Int.ofNat (nat_lit 31162368207600))]
theorem block014_data_flat020_step : block014_data_flat020 = (CoefficientMerge.scale (31162368207600 : Int) atom0987Coded) := by decide +kernel
theorem block014_data_flat020_original : block014_data_flat020 = (CoefficientMerge.scale (31162368207600 : Int) atom0987Coded) := by
  rw [block014_data_flat020_step]
def block014_data_flat021 : CoefficientMerge.Poly := [(nat_lit 1949, Int.ofNat (nat_lit 26086557772800)), (nat_lit 1950, Int.ofNat (nat_lit 31162368207600))]
theorem block014_data_flat021_step : block014_data_flat021 = (CoefficientMerge.fastMerge block014_data_flat019 block014_data_flat020) := by decide +kernel
theorem block014_data_flat021_original : block014_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (26086557772800 : Int) atom0986Coded) (CoefficientMerge.scale (31162368207600 : Int) atom0987Coded)) := by
  rw [block014_data_flat021_step, block014_data_flat019_original, block014_data_flat020_original]
def block014_data_flat022 : CoefficientMerge.Poly := [(nat_lit 1951, Int.ofNat (nat_lit 37890854593200))]
theorem block014_data_flat022_step : block014_data_flat022 = (CoefficientMerge.scale (37890854593200 : Int) atom0988Coded) := by decide +kernel
theorem block014_data_flat022_original : block014_data_flat022 = (CoefficientMerge.scale (37890854593200 : Int) atom0988Coded) := by
  rw [block014_data_flat022_step]
def block014_data_flat023 : CoefficientMerge.Poly := [(nat_lit 1952, Int.ofNat (nat_lit 44619340978800))]
theorem block014_data_flat023_step : block014_data_flat023 = (CoefficientMerge.scale (44619340978800 : Int) atom0989Coded) := by decide +kernel
theorem block014_data_flat023_original : block014_data_flat023 = (CoefficientMerge.scale (44619340978800 : Int) atom0989Coded) := by
  rw [block014_data_flat023_step]
def block014_data_flat024 : CoefficientMerge.Poly := [(nat_lit 1962, Int.ofNat (nat_lit 10739741241600))]
theorem block014_data_flat024_step : block014_data_flat024 = (CoefficientMerge.scale (10739741241600 : Int) atom0990Coded) := by decide +kernel
theorem block014_data_flat024_original : block014_data_flat024 = (CoefficientMerge.scale (10739741241600 : Int) atom0990Coded) := by
  rw [block014_data_flat024_step]
def block014_data_flat025 : CoefficientMerge.Poly := [(nat_lit 1952, Int.ofNat (nat_lit 44619340978800)), (nat_lit 1962, Int.ofNat (nat_lit 10739741241600))]
theorem block014_data_flat025_step : block014_data_flat025 = (CoefficientMerge.fastMerge block014_data_flat023 block014_data_flat024) := by decide +kernel
theorem block014_data_flat025_original : block014_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (44619340978800 : Int) atom0989Coded) (CoefficientMerge.scale (10739741241600 : Int) atom0990Coded)) := by
  rw [block014_data_flat025_step, block014_data_flat023_original, block014_data_flat024_original]
def block014_data_flat026 : CoefficientMerge.Poly := [(nat_lit 1951, Int.ofNat (nat_lit 37890854593200)), (nat_lit 1952, Int.ofNat (nat_lit 44619340978800)), (nat_lit 1962, Int.ofNat (nat_lit 10739741241600))]
theorem block014_data_flat026_step : block014_data_flat026 = (CoefficientMerge.fastMerge block014_data_flat022 block014_data_flat025) := by decide +kernel
theorem block014_data_flat026_original : block014_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (37890854593200 : Int) atom0988Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44619340978800 : Int) atom0989Coded) (CoefficientMerge.scale (10739741241600 : Int) atom0990Coded))) := by
  rw [block014_data_flat026_step, block014_data_flat022_original, block014_data_flat025_original]
def block014_data_flat027 : CoefficientMerge.Poly := [(nat_lit 1949, Int.ofNat (nat_lit 26086557772800)), (nat_lit 1950, Int.ofNat (nat_lit 31162368207600)), (nat_lit 1951, Int.ofNat (nat_lit 37890854593200)), (nat_lit 1952, Int.ofNat (nat_lit 44619340978800)), (nat_lit 1962, Int.ofNat (nat_lit 10739741241600))]
theorem block014_data_flat027_step : block014_data_flat027 = (CoefficientMerge.fastMerge block014_data_flat021 block014_data_flat026) := by decide +kernel
theorem block014_data_flat027_original : block014_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26086557772800 : Int) atom0986Coded) (CoefficientMerge.scale (31162368207600 : Int) atom0987Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37890854593200 : Int) atom0988Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44619340978800 : Int) atom0989Coded) (CoefficientMerge.scale (10739741241600 : Int) atom0990Coded)))) := by
  rw [block014_data_flat027_step, block014_data_flat021_original, block014_data_flat026_original]
def block014_data_flat028 : CoefficientMerge.Poly := [(nat_lit 1963, Int.ofNat (nat_lit 19770762816000))]
theorem block014_data_flat028_step : block014_data_flat028 = (CoefficientMerge.scale (19770762816000 : Int) atom0991Coded) := by decide +kernel
theorem block014_data_flat028_original : block014_data_flat028 = (CoefficientMerge.scale (19770762816000 : Int) atom0991Coded) := by
  rw [block014_data_flat028_step]
def block014_data_flat029 : CoefficientMerge.Poly := [(nat_lit 1964, Int.ofNat (nat_lit 19283908089600))]
theorem block014_data_flat029_step : block014_data_flat029 = (CoefficientMerge.scale (19283908089600 : Int) atom0992Coded) := by decide +kernel
theorem block014_data_flat029_original : block014_data_flat029 = (CoefficientMerge.scale (19283908089600 : Int) atom0992Coded) := by
  rw [block014_data_flat029_step]
def block014_data_flat030 : CoefficientMerge.Poly := [(nat_lit 1963, Int.ofNat (nat_lit 19770762816000)), (nat_lit 1964, Int.ofNat (nat_lit 19283908089600))]
theorem block014_data_flat030_step : block014_data_flat030 = (CoefficientMerge.fastMerge block014_data_flat028 block014_data_flat029) := by decide +kernel
theorem block014_data_flat030_original : block014_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (19770762816000 : Int) atom0991Coded) (CoefficientMerge.scale (19283908089600 : Int) atom0992Coded)) := by
  rw [block014_data_flat030_step, block014_data_flat028_original, block014_data_flat029_original]
def block014_data_flat031 : CoefficientMerge.Poly := [(nat_lit 1965, Int.ofNat (nat_lit 18160623129600))]
theorem block014_data_flat031_step : block014_data_flat031 = (CoefficientMerge.scale (18160623129600 : Int) atom0993Coded) := by decide +kernel
theorem block014_data_flat031_original : block014_data_flat031 = (CoefficientMerge.scale (18160623129600 : Int) atom0993Coded) := by
  rw [block014_data_flat031_step]
def block014_data_flat032 : CoefficientMerge.Poly := [(nat_lit 1966, Int.ofNat (nat_lit 18614864217600))]
theorem block014_data_flat032_step : block014_data_flat032 = (CoefficientMerge.scale (18614864217600 : Int) atom0994Coded) := by decide +kernel
theorem block014_data_flat032_original : block014_data_flat032 = (CoefficientMerge.scale (18614864217600 : Int) atom0994Coded) := by
  rw [block014_data_flat032_step]
def block014_data_flat033 : CoefficientMerge.Poly := [(nat_lit 1967, Int.ofNat (nat_lit 19069105305600))]
theorem block014_data_flat033_step : block014_data_flat033 = (CoefficientMerge.scale (19069105305600 : Int) atom0995Coded) := by decide +kernel
theorem block014_data_flat033_original : block014_data_flat033 = (CoefficientMerge.scale (19069105305600 : Int) atom0995Coded) := by
  rw [block014_data_flat033_step]
def block014_data_flat034 : CoefficientMerge.Poly := [(nat_lit 1966, Int.ofNat (nat_lit 18614864217600)), (nat_lit 1967, Int.ofNat (nat_lit 19069105305600))]
theorem block014_data_flat034_step : block014_data_flat034 = (CoefficientMerge.fastMerge block014_data_flat032 block014_data_flat033) := by decide +kernel
theorem block014_data_flat034_original : block014_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (18614864217600 : Int) atom0994Coded) (CoefficientMerge.scale (19069105305600 : Int) atom0995Coded)) := by
  rw [block014_data_flat034_step, block014_data_flat032_original, block014_data_flat033_original]
def block014_data_flat035 : CoefficientMerge.Poly := [(nat_lit 1965, Int.ofNat (nat_lit 18160623129600)), (nat_lit 1966, Int.ofNat (nat_lit 18614864217600)), (nat_lit 1967, Int.ofNat (nat_lit 19069105305600))]
theorem block014_data_flat035_step : block014_data_flat035 = (CoefficientMerge.fastMerge block014_data_flat031 block014_data_flat034) := by decide +kernel
theorem block014_data_flat035_original : block014_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (18160623129600 : Int) atom0993Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18614864217600 : Int) atom0994Coded) (CoefficientMerge.scale (19069105305600 : Int) atom0995Coded))) := by
  rw [block014_data_flat035_step, block014_data_flat031_original, block014_data_flat034_original]
def block014_data_flat036 : CoefficientMerge.Poly := [(nat_lit 1963, Int.ofNat (nat_lit 19770762816000)), (nat_lit 1964, Int.ofNat (nat_lit 19283908089600)), (nat_lit 1965, Int.ofNat (nat_lit 18160623129600)), (nat_lit 1966, Int.ofNat (nat_lit 18614864217600)), (nat_lit 1967, Int.ofNat (nat_lit 19069105305600))]
theorem block014_data_flat036_step : block014_data_flat036 = (CoefficientMerge.fastMerge block014_data_flat030 block014_data_flat035) := by decide +kernel
theorem block014_data_flat036_original : block014_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19770762816000 : Int) atom0991Coded) (CoefficientMerge.scale (19283908089600 : Int) atom0992Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18160623129600 : Int) atom0993Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18614864217600 : Int) atom0994Coded) (CoefficientMerge.scale (19069105305600 : Int) atom0995Coded)))) := by
  rw [block014_data_flat036_step, block014_data_flat030_original, block014_data_flat035_original]
def block014_data_flat037 : CoefficientMerge.Poly := [(nat_lit 1949, Int.ofNat (nat_lit 26086557772800)), (nat_lit 1950, Int.ofNat (nat_lit 31162368207600)), (nat_lit 1951, Int.ofNat (nat_lit 37890854593200)), (nat_lit 1952, Int.ofNat (nat_lit 44619340978800)), (nat_lit 1962, Int.ofNat (nat_lit 10739741241600)), (nat_lit 1963, Int.ofNat (nat_lit 19770762816000)), (nat_lit 1964, Int.ofNat (nat_lit 19283908089600)), (nat_lit 1965, Int.ofNat (nat_lit 18160623129600)), (nat_lit 1966, Int.ofNat (nat_lit 18614864217600)), (nat_lit 1967, Int.ofNat (nat_lit 19069105305600))]
theorem block014_data_flat037_step : block014_data_flat037 = (CoefficientMerge.fastMerge block014_data_flat027 block014_data_flat036) := by decide +kernel
theorem block014_data_flat037_original : block014_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26086557772800 : Int) atom0986Coded) (CoefficientMerge.scale (31162368207600 : Int) atom0987Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37890854593200 : Int) atom0988Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44619340978800 : Int) atom0989Coded) (CoefficientMerge.scale (10739741241600 : Int) atom0990Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19770762816000 : Int) atom0991Coded) (CoefficientMerge.scale (19283908089600 : Int) atom0992Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18160623129600 : Int) atom0993Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18614864217600 : Int) atom0994Coded) (CoefficientMerge.scale (19069105305600 : Int) atom0995Coded))))) := by
  rw [block014_data_flat037_step, block014_data_flat027_original, block014_data_flat036_original]
def block014_data_flat038 : CoefficientMerge.Poly := [(nat_lit 1931, Int.ofNat (nat_lit 37738841800608)), (nat_lit 1940, Int.ofNat (nat_lit 8316316713600)), (nat_lit 1941, Int.ofNat (nat_lit 14616092937600)), (nat_lit 1942, Int.ofNat (nat_lit 14686645276800)), (nat_lit 1943, Int.ofNat (nat_lit 14704288099200)), (nat_lit 1944, Int.ofNat (nat_lit 13399306704000)), (nat_lit 1945, Int.ofNat (nat_lit 14099031273600)), (nat_lit 1946, Int.ofNat (nat_lit 14798755843200)), (nat_lit 1947, Int.ofNat (nat_lit 23245546060800)), (nat_lit 1948, Int.ofNat (nat_lit 20719776344400)), (nat_lit 1949, Int.ofNat (nat_lit 26086557772800)), (nat_lit 1950, Int.ofNat (nat_lit 31162368207600)), (nat_lit 1951, Int.ofNat (nat_lit 37890854593200)), (nat_lit 1952, Int.ofNat (nat_lit 44619340978800)), (nat_lit 1962, Int.ofNat (nat_lit 10739741241600)), (nat_lit 1963, Int.ofNat (nat_lit 19770762816000)), (nat_lit 1964, Int.ofNat (nat_lit 19283908089600)), (nat_lit 1965, Int.ofNat (nat_lit 18160623129600)), (nat_lit 1966, Int.ofNat (nat_lit 18614864217600)), (nat_lit 1967, Int.ofNat (nat_lit 19069105305600))]
theorem block014_data_flat038_step : block014_data_flat038 = (CoefficientMerge.fastMerge block014_data_flat018 block014_data_flat037) := by decide +kernel
theorem block014_data_flat038_original : block014_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37738841800608 : Int) atom0976Coded) (CoefficientMerge.scale (8316316713600 : Int) atom0977Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14616092937600 : Int) atom0978Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14686645276800 : Int) atom0979Coded) (CoefficientMerge.scale (14704288099200 : Int) atom0980Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13399306704000 : Int) atom0981Coded) (CoefficientMerge.scale (14099031273600 : Int) atom0982Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14798755843200 : Int) atom0983Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23245546060800 : Int) atom0984Coded) (CoefficientMerge.scale (20719776344400 : Int) atom0985Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26086557772800 : Int) atom0986Coded) (CoefficientMerge.scale (31162368207600 : Int) atom0987Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37890854593200 : Int) atom0988Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44619340978800 : Int) atom0989Coded) (CoefficientMerge.scale (10739741241600 : Int) atom0990Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19770762816000 : Int) atom0991Coded) (CoefficientMerge.scale (19283908089600 : Int) atom0992Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18160623129600 : Int) atom0993Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18614864217600 : Int) atom0994Coded) (CoefficientMerge.scale (19069105305600 : Int) atom0995Coded)))))) := by
  rw [block014_data_flat038_step, block014_data_flat018_original, block014_data_flat037_original]
def block014_data_flat039 : CoefficientMerge.Poly := [(nat_lit 1968, Int.ofNat (nat_lit 27327917030400))]
theorem block014_data_flat039_step : block014_data_flat039 = (CoefficientMerge.scale (27327917030400 : Int) atom0996Coded) := by decide +kernel
theorem block014_data_flat039_original : block014_data_flat039 = (CoefficientMerge.scale (27327917030400 : Int) atom0996Coded) := by
  rw [block014_data_flat039_step]
def block014_data_flat040 : CoefficientMerge.Poly := [(nat_lit 1969, Int.ofNat (nat_lit 24967957392000))]
theorem block014_data_flat040_step : block014_data_flat040 = (CoefficientMerge.scale (24967957392000 : Int) atom0997Coded) := by decide +kernel
theorem block014_data_flat040_original : block014_data_flat040 = (CoefficientMerge.scale (24967957392000 : Int) atom0997Coded) := by
  rw [block014_data_flat040_step]
def block014_data_flat041 : CoefficientMerge.Poly := [(nat_lit 1968, Int.ofNat (nat_lit 27327917030400)), (nat_lit 1969, Int.ofNat (nat_lit 24967957392000))]
theorem block014_data_flat041_step : block014_data_flat041 = (CoefficientMerge.fastMerge block014_data_flat039 block014_data_flat040) := by decide +kernel
theorem block014_data_flat041_original : block014_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (27327917030400 : Int) atom0996Coded) (CoefficientMerge.scale (24967957392000 : Int) atom0997Coded)) := by
  rw [block014_data_flat041_step, block014_data_flat039_original, block014_data_flat040_original]
def block014_data_flat042 : CoefficientMerge.Poly := [(nat_lit 1970, Int.ofNat (nat_lit 31850587238400))]
theorem block014_data_flat042_step : block014_data_flat042 = (CoefficientMerge.scale (31850587238400 : Int) atom0998Coded) := by decide +kernel
theorem block014_data_flat042_original : block014_data_flat042 = (CoefficientMerge.scale (31850587238400 : Int) atom0998Coded) := by
  rw [block014_data_flat042_step]
def block014_data_flat043 : CoefficientMerge.Poly := [(nat_lit 1971, Int.ofNat (nat_lit 35857179388800))]
theorem block014_data_flat043_step : block014_data_flat043 = (CoefficientMerge.scale (35857179388800 : Int) atom0999Coded) := by decide +kernel
theorem block014_data_flat043_original : block014_data_flat043 = (CoefficientMerge.scale (35857179388800 : Int) atom0999Coded) := by
  rw [block014_data_flat043_step]
def block014_data_flat044 : CoefficientMerge.Poly := [(nat_lit 1972, Int.ofNat (nat_lit 42965247024000))]
theorem block014_data_flat044_step : block014_data_flat044 = (CoefficientMerge.scale (42965247024000 : Int) atom1000Coded) := by decide +kernel
theorem block014_data_flat044_original : block014_data_flat044 = (CoefficientMerge.scale (42965247024000 : Int) atom1000Coded) := by
  rw [block014_data_flat044_step]
def block014_data_flat045 : CoefficientMerge.Poly := [(nat_lit 1971, Int.ofNat (nat_lit 35857179388800)), (nat_lit 1972, Int.ofNat (nat_lit 42965247024000))]
theorem block014_data_flat045_step : block014_data_flat045 = (CoefficientMerge.fastMerge block014_data_flat043 block014_data_flat044) := by decide +kernel
theorem block014_data_flat045_original : block014_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (35857179388800 : Int) atom0999Coded) (CoefficientMerge.scale (42965247024000 : Int) atom1000Coded)) := by
  rw [block014_data_flat045_step, block014_data_flat043_original, block014_data_flat044_original]
def block014_data_flat046 : CoefficientMerge.Poly := [(nat_lit 1970, Int.ofNat (nat_lit 31850587238400)), (nat_lit 1971, Int.ofNat (nat_lit 35857179388800)), (nat_lit 1972, Int.ofNat (nat_lit 42965247024000))]
theorem block014_data_flat046_step : block014_data_flat046 = (CoefficientMerge.fastMerge block014_data_flat042 block014_data_flat045) := by decide +kernel
theorem block014_data_flat046_original : block014_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (31850587238400 : Int) atom0998Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35857179388800 : Int) atom0999Coded) (CoefficientMerge.scale (42965247024000 : Int) atom1000Coded))) := by
  rw [block014_data_flat046_step, block014_data_flat042_original, block014_data_flat045_original]
def block014_data_flat047 : CoefficientMerge.Poly := [(nat_lit 1968, Int.ofNat (nat_lit 27327917030400)), (nat_lit 1969, Int.ofNat (nat_lit 24967957392000)), (nat_lit 1970, Int.ofNat (nat_lit 31850587238400)), (nat_lit 1971, Int.ofNat (nat_lit 35857179388800)), (nat_lit 1972, Int.ofNat (nat_lit 42965247024000))]
theorem block014_data_flat047_step : block014_data_flat047 = (CoefficientMerge.fastMerge block014_data_flat041 block014_data_flat046) := by decide +kernel
theorem block014_data_flat047_original : block014_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (27327917030400 : Int) atom0996Coded) (CoefficientMerge.scale (24967957392000 : Int) atom0997Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31850587238400 : Int) atom0998Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35857179388800 : Int) atom0999Coded) (CoefficientMerge.scale (42965247024000 : Int) atom1000Coded)))) := by
  rw [block014_data_flat047_step, block014_data_flat041_original, block014_data_flat046_original]
def block014_data_flat048 : CoefficientMerge.Poly := [(nat_lit 1973, Int.ofNat (nat_lit 50073314659200))]
theorem block014_data_flat048_step : block014_data_flat048 = (CoefficientMerge.scale (50073314659200 : Int) atom1001Coded) := by decide +kernel
theorem block014_data_flat048_original : block014_data_flat048 = (CoefficientMerge.scale (50073314659200 : Int) atom1001Coded) := by
  rw [block014_data_flat048_step]
def block014_data_flat049 : CoefficientMerge.Poly := [(nat_lit 1984, Int.ofNat (nat_lit 13470986592000))]
theorem block014_data_flat049_step : block014_data_flat049 = (CoefficientMerge.scale (13470986592000 : Int) atom1002Coded) := by decide +kernel
theorem block014_data_flat049_original : block014_data_flat049 = (CoefficientMerge.scale (13470986592000 : Int) atom1002Coded) := by
  rw [block014_data_flat049_step]
def block014_data_flat050 : CoefficientMerge.Poly := [(nat_lit 1973, Int.ofNat (nat_lit 50073314659200)), (nat_lit 1984, Int.ofNat (nat_lit 13470986592000))]
theorem block014_data_flat050_step : block014_data_flat050 = (CoefficientMerge.fastMerge block014_data_flat048 block014_data_flat049) := by decide +kernel
theorem block014_data_flat050_original : block014_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (50073314659200 : Int) atom1001Coded) (CoefficientMerge.scale (13470986592000 : Int) atom1002Coded)) := by
  rw [block014_data_flat050_step, block014_data_flat048_original, block014_data_flat049_original]
def block014_data_flat051 : CoefficientMerge.Poly := [(nat_lit 1985, Int.ofNat (nat_lit 25277957510400))]
theorem block014_data_flat051_step : block014_data_flat051 = (CoefficientMerge.scale (25277957510400 : Int) atom1003Coded) := by decide +kernel
theorem block014_data_flat051_original : block014_data_flat051 = (CoefficientMerge.scale (25277957510400 : Int) atom1003Coded) := by
  rw [block014_data_flat051_step]
def block014_data_flat052 : CoefficientMerge.Poly := [(nat_lit 1986, Int.ofNat (nat_lit 23313843302400))]
theorem block014_data_flat052_step : block014_data_flat052 = (CoefficientMerge.scale (23313843302400 : Int) atom1004Coded) := by decide +kernel
theorem block014_data_flat052_original : block014_data_flat052 = (CoefficientMerge.scale (23313843302400 : Int) atom1004Coded) := by
  rw [block014_data_flat052_step]
def block014_data_flat053 : CoefficientMerge.Poly := [(nat_lit 1987, Int.ofNat (nat_lit 23354435059200))]
theorem block014_data_flat053_step : block014_data_flat053 = (CoefficientMerge.scale (23354435059200 : Int) atom1005Coded) := by decide +kernel
theorem block014_data_flat053_original : block014_data_flat053 = (CoefficientMerge.scale (23354435059200 : Int) atom1005Coded) := by
  rw [block014_data_flat053_step]
def block014_data_flat054 : CoefficientMerge.Poly := [(nat_lit 1986, Int.ofNat (nat_lit 23313843302400)), (nat_lit 1987, Int.ofNat (nat_lit 23354435059200))]
theorem block014_data_flat054_step : block014_data_flat054 = (CoefficientMerge.fastMerge block014_data_flat052 block014_data_flat053) := by decide +kernel
theorem block014_data_flat054_original : block014_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (23313843302400 : Int) atom1004Coded) (CoefficientMerge.scale (23354435059200 : Int) atom1005Coded)) := by
  rw [block014_data_flat054_step, block014_data_flat052_original, block014_data_flat053_original]
def block014_data_flat055 : CoefficientMerge.Poly := [(nat_lit 1985, Int.ofNat (nat_lit 25277957510400)), (nat_lit 1986, Int.ofNat (nat_lit 23313843302400)), (nat_lit 1987, Int.ofNat (nat_lit 23354435059200))]
theorem block014_data_flat055_step : block014_data_flat055 = (CoefficientMerge.fastMerge block014_data_flat051 block014_data_flat054) := by decide +kernel
theorem block014_data_flat055_original : block014_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (25277957510400 : Int) atom1003Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23313843302400 : Int) atom1004Coded) (CoefficientMerge.scale (23354435059200 : Int) atom1005Coded))) := by
  rw [block014_data_flat055_step, block014_data_flat051_original, block014_data_flat054_original]
def block014_data_flat056 : CoefficientMerge.Poly := [(nat_lit 1973, Int.ofNat (nat_lit 50073314659200)), (nat_lit 1984, Int.ofNat (nat_lit 13470986592000)), (nat_lit 1985, Int.ofNat (nat_lit 25277957510400)), (nat_lit 1986, Int.ofNat (nat_lit 23313843302400)), (nat_lit 1987, Int.ofNat (nat_lit 23354435059200))]
theorem block014_data_flat056_step : block014_data_flat056 = (CoefficientMerge.fastMerge block014_data_flat050 block014_data_flat055) := by decide +kernel
theorem block014_data_flat056_original : block014_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (50073314659200 : Int) atom1001Coded) (CoefficientMerge.scale (13470986592000 : Int) atom1002Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25277957510400 : Int) atom1003Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23313843302400 : Int) atom1004Coded) (CoefficientMerge.scale (23354435059200 : Int) atom1005Coded)))) := by
  rw [block014_data_flat056_step, block014_data_flat050_original, block014_data_flat055_original]
def block014_data_flat057 : CoefficientMerge.Poly := [(nat_lit 1968, Int.ofNat (nat_lit 27327917030400)), (nat_lit 1969, Int.ofNat (nat_lit 24967957392000)), (nat_lit 1970, Int.ofNat (nat_lit 31850587238400)), (nat_lit 1971, Int.ofNat (nat_lit 35857179388800)), (nat_lit 1972, Int.ofNat (nat_lit 42965247024000)), (nat_lit 1973, Int.ofNat (nat_lit 50073314659200)), (nat_lit 1984, Int.ofNat (nat_lit 13470986592000)), (nat_lit 1985, Int.ofNat (nat_lit 25277957510400)), (nat_lit 1986, Int.ofNat (nat_lit 23313843302400)), (nat_lit 1987, Int.ofNat (nat_lit 23354435059200))]
theorem block014_data_flat057_step : block014_data_flat057 = (CoefficientMerge.fastMerge block014_data_flat047 block014_data_flat056) := by decide +kernel
theorem block014_data_flat057_original : block014_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (27327917030400 : Int) atom0996Coded) (CoefficientMerge.scale (24967957392000 : Int) atom0997Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31850587238400 : Int) atom0998Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35857179388800 : Int) atom0999Coded) (CoefficientMerge.scale (42965247024000 : Int) atom1000Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (50073314659200 : Int) atom1001Coded) (CoefficientMerge.scale (13470986592000 : Int) atom1002Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25277957510400 : Int) atom1003Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23313843302400 : Int) atom1004Coded) (CoefficientMerge.scale (23354435059200 : Int) atom1005Coded))))) := by
  rw [block014_data_flat057_step, block014_data_flat047_original, block014_data_flat056_original]
def block014_data_flat058 : CoefficientMerge.Poly := [(nat_lit 1988, Int.ofNat (nat_lit 23395026816000))]
theorem block014_data_flat058_step : block014_data_flat058 = (CoefficientMerge.scale (23395026816000 : Int) atom1006Coded) := by decide +kernel
theorem block014_data_flat058_original : block014_data_flat058 = (CoefficientMerge.scale (23395026816000 : Int) atom1006Coded) := by
  rw [block014_data_flat058_step]
def block014_data_flat059 : CoefficientMerge.Poly := [(nat_lit 1989, Int.ofNat (nat_lit 31410288000000))]
theorem block014_data_flat059_step : block014_data_flat059 = (CoefficientMerge.scale (31410288000000 : Int) atom1007Coded) := by decide +kernel
theorem block014_data_flat059_original : block014_data_flat059 = (CoefficientMerge.scale (31410288000000 : Int) atom1007Coded) := by
  rw [block014_data_flat059_step]
def block014_data_flat060 : CoefficientMerge.Poly := [(nat_lit 1988, Int.ofNat (nat_lit 23395026816000)), (nat_lit 1989, Int.ofNat (nat_lit 31410288000000))]
theorem block014_data_flat060_step : block014_data_flat060 = (CoefficientMerge.fastMerge block014_data_flat058 block014_data_flat059) := by decide +kernel
theorem block014_data_flat060_original : block014_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (23395026816000 : Int) atom1006Coded) (CoefficientMerge.scale (31410288000000 : Int) atom1007Coded)) := by
  rw [block014_data_flat060_step, block014_data_flat058_original, block014_data_flat059_original]
def block014_data_flat061 : CoefficientMerge.Poly := [(nat_lit 1990, Int.ofNat (nat_lit 28735500628800))]
theorem block014_data_flat061_step : block014_data_flat061 = (CoefficientMerge.scale (28735500628800 : Int) atom1008Coded) := by decide +kernel
theorem block014_data_flat061_original : block014_data_flat061 = (CoefficientMerge.scale (28735500628800 : Int) atom1008Coded) := by
  rw [block014_data_flat061_step]
def block014_data_flat062 : CoefficientMerge.Poly := [(nat_lit 1991, Int.ofNat (nat_lit 37614616704000))]
theorem block014_data_flat062_step : block014_data_flat062 = (CoefficientMerge.scale (37614616704000 : Int) atom1009Coded) := by decide +kernel
theorem block014_data_flat062_original : block014_data_flat062 = (CoefficientMerge.scale (37614616704000 : Int) atom1009Coded) := by
  rw [block014_data_flat062_step]
def block014_data_flat063 : CoefficientMerge.Poly := [(nat_lit 1992, Int.ofNat (nat_lit 39335264740800))]
theorem block014_data_flat063_step : block014_data_flat063 = (CoefficientMerge.scale (39335264740800 : Int) atom1010Coded) := by decide +kernel
theorem block014_data_flat063_original : block014_data_flat063 = (CoefficientMerge.scale (39335264740800 : Int) atom1010Coded) := by
  rw [block014_data_flat063_step]
def block014_data_flat064 : CoefficientMerge.Poly := [(nat_lit 1991, Int.ofNat (nat_lit 37614616704000)), (nat_lit 1992, Int.ofNat (nat_lit 39335264740800))]
theorem block014_data_flat064_step : block014_data_flat064 = (CoefficientMerge.fastMerge block014_data_flat062 block014_data_flat063) := by decide +kernel
theorem block014_data_flat064_original : block014_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (37614616704000 : Int) atom1009Coded) (CoefficientMerge.scale (39335264740800 : Int) atom1010Coded)) := by
  rw [block014_data_flat064_step, block014_data_flat062_original, block014_data_flat063_original]
def block014_data_flat065 : CoefficientMerge.Poly := [(nat_lit 1990, Int.ofNat (nat_lit 28735500628800)), (nat_lit 1991, Int.ofNat (nat_lit 37614616704000)), (nat_lit 1992, Int.ofNat (nat_lit 39335264740800))]
theorem block014_data_flat065_step : block014_data_flat065 = (CoefficientMerge.fastMerge block014_data_flat061 block014_data_flat064) := by decide +kernel
theorem block014_data_flat065_original : block014_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (28735500628800 : Int) atom1008Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37614616704000 : Int) atom1009Coded) (CoefficientMerge.scale (39335264740800 : Int) atom1010Coded))) := by
  rw [block014_data_flat065_step, block014_data_flat061_original, block014_data_flat064_original]
def block014_data_flat066 : CoefficientMerge.Poly := [(nat_lit 1988, Int.ofNat (nat_lit 23395026816000)), (nat_lit 1989, Int.ofNat (nat_lit 31410288000000)), (nat_lit 1990, Int.ofNat (nat_lit 28735500628800)), (nat_lit 1991, Int.ofNat (nat_lit 37614616704000)), (nat_lit 1992, Int.ofNat (nat_lit 39335264740800))]
theorem block014_data_flat066_step : block014_data_flat066 = (CoefficientMerge.fastMerge block014_data_flat060 block014_data_flat065) := by decide +kernel
theorem block014_data_flat066_original : block014_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23395026816000 : Int) atom1006Coded) (CoefficientMerge.scale (31410288000000 : Int) atom1007Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28735500628800 : Int) atom1008Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37614616704000 : Int) atom1009Coded) (CoefficientMerge.scale (39335264740800 : Int) atom1010Coded)))) := by
  rw [block014_data_flat066_step, block014_data_flat060_original, block014_data_flat065_original]
def block014_data_flat067 : CoefficientMerge.Poly := [(nat_lit 1993, Int.ofNat (nat_lit 46388243563200))]
theorem block014_data_flat067_step : block014_data_flat067 = (CoefficientMerge.scale (46388243563200 : Int) atom1011Coded) := by decide +kernel
theorem block014_data_flat067_original : block014_data_flat067 = (CoefficientMerge.scale (46388243563200 : Int) atom1011Coded) := by
  rw [block014_data_flat067_step]
def block014_data_flat068 : CoefficientMerge.Poly := [(nat_lit 1994, Int.ofNat (nat_lit 53441222385600))]
theorem block014_data_flat068_step : block014_data_flat068 = (CoefficientMerge.scale (53441222385600 : Int) atom1012Coded) := by decide +kernel
theorem block014_data_flat068_original : block014_data_flat068 = (CoefficientMerge.scale (53441222385600 : Int) atom1012Coded) := by
  rw [block014_data_flat068_step]
def block014_data_flat069 : CoefficientMerge.Poly := [(nat_lit 1993, Int.ofNat (nat_lit 46388243563200)), (nat_lit 1994, Int.ofNat (nat_lit 53441222385600))]
theorem block014_data_flat069_step : block014_data_flat069 = (CoefficientMerge.fastMerge block014_data_flat067 block014_data_flat068) := by decide +kernel
theorem block014_data_flat069_original : block014_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (46388243563200 : Int) atom1011Coded) (CoefficientMerge.scale (53441222385600 : Int) atom1012Coded)) := by
  rw [block014_data_flat069_step, block014_data_flat067_original, block014_data_flat068_original]
def block014_data_flat070 : CoefficientMerge.Poly := [(nat_lit 2006, Int.ofNat (nat_lit 16246935936000))]
theorem block014_data_flat070_step : block014_data_flat070 = (CoefficientMerge.scale (16246935936000 : Int) atom1013Coded) := by decide +kernel
theorem block014_data_flat070_original : block014_data_flat070 = (CoefficientMerge.scale (16246935936000 : Int) atom1013Coded) := by
  rw [block014_data_flat070_step]
def block014_data_flat071 : CoefficientMerge.Poly := [(nat_lit 2007, Int.ofNat (nat_lit 28498236883200))]
theorem block014_data_flat071_step : block014_data_flat071 = (CoefficientMerge.scale (28498236883200 : Int) atom1014Coded) := by decide +kernel
theorem block014_data_flat071_original : block014_data_flat071 = (CoefficientMerge.scale (28498236883200 : Int) atom1014Coded) := by
  rw [block014_data_flat071_step]
def block014_data_flat072 : CoefficientMerge.Poly := [(nat_lit 2008, Int.ofNat (nat_lit 27957013459200))]
theorem block014_data_flat072_step : block014_data_flat072 = (CoefficientMerge.scale (27957013459200 : Int) atom1015Coded) := by decide +kernel
theorem block014_data_flat072_original : block014_data_flat072 = (CoefficientMerge.scale (27957013459200 : Int) atom1015Coded) := by
  rw [block014_data_flat072_step]
def block014_data_flat073 : CoefficientMerge.Poly := [(nat_lit 2007, Int.ofNat (nat_lit 28498236883200)), (nat_lit 2008, Int.ofNat (nat_lit 27957013459200))]
theorem block014_data_flat073_step : block014_data_flat073 = (CoefficientMerge.fastMerge block014_data_flat071 block014_data_flat072) := by decide +kernel
theorem block014_data_flat073_original : block014_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (28498236883200 : Int) atom1014Coded) (CoefficientMerge.scale (27957013459200 : Int) atom1015Coded)) := by
  rw [block014_data_flat073_step, block014_data_flat071_original, block014_data_flat072_original]
def block014_data_flat074 : CoefficientMerge.Poly := [(nat_lit 2006, Int.ofNat (nat_lit 16246935936000)), (nat_lit 2007, Int.ofNat (nat_lit 28498236883200)), (nat_lit 2008, Int.ofNat (nat_lit 27957013459200))]
theorem block014_data_flat074_step : block014_data_flat074 = (CoefficientMerge.fastMerge block014_data_flat070 block014_data_flat073) := by decide +kernel
theorem block014_data_flat074_original : block014_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (16246935936000 : Int) atom1013Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28498236883200 : Int) atom1014Coded) (CoefficientMerge.scale (27957013459200 : Int) atom1015Coded))) := by
  rw [block014_data_flat074_step, block014_data_flat070_original, block014_data_flat073_original]
def block014_data_flat075 : CoefficientMerge.Poly := [(nat_lit 1993, Int.ofNat (nat_lit 46388243563200)), (nat_lit 1994, Int.ofNat (nat_lit 53441222385600)), (nat_lit 2006, Int.ofNat (nat_lit 16246935936000)), (nat_lit 2007, Int.ofNat (nat_lit 28498236883200)), (nat_lit 2008, Int.ofNat (nat_lit 27957013459200))]
theorem block014_data_flat075_step : block014_data_flat075 = (CoefficientMerge.fastMerge block014_data_flat069 block014_data_flat074) := by decide +kernel
theorem block014_data_flat075_original : block014_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46388243563200 : Int) atom1011Coded) (CoefficientMerge.scale (53441222385600 : Int) atom1012Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16246935936000 : Int) atom1013Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28498236883200 : Int) atom1014Coded) (CoefficientMerge.scale (27957013459200 : Int) atom1015Coded)))) := by
  rw [block014_data_flat075_step, block014_data_flat069_original, block014_data_flat074_original]
def block014_data_flat076 : CoefficientMerge.Poly := [(nat_lit 1988, Int.ofNat (nat_lit 23395026816000)), (nat_lit 1989, Int.ofNat (nat_lit 31410288000000)), (nat_lit 1990, Int.ofNat (nat_lit 28735500628800)), (nat_lit 1991, Int.ofNat (nat_lit 37614616704000)), (nat_lit 1992, Int.ofNat (nat_lit 39335264740800)), (nat_lit 1993, Int.ofNat (nat_lit 46388243563200)), (nat_lit 1994, Int.ofNat (nat_lit 53441222385600)), (nat_lit 2006, Int.ofNat (nat_lit 16246935936000)), (nat_lit 2007, Int.ofNat (nat_lit 28498236883200)), (nat_lit 2008, Int.ofNat (nat_lit 27957013459200))]
theorem block014_data_flat076_step : block014_data_flat076 = (CoefficientMerge.fastMerge block014_data_flat066 block014_data_flat075) := by decide +kernel
theorem block014_data_flat076_original : block014_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23395026816000 : Int) atom1006Coded) (CoefficientMerge.scale (31410288000000 : Int) atom1007Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28735500628800 : Int) atom1008Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37614616704000 : Int) atom1009Coded) (CoefficientMerge.scale (39335264740800 : Int) atom1010Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46388243563200 : Int) atom1011Coded) (CoefficientMerge.scale (53441222385600 : Int) atom1012Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16246935936000 : Int) atom1013Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28498236883200 : Int) atom1014Coded) (CoefficientMerge.scale (27957013459200 : Int) atom1015Coded))))) := by
  rw [block014_data_flat076_step, block014_data_flat066_original, block014_data_flat075_original]
def block014_data_flat077 : CoefficientMerge.Poly := [(nat_lit 1968, Int.ofNat (nat_lit 27327917030400)), (nat_lit 1969, Int.ofNat (nat_lit 24967957392000)), (nat_lit 1970, Int.ofNat (nat_lit 31850587238400)), (nat_lit 1971, Int.ofNat (nat_lit 35857179388800)), (nat_lit 1972, Int.ofNat (nat_lit 42965247024000)), (nat_lit 1973, Int.ofNat (nat_lit 50073314659200)), (nat_lit 1984, Int.ofNat (nat_lit 13470986592000)), (nat_lit 1985, Int.ofNat (nat_lit 25277957510400)), (nat_lit 1986, Int.ofNat (nat_lit 23313843302400)), (nat_lit 1987, Int.ofNat (nat_lit 23354435059200)), (nat_lit 1988, Int.ofNat (nat_lit 23395026816000)), (nat_lit 1989, Int.ofNat (nat_lit 31410288000000)), (nat_lit 1990, Int.ofNat (nat_lit 28735500628800)), (nat_lit 1991, Int.ofNat (nat_lit 37614616704000)), (nat_lit 1992, Int.ofNat (nat_lit 39335264740800)), (nat_lit 1993, Int.ofNat (nat_lit 46388243563200)), (nat_lit 1994, Int.ofNat (nat_lit 53441222385600)), (nat_lit 2006, Int.ofNat (nat_lit 16246935936000)), (nat_lit 2007, Int.ofNat (nat_lit 28498236883200)), (nat_lit 2008, Int.ofNat (nat_lit 27957013459200))]
theorem block014_data_flat077_step : block014_data_flat077 = (CoefficientMerge.fastMerge block014_data_flat057 block014_data_flat076) := by decide +kernel
theorem block014_data_flat077_original : block014_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (27327917030400 : Int) atom0996Coded) (CoefficientMerge.scale (24967957392000 : Int) atom0997Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31850587238400 : Int) atom0998Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35857179388800 : Int) atom0999Coded) (CoefficientMerge.scale (42965247024000 : Int) atom1000Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (50073314659200 : Int) atom1001Coded) (CoefficientMerge.scale (13470986592000 : Int) atom1002Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25277957510400 : Int) atom1003Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23313843302400 : Int) atom1004Coded) (CoefficientMerge.scale (23354435059200 : Int) atom1005Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23395026816000 : Int) atom1006Coded) (CoefficientMerge.scale (31410288000000 : Int) atom1007Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28735500628800 : Int) atom1008Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37614616704000 : Int) atom1009Coded) (CoefficientMerge.scale (39335264740800 : Int) atom1010Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46388243563200 : Int) atom1011Coded) (CoefficientMerge.scale (53441222385600 : Int) atom1012Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16246935936000 : Int) atom1013Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28498236883200 : Int) atom1014Coded) (CoefficientMerge.scale (27957013459200 : Int) atom1015Coded)))))) := by
  rw [block014_data_flat077_step, block014_data_flat057_original, block014_data_flat076_original]
def block014_data_flat078 : CoefficientMerge.Poly := [(nat_lit 1931, Int.ofNat (nat_lit 37738841800608)), (nat_lit 1940, Int.ofNat (nat_lit 8316316713600)), (nat_lit 1941, Int.ofNat (nat_lit 14616092937600)), (nat_lit 1942, Int.ofNat (nat_lit 14686645276800)), (nat_lit 1943, Int.ofNat (nat_lit 14704288099200)), (nat_lit 1944, Int.ofNat (nat_lit 13399306704000)), (nat_lit 1945, Int.ofNat (nat_lit 14099031273600)), (nat_lit 1946, Int.ofNat (nat_lit 14798755843200)), (nat_lit 1947, Int.ofNat (nat_lit 23245546060800)), (nat_lit 1948, Int.ofNat (nat_lit 20719776344400)), (nat_lit 1949, Int.ofNat (nat_lit 26086557772800)), (nat_lit 1950, Int.ofNat (nat_lit 31162368207600)), (nat_lit 1951, Int.ofNat (nat_lit 37890854593200)), (nat_lit 1952, Int.ofNat (nat_lit 44619340978800)), (nat_lit 1962, Int.ofNat (nat_lit 10739741241600)), (nat_lit 1963, Int.ofNat (nat_lit 19770762816000)), (nat_lit 1964, Int.ofNat (nat_lit 19283908089600)), (nat_lit 1965, Int.ofNat (nat_lit 18160623129600)), (nat_lit 1966, Int.ofNat (nat_lit 18614864217600)), (nat_lit 1967, Int.ofNat (nat_lit 19069105305600)), (nat_lit 1968, Int.ofNat (nat_lit 27327917030400)), (nat_lit 1969, Int.ofNat (nat_lit 24967957392000)), (nat_lit 1970, Int.ofNat (nat_lit 31850587238400)), (nat_lit 1971, Int.ofNat (nat_lit 35857179388800)), (nat_lit 1972, Int.ofNat (nat_lit 42965247024000)), (nat_lit 1973, Int.ofNat (nat_lit 50073314659200)), (nat_lit 1984, Int.ofNat (nat_lit 13470986592000)), (nat_lit 1985, Int.ofNat (nat_lit 25277957510400)), (nat_lit 1986, Int.ofNat (nat_lit 23313843302400)), (nat_lit 1987, Int.ofNat (nat_lit 23354435059200)), (nat_lit 1988, Int.ofNat (nat_lit 23395026816000)), (nat_lit 1989, Int.ofNat (nat_lit 31410288000000)), (nat_lit 1990, Int.ofNat (nat_lit 28735500628800)), (nat_lit 1991, Int.ofNat (nat_lit 37614616704000)), (nat_lit 1992, Int.ofNat (nat_lit 39335264740800)), (nat_lit 1993, Int.ofNat (nat_lit 46388243563200)), (nat_lit 1994, Int.ofNat (nat_lit 53441222385600)), (nat_lit 2006, Int.ofNat (nat_lit 16246935936000)), (nat_lit 2007, Int.ofNat (nat_lit 28498236883200)), (nat_lit 2008, Int.ofNat (nat_lit 27957013459200))]
theorem block014_data_flat078_step : block014_data_flat078 = (CoefficientMerge.fastMerge block014_data_flat038 block014_data_flat077) := by decide +kernel
theorem block014_data_flat078_original : block014_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37738841800608 : Int) atom0976Coded) (CoefficientMerge.scale (8316316713600 : Int) atom0977Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14616092937600 : Int) atom0978Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14686645276800 : Int) atom0979Coded) (CoefficientMerge.scale (14704288099200 : Int) atom0980Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13399306704000 : Int) atom0981Coded) (CoefficientMerge.scale (14099031273600 : Int) atom0982Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14798755843200 : Int) atom0983Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23245546060800 : Int) atom0984Coded) (CoefficientMerge.scale (20719776344400 : Int) atom0985Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26086557772800 : Int) atom0986Coded) (CoefficientMerge.scale (31162368207600 : Int) atom0987Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37890854593200 : Int) atom0988Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44619340978800 : Int) atom0989Coded) (CoefficientMerge.scale (10739741241600 : Int) atom0990Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19770762816000 : Int) atom0991Coded) (CoefficientMerge.scale (19283908089600 : Int) atom0992Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18160623129600 : Int) atom0993Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18614864217600 : Int) atom0994Coded) (CoefficientMerge.scale (19069105305600 : Int) atom0995Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (27327917030400 : Int) atom0996Coded) (CoefficientMerge.scale (24967957392000 : Int) atom0997Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31850587238400 : Int) atom0998Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35857179388800 : Int) atom0999Coded) (CoefficientMerge.scale (42965247024000 : Int) atom1000Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (50073314659200 : Int) atom1001Coded) (CoefficientMerge.scale (13470986592000 : Int) atom1002Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25277957510400 : Int) atom1003Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23313843302400 : Int) atom1004Coded) (CoefficientMerge.scale (23354435059200 : Int) atom1005Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23395026816000 : Int) atom1006Coded) (CoefficientMerge.scale (31410288000000 : Int) atom1007Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28735500628800 : Int) atom1008Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37614616704000 : Int) atom1009Coded) (CoefficientMerge.scale (39335264740800 : Int) atom1010Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46388243563200 : Int) atom1011Coded) (CoefficientMerge.scale (53441222385600 : Int) atom1012Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16246935936000 : Int) atom1013Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28498236883200 : Int) atom1014Coded) (CoefficientMerge.scale (27957013459200 : Int) atom1015Coded))))))) := by
  rw [block014_data_flat078_step, block014_data_flat038_original, block014_data_flat077_original]
def block014_data_flat079 : CoefficientMerge.Poly := [(nat_lit 2009, Int.ofNat (nat_lit 27415790035200))]
theorem block014_data_flat079_step : block014_data_flat079 = (CoefficientMerge.scale (27415790035200 : Int) atom1016Coded) := by decide +kernel
theorem block014_data_flat079_original : block014_data_flat079 = (CoefficientMerge.scale (27415790035200 : Int) atom1016Coded) := by
  rw [block014_data_flat079_step]
def block014_data_flat080 : CoefficientMerge.Poly := [(nat_lit 2010, Int.ofNat (nat_lit 34868811801600))]
theorem block014_data_flat080_step : block014_data_flat080 = (CoefficientMerge.scale (34868811801600 : Int) atom1017Coded) := by decide +kernel
theorem block014_data_flat080_original : block014_data_flat080 = (CoefficientMerge.scale (34868811801600 : Int) atom1017Coded) := by
  rw [block014_data_flat080_step]
def block014_data_flat081 : CoefficientMerge.Poly := [(nat_lit 2009, Int.ofNat (nat_lit 27415790035200)), (nat_lit 2010, Int.ofNat (nat_lit 34868811801600))]
theorem block014_data_flat081_step : block014_data_flat081 = (CoefficientMerge.fastMerge block014_data_flat079 block014_data_flat080) := by decide +kernel
theorem block014_data_flat081_original : block014_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (27415790035200 : Int) atom1016Coded) (CoefficientMerge.scale (34868811801600 : Int) atom1017Coded)) := by
  rw [block014_data_flat081_step, block014_data_flat079_original, block014_data_flat080_original]
def block014_data_flat082 : CoefficientMerge.Poly := [(nat_lit 2011, Int.ofNat (nat_lit 31796949592800))]
theorem block014_data_flat082_step : block014_data_flat082 = (CoefficientMerge.scale (31796949592800 : Int) atom1018Coded) := by decide +kernel
theorem block014_data_flat082_original : block014_data_flat082 = (CoefficientMerge.scale (31796949592800 : Int) atom1018Coded) := by
  rw [block014_data_flat082_step]
def block014_data_flat083 : CoefficientMerge.Poly := [(nat_lit 2012, Int.ofNat (nat_lit 42754799001600))]
theorem block014_data_flat083_step : block014_data_flat083 = (CoefficientMerge.scale (42754799001600 : Int) atom1019Coded) := by decide +kernel
theorem block014_data_flat083_original : block014_data_flat083 = (CoefficientMerge.scale (42754799001600 : Int) atom1019Coded) := by
  rw [block014_data_flat083_step]
def block014_data_flat084 : CoefficientMerge.Poly := [(nat_lit 2013, Int.ofNat (nat_lit 41641715556000))]
theorem block014_data_flat084_step : block014_data_flat084 = (CoefficientMerge.scale (41641715556000 : Int) atom1020Coded) := by decide +kernel
theorem block014_data_flat084_original : block014_data_flat084 = (CoefficientMerge.scale (41641715556000 : Int) atom1020Coded) := by
  rw [block014_data_flat084_step]
def block014_data_flat085 : CoefficientMerge.Poly := [(nat_lit 2012, Int.ofNat (nat_lit 42754799001600)), (nat_lit 2013, Int.ofNat (nat_lit 41641715556000))]
theorem block014_data_flat085_step : block014_data_flat085 = (CoefficientMerge.fastMerge block014_data_flat083 block014_data_flat084) := by decide +kernel
theorem block014_data_flat085_original : block014_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (42754799001600 : Int) atom1019Coded) (CoefficientMerge.scale (41641715556000 : Int) atom1020Coded)) := by
  rw [block014_data_flat085_step, block014_data_flat083_original, block014_data_flat084_original]
def block014_data_flat086 : CoefficientMerge.Poly := [(nat_lit 2011, Int.ofNat (nat_lit 31796949592800)), (nat_lit 2012, Int.ofNat (nat_lit 42754799001600)), (nat_lit 2013, Int.ofNat (nat_lit 41641715556000))]
theorem block014_data_flat086_step : block014_data_flat086 = (CoefficientMerge.fastMerge block014_data_flat082 block014_data_flat085) := by decide +kernel
theorem block014_data_flat086_original : block014_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (31796949592800 : Int) atom1018Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42754799001600 : Int) atom1019Coded) (CoefficientMerge.scale (41641715556000 : Int) atom1020Coded))) := by
  rw [block014_data_flat086_step, block014_data_flat082_original, block014_data_flat085_original]
def block014_data_flat087 : CoefficientMerge.Poly := [(nat_lit 2009, Int.ofNat (nat_lit 27415790035200)), (nat_lit 2010, Int.ofNat (nat_lit 34868811801600)), (nat_lit 2011, Int.ofNat (nat_lit 31796949592800)), (nat_lit 2012, Int.ofNat (nat_lit 42754799001600)), (nat_lit 2013, Int.ofNat (nat_lit 41641715556000))]
theorem block014_data_flat087_step : block014_data_flat087 = (CoefficientMerge.fastMerge block014_data_flat081 block014_data_flat086) := by decide +kernel
theorem block014_data_flat087_original : block014_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (27415790035200 : Int) atom1016Coded) (CoefficientMerge.scale (34868811801600 : Int) atom1017Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31796949592800 : Int) atom1018Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42754799001600 : Int) atom1019Coded) (CoefficientMerge.scale (41641715556000 : Int) atom1020Coded)))) := by
  rw [block014_data_flat087_step, block014_data_flat081_original, block014_data_flat086_original]
def block014_data_flat088 : CoefficientMerge.Poly := [(nat_lit 2014, Int.ofNat (nat_lit 48385300672800))]
theorem block014_data_flat088_step : block014_data_flat088 = (CoefficientMerge.scale (48385300672800 : Int) atom1021Coded) := by decide +kernel
theorem block014_data_flat088_original : block014_data_flat088 = (CoefficientMerge.scale (48385300672800 : Int) atom1021Coded) := by
  rw [block014_data_flat088_step]
def block014_data_flat089 : CoefficientMerge.Poly := [(nat_lit 2015, Int.ofNat (nat_lit 55128885789600))]
theorem block014_data_flat089_step : block014_data_flat089 = (CoefficientMerge.scale (55128885789600 : Int) atom1022Coded) := by decide +kernel
theorem block014_data_flat089_original : block014_data_flat089 = (CoefficientMerge.scale (55128885789600 : Int) atom1022Coded) := by
  rw [block014_data_flat089_step]
def block014_data_flat090 : CoefficientMerge.Poly := [(nat_lit 2014, Int.ofNat (nat_lit 48385300672800)), (nat_lit 2015, Int.ofNat (nat_lit 55128885789600))]
theorem block014_data_flat090_step : block014_data_flat090 = (CoefficientMerge.fastMerge block014_data_flat088 block014_data_flat089) := by decide +kernel
theorem block014_data_flat090_original : block014_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (48385300672800 : Int) atom1021Coded) (CoefficientMerge.scale (55128885789600 : Int) atom1022Coded)) := by
  rw [block014_data_flat090_step, block014_data_flat088_original, block014_data_flat089_original]
def block014_data_flat091 : CoefficientMerge.Poly := [(nat_lit 2028, Int.ofNat (nat_lit 17118445881600))]
theorem block014_data_flat091_step : block014_data_flat091 = (CoefficientMerge.scale (17118445881600 : Int) atom1023Coded) := by decide +kernel
theorem block014_data_flat091_original : block014_data_flat091 = (CoefficientMerge.scale (17118445881600 : Int) atom1023Coded) := by
  rw [block014_data_flat091_step]
def block014_data_flat092 : CoefficientMerge.Poly := [(nat_lit 2029, Int.ofNat (nat_lit 32518507392000))]
theorem block014_data_flat092_step : block014_data_flat092 = (CoefficientMerge.scale (32518507392000 : Int) atom1024Coded) := by decide +kernel
theorem block014_data_flat092_original : block014_data_flat092 = (CoefficientMerge.scale (32518507392000 : Int) atom1024Coded) := by
  rw [block014_data_flat092_step]
def block014_data_flat093 : CoefficientMerge.Poly := [(nat_lit 2030, Int.ofNat (nat_lit 31227302937600))]
theorem block014_data_flat093_step : block014_data_flat093 = (CoefficientMerge.scale (31227302937600 : Int) atom1025Coded) := by decide +kernel
theorem block014_data_flat093_original : block014_data_flat093 = (CoefficientMerge.scale (31227302937600 : Int) atom1025Coded) := by
  rw [block014_data_flat093_step]
def block014_data_flat094 : CoefficientMerge.Poly := [(nat_lit 2029, Int.ofNat (nat_lit 32518507392000)), (nat_lit 2030, Int.ofNat (nat_lit 31227302937600))]
theorem block014_data_flat094_step : block014_data_flat094 = (CoefficientMerge.fastMerge block014_data_flat092 block014_data_flat093) := by decide +kernel
theorem block014_data_flat094_original : block014_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (32518507392000 : Int) atom1024Coded) (CoefficientMerge.scale (31227302937600 : Int) atom1025Coded)) := by
  rw [block014_data_flat094_step, block014_data_flat092_original, block014_data_flat093_original]
def block014_data_flat095 : CoefficientMerge.Poly := [(nat_lit 2028, Int.ofNat (nat_lit 17118445881600)), (nat_lit 2029, Int.ofNat (nat_lit 32518507392000)), (nat_lit 2030, Int.ofNat (nat_lit 31227302937600))]
theorem block014_data_flat095_step : block014_data_flat095 = (CoefficientMerge.fastMerge block014_data_flat091 block014_data_flat094) := by decide +kernel
theorem block014_data_flat095_original : block014_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (17118445881600 : Int) atom1023Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32518507392000 : Int) atom1024Coded) (CoefficientMerge.scale (31227302937600 : Int) atom1025Coded))) := by
  rw [block014_data_flat095_step, block014_data_flat091_original, block014_data_flat094_original]
def block014_data_flat096 : CoefficientMerge.Poly := [(nat_lit 2014, Int.ofNat (nat_lit 48385300672800)), (nat_lit 2015, Int.ofNat (nat_lit 55128885789600)), (nat_lit 2028, Int.ofNat (nat_lit 17118445881600)), (nat_lit 2029, Int.ofNat (nat_lit 32518507392000)), (nat_lit 2030, Int.ofNat (nat_lit 31227302937600))]
theorem block014_data_flat096_step : block014_data_flat096 = (CoefficientMerge.fastMerge block014_data_flat090 block014_data_flat095) := by decide +kernel
theorem block014_data_flat096_original : block014_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48385300672800 : Int) atom1021Coded) (CoefficientMerge.scale (55128885789600 : Int) atom1022Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17118445881600 : Int) atom1023Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32518507392000 : Int) atom1024Coded) (CoefficientMerge.scale (31227302937600 : Int) atom1025Coded)))) := by
  rw [block014_data_flat096_step, block014_data_flat090_original, block014_data_flat095_original]
def block014_data_flat097 : CoefficientMerge.Poly := [(nat_lit 2009, Int.ofNat (nat_lit 27415790035200)), (nat_lit 2010, Int.ofNat (nat_lit 34868811801600)), (nat_lit 2011, Int.ofNat (nat_lit 31796949592800)), (nat_lit 2012, Int.ofNat (nat_lit 42754799001600)), (nat_lit 2013, Int.ofNat (nat_lit 41641715556000)), (nat_lit 2014, Int.ofNat (nat_lit 48385300672800)), (nat_lit 2015, Int.ofNat (nat_lit 55128885789600)), (nat_lit 2028, Int.ofNat (nat_lit 17118445881600)), (nat_lit 2029, Int.ofNat (nat_lit 32518507392000)), (nat_lit 2030, Int.ofNat (nat_lit 31227302937600))]
theorem block014_data_flat097_step : block014_data_flat097 = (CoefficientMerge.fastMerge block014_data_flat087 block014_data_flat096) := by decide +kernel
theorem block014_data_flat097_original : block014_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (27415790035200 : Int) atom1016Coded) (CoefficientMerge.scale (34868811801600 : Int) atom1017Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31796949592800 : Int) atom1018Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42754799001600 : Int) atom1019Coded) (CoefficientMerge.scale (41641715556000 : Int) atom1020Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48385300672800 : Int) atom1021Coded) (CoefficientMerge.scale (55128885789600 : Int) atom1022Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17118445881600 : Int) atom1023Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32518507392000 : Int) atom1024Coded) (CoefficientMerge.scale (31227302937600 : Int) atom1025Coded))))) := by
  rw [block014_data_flat097_step, block014_data_flat087_original, block014_data_flat096_original]
def block014_data_flat098 : CoefficientMerge.Poly := [(nat_lit 2031, Int.ofNat (nat_lit 34633735248000))]
theorem block014_data_flat098_step : block014_data_flat098 = (CoefficientMerge.scale (34633735248000 : Int) atom1026Coded) := by decide +kernel
theorem block014_data_flat098_original : block014_data_flat098 = (CoefficientMerge.scale (34633735248000 : Int) atom1026Coded) := by
  rw [block014_data_flat098_step]
def block014_data_flat099 : CoefficientMerge.Poly := [(nat_lit 2032, Int.ofNat (nat_lit 33705364364000))]
theorem block014_data_flat099_step : block014_data_flat099 = (CoefficientMerge.scale (33705364364000 : Int) atom1027Coded) := by decide +kernel
theorem block014_data_flat099_original : block014_data_flat099 = (CoefficientMerge.scale (33705364364000 : Int) atom1027Coded) := by
  rw [block014_data_flat099_step]
def block014_data_flat100 : CoefficientMerge.Poly := [(nat_lit 2031, Int.ofNat (nat_lit 34633735248000)), (nat_lit 2032, Int.ofNat (nat_lit 33705364364000))]
theorem block014_data_flat100_step : block014_data_flat100 = (CoefficientMerge.fastMerge block014_data_flat098 block014_data_flat099) := by decide +kernel
theorem block014_data_flat100_original : block014_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (34633735248000 : Int) atom1026Coded) (CoefficientMerge.scale (33705364364000 : Int) atom1027Coded)) := by
  rw [block014_data_flat100_step, block014_data_flat098_original, block014_data_flat099_original]
def block014_data_flat101 : CoefficientMerge.Poly := [(nat_lit 2033, Int.ofNat (nat_lit 43390369097600))]
theorem block014_data_flat101_step : block014_data_flat101 = (CoefficientMerge.scale (43390369097600 : Int) atom1028Coded) := by decide +kernel
theorem block014_data_flat101_original : block014_data_flat101 = (CoefficientMerge.scale (43390369097600 : Int) atom1028Coded) := by
  rw [block014_data_flat101_step]
def block014_data_flat102 : CoefficientMerge.Poly := [(nat_lit 2034, Int.ofNat (nat_lit 42915361938400))]
theorem block014_data_flat102_step : block014_data_flat102 = (CoefficientMerge.scale (42915361938400 : Int) atom1029Coded) := by decide +kernel
theorem block014_data_flat102_original : block014_data_flat102 = (CoefficientMerge.scale (42915361938400 : Int) atom1029Coded) := by
  rw [block014_data_flat102_step]
def block014_data_flat103 : CoefficientMerge.Poly := [(nat_lit 2035, Int.ofNat (nat_lit 48592346426400))]
theorem block014_data_flat103_step : block014_data_flat103 = (CoefficientMerge.scale (48592346426400 : Int) atom1030Coded) := by decide +kernel
theorem block014_data_flat103_original : block014_data_flat103 = (CoefficientMerge.scale (48592346426400 : Int) atom1030Coded) := by
  rw [block014_data_flat103_step]
def block014_data_flat104 : CoefficientMerge.Poly := [(nat_lit 2034, Int.ofNat (nat_lit 42915361938400)), (nat_lit 2035, Int.ofNat (nat_lit 48592346426400))]
theorem block014_data_flat104_step : block014_data_flat104 = (CoefficientMerge.fastMerge block014_data_flat102 block014_data_flat103) := by decide +kernel
theorem block014_data_flat104_original : block014_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (42915361938400 : Int) atom1029Coded) (CoefficientMerge.scale (48592346426400 : Int) atom1030Coded)) := by
  rw [block014_data_flat104_step, block014_data_flat102_original, block014_data_flat103_original]
def block014_data_flat105 : CoefficientMerge.Poly := [(nat_lit 2033, Int.ofNat (nat_lit 43390369097600)), (nat_lit 2034, Int.ofNat (nat_lit 42915361938400)), (nat_lit 2035, Int.ofNat (nat_lit 48592346426400))]
theorem block014_data_flat105_step : block014_data_flat105 = (CoefficientMerge.fastMerge block014_data_flat101 block014_data_flat104) := by decide +kernel
theorem block014_data_flat105_original : block014_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (43390369097600 : Int) atom1028Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42915361938400 : Int) atom1029Coded) (CoefficientMerge.scale (48592346426400 : Int) atom1030Coded))) := by
  rw [block014_data_flat105_step, block014_data_flat101_original, block014_data_flat104_original]
def block014_data_flat106 : CoefficientMerge.Poly := [(nat_lit 2031, Int.ofNat (nat_lit 34633735248000)), (nat_lit 2032, Int.ofNat (nat_lit 33705364364000)), (nat_lit 2033, Int.ofNat (nat_lit 43390369097600)), (nat_lit 2034, Int.ofNat (nat_lit 42915361938400)), (nat_lit 2035, Int.ofNat (nat_lit 48592346426400))]
theorem block014_data_flat106_step : block014_data_flat106 = (CoefficientMerge.fastMerge block014_data_flat100 block014_data_flat105) := by decide +kernel
theorem block014_data_flat106_original : block014_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34633735248000 : Int) atom1026Coded) (CoefficientMerge.scale (33705364364000 : Int) atom1027Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43390369097600 : Int) atom1028Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42915361938400 : Int) atom1029Coded) (CoefficientMerge.scale (48592346426400 : Int) atom1030Coded)))) := by
  rw [block014_data_flat106_step, block014_data_flat100_original, block014_data_flat105_original]
def block014_data_flat107 : CoefficientMerge.Poly := [(nat_lit 2036, Int.ofNat (nat_lit 55028408400000))]
theorem block014_data_flat107_step : block014_data_flat107 = (CoefficientMerge.scale (55028408400000 : Int) atom1031Coded) := by decide +kernel
theorem block014_data_flat107_original : block014_data_flat107 = (CoefficientMerge.scale (55028408400000 : Int) atom1031Coded) := by
  rw [block014_data_flat107_step]
def block014_data_flat108 : CoefficientMerge.Poly := [(nat_lit 2050, Int.ofNat (nat_lit 19975700563200))]
theorem block014_data_flat108_step : block014_data_flat108 = (CoefficientMerge.scale (19975700563200 : Int) atom1032Coded) := by decide +kernel
theorem block014_data_flat108_original : block014_data_flat108 = (CoefficientMerge.scale (19975700563200 : Int) atom1032Coded) := by
  rw [block014_data_flat108_step]
def block014_data_flat109 : CoefficientMerge.Poly := [(nat_lit 2036, Int.ofNat (nat_lit 55028408400000)), (nat_lit 2050, Int.ofNat (nat_lit 19975700563200))]
theorem block014_data_flat109_step : block014_data_flat109 = (CoefficientMerge.fastMerge block014_data_flat107 block014_data_flat108) := by decide +kernel
theorem block014_data_flat109_original : block014_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (55028408400000 : Int) atom1031Coded) (CoefficientMerge.scale (19975700563200 : Int) atom1032Coded)) := by
  rw [block014_data_flat109_step, block014_data_flat107_original, block014_data_flat108_original]
def block014_data_flat110 : CoefficientMerge.Poly := [(nat_lit 2051, Int.ofNat (nat_lit 36571516070400))]
theorem block014_data_flat110_step : block014_data_flat110 = (CoefficientMerge.scale (36571516070400 : Int) atom1033Coded) := by decide +kernel
theorem block014_data_flat110_original : block014_data_flat110 = (CoefficientMerge.scale (36571516070400 : Int) atom1033Coded) := by
  rw [block014_data_flat110_step]
def block014_data_flat111 : CoefficientMerge.Poly := [(nat_lit 2052, Int.ofNat (nat_lit 38601069393600))]
theorem block014_data_flat111_step : block014_data_flat111 = (CoefficientMerge.scale (38601069393600 : Int) atom1034Coded) := by decide +kernel
theorem block014_data_flat111_original : block014_data_flat111 = (CoefficientMerge.scale (38601069393600 : Int) atom1034Coded) := by
  rw [block014_data_flat111_step]
def block014_data_flat112 : CoefficientMerge.Poly := [(nat_lit 2053, Int.ofNat (nat_lit 36159816938400))]
theorem block014_data_flat112_step : block014_data_flat112 = (CoefficientMerge.scale (36159816938400 : Int) atom1035Coded) := by decide +kernel
theorem block014_data_flat112_original : block014_data_flat112 = (CoefficientMerge.scale (36159816938400 : Int) atom1035Coded) := by
  rw [block014_data_flat112_step]
def block014_data_flat113 : CoefficientMerge.Poly := [(nat_lit 2052, Int.ofNat (nat_lit 38601069393600)), (nat_lit 2053, Int.ofNat (nat_lit 36159816938400))]
theorem block014_data_flat113_step : block014_data_flat113 = (CoefficientMerge.fastMerge block014_data_flat111 block014_data_flat112) := by decide +kernel
theorem block014_data_flat113_original : block014_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (38601069393600 : Int) atom1034Coded) (CoefficientMerge.scale (36159816938400 : Int) atom1035Coded)) := by
  rw [block014_data_flat113_step, block014_data_flat111_original, block014_data_flat112_original]
def block014_data_flat114 : CoefficientMerge.Poly := [(nat_lit 2051, Int.ofNat (nat_lit 36571516070400)), (nat_lit 2052, Int.ofNat (nat_lit 38601069393600)), (nat_lit 2053, Int.ofNat (nat_lit 36159816938400))]
theorem block014_data_flat114_step : block014_data_flat114 = (CoefficientMerge.fastMerge block014_data_flat110 block014_data_flat113) := by decide +kernel
theorem block014_data_flat114_original : block014_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (36571516070400 : Int) atom1033Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38601069393600 : Int) atom1034Coded) (CoefficientMerge.scale (36159816938400 : Int) atom1035Coded))) := by
  rw [block014_data_flat114_step, block014_data_flat110_original, block014_data_flat113_original]
def block014_data_flat115 : CoefficientMerge.Poly := [(nat_lit 2036, Int.ofNat (nat_lit 55028408400000)), (nat_lit 2050, Int.ofNat (nat_lit 19975700563200)), (nat_lit 2051, Int.ofNat (nat_lit 36571516070400)), (nat_lit 2052, Int.ofNat (nat_lit 38601069393600)), (nat_lit 2053, Int.ofNat (nat_lit 36159816938400))]
theorem block014_data_flat115_step : block014_data_flat115 = (CoefficientMerge.fastMerge block014_data_flat109 block014_data_flat114) := by decide +kernel
theorem block014_data_flat115_original : block014_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55028408400000 : Int) atom1031Coded) (CoefficientMerge.scale (19975700563200 : Int) atom1032Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36571516070400 : Int) atom1033Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38601069393600 : Int) atom1034Coded) (CoefficientMerge.scale (36159816938400 : Int) atom1035Coded)))) := by
  rw [block014_data_flat115_step, block014_data_flat109_original, block014_data_flat114_original]
def block014_data_flat116 : CoefficientMerge.Poly := [(nat_lit 2031, Int.ofNat (nat_lit 34633735248000)), (nat_lit 2032, Int.ofNat (nat_lit 33705364364000)), (nat_lit 2033, Int.ofNat (nat_lit 43390369097600)), (nat_lit 2034, Int.ofNat (nat_lit 42915361938400)), (nat_lit 2035, Int.ofNat (nat_lit 48592346426400)), (nat_lit 2036, Int.ofNat (nat_lit 55028408400000)), (nat_lit 2050, Int.ofNat (nat_lit 19975700563200)), (nat_lit 2051, Int.ofNat (nat_lit 36571516070400)), (nat_lit 2052, Int.ofNat (nat_lit 38601069393600)), (nat_lit 2053, Int.ofNat (nat_lit 36159816938400))]
theorem block014_data_flat116_step : block014_data_flat116 = (CoefficientMerge.fastMerge block014_data_flat106 block014_data_flat115) := by decide +kernel
theorem block014_data_flat116_original : block014_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34633735248000 : Int) atom1026Coded) (CoefficientMerge.scale (33705364364000 : Int) atom1027Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43390369097600 : Int) atom1028Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42915361938400 : Int) atom1029Coded) (CoefficientMerge.scale (48592346426400 : Int) atom1030Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55028408400000 : Int) atom1031Coded) (CoefficientMerge.scale (19975700563200 : Int) atom1032Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36571516070400 : Int) atom1033Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38601069393600 : Int) atom1034Coded) (CoefficientMerge.scale (36159816938400 : Int) atom1035Coded))))) := by
  rw [block014_data_flat116_step, block014_data_flat106_original, block014_data_flat115_original]
def block014_data_flat117 : CoefficientMerge.Poly := [(nat_lit 2009, Int.ofNat (nat_lit 27415790035200)), (nat_lit 2010, Int.ofNat (nat_lit 34868811801600)), (nat_lit 2011, Int.ofNat (nat_lit 31796949592800)), (nat_lit 2012, Int.ofNat (nat_lit 42754799001600)), (nat_lit 2013, Int.ofNat (nat_lit 41641715556000)), (nat_lit 2014, Int.ofNat (nat_lit 48385300672800)), (nat_lit 2015, Int.ofNat (nat_lit 55128885789600)), (nat_lit 2028, Int.ofNat (nat_lit 17118445881600)), (nat_lit 2029, Int.ofNat (nat_lit 32518507392000)), (nat_lit 2030, Int.ofNat (nat_lit 31227302937600)), (nat_lit 2031, Int.ofNat (nat_lit 34633735248000)), (nat_lit 2032, Int.ofNat (nat_lit 33705364364000)), (nat_lit 2033, Int.ofNat (nat_lit 43390369097600)), (nat_lit 2034, Int.ofNat (nat_lit 42915361938400)), (nat_lit 2035, Int.ofNat (nat_lit 48592346426400)), (nat_lit 2036, Int.ofNat (nat_lit 55028408400000)), (nat_lit 2050, Int.ofNat (nat_lit 19975700563200)), (nat_lit 2051, Int.ofNat (nat_lit 36571516070400)), (nat_lit 2052, Int.ofNat (nat_lit 38601069393600)), (nat_lit 2053, Int.ofNat (nat_lit 36159816938400))]
theorem block014_data_flat117_step : block014_data_flat117 = (CoefficientMerge.fastMerge block014_data_flat097 block014_data_flat116) := by decide +kernel
theorem block014_data_flat117_original : block014_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (27415790035200 : Int) atom1016Coded) (CoefficientMerge.scale (34868811801600 : Int) atom1017Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31796949592800 : Int) atom1018Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42754799001600 : Int) atom1019Coded) (CoefficientMerge.scale (41641715556000 : Int) atom1020Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48385300672800 : Int) atom1021Coded) (CoefficientMerge.scale (55128885789600 : Int) atom1022Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17118445881600 : Int) atom1023Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32518507392000 : Int) atom1024Coded) (CoefficientMerge.scale (31227302937600 : Int) atom1025Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34633735248000 : Int) atom1026Coded) (CoefficientMerge.scale (33705364364000 : Int) atom1027Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43390369097600 : Int) atom1028Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42915361938400 : Int) atom1029Coded) (CoefficientMerge.scale (48592346426400 : Int) atom1030Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55028408400000 : Int) atom1031Coded) (CoefficientMerge.scale (19975700563200 : Int) atom1032Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36571516070400 : Int) atom1033Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38601069393600 : Int) atom1034Coded) (CoefficientMerge.scale (36159816938400 : Int) atom1035Coded)))))) := by
  rw [block014_data_flat117_step, block014_data_flat097_original, block014_data_flat116_original]
def block014_data_flat118 : CoefficientMerge.Poly := [(nat_lit 2054, Int.ofNat (nat_lit 47594873289600))]
theorem block014_data_flat118_step : block014_data_flat118 = (CoefficientMerge.scale (47594873289600 : Int) atom1036Coded) := by decide +kernel
theorem block014_data_flat118_original : block014_data_flat118 = (CoefficientMerge.scale (47594873289600 : Int) atom1036Coded) := by
  rw [block014_data_flat118_step]
def block014_data_flat119 : CoefficientMerge.Poly := [(nat_lit 2055, Int.ofNat (nat_lit 47799330616800))]
theorem block014_data_flat119_step : block014_data_flat119 = (CoefficientMerge.scale (47799330616800 : Int) atom1037Coded) := by decide +kernel
theorem block014_data_flat119_original : block014_data_flat119 = (CoefficientMerge.scale (47799330616800 : Int) atom1037Coded) := by
  rw [block014_data_flat119_step]
def block014_data_flat120 : CoefficientMerge.Poly := [(nat_lit 2054, Int.ofNat (nat_lit 47594873289600)), (nat_lit 2055, Int.ofNat (nat_lit 47799330616800))]
theorem block014_data_flat120_step : block014_data_flat120 = (CoefficientMerge.fastMerge block014_data_flat118 block014_data_flat119) := by decide +kernel
theorem block014_data_flat120_original : block014_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (47594873289600 : Int) atom1036Coded) (CoefficientMerge.scale (47799330616800 : Int) atom1037Coded)) := by
  rw [block014_data_flat120_step, block014_data_flat118_original, block014_data_flat119_original]
def block014_data_flat121 : CoefficientMerge.Poly := [(nat_lit 2056, Int.ofNat (nat_lit 46286873474400))]
theorem block014_data_flat121_step : block014_data_flat121 = (CoefficientMerge.scale (46286873474400 : Int) atom1038Coded) := by decide +kernel
theorem block014_data_flat121_original : block014_data_flat121 = (CoefficientMerge.scale (46286873474400 : Int) atom1038Coded) := by
  rw [block014_data_flat121_step]
def block014_data_flat122 : CoefficientMerge.Poly := [(nat_lit 2057, Int.ofNat (nat_lit 58138510147200))]
theorem block014_data_flat122_step : block014_data_flat122 = (CoefficientMerge.scale (58138510147200 : Int) atom1039Coded) := by decide +kernel
theorem block014_data_flat122_original : block014_data_flat122 = (CoefficientMerge.scale (58138510147200 : Int) atom1039Coded) := by
  rw [block014_data_flat122_step]
def block014_data_flat123 : CoefficientMerge.Poly := [(nat_lit 2072, Int.ofNat (nat_lit 23439806611200))]
theorem block014_data_flat123_step : block014_data_flat123 = (CoefficientMerge.scale (23439806611200 : Int) atom1040Coded) := by decide +kernel
theorem block014_data_flat123_original : block014_data_flat123 = (CoefficientMerge.scale (23439806611200 : Int) atom1040Coded) := by
  rw [block014_data_flat123_step]
def block014_data_flat124 : CoefficientMerge.Poly := [(nat_lit 2057, Int.ofNat (nat_lit 58138510147200)), (nat_lit 2072, Int.ofNat (nat_lit 23439806611200))]
theorem block014_data_flat124_step : block014_data_flat124 = (CoefficientMerge.fastMerge block014_data_flat122 block014_data_flat123) := by decide +kernel
theorem block014_data_flat124_original : block014_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (58138510147200 : Int) atom1039Coded) (CoefficientMerge.scale (23439806611200 : Int) atom1040Coded)) := by
  rw [block014_data_flat124_step, block014_data_flat122_original, block014_data_flat123_original]
def block014_data_flat125 : CoefficientMerge.Poly := [(nat_lit 2056, Int.ofNat (nat_lit 46286873474400)), (nat_lit 2057, Int.ofNat (nat_lit 58138510147200)), (nat_lit 2072, Int.ofNat (nat_lit 23439806611200))]
theorem block014_data_flat125_step : block014_data_flat125 = (CoefficientMerge.fastMerge block014_data_flat121 block014_data_flat124) := by decide +kernel
theorem block014_data_flat125_original : block014_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (46286873474400 : Int) atom1038Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (58138510147200 : Int) atom1039Coded) (CoefficientMerge.scale (23439806611200 : Int) atom1040Coded))) := by
  rw [block014_data_flat125_step, block014_data_flat121_original, block014_data_flat124_original]
def block014_data_flat126 : CoefficientMerge.Poly := [(nat_lit 2054, Int.ofNat (nat_lit 47594873289600)), (nat_lit 2055, Int.ofNat (nat_lit 47799330616800)), (nat_lit 2056, Int.ofNat (nat_lit 46286873474400)), (nat_lit 2057, Int.ofNat (nat_lit 58138510147200)), (nat_lit 2072, Int.ofNat (nat_lit 23439806611200))]
theorem block014_data_flat126_step : block014_data_flat126 = (CoefficientMerge.fastMerge block014_data_flat120 block014_data_flat125) := by decide +kernel
theorem block014_data_flat126_original : block014_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (47594873289600 : Int) atom1036Coded) (CoefficientMerge.scale (47799330616800 : Int) atom1037Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46286873474400 : Int) atom1038Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (58138510147200 : Int) atom1039Coded) (CoefficientMerge.scale (23439806611200 : Int) atom1040Coded)))) := by
  rw [block014_data_flat126_step, block014_data_flat120_original, block014_data_flat125_original]
def block014_data_flat127 : CoefficientMerge.Poly := [(nat_lit 2073, Int.ofNat (nat_lit 42456561436800))]
theorem block014_data_flat127_step : block014_data_flat127 = (CoefficientMerge.scale (42456561436800 : Int) atom1041Coded) := by decide +kernel
theorem block014_data_flat127_original : block014_data_flat127 = (CoefficientMerge.scale (42456561436800 : Int) atom1041Coded) := by
  rw [block014_data_flat127_step]
def block014_data_flat128 : CoefficientMerge.Poly := [(nat_lit 2074, Int.ofNat (nat_lit 38495120076000))]
theorem block014_data_flat128_step : block014_data_flat128 = (CoefficientMerge.scale (38495120076000 : Int) atom1042Coded) := by decide +kernel
theorem block014_data_flat128_original : block014_data_flat128 = (CoefficientMerge.scale (38495120076000 : Int) atom1042Coded) := by
  rw [block014_data_flat128_step]
def block014_data_flat129 : CoefficientMerge.Poly := [(nat_lit 2073, Int.ofNat (nat_lit 42456561436800)), (nat_lit 2074, Int.ofNat (nat_lit 38495120076000))]
theorem block014_data_flat129_step : block014_data_flat129 = (CoefficientMerge.fastMerge block014_data_flat127 block014_data_flat128) := by decide +kernel
theorem block014_data_flat129_original : block014_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (42456561436800 : Int) atom1041Coded) (CoefficientMerge.scale (38495120076000 : Int) atom1042Coded)) := by
  rw [block014_data_flat129_step, block014_data_flat127_original, block014_data_flat128_original]
def block014_data_flat130 : CoefficientMerge.Poly := [(nat_lit 2075, Int.ofNat (nat_lit 53992907337600))]
theorem block014_data_flat130_step : block014_data_flat130 = (CoefficientMerge.scale (53992907337600 : Int) atom1043Coded) := by decide +kernel
theorem block014_data_flat130_original : block014_data_flat130 = (CoefficientMerge.scale (53992907337600 : Int) atom1043Coded) := by
  rw [block014_data_flat130_step]
def block014_data_flat131 : CoefficientMerge.Poly := [(nat_lit 2076, Int.ofNat (nat_lit 55096182136800))]
theorem block014_data_flat131_step : block014_data_flat131 = (CoefficientMerge.scale (55096182136800 : Int) atom1044Coded) := by decide +kernel
theorem block014_data_flat131_original : block014_data_flat131 = (CoefficientMerge.scale (55096182136800 : Int) atom1044Coded) := by
  rw [block014_data_flat131_step]
def block014_data_flat132 : CoefficientMerge.Poly := [(nat_lit 2077, Int.ofNat (nat_lit 48432127111200))]
theorem block014_data_flat132_step : block014_data_flat132 = (CoefficientMerge.scale (48432127111200 : Int) atom1045Coded) := by decide +kernel
theorem block014_data_flat132_original : block014_data_flat132 = (CoefficientMerge.scale (48432127111200 : Int) atom1045Coded) := by
  rw [block014_data_flat132_step]
def block014_data_flat133 : CoefficientMerge.Poly := [(nat_lit 2076, Int.ofNat (nat_lit 55096182136800)), (nat_lit 2077, Int.ofNat (nat_lit 48432127111200))]
theorem block014_data_flat133_step : block014_data_flat133 = (CoefficientMerge.fastMerge block014_data_flat131 block014_data_flat132) := by decide +kernel
theorem block014_data_flat133_original : block014_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (55096182136800 : Int) atom1044Coded) (CoefficientMerge.scale (48432127111200 : Int) atom1045Coded)) := by
  rw [block014_data_flat133_step, block014_data_flat131_original, block014_data_flat132_original]
def block014_data_flat134 : CoefficientMerge.Poly := [(nat_lit 2075, Int.ofNat (nat_lit 53992907337600)), (nat_lit 2076, Int.ofNat (nat_lit 55096182136800)), (nat_lit 2077, Int.ofNat (nat_lit 48432127111200))]
theorem block014_data_flat134_step : block014_data_flat134 = (CoefficientMerge.fastMerge block014_data_flat130 block014_data_flat133) := by decide +kernel
theorem block014_data_flat134_original : block014_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (53992907337600 : Int) atom1043Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55096182136800 : Int) atom1044Coded) (CoefficientMerge.scale (48432127111200 : Int) atom1045Coded))) := by
  rw [block014_data_flat134_step, block014_data_flat130_original, block014_data_flat133_original]
def block014_data_flat135 : CoefficientMerge.Poly := [(nat_lit 2073, Int.ofNat (nat_lit 42456561436800)), (nat_lit 2074, Int.ofNat (nat_lit 38495120076000)), (nat_lit 2075, Int.ofNat (nat_lit 53992907337600)), (nat_lit 2076, Int.ofNat (nat_lit 55096182136800)), (nat_lit 2077, Int.ofNat (nat_lit 48432127111200))]
theorem block014_data_flat135_step : block014_data_flat135 = (CoefficientMerge.fastMerge block014_data_flat129 block014_data_flat134) := by decide +kernel
theorem block014_data_flat135_original : block014_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (42456561436800 : Int) atom1041Coded) (CoefficientMerge.scale (38495120076000 : Int) atom1042Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53992907337600 : Int) atom1043Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55096182136800 : Int) atom1044Coded) (CoefficientMerge.scale (48432127111200 : Int) atom1045Coded)))) := by
  rw [block014_data_flat135_step, block014_data_flat129_original, block014_data_flat134_original]
def block014_data_flat136 : CoefficientMerge.Poly := [(nat_lit 2054, Int.ofNat (nat_lit 47594873289600)), (nat_lit 2055, Int.ofNat (nat_lit 47799330616800)), (nat_lit 2056, Int.ofNat (nat_lit 46286873474400)), (nat_lit 2057, Int.ofNat (nat_lit 58138510147200)), (nat_lit 2072, Int.ofNat (nat_lit 23439806611200)), (nat_lit 2073, Int.ofNat (nat_lit 42456561436800)), (nat_lit 2074, Int.ofNat (nat_lit 38495120076000)), (nat_lit 2075, Int.ofNat (nat_lit 53992907337600)), (nat_lit 2076, Int.ofNat (nat_lit 55096182136800)), (nat_lit 2077, Int.ofNat (nat_lit 48432127111200))]
theorem block014_data_flat136_step : block014_data_flat136 = (CoefficientMerge.fastMerge block014_data_flat126 block014_data_flat135) := by decide +kernel
theorem block014_data_flat136_original : block014_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (47594873289600 : Int) atom1036Coded) (CoefficientMerge.scale (47799330616800 : Int) atom1037Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46286873474400 : Int) atom1038Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (58138510147200 : Int) atom1039Coded) (CoefficientMerge.scale (23439806611200 : Int) atom1040Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (42456561436800 : Int) atom1041Coded) (CoefficientMerge.scale (38495120076000 : Int) atom1042Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53992907337600 : Int) atom1043Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55096182136800 : Int) atom1044Coded) (CoefficientMerge.scale (48432127111200 : Int) atom1045Coded))))) := by
  rw [block014_data_flat136_step, block014_data_flat126_original, block014_data_flat135_original]
def block014_data_flat137 : CoefficientMerge.Poly := [(nat_lit 2078, Int.ofNat (nat_lit 65831614531200))]
theorem block014_data_flat137_step : block014_data_flat137 = (CoefficientMerge.scale (65831614531200 : Int) atom1046Coded) := by decide +kernel
theorem block014_data_flat137_original : block014_data_flat137 = (CoefficientMerge.scale (65831614531200 : Int) atom1046Coded) := by
  rw [block014_data_flat137_step]
def block014_data_flat138 : CoefficientMerge.Poly := [(nat_lit 2094, Int.ofNat (nat_lit 27544406400000))]
theorem block014_data_flat138_step : block014_data_flat138 = (CoefficientMerge.scale (27544406400000 : Int) atom1047Coded) := by decide +kernel
theorem block014_data_flat138_original : block014_data_flat138 = (CoefficientMerge.scale (27544406400000 : Int) atom1047Coded) := by
  rw [block014_data_flat138_step]
def block014_data_flat139 : CoefficientMerge.Poly := [(nat_lit 2078, Int.ofNat (nat_lit 65831614531200)), (nat_lit 2094, Int.ofNat (nat_lit 27544406400000))]
theorem block014_data_flat139_step : block014_data_flat139 = (CoefficientMerge.fastMerge block014_data_flat137 block014_data_flat138) := by decide +kernel
theorem block014_data_flat139_original : block014_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (65831614531200 : Int) atom1046Coded) (CoefficientMerge.scale (27544406400000 : Int) atom1047Coded)) := by
  rw [block014_data_flat139_step, block014_data_flat137_original, block014_data_flat138_original]
def block014_data_flat140 : CoefficientMerge.Poly := [(nat_lit 2095, Int.ofNat (nat_lit 49565736486000))]
theorem block014_data_flat140_step : block014_data_flat140 = (CoefficientMerge.scale (49565736486000 : Int) atom1048Coded) := by decide +kernel
theorem block014_data_flat140_original : block014_data_flat140 = (CoefficientMerge.scale (49565736486000 : Int) atom1048Coded) := by
  rw [block014_data_flat140_step]
def block014_data_flat141 : CoefficientMerge.Poly := [(nat_lit 2096, Int.ofNat (nat_lit 69701433984000))]
theorem block014_data_flat141_step : block014_data_flat141 = (CoefficientMerge.scale (69701433984000 : Int) atom1049Coded) := by decide +kernel
theorem block014_data_flat141_original : block014_data_flat141 = (CoefficientMerge.scale (69701433984000 : Int) atom1049Coded) := by
  rw [block014_data_flat141_step]
def block014_data_flat142 : CoefficientMerge.Poly := [(nat_lit 2097, Int.ofNat (nat_lit 67506930565200))]
theorem block014_data_flat142_step : block014_data_flat142 = (CoefficientMerge.scale (67506930565200 : Int) atom1050Coded) := by decide +kernel
theorem block014_data_flat142_original : block014_data_flat142 = (CoefficientMerge.scale (67506930565200 : Int) atom1050Coded) := by
  rw [block014_data_flat142_step]
def block014_data_flat143 : CoefficientMerge.Poly := [(nat_lit 2096, Int.ofNat (nat_lit 69701433984000)), (nat_lit 2097, Int.ofNat (nat_lit 67506930565200))]
theorem block014_data_flat143_step : block014_data_flat143 = (CoefficientMerge.fastMerge block014_data_flat141 block014_data_flat142) := by decide +kernel
theorem block014_data_flat143_original : block014_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (69701433984000 : Int) atom1049Coded) (CoefficientMerge.scale (67506930565200 : Int) atom1050Coded)) := by
  rw [block014_data_flat143_step, block014_data_flat141_original, block014_data_flat142_original]
def block014_data_flat144 : CoefficientMerge.Poly := [(nat_lit 2095, Int.ofNat (nat_lit 49565736486000)), (nat_lit 2096, Int.ofNat (nat_lit 69701433984000)), (nat_lit 2097, Int.ofNat (nat_lit 67506930565200))]
theorem block014_data_flat144_step : block014_data_flat144 = (CoefficientMerge.fastMerge block014_data_flat140 block014_data_flat143) := by decide +kernel
theorem block014_data_flat144_original : block014_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (49565736486000 : Int) atom1048Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (69701433984000 : Int) atom1049Coded) (CoefficientMerge.scale (67506930565200 : Int) atom1050Coded))) := by
  rw [block014_data_flat144_step, block014_data_flat140_original, block014_data_flat143_original]
def block014_data_flat145 : CoefficientMerge.Poly := [(nat_lit 2078, Int.ofNat (nat_lit 65831614531200)), (nat_lit 2094, Int.ofNat (nat_lit 27544406400000)), (nat_lit 2095, Int.ofNat (nat_lit 49565736486000)), (nat_lit 2096, Int.ofNat (nat_lit 69701433984000)), (nat_lit 2097, Int.ofNat (nat_lit 67506930565200))]
theorem block014_data_flat145_step : block014_data_flat145 = (CoefficientMerge.fastMerge block014_data_flat139 block014_data_flat144) := by decide +kernel
theorem block014_data_flat145_original : block014_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (65831614531200 : Int) atom1046Coded) (CoefficientMerge.scale (27544406400000 : Int) atom1047Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49565736486000 : Int) atom1048Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (69701433984000 : Int) atom1049Coded) (CoefficientMerge.scale (67506930565200 : Int) atom1050Coded)))) := by
  rw [block014_data_flat145_step, block014_data_flat139_original, block014_data_flat144_original]
def block014_data_flat146 : CoefficientMerge.Poly := [(nat_lit 2098, Int.ofNat (nat_lit 46776865338000))]
theorem block014_data_flat146_step : block014_data_flat146 = (CoefficientMerge.scale (46776865338000 : Int) atom1051Coded) := by decide +kernel
theorem block014_data_flat146_original : block014_data_flat146 = (CoefficientMerge.scale (46776865338000 : Int) atom1051Coded) := by
  rw [block014_data_flat146_step]
def block014_data_flat147 : CoefficientMerge.Poly := [(nat_lit 2099, Int.ofNat (nat_lit 68668144750800))]
theorem block014_data_flat147_step : block014_data_flat147 = (CoefficientMerge.scale (68668144750800 : Int) atom1052Coded) := by decide +kernel
theorem block014_data_flat147_original : block014_data_flat147 = (CoefficientMerge.scale (68668144750800 : Int) atom1052Coded) := by
  rw [block014_data_flat147_step]
def block014_data_flat148 : CoefficientMerge.Poly := [(nat_lit 2098, Int.ofNat (nat_lit 46776865338000)), (nat_lit 2099, Int.ofNat (nat_lit 68668144750800))]
theorem block014_data_flat148_step : block014_data_flat148 = (CoefficientMerge.fastMerge block014_data_flat146 block014_data_flat147) := by decide +kernel
theorem block014_data_flat148_original : block014_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (46776865338000 : Int) atom1051Coded) (CoefficientMerge.scale (68668144750800 : Int) atom1052Coded)) := by
  rw [block014_data_flat148_step, block014_data_flat146_original, block014_data_flat147_original]
def block014_data_flat149 : CoefficientMerge.Poly := [(nat_lit 2116, Int.ofNat (nat_lit 19150031093760))]
theorem block014_data_flat149_step : block014_data_flat149 = (CoefficientMerge.scale (19150031093760 : Int) atom1053Coded) := by decide +kernel
theorem block014_data_flat149_original : block014_data_flat149 = (CoefficientMerge.scale (19150031093760 : Int) atom1053Coded) := by
  rw [block014_data_flat149_step]
def block014_data_flat150 : CoefficientMerge.Poly := [(nat_lit 2117, Int.ofNat (nat_lit 54894908250000))]
theorem block014_data_flat150_step : block014_data_flat150 = (CoefficientMerge.scale (54894908250000 : Int) atom1054Coded) := by decide +kernel
theorem block014_data_flat150_original : block014_data_flat150 = (CoefficientMerge.scale (54894908250000 : Int) atom1054Coded) := by
  rw [block014_data_flat150_step]
def block014_data_flat151 : CoefficientMerge.Poly := [(nat_lit 2118, Int.ofNat (nat_lit 55511190567000))]
theorem block014_data_flat151_step : block014_data_flat151 = (CoefficientMerge.scale (55511190567000 : Int) atom1055Coded) := by decide +kernel
theorem block014_data_flat151_original : block014_data_flat151 = (CoefficientMerge.scale (55511190567000 : Int) atom1055Coded) := by
  rw [block014_data_flat151_step]
def block014_data_flat152 : CoefficientMerge.Poly := [(nat_lit 2117, Int.ofNat (nat_lit 54894908250000)), (nat_lit 2118, Int.ofNat (nat_lit 55511190567000))]
theorem block014_data_flat152_step : block014_data_flat152 = (CoefficientMerge.fastMerge block014_data_flat150 block014_data_flat151) := by decide +kernel
theorem block014_data_flat152_original : block014_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (54894908250000 : Int) atom1054Coded) (CoefficientMerge.scale (55511190567000 : Int) atom1055Coded)) := by
  rw [block014_data_flat152_step, block014_data_flat150_original, block014_data_flat151_original]
def block014_data_flat153 : CoefficientMerge.Poly := [(nat_lit 2116, Int.ofNat (nat_lit 19150031093760)), (nat_lit 2117, Int.ofNat (nat_lit 54894908250000)), (nat_lit 2118, Int.ofNat (nat_lit 55511190567000))]
theorem block014_data_flat153_step : block014_data_flat153 = (CoefficientMerge.fastMerge block014_data_flat149 block014_data_flat152) := by decide +kernel
theorem block014_data_flat153_original : block014_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (19150031093760 : Int) atom1053Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54894908250000 : Int) atom1054Coded) (CoefficientMerge.scale (55511190567000 : Int) atom1055Coded))) := by
  rw [block014_data_flat153_step, block014_data_flat149_original, block014_data_flat152_original]
def block014_data_flat154 : CoefficientMerge.Poly := [(nat_lit 2098, Int.ofNat (nat_lit 46776865338000)), (nat_lit 2099, Int.ofNat (nat_lit 68668144750800)), (nat_lit 2116, Int.ofNat (nat_lit 19150031093760)), (nat_lit 2117, Int.ofNat (nat_lit 54894908250000)), (nat_lit 2118, Int.ofNat (nat_lit 55511190567000))]
theorem block014_data_flat154_step : block014_data_flat154 = (CoefficientMerge.fastMerge block014_data_flat148 block014_data_flat153) := by decide +kernel
theorem block014_data_flat154_original : block014_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46776865338000 : Int) atom1051Coded) (CoefficientMerge.scale (68668144750800 : Int) atom1052Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19150031093760 : Int) atom1053Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54894908250000 : Int) atom1054Coded) (CoefficientMerge.scale (55511190567000 : Int) atom1055Coded)))) := by
  rw [block014_data_flat154_step, block014_data_flat148_original, block014_data_flat153_original]
def block014_data_flat155 : CoefficientMerge.Poly := [(nat_lit 2078, Int.ofNat (nat_lit 65831614531200)), (nat_lit 2094, Int.ofNat (nat_lit 27544406400000)), (nat_lit 2095, Int.ofNat (nat_lit 49565736486000)), (nat_lit 2096, Int.ofNat (nat_lit 69701433984000)), (nat_lit 2097, Int.ofNat (nat_lit 67506930565200)), (nat_lit 2098, Int.ofNat (nat_lit 46776865338000)), (nat_lit 2099, Int.ofNat (nat_lit 68668144750800)), (nat_lit 2116, Int.ofNat (nat_lit 19150031093760)), (nat_lit 2117, Int.ofNat (nat_lit 54894908250000)), (nat_lit 2118, Int.ofNat (nat_lit 55511190567000))]
theorem block014_data_flat155_step : block014_data_flat155 = (CoefficientMerge.fastMerge block014_data_flat145 block014_data_flat154) := by decide +kernel
theorem block014_data_flat155_original : block014_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (65831614531200 : Int) atom1046Coded) (CoefficientMerge.scale (27544406400000 : Int) atom1047Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49565736486000 : Int) atom1048Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (69701433984000 : Int) atom1049Coded) (CoefficientMerge.scale (67506930565200 : Int) atom1050Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46776865338000 : Int) atom1051Coded) (CoefficientMerge.scale (68668144750800 : Int) atom1052Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19150031093760 : Int) atom1053Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54894908250000 : Int) atom1054Coded) (CoefficientMerge.scale (55511190567000 : Int) atom1055Coded))))) := by
  rw [block014_data_flat155_step, block014_data_flat145_original, block014_data_flat154_original]
def block014_data_flat156 : CoefficientMerge.Poly := [(nat_lit 2054, Int.ofNat (nat_lit 47594873289600)), (nat_lit 2055, Int.ofNat (nat_lit 47799330616800)), (nat_lit 2056, Int.ofNat (nat_lit 46286873474400)), (nat_lit 2057, Int.ofNat (nat_lit 58138510147200)), (nat_lit 2072, Int.ofNat (nat_lit 23439806611200)), (nat_lit 2073, Int.ofNat (nat_lit 42456561436800)), (nat_lit 2074, Int.ofNat (nat_lit 38495120076000)), (nat_lit 2075, Int.ofNat (nat_lit 53992907337600)), (nat_lit 2076, Int.ofNat (nat_lit 55096182136800)), (nat_lit 2077, Int.ofNat (nat_lit 48432127111200)), (nat_lit 2078, Int.ofNat (nat_lit 65831614531200)), (nat_lit 2094, Int.ofNat (nat_lit 27544406400000)), (nat_lit 2095, Int.ofNat (nat_lit 49565736486000)), (nat_lit 2096, Int.ofNat (nat_lit 69701433984000)), (nat_lit 2097, Int.ofNat (nat_lit 67506930565200)), (nat_lit 2098, Int.ofNat (nat_lit 46776865338000)), (nat_lit 2099, Int.ofNat (nat_lit 68668144750800)), (nat_lit 2116, Int.ofNat (nat_lit 19150031093760)), (nat_lit 2117, Int.ofNat (nat_lit 54894908250000)), (nat_lit 2118, Int.ofNat (nat_lit 55511190567000))]
theorem block014_data_flat156_step : block014_data_flat156 = (CoefficientMerge.fastMerge block014_data_flat136 block014_data_flat155) := by decide +kernel
theorem block014_data_flat156_original : block014_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (47594873289600 : Int) atom1036Coded) (CoefficientMerge.scale (47799330616800 : Int) atom1037Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46286873474400 : Int) atom1038Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (58138510147200 : Int) atom1039Coded) (CoefficientMerge.scale (23439806611200 : Int) atom1040Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (42456561436800 : Int) atom1041Coded) (CoefficientMerge.scale (38495120076000 : Int) atom1042Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53992907337600 : Int) atom1043Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55096182136800 : Int) atom1044Coded) (CoefficientMerge.scale (48432127111200 : Int) atom1045Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (65831614531200 : Int) atom1046Coded) (CoefficientMerge.scale (27544406400000 : Int) atom1047Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49565736486000 : Int) atom1048Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (69701433984000 : Int) atom1049Coded) (CoefficientMerge.scale (67506930565200 : Int) atom1050Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46776865338000 : Int) atom1051Coded) (CoefficientMerge.scale (68668144750800 : Int) atom1052Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19150031093760 : Int) atom1053Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54894908250000 : Int) atom1054Coded) (CoefficientMerge.scale (55511190567000 : Int) atom1055Coded)))))) := by
  rw [block014_data_flat156_step, block014_data_flat136_original, block014_data_flat155_original]
def block014_data_flat157 : CoefficientMerge.Poly := [(nat_lit 2009, Int.ofNat (nat_lit 27415790035200)), (nat_lit 2010, Int.ofNat (nat_lit 34868811801600)), (nat_lit 2011, Int.ofNat (nat_lit 31796949592800)), (nat_lit 2012, Int.ofNat (nat_lit 42754799001600)), (nat_lit 2013, Int.ofNat (nat_lit 41641715556000)), (nat_lit 2014, Int.ofNat (nat_lit 48385300672800)), (nat_lit 2015, Int.ofNat (nat_lit 55128885789600)), (nat_lit 2028, Int.ofNat (nat_lit 17118445881600)), (nat_lit 2029, Int.ofNat (nat_lit 32518507392000)), (nat_lit 2030, Int.ofNat (nat_lit 31227302937600)), (nat_lit 2031, Int.ofNat (nat_lit 34633735248000)), (nat_lit 2032, Int.ofNat (nat_lit 33705364364000)), (nat_lit 2033, Int.ofNat (nat_lit 43390369097600)), (nat_lit 2034, Int.ofNat (nat_lit 42915361938400)), (nat_lit 2035, Int.ofNat (nat_lit 48592346426400)), (nat_lit 2036, Int.ofNat (nat_lit 55028408400000)), (nat_lit 2050, Int.ofNat (nat_lit 19975700563200)), (nat_lit 2051, Int.ofNat (nat_lit 36571516070400)), (nat_lit 2052, Int.ofNat (nat_lit 38601069393600)), (nat_lit 2053, Int.ofNat (nat_lit 36159816938400)), (nat_lit 2054, Int.ofNat (nat_lit 47594873289600)), (nat_lit 2055, Int.ofNat (nat_lit 47799330616800)), (nat_lit 2056, Int.ofNat (nat_lit 46286873474400)), (nat_lit 2057, Int.ofNat (nat_lit 58138510147200)), (nat_lit 2072, Int.ofNat (nat_lit 23439806611200)), (nat_lit 2073, Int.ofNat (nat_lit 42456561436800)), (nat_lit 2074, Int.ofNat (nat_lit 38495120076000)), (nat_lit 2075, Int.ofNat (nat_lit 53992907337600)), (nat_lit 2076, Int.ofNat (nat_lit 55096182136800)), (nat_lit 2077, Int.ofNat (nat_lit 48432127111200)), (nat_lit 2078, Int.ofNat (nat_lit 65831614531200)), (nat_lit 2094, Int.ofNat (nat_lit 27544406400000)), (nat_lit 2095, Int.ofNat (nat_lit 49565736486000)), (nat_lit 2096, Int.ofNat (nat_lit 69701433984000)), (nat_lit 2097, Int.ofNat (nat_lit 67506930565200)), (nat_lit 2098, Int.ofNat (nat_lit 46776865338000)), (nat_lit 2099, Int.ofNat (nat_lit 68668144750800)), (nat_lit 2116, Int.ofNat (nat_lit 19150031093760)), (nat_lit 2117, Int.ofNat (nat_lit 54894908250000)), (nat_lit 2118, Int.ofNat (nat_lit 55511190567000))]
theorem block014_data_flat157_step : block014_data_flat157 = (CoefficientMerge.fastMerge block014_data_flat117 block014_data_flat156) := by decide +kernel
theorem block014_data_flat157_original : block014_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (27415790035200 : Int) atom1016Coded) (CoefficientMerge.scale (34868811801600 : Int) atom1017Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31796949592800 : Int) atom1018Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42754799001600 : Int) atom1019Coded) (CoefficientMerge.scale (41641715556000 : Int) atom1020Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48385300672800 : Int) atom1021Coded) (CoefficientMerge.scale (55128885789600 : Int) atom1022Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17118445881600 : Int) atom1023Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32518507392000 : Int) atom1024Coded) (CoefficientMerge.scale (31227302937600 : Int) atom1025Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34633735248000 : Int) atom1026Coded) (CoefficientMerge.scale (33705364364000 : Int) atom1027Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43390369097600 : Int) atom1028Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42915361938400 : Int) atom1029Coded) (CoefficientMerge.scale (48592346426400 : Int) atom1030Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55028408400000 : Int) atom1031Coded) (CoefficientMerge.scale (19975700563200 : Int) atom1032Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36571516070400 : Int) atom1033Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38601069393600 : Int) atom1034Coded) (CoefficientMerge.scale (36159816938400 : Int) atom1035Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (47594873289600 : Int) atom1036Coded) (CoefficientMerge.scale (47799330616800 : Int) atom1037Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46286873474400 : Int) atom1038Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (58138510147200 : Int) atom1039Coded) (CoefficientMerge.scale (23439806611200 : Int) atom1040Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (42456561436800 : Int) atom1041Coded) (CoefficientMerge.scale (38495120076000 : Int) atom1042Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53992907337600 : Int) atom1043Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55096182136800 : Int) atom1044Coded) (CoefficientMerge.scale (48432127111200 : Int) atom1045Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (65831614531200 : Int) atom1046Coded) (CoefficientMerge.scale (27544406400000 : Int) atom1047Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49565736486000 : Int) atom1048Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (69701433984000 : Int) atom1049Coded) (CoefficientMerge.scale (67506930565200 : Int) atom1050Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46776865338000 : Int) atom1051Coded) (CoefficientMerge.scale (68668144750800 : Int) atom1052Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19150031093760 : Int) atom1053Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54894908250000 : Int) atom1054Coded) (CoefficientMerge.scale (55511190567000 : Int) atom1055Coded))))))) := by
  rw [block014_data_flat157_step, block014_data_flat117_original, block014_data_flat156_original]
def block014_data_flat158 : CoefficientMerge.Poly := [(nat_lit 1931, Int.ofNat (nat_lit 37738841800608)), (nat_lit 1940, Int.ofNat (nat_lit 8316316713600)), (nat_lit 1941, Int.ofNat (nat_lit 14616092937600)), (nat_lit 1942, Int.ofNat (nat_lit 14686645276800)), (nat_lit 1943, Int.ofNat (nat_lit 14704288099200)), (nat_lit 1944, Int.ofNat (nat_lit 13399306704000)), (nat_lit 1945, Int.ofNat (nat_lit 14099031273600)), (nat_lit 1946, Int.ofNat (nat_lit 14798755843200)), (nat_lit 1947, Int.ofNat (nat_lit 23245546060800)), (nat_lit 1948, Int.ofNat (nat_lit 20719776344400)), (nat_lit 1949, Int.ofNat (nat_lit 26086557772800)), (nat_lit 1950, Int.ofNat (nat_lit 31162368207600)), (nat_lit 1951, Int.ofNat (nat_lit 37890854593200)), (nat_lit 1952, Int.ofNat (nat_lit 44619340978800)), (nat_lit 1962, Int.ofNat (nat_lit 10739741241600)), (nat_lit 1963, Int.ofNat (nat_lit 19770762816000)), (nat_lit 1964, Int.ofNat (nat_lit 19283908089600)), (nat_lit 1965, Int.ofNat (nat_lit 18160623129600)), (nat_lit 1966, Int.ofNat (nat_lit 18614864217600)), (nat_lit 1967, Int.ofNat (nat_lit 19069105305600)), (nat_lit 1968, Int.ofNat (nat_lit 27327917030400)), (nat_lit 1969, Int.ofNat (nat_lit 24967957392000)), (nat_lit 1970, Int.ofNat (nat_lit 31850587238400)), (nat_lit 1971, Int.ofNat (nat_lit 35857179388800)), (nat_lit 1972, Int.ofNat (nat_lit 42965247024000)), (nat_lit 1973, Int.ofNat (nat_lit 50073314659200)), (nat_lit 1984, Int.ofNat (nat_lit 13470986592000)), (nat_lit 1985, Int.ofNat (nat_lit 25277957510400)), (nat_lit 1986, Int.ofNat (nat_lit 23313843302400)), (nat_lit 1987, Int.ofNat (nat_lit 23354435059200)), (nat_lit 1988, Int.ofNat (nat_lit 23395026816000)), (nat_lit 1989, Int.ofNat (nat_lit 31410288000000)), (nat_lit 1990, Int.ofNat (nat_lit 28735500628800)), (nat_lit 1991, Int.ofNat (nat_lit 37614616704000)), (nat_lit 1992, Int.ofNat (nat_lit 39335264740800)), (nat_lit 1993, Int.ofNat (nat_lit 46388243563200)), (nat_lit 1994, Int.ofNat (nat_lit 53441222385600)), (nat_lit 2006, Int.ofNat (nat_lit 16246935936000)), (nat_lit 2007, Int.ofNat (nat_lit 28498236883200)), (nat_lit 2008, Int.ofNat (nat_lit 27957013459200)), (nat_lit 2009, Int.ofNat (nat_lit 27415790035200)), (nat_lit 2010, Int.ofNat (nat_lit 34868811801600)), (nat_lit 2011, Int.ofNat (nat_lit 31796949592800)), (nat_lit 2012, Int.ofNat (nat_lit 42754799001600)), (nat_lit 2013, Int.ofNat (nat_lit 41641715556000)), (nat_lit 2014, Int.ofNat (nat_lit 48385300672800)), (nat_lit 2015, Int.ofNat (nat_lit 55128885789600)), (nat_lit 2028, Int.ofNat (nat_lit 17118445881600)), (nat_lit 2029, Int.ofNat (nat_lit 32518507392000)), (nat_lit 2030, Int.ofNat (nat_lit 31227302937600)), (nat_lit 2031, Int.ofNat (nat_lit 34633735248000)), (nat_lit 2032, Int.ofNat (nat_lit 33705364364000)), (nat_lit 2033, Int.ofNat (nat_lit 43390369097600)), (nat_lit 2034, Int.ofNat (nat_lit 42915361938400)), (nat_lit 2035, Int.ofNat (nat_lit 48592346426400)), (nat_lit 2036, Int.ofNat (nat_lit 55028408400000)), (nat_lit 2050, Int.ofNat (nat_lit 19975700563200)), (nat_lit 2051, Int.ofNat (nat_lit 36571516070400)), (nat_lit 2052, Int.ofNat (nat_lit 38601069393600)), (nat_lit 2053, Int.ofNat (nat_lit 36159816938400)), (nat_lit 2054, Int.ofNat (nat_lit 47594873289600)), (nat_lit 2055, Int.ofNat (nat_lit 47799330616800)), (nat_lit 2056, Int.ofNat (nat_lit 46286873474400)), (nat_lit 2057, Int.ofNat (nat_lit 58138510147200)), (nat_lit 2072, Int.ofNat (nat_lit 23439806611200)), (nat_lit 2073, Int.ofNat (nat_lit 42456561436800)), (nat_lit 2074, Int.ofNat (nat_lit 38495120076000)), (nat_lit 2075, Int.ofNat (nat_lit 53992907337600)), (nat_lit 2076, Int.ofNat (nat_lit 55096182136800)), (nat_lit 2077, Int.ofNat (nat_lit 48432127111200)), (nat_lit 2078, Int.ofNat (nat_lit 65831614531200)), (nat_lit 2094, Int.ofNat (nat_lit 27544406400000)), (nat_lit 2095, Int.ofNat (nat_lit 49565736486000)), (nat_lit 2096, Int.ofNat (nat_lit 69701433984000)), (nat_lit 2097, Int.ofNat (nat_lit 67506930565200)), (nat_lit 2098, Int.ofNat (nat_lit 46776865338000)), (nat_lit 2099, Int.ofNat (nat_lit 68668144750800)), (nat_lit 2116, Int.ofNat (nat_lit 19150031093760)), (nat_lit 2117, Int.ofNat (nat_lit 54894908250000)), (nat_lit 2118, Int.ofNat (nat_lit 55511190567000))]
theorem block014_data_flat158_step : block014_data_flat158 = (CoefficientMerge.fastMerge block014_data_flat078 block014_data_flat157) := by decide +kernel
theorem block014_data_flat158_original : block014_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37738841800608 : Int) atom0976Coded) (CoefficientMerge.scale (8316316713600 : Int) atom0977Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14616092937600 : Int) atom0978Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14686645276800 : Int) atom0979Coded) (CoefficientMerge.scale (14704288099200 : Int) atom0980Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13399306704000 : Int) atom0981Coded) (CoefficientMerge.scale (14099031273600 : Int) atom0982Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14798755843200 : Int) atom0983Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23245546060800 : Int) atom0984Coded) (CoefficientMerge.scale (20719776344400 : Int) atom0985Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26086557772800 : Int) atom0986Coded) (CoefficientMerge.scale (31162368207600 : Int) atom0987Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37890854593200 : Int) atom0988Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44619340978800 : Int) atom0989Coded) (CoefficientMerge.scale (10739741241600 : Int) atom0990Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19770762816000 : Int) atom0991Coded) (CoefficientMerge.scale (19283908089600 : Int) atom0992Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18160623129600 : Int) atom0993Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18614864217600 : Int) atom0994Coded) (CoefficientMerge.scale (19069105305600 : Int) atom0995Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (27327917030400 : Int) atom0996Coded) (CoefficientMerge.scale (24967957392000 : Int) atom0997Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31850587238400 : Int) atom0998Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35857179388800 : Int) atom0999Coded) (CoefficientMerge.scale (42965247024000 : Int) atom1000Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (50073314659200 : Int) atom1001Coded) (CoefficientMerge.scale (13470986592000 : Int) atom1002Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25277957510400 : Int) atom1003Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23313843302400 : Int) atom1004Coded) (CoefficientMerge.scale (23354435059200 : Int) atom1005Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23395026816000 : Int) atom1006Coded) (CoefficientMerge.scale (31410288000000 : Int) atom1007Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28735500628800 : Int) atom1008Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37614616704000 : Int) atom1009Coded) (CoefficientMerge.scale (39335264740800 : Int) atom1010Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46388243563200 : Int) atom1011Coded) (CoefficientMerge.scale (53441222385600 : Int) atom1012Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16246935936000 : Int) atom1013Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28498236883200 : Int) atom1014Coded) (CoefficientMerge.scale (27957013459200 : Int) atom1015Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (27415790035200 : Int) atom1016Coded) (CoefficientMerge.scale (34868811801600 : Int) atom1017Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31796949592800 : Int) atom1018Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42754799001600 : Int) atom1019Coded) (CoefficientMerge.scale (41641715556000 : Int) atom1020Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48385300672800 : Int) atom1021Coded) (CoefficientMerge.scale (55128885789600 : Int) atom1022Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17118445881600 : Int) atom1023Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32518507392000 : Int) atom1024Coded) (CoefficientMerge.scale (31227302937600 : Int) atom1025Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34633735248000 : Int) atom1026Coded) (CoefficientMerge.scale (33705364364000 : Int) atom1027Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43390369097600 : Int) atom1028Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42915361938400 : Int) atom1029Coded) (CoefficientMerge.scale (48592346426400 : Int) atom1030Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55028408400000 : Int) atom1031Coded) (CoefficientMerge.scale (19975700563200 : Int) atom1032Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36571516070400 : Int) atom1033Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38601069393600 : Int) atom1034Coded) (CoefficientMerge.scale (36159816938400 : Int) atom1035Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (47594873289600 : Int) atom1036Coded) (CoefficientMerge.scale (47799330616800 : Int) atom1037Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46286873474400 : Int) atom1038Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (58138510147200 : Int) atom1039Coded) (CoefficientMerge.scale (23439806611200 : Int) atom1040Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (42456561436800 : Int) atom1041Coded) (CoefficientMerge.scale (38495120076000 : Int) atom1042Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53992907337600 : Int) atom1043Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55096182136800 : Int) atom1044Coded) (CoefficientMerge.scale (48432127111200 : Int) atom1045Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (65831614531200 : Int) atom1046Coded) (CoefficientMerge.scale (27544406400000 : Int) atom1047Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49565736486000 : Int) atom1048Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (69701433984000 : Int) atom1049Coded) (CoefficientMerge.scale (67506930565200 : Int) atom1050Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46776865338000 : Int) atom1051Coded) (CoefficientMerge.scale (68668144750800 : Int) atom1052Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19150031093760 : Int) atom1053Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54894908250000 : Int) atom1054Coded) (CoefficientMerge.scale (55511190567000 : Int) atom1055Coded)))))))) := by
  rw [block014_data_flat158_step, block014_data_flat078_original, block014_data_flat157_original]
def block014_data_flat159 : CoefficientMerge.Poly := [(nat_lit 1931, Int.ofNat (nat_lit 37738841800608)), (nat_lit 1940, Int.ofNat (nat_lit 8316316713600)), (nat_lit 1941, Int.ofNat (nat_lit 14616092937600)), (nat_lit 1942, Int.ofNat (nat_lit 14686645276800)), (nat_lit 1943, Int.ofNat (nat_lit 14704288099200)), (nat_lit 1944, Int.ofNat (nat_lit 13399306704000)), (nat_lit 1945, Int.ofNat (nat_lit 14099031273600)), (nat_lit 1946, Int.ofNat (nat_lit 14798755843200)), (nat_lit 1947, Int.ofNat (nat_lit 23245546060800)), (nat_lit 1948, Int.ofNat (nat_lit 20719776344400)), (nat_lit 1949, Int.ofNat (nat_lit 26086557772800)), (nat_lit 1950, Int.ofNat (nat_lit 31162368207600)), (nat_lit 1951, Int.ofNat (nat_lit 37890854593200)), (nat_lit 1952, Int.ofNat (nat_lit 44619340978800)), (nat_lit 1962, Int.ofNat (nat_lit 10739741241600)), (nat_lit 1963, Int.ofNat (nat_lit 19770762816000)), (nat_lit 1964, Int.ofNat (nat_lit 19283908089600)), (nat_lit 1965, Int.ofNat (nat_lit 18160623129600)), (nat_lit 1966, Int.ofNat (nat_lit 18614864217600)), (nat_lit 1967, Int.ofNat (nat_lit 19069105305600)), (nat_lit 1968, Int.ofNat (nat_lit 27327917030400)), (nat_lit 1969, Int.ofNat (nat_lit 24967957392000)), (nat_lit 1970, Int.ofNat (nat_lit 31850587238400)), (nat_lit 1971, Int.ofNat (nat_lit 35857179388800)), (nat_lit 1972, Int.ofNat (nat_lit 42965247024000)), (nat_lit 1973, Int.ofNat (nat_lit 50073314659200)), (nat_lit 1984, Int.ofNat (nat_lit 13470986592000)), (nat_lit 1985, Int.ofNat (nat_lit 25277957510400)), (nat_lit 1986, Int.ofNat (nat_lit 23313843302400)), (nat_lit 1987, Int.ofNat (nat_lit 23354435059200)), (nat_lit 1988, Int.ofNat (nat_lit 23395026816000)), (nat_lit 1989, Int.ofNat (nat_lit 31410288000000)), (nat_lit 1990, Int.ofNat (nat_lit 28735500628800)), (nat_lit 1991, Int.ofNat (nat_lit 37614616704000)), (nat_lit 1992, Int.ofNat (nat_lit 39335264740800)), (nat_lit 1993, Int.ofNat (nat_lit 46388243563200)), (nat_lit 1994, Int.ofNat (nat_lit 53441222385600)), (nat_lit 2006, Int.ofNat (nat_lit 16246935936000)), (nat_lit 2007, Int.ofNat (nat_lit 28498236883200)), (nat_lit 2008, Int.ofNat (nat_lit 27957013459200)), (nat_lit 2009, Int.ofNat (nat_lit 27415790035200)), (nat_lit 2010, Int.ofNat (nat_lit 34868811801600)), (nat_lit 2011, Int.ofNat (nat_lit 31796949592800)), (nat_lit 2012, Int.ofNat (nat_lit 42754799001600)), (nat_lit 2013, Int.ofNat (nat_lit 41641715556000)), (nat_lit 2014, Int.ofNat (nat_lit 48385300672800)), (nat_lit 2015, Int.ofNat (nat_lit 55128885789600)), (nat_lit 2028, Int.ofNat (nat_lit 17118445881600)), (nat_lit 2029, Int.ofNat (nat_lit 32518507392000)), (nat_lit 2030, Int.ofNat (nat_lit 31227302937600)), (nat_lit 2031, Int.ofNat (nat_lit 34633735248000)), (nat_lit 2032, Int.ofNat (nat_lit 33705364364000)), (nat_lit 2033, Int.ofNat (nat_lit 43390369097600)), (nat_lit 2034, Int.ofNat (nat_lit 42915361938400)), (nat_lit 2035, Int.ofNat (nat_lit 48592346426400)), (nat_lit 2036, Int.ofNat (nat_lit 55028408400000)), (nat_lit 2050, Int.ofNat (nat_lit 19975700563200)), (nat_lit 2051, Int.ofNat (nat_lit 36571516070400)), (nat_lit 2052, Int.ofNat (nat_lit 38601069393600)), (nat_lit 2053, Int.ofNat (nat_lit 36159816938400)), (nat_lit 2054, Int.ofNat (nat_lit 47594873289600)), (nat_lit 2055, Int.ofNat (nat_lit 47799330616800)), (nat_lit 2056, Int.ofNat (nat_lit 46286873474400)), (nat_lit 2057, Int.ofNat (nat_lit 58138510147200)), (nat_lit 2072, Int.ofNat (nat_lit 23439806611200)), (nat_lit 2073, Int.ofNat (nat_lit 42456561436800)), (nat_lit 2074, Int.ofNat (nat_lit 38495120076000)), (nat_lit 2075, Int.ofNat (nat_lit 53992907337600)), (nat_lit 2076, Int.ofNat (nat_lit 55096182136800)), (nat_lit 2077, Int.ofNat (nat_lit 48432127111200)), (nat_lit 2078, Int.ofNat (nat_lit 65831614531200)), (nat_lit 2094, Int.ofNat (nat_lit 27544406400000)), (nat_lit 2095, Int.ofNat (nat_lit 49565736486000)), (nat_lit 2096, Int.ofNat (nat_lit 69701433984000)), (nat_lit 2097, Int.ofNat (nat_lit 67506930565200)), (nat_lit 2098, Int.ofNat (nat_lit 46776865338000)), (nat_lit 2099, Int.ofNat (nat_lit 68668144750800)), (nat_lit 2116, Int.ofNat (nat_lit 19150031093760)), (nat_lit 2117, Int.ofNat (nat_lit 54894908250000)), (nat_lit 2118, Int.ofNat (nat_lit 55511190567000))]
theorem block014_data_flat159_step : block014_data_flat159 = (CoefficientMerge.trim block014_data_flat158) := by decide +kernel
theorem block014_data_flat159_original : block014_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37738841800608 : Int) atom0976Coded) (CoefficientMerge.scale (8316316713600 : Int) atom0977Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14616092937600 : Int) atom0978Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14686645276800 : Int) atom0979Coded) (CoefficientMerge.scale (14704288099200 : Int) atom0980Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13399306704000 : Int) atom0981Coded) (CoefficientMerge.scale (14099031273600 : Int) atom0982Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14798755843200 : Int) atom0983Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23245546060800 : Int) atom0984Coded) (CoefficientMerge.scale (20719776344400 : Int) atom0985Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26086557772800 : Int) atom0986Coded) (CoefficientMerge.scale (31162368207600 : Int) atom0987Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37890854593200 : Int) atom0988Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44619340978800 : Int) atom0989Coded) (CoefficientMerge.scale (10739741241600 : Int) atom0990Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19770762816000 : Int) atom0991Coded) (CoefficientMerge.scale (19283908089600 : Int) atom0992Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18160623129600 : Int) atom0993Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18614864217600 : Int) atom0994Coded) (CoefficientMerge.scale (19069105305600 : Int) atom0995Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (27327917030400 : Int) atom0996Coded) (CoefficientMerge.scale (24967957392000 : Int) atom0997Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31850587238400 : Int) atom0998Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35857179388800 : Int) atom0999Coded) (CoefficientMerge.scale (42965247024000 : Int) atom1000Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (50073314659200 : Int) atom1001Coded) (CoefficientMerge.scale (13470986592000 : Int) atom1002Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25277957510400 : Int) atom1003Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23313843302400 : Int) atom1004Coded) (CoefficientMerge.scale (23354435059200 : Int) atom1005Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23395026816000 : Int) atom1006Coded) (CoefficientMerge.scale (31410288000000 : Int) atom1007Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28735500628800 : Int) atom1008Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37614616704000 : Int) atom1009Coded) (CoefficientMerge.scale (39335264740800 : Int) atom1010Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46388243563200 : Int) atom1011Coded) (CoefficientMerge.scale (53441222385600 : Int) atom1012Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16246935936000 : Int) atom1013Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28498236883200 : Int) atom1014Coded) (CoefficientMerge.scale (27957013459200 : Int) atom1015Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (27415790035200 : Int) atom1016Coded) (CoefficientMerge.scale (34868811801600 : Int) atom1017Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31796949592800 : Int) atom1018Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42754799001600 : Int) atom1019Coded) (CoefficientMerge.scale (41641715556000 : Int) atom1020Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48385300672800 : Int) atom1021Coded) (CoefficientMerge.scale (55128885789600 : Int) atom1022Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17118445881600 : Int) atom1023Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32518507392000 : Int) atom1024Coded) (CoefficientMerge.scale (31227302937600 : Int) atom1025Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34633735248000 : Int) atom1026Coded) (CoefficientMerge.scale (33705364364000 : Int) atom1027Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43390369097600 : Int) atom1028Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42915361938400 : Int) atom1029Coded) (CoefficientMerge.scale (48592346426400 : Int) atom1030Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55028408400000 : Int) atom1031Coded) (CoefficientMerge.scale (19975700563200 : Int) atom1032Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36571516070400 : Int) atom1033Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38601069393600 : Int) atom1034Coded) (CoefficientMerge.scale (36159816938400 : Int) atom1035Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (47594873289600 : Int) atom1036Coded) (CoefficientMerge.scale (47799330616800 : Int) atom1037Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46286873474400 : Int) atom1038Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (58138510147200 : Int) atom1039Coded) (CoefficientMerge.scale (23439806611200 : Int) atom1040Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (42456561436800 : Int) atom1041Coded) (CoefficientMerge.scale (38495120076000 : Int) atom1042Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53992907337600 : Int) atom1043Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55096182136800 : Int) atom1044Coded) (CoefficientMerge.scale (48432127111200 : Int) atom1045Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (65831614531200 : Int) atom1046Coded) (CoefficientMerge.scale (27544406400000 : Int) atom1047Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49565736486000 : Int) atom1048Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (69701433984000 : Int) atom1049Coded) (CoefficientMerge.scale (67506930565200 : Int) atom1050Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46776865338000 : Int) atom1051Coded) (CoefficientMerge.scale (68668144750800 : Int) atom1052Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19150031093760 : Int) atom1053Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54894908250000 : Int) atom1054Coded) (CoefficientMerge.scale (55511190567000 : Int) atom1055Coded))))))))) := by
  rw [block014_data_flat159_step, block014_data_flat158_original]
theorem block014_data : block014 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37738841800608 : Int) atom0976Coded) (CoefficientMerge.scale (8316316713600 : Int) atom0977Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14616092937600 : Int) atom0978Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14686645276800 : Int) atom0979Coded) (CoefficientMerge.scale (14704288099200 : Int) atom0980Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13399306704000 : Int) atom0981Coded) (CoefficientMerge.scale (14099031273600 : Int) atom0982Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14798755843200 : Int) atom0983Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23245546060800 : Int) atom0984Coded) (CoefficientMerge.scale (20719776344400 : Int) atom0985Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26086557772800 : Int) atom0986Coded) (CoefficientMerge.scale (31162368207600 : Int) atom0987Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37890854593200 : Int) atom0988Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44619340978800 : Int) atom0989Coded) (CoefficientMerge.scale (10739741241600 : Int) atom0990Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19770762816000 : Int) atom0991Coded) (CoefficientMerge.scale (19283908089600 : Int) atom0992Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18160623129600 : Int) atom0993Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18614864217600 : Int) atom0994Coded) (CoefficientMerge.scale (19069105305600 : Int) atom0995Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (27327917030400 : Int) atom0996Coded) (CoefficientMerge.scale (24967957392000 : Int) atom0997Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31850587238400 : Int) atom0998Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35857179388800 : Int) atom0999Coded) (CoefficientMerge.scale (42965247024000 : Int) atom1000Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (50073314659200 : Int) atom1001Coded) (CoefficientMerge.scale (13470986592000 : Int) atom1002Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25277957510400 : Int) atom1003Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23313843302400 : Int) atom1004Coded) (CoefficientMerge.scale (23354435059200 : Int) atom1005Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23395026816000 : Int) atom1006Coded) (CoefficientMerge.scale (31410288000000 : Int) atom1007Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28735500628800 : Int) atom1008Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37614616704000 : Int) atom1009Coded) (CoefficientMerge.scale (39335264740800 : Int) atom1010Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46388243563200 : Int) atom1011Coded) (CoefficientMerge.scale (53441222385600 : Int) atom1012Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16246935936000 : Int) atom1013Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28498236883200 : Int) atom1014Coded) (CoefficientMerge.scale (27957013459200 : Int) atom1015Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (27415790035200 : Int) atom1016Coded) (CoefficientMerge.scale (34868811801600 : Int) atom1017Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31796949592800 : Int) atom1018Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42754799001600 : Int) atom1019Coded) (CoefficientMerge.scale (41641715556000 : Int) atom1020Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48385300672800 : Int) atom1021Coded) (CoefficientMerge.scale (55128885789600 : Int) atom1022Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17118445881600 : Int) atom1023Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32518507392000 : Int) atom1024Coded) (CoefficientMerge.scale (31227302937600 : Int) atom1025Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34633735248000 : Int) atom1026Coded) (CoefficientMerge.scale (33705364364000 : Int) atom1027Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43390369097600 : Int) atom1028Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42915361938400 : Int) atom1029Coded) (CoefficientMerge.scale (48592346426400 : Int) atom1030Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55028408400000 : Int) atom1031Coded) (CoefficientMerge.scale (19975700563200 : Int) atom1032Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36571516070400 : Int) atom1033Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38601069393600 : Int) atom1034Coded) (CoefficientMerge.scale (36159816938400 : Int) atom1035Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (47594873289600 : Int) atom1036Coded) (CoefficientMerge.scale (47799330616800 : Int) atom1037Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46286873474400 : Int) atom1038Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (58138510147200 : Int) atom1039Coded) (CoefficientMerge.scale (23439806611200 : Int) atom1040Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (42456561436800 : Int) atom1041Coded) (CoefficientMerge.scale (38495120076000 : Int) atom1042Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53992907337600 : Int) atom1043Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55096182136800 : Int) atom1044Coded) (CoefficientMerge.scale (48432127111200 : Int) atom1045Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (65831614531200 : Int) atom1046Coded) (CoefficientMerge.scale (27544406400000 : Int) atom1047Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49565736486000 : Int) atom1048Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (69701433984000 : Int) atom1049Coded) (CoefficientMerge.scale (67506930565200 : Int) atom1050Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46776865338000 : Int) atom1051Coded) (CoefficientMerge.scale (68668144750800 : Int) atom1052Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19150031093760 : Int) atom1053Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54894908250000 : Int) atom1054Coded) (CoefficientMerge.scale (55511190567000 : Int) atom1055Coded)))))))) := by
  have h : block014 = block014_data_flat159 := by decide +kernel
  exact h.trans block014_data_flat159_original
theorem block014_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) block014 := by
  rw [block014_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0976Coded_nonneg g hg hA hB) (atom0977Coded_nonneg g hg hA hB)) (add_nonneg (atom0978Coded_nonneg g hg hA hB) (add_nonneg (atom0979Coded_nonneg g hg hA hB) (atom0980Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0981Coded_nonneg g hg hA hB) (atom0982Coded_nonneg g hg hA hB)) (add_nonneg (atom0983Coded_nonneg g hg hA hB) (add_nonneg (atom0984Coded_nonneg g hg hA hB) (atom0985Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0986Coded_nonneg g hg hA hB) (atom0987Coded_nonneg g hg hA hB)) (add_nonneg (atom0988Coded_nonneg g hg hA hB) (add_nonneg (atom0989Coded_nonneg g hg hA hB) (atom0990Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0991Coded_nonneg g hg hA hB) (atom0992Coded_nonneg g hg hA hB)) (add_nonneg (atom0993Coded_nonneg g hg hA hB) (add_nonneg (atom0994Coded_nonneg g hg hA hB) (atom0995Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0996Coded_nonneg g hg hA hB) (atom0997Coded_nonneg g hg hA hB)) (add_nonneg (atom0998Coded_nonneg g hg hA hB) (add_nonneg (atom0999Coded_nonneg g hg hA hB) (atom1000Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1001Coded_nonneg g hg hA hB) (atom1002Coded_nonneg g hg hA hB)) (add_nonneg (atom1003Coded_nonneg g hg hA hB) (add_nonneg (atom1004Coded_nonneg g hg hA hB) (atom1005Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1006Coded_nonneg g hg hA hB) (atom1007Coded_nonneg g hg hA hB)) (add_nonneg (atom1008Coded_nonneg g hg hA hB) (add_nonneg (atom1009Coded_nonneg g hg hA hB) (atom1010Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1011Coded_nonneg g hg hA hB) (atom1012Coded_nonneg g hg hA hB)) (add_nonneg (atom1013Coded_nonneg g hg hA hB) (add_nonneg (atom1014Coded_nonneg g hg hA hB) (atom1015Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1016Coded_nonneg g hg hA hB) (atom1017Coded_nonneg g hg hA hB)) (add_nonneg (atom1018Coded_nonneg g hg hA hB) (add_nonneg (atom1019Coded_nonneg g hg hA hB) (atom1020Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1021Coded_nonneg g hg hA hB) (atom1022Coded_nonneg g hg hA hB)) (add_nonneg (atom1023Coded_nonneg g hg hA hB) (add_nonneg (atom1024Coded_nonneg g hg hA hB) (atom1025Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1026Coded_nonneg g hg hA hB) (atom1027Coded_nonneg g hg hA hB)) (add_nonneg (atom1028Coded_nonneg g hg hA hB) (add_nonneg (atom1029Coded_nonneg g hg hA hB) (atom1030Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1031Coded_nonneg g hg hA hB) (atom1032Coded_nonneg g hg hA hB)) (add_nonneg (atom1033Coded_nonneg g hg hA hB) (add_nonneg (atom1034Coded_nonneg g hg hA hB) (atom1035Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1036Coded_nonneg g hg hA hB) (atom1037Coded_nonneg g hg hA hB)) (add_nonneg (atom1038Coded_nonneg g hg hA hB) (add_nonneg (atom1039Coded_nonneg g hg hA hB) (atom1040Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1041Coded_nonneg g hg hA hB) (atom1042Coded_nonneg g hg hA hB)) (add_nonneg (atom1043Coded_nonneg g hg hA hB) (add_nonneg (atom1044Coded_nonneg g hg hA hB) (atom1045Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1046Coded_nonneg g hg hA hB) (atom1047Coded_nonneg g hg hA hB)) (add_nonneg (atom1048Coded_nonneg g hg hA hB) (add_nonneg (atom1049Coded_nonneg g hg hA hB) (atom1050Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1051Coded_nonneg g hg hA hB) (atom1052Coded_nonneg g hg hA hB)) (add_nonneg (atom1053Coded_nonneg g hg hA hB) (add_nonneg (atom1054Coded_nonneg g hg hA hB) (atom1055Coded_nonneg g hg hA hB))))))))

end APPT.Finite21
