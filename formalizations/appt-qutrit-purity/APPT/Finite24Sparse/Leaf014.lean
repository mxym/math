import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom0929 : SparsePolynomial.Poly := [([2,10,13], 1)]
theorem eval_atom0929 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0929 = ((g 2) * (g 10) * (g 13)) := by
  norm_num [atom0929, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0929_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (403961087933568 : Int) atom0929) := by
  rw [SparsePolynomial.eval_scale, eval_atom0929]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0930 : SparsePolynomial.Poly := [([2,10,14], 1)]
theorem eval_atom0930 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0930 = ((g 2) * (g 10) * (g 14)) := by
  norm_num [atom0930, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0930_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (381526078906368 : Int) atom0930) := by
  rw [SparsePolynomial.eval_scale, eval_atom0930]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0931 : SparsePolynomial.Poly := [([2,10,15], 1)]
theorem eval_atom0931 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0931 = ((g 2) * (g 10) * (g 15)) := by
  norm_num [atom0931, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0931_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (373878076474368 : Int) atom0931) := by
  rw [SparsePolynomial.eval_scale, eval_atom0931]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0932 : SparsePolynomial.Poly := [([2,10,16], 1)]
theorem eval_atom0932 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0932 = ((g 2) * (g 10) * (g 16)) := by
  norm_num [atom0932, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0932_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (354407563795968 : Int) atom0932) := by
  rw [SparsePolynomial.eval_scale, eval_atom0932]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0933 : SparsePolynomial.Poly := [([2,10,17], 1)]
theorem eval_atom0933 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0933 = ((g 2) * (g 10) * (g 17)) := by
  norm_num [atom0933, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0933_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (344869789575168 : Int) atom0933) := by
  rw [SparsePolynomial.eval_scale, eval_atom0933]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0934 : SparsePolynomial.Poly := [([2,10,18], 1)]
theorem eval_atom0934 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0934 = ((g 2) * (g 10) * (g 18)) := by
  norm_num [atom0934, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0934_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (379974615939072 : Int) atom0934) := by
  rw [SparsePolynomial.eval_scale, eval_atom0934]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0935 : SparsePolynomial.Poly := [([2,10,19], 1)]
theorem eval_atom0935 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0935 = ((g 2) * (g 10) * (g 19)) := by
  norm_num [atom0935, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0935_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (329477914529280 : Int) atom0935) := by
  rw [SparsePolynomial.eval_scale, eval_atom0935]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0936 : SparsePolynomial.Poly := [([2,10,20], 1)]
theorem eval_atom0936 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0936 = ((g 2) * (g 10) * (g 20)) := by
  norm_num [atom0936, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0936_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (419823011570688 : Int) atom0936) := by
  rw [SparsePolynomial.eval_scale, eval_atom0936]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 10) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0937 : SparsePolynomial.Poly := [([2,10,21], 1)]
theorem eval_atom0937 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0937 = ((g 2) * (g 10) * (g 21)) := by
  norm_num [atom0937, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0937_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (399350123656704 : Int) atom0937) := by
  rw [SparsePolynomial.eval_scale, eval_atom0937]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 10) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0938 : SparsePolynomial.Poly := [([2,10,22], 1)]
theorem eval_atom0938 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0938 = ((g 2) * (g 10) * (g 22)) := by
  norm_num [atom0938, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0938_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (445024402859520 : Int) atom0938) := by
  rw [SparsePolynomial.eval_scale, eval_atom0938]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 10) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0939 : SparsePolynomial.Poly := [([2,10,23], 1)]
theorem eval_atom0939 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0939 = ((g 2) * (g 10) * (g 23)) := by
  norm_num [atom0939, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0939_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (523432068039936 : Int) atom0939) := by
  rw [SparsePolynomial.eval_scale, eval_atom0939]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 10) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0940 : SparsePolynomial.Poly := [([2,11,11], 1)]
theorem eval_atom0940 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0940 = ((g 2) * (g 11) * (g 11)) := by
  norm_num [atom0940, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0940_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (247082976765504 : Int) atom0940) := by
  rw [SparsePolynomial.eval_scale, eval_atom0940]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0941 : SparsePolynomial.Poly := [([2,11,12], 1)]
theorem eval_atom0941 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0941 = ((g 2) * (g 11) * (g 12)) := by
  norm_num [atom0941, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0941_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (484045607060928 : Int) atom0941) := by
  rw [SparsePolynomial.eval_scale, eval_atom0941]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0942 : SparsePolynomial.Poly := [([2,11,13], 1)]
theorem eval_atom0942 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0942 = ((g 2) * (g 11) * (g 13)) := by
  norm_num [atom0942, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0942_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (457120118911104 : Int) atom0942) := by
  rw [SparsePolynomial.eval_scale, eval_atom0942]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0943 : SparsePolynomial.Poly := [([2,11,14], 1)]
theorem eval_atom0943 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0943 = ((g 2) * (g 11) * (g 14)) := by
  norm_num [atom0943, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0943_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (426520367944704 : Int) atom0943) := by
  rw [SparsePolynomial.eval_scale, eval_atom0943]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0944 : SparsePolynomial.Poly := [([2,11,15], 1)]
theorem eval_atom0944 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0944 = ((g 2) * (g 11) * (g 15)) := by
  norm_num [atom0944, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0944_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (410707623573504 : Int) atom0944) := by
  rw [SparsePolynomial.eval_scale, eval_atom0944]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0945 : SparsePolynomial.Poly := [([2,11,16], 1)]
theorem eval_atom0945 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0945 = ((g 2) * (g 11) * (g 16)) := by
  norm_num [atom0945, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0945_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (386155409531904 : Int) atom0945) := by
  rw [SparsePolynomial.eval_scale, eval_atom0945]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0946 : SparsePolynomial.Poly := [([2,11,17], 1)]
theorem eval_atom0946 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0946 = ((g 2) * (g 11) * (g 17)) := by
  norm_num [atom0946, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0946_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (371535933947904 : Int) atom0946) := by
  rw [SparsePolynomial.eval_scale, eval_atom0946]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0947 : SparsePolynomial.Poly := [([2,11,18], 1)]
theorem eval_atom0947 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0947 = ((g 2) * (g 11) * (g 18)) := by
  norm_num [atom0947, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0947_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (413692392979008 : Int) atom0947) := by
  rw [SparsePolynomial.eval_scale, eval_atom0947]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0948 : SparsePolynomial.Poly := [([2,11,19], 1)]
theorem eval_atom0948 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0948 = ((g 2) * (g 11) * (g 19)) := by
  norm_num [atom0948, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0948_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (347494413911040 : Int) atom0948) := by
  rw [SparsePolynomial.eval_scale, eval_atom0948]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0949 : SparsePolynomial.Poly := [([2,11,20], 1)]
theorem eval_atom0949 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0949 = ((g 2) * (g 11) * (g 20)) := by
  norm_num [atom0949, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0949_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (444055027065408 : Int) atom0949) := by
  rw [SparsePolynomial.eval_scale, eval_atom0949]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0950 : SparsePolynomial.Poly := [([2,11,21], 1)]
theorem eval_atom0950 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0950 = ((g 2) * (g 11) * (g 21)) := by
  norm_num [atom0950, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0950_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (410230735782912 : Int) atom0950) := by
  rw [SparsePolynomial.eval_scale, eval_atom0950]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 11) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0951 : SparsePolynomial.Poly := [([2,11,22], 1)]
theorem eval_atom0951 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0951 = ((g 2) * (g 11) * (g 22)) := by
  norm_num [atom0951, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0951_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (452841657269760 : Int) atom0951) := by
  rw [SparsePolynomial.eval_scale, eval_atom0951]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 11) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0952 : SparsePolynomial.Poly := [([2,11,23], 1)]
theorem eval_atom0952 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0952 = ((g 2) * (g 11) * (g 23)) := by
  norm_num [atom0952, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0952_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (528185964734208 : Int) atom0952) := by
  rw [SparsePolynomial.eval_scale, eval_atom0952]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 11) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0953 : SparsePolynomial.Poly := [([2,12,12], 1)]
theorem eval_atom0953 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0953 = ((g 2) * (g 12) * (g 12)) := by
  norm_num [atom0953, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0953_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (284228831677824 : Int) atom0953) := by
  rw [SparsePolynomial.eval_scale, eval_atom0953]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0954 : SparsePolynomial.Poly := [([2,12,13], 1)]
theorem eval_atom0954 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0954 = ((g 2) * (g 12) * (g 13)) := by
  norm_num [atom0954, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0954_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (526699029124224 : Int) atom0954) := by
  rw [SparsePolynomial.eval_scale, eval_atom0954]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0955 : SparsePolynomial.Poly := [([2,12,14], 1)]
theorem eval_atom0955 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0955 = ((g 2) * (g 12) * (g 14)) := by
  norm_num [atom0955, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0955_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (493080024628224 : Int) atom0955) := by
  rw [SparsePolynomial.eval_scale, eval_atom0955]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0956 : SparsePolynomial.Poly := [([2,12,15], 1)]
theorem eval_atom0956 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0956 = ((g 2) * (g 12) * (g 15)) := by
  norm_num [atom0956, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0956_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (474248026727424 : Int) atom0956) := by
  rw [SparsePolynomial.eval_scale, eval_atom0956]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0957 : SparsePolynomial.Poly := [([2,12,16], 1)]
theorem eval_atom0957 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0957 = ((g 2) * (g 12) * (g 16)) := by
  norm_num [atom0957, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0957_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (443593518580224 : Int) atom0957) := by
  rw [SparsePolynomial.eval_scale, eval_atom0957]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0958 : SparsePolynomial.Poly := [([2,12,17], 1)]
theorem eval_atom0958 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0958 = ((g 2) * (g 12) * (g 17)) := by
  norm_num [atom0958, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0958_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (422871748890624 : Int) atom0958) := by
  rw [SparsePolynomial.eval_scale, eval_atom0958]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0959 : SparsePolynomial.Poly := [([2,12,18], 1)]
theorem eval_atom0959 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0959 = ((g 2) * (g 12) * (g 18)) := by
  norm_num [atom0959, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0959_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (484590100376448 : Int) atom0959) := by
  rw [SparsePolynomial.eval_scale, eval_atom0959]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0960 : SparsePolynomial.Poly := [([2,12,19], 1)]
theorem eval_atom0960 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0960 = ((g 2) * (g 12) * (g 19)) := by
  norm_num [atom0960, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0960_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (377389276323840 : Int) atom0960) := by
  rw [SparsePolynomial.eval_scale, eval_atom0960]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0961 : SparsePolynomial.Poly := [([2,12,20], 1)]
theorem eval_atom0961 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0961 = ((g 2) * (g 12) * (g 20)) := by
  norm_num [atom0961, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0961_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (521076290917248 : Int) atom0961) := by
  rw [SparsePolynomial.eval_scale, eval_atom0961]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0962 : SparsePolynomial.Poly := [([2,12,21], 1)]
theorem eval_atom0962 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0962 = ((g 2) * (g 12) * (g 21)) := by
  norm_num [atom0962, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0962_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (409448281347072 : Int) atom0962) := by
  rw [SparsePolynomial.eval_scale, eval_atom0962]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 12) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0963 : SparsePolynomial.Poly := [([2,12,22], 1)]
theorem eval_atom0963 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0963 = ((g 2) * (g 12) * (g 22)) := by
  norm_num [atom0963, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0963_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (433641756303360 : Int) atom0963) := by
  rw [SparsePolynomial.eval_scale, eval_atom0963]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 12) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0964 : SparsePolynomial.Poly := [([2,12,23], 1)]
theorem eval_atom0964 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0964 = ((g 2) * (g 12) * (g 23)) := by
  norm_num [atom0964, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0964_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (490568617237248 : Int) atom0964) := by
  rw [SparsePolynomial.eval_scale, eval_atom0964]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 12) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0965 : SparsePolynomial.Poly := [([2,13,13], 1)]
theorem eval_atom0965 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0965 = ((g 2) * (g 13) * (g 13)) := by
  norm_num [atom0965, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0965_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (289736398828800 : Int) atom0965) := by
  rw [SparsePolynomial.eval_scale, eval_atom0965]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0966 : SparsePolynomial.Poly := [([2,13,14], 1)]
theorem eval_atom0966 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0966 = ((g 2) * (g 13) * (g 14)) := by
  norm_num [atom0966, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0966_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (526404059596800 : Int) atom0966) := by
  rw [SparsePolynomial.eval_scale, eval_atom0966]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0967 : SparsePolynomial.Poly := [([2,13,15], 1)]
theorem eval_atom0967 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0967 = ((g 2) * (g 13) * (g 15)) := by
  norm_num [atom0967, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0967_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (497366134272000 : Int) atom0967) := by
  rw [SparsePolynomial.eval_scale, eval_atom0967]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0968 : SparsePolynomial.Poly := [([2,13,16], 1)]
theorem eval_atom0968 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0968 = ((g 2) * (g 13) * (g 16)) := by
  norm_num [atom0968, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0968_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (459588739276800 : Int) atom0968) := by
  rw [SparsePolynomial.eval_scale, eval_atom0968]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0969 : SparsePolynomial.Poly := [([2,13,17], 1)]
theorem eval_atom0969 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0969 = ((g 2) * (g 13) * (g 17)) := by
  norm_num [atom0969, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0969_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (431744082739200 : Int) atom0969) := by
  rw [SparsePolynomial.eval_scale, eval_atom0969]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0970 : SparsePolynomial.Poly := [([2,13,18], 1)]
theorem eval_atom0970 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0970 = ((g 2) * (g 13) * (g 18)) := by
  norm_num [atom0970, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0970_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (482321582265600 : Int) atom0970) := by
  rw [SparsePolynomial.eval_scale, eval_atom0970]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0971 : SparsePolynomial.Poly := [([2,13,19], 1)]
theorem eval_atom0971 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0971 = ((g 2) * (g 13) * (g 19)) := by
  norm_num [atom0971, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0971_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (377204281977600 : Int) atom0971) := by
  rw [SparsePolynomial.eval_scale, eval_atom0971]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0972 : SparsePolynomial.Poly := [([2,13,20], 1)]
theorem eval_atom0972 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0972 = ((g 2) * (g 13) * (g 20)) := by
  norm_num [atom0972, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0972_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (524931329260800 : Int) atom0972) := by
  rw [SparsePolynomial.eval_scale, eval_atom0972]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0973 : SparsePolynomial.Poly := [([2,13,21], 1)]
theorem eval_atom0973 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0973 = ((g 2) * (g 13) * (g 21)) := by
  norm_num [atom0973, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0973_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (405394404307200 : Int) atom0973) := by
  rw [SparsePolynomial.eval_scale, eval_atom0973]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 13) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0974 : SparsePolynomial.Poly := [([2,13,22], 1)]
theorem eval_atom0974 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0974 = ((g 2) * (g 13) * (g 22)) := by
  norm_num [atom0974, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0974_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (429382919750400 : Int) atom0974) := by
  rw [SparsePolynomial.eval_scale, eval_atom0974]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 13) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0975 : SparsePolynomial.Poly := [([2,13,23], 1)]
theorem eval_atom0975 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0975 = ((g 2) * (g 13) * (g 23)) := by
  norm_num [atom0975, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0975_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (486104821171200 : Int) atom0975) := by
  rw [SparsePolynomial.eval_scale, eval_atom0975]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 13) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0976 : SparsePolynomial.Poly := [([2,14,14], 1)]
theorem eval_atom0976 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0976 = ((g 2) * (g 14) * (g 14)) := by
  norm_num [atom0976, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0976_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (283933862150400 : Int) atom0976) := by
  rw [SparsePolynomial.eval_scale, eval_atom0976]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0977 : SparsePolynomial.Poly := [([2,14,15], 1)]
theorem eval_atom0977 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0977 = ((g 2) * (g 14) * (g 15)) := by
  norm_num [atom0977, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0977_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (525551462150400 : Int) atom0977) := by
  rw [SparsePolynomial.eval_scale, eval_atom0977]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0978 : SparsePolynomial.Poly := [([2,14,16], 1)]
theorem eval_atom0978 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0978 = ((g 2) * (g 14) * (g 16)) := by
  norm_num [atom0978, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0978_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (479630587564800 : Int) atom0978) := by
  rw [SparsePolynomial.eval_scale, eval_atom0978]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0979 : SparsePolynomial.Poly := [([2,14,17], 1)]
theorem eval_atom0979 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0979 = ((g 2) * (g 14) * (g 17)) := by
  norm_num [atom0979, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0979_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (443642451436800 : Int) atom0979) := by
  rw [SparsePolynomial.eval_scale, eval_atom0979]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0980 : SparsePolynomial.Poly := [([2,14,18], 1)]
theorem eval_atom0980 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0980 = ((g 2) * (g 14) * (g 18)) := by
  norm_num [atom0980, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0980_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (472704538521600 : Int) atom0980) := by
  rw [SparsePolynomial.eval_scale, eval_atom0980]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0981 : SparsePolynomial.Poly := [([2,14,19], 1)]
theorem eval_atom0981 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0981 = ((g 2) * (g 14) * (g 19)) := by
  norm_num [atom0981, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0981_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (375370378336800 : Int) atom0981) := by
  rw [SparsePolynomial.eval_scale, eval_atom0981]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0982 : SparsePolynomial.Poly := [([2,14,20], 1)]
theorem eval_atom0982 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0982 = ((g 2) * (g 14) * (g 20)) := by
  norm_num [atom0982, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0982_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (521437841971200 : Int) atom0982) := by
  rw [SparsePolynomial.eval_scale, eval_atom0982]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0983 : SparsePolynomial.Poly := [([2,14,21], 1)]
theorem eval_atom0983 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0983 = ((g 2) * (g 14) * (g 21)) := by
  norm_num [atom0983, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0983_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (404962695244800 : Int) atom0983) := by
  rw [SparsePolynomial.eval_scale, eval_atom0983]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 14) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0984 : SparsePolynomial.Poly := [([2,14,22], 1)]
theorem eval_atom0984 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0984 = ((g 2) * (g 14) * (g 22)) := by
  norm_num [atom0984, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0984_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (411634200146400 : Int) atom0984) := by
  rw [SparsePolynomial.eval_scale, eval_atom0984]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 14) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0985 : SparsePolynomial.Poly := [([2,14,23], 1)]
theorem eval_atom0985 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0985 = ((g 2) * (g 14) * (g 23)) := by
  norm_num [atom0985, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0985_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (463618871100000 : Int) atom0985) := by
  rw [SparsePolynomial.eval_scale, eval_atom0985]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 14) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0986 : SparsePolynomial.Poly := [([2,15,15], 1)]
theorem eval_atom0986 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0986 = ((g 2) * (g 15) * (g 15)) := by
  norm_num [atom0986, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0986_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (291966841958400 : Int) atom0986) := by
  rw [SparsePolynomial.eval_scale, eval_atom0986]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0987 : SparsePolynomial.Poly := [([2,15,16], 1)]
theorem eval_atom0987 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0987 = ((g 2) * (g 15) * (g 16)) := by
  norm_num [atom0987, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0987_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (515495981952000 : Int) atom0987) := by
  rw [SparsePolynomial.eval_scale, eval_atom0987]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0988 : SparsePolynomial.Poly := [([2,15,17], 1)]
theorem eval_atom0988 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0988 = ((g 2) * (g 15) * (g 17)) := by
  norm_num [atom0988, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0988_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (470343773491200 : Int) atom0988) := by
  rw [SparsePolynomial.eval_scale, eval_atom0988]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0989 : SparsePolynomial.Poly := [([2,15,18], 1)]
theorem eval_atom0989 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0989 = ((g 2) * (g 15) * (g 18)) := by
  norm_num [atom0989, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0989_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (492661507968000 : Int) atom0989) := by
  rw [SparsePolynomial.eval_scale, eval_atom0989]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0990 : SparsePolynomial.Poly := [([2,15,19], 1)]
theorem eval_atom0990 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0990 = ((g 2) * (g 15) * (g 19)) := by
  norm_num [atom0990, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0990_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (379248139468800 : Int) atom0990) := by
  rw [SparsePolynomial.eval_scale, eval_atom0990]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0991 : SparsePolynomial.Poly := [([2,15,20], 1)]
theorem eval_atom0991 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0991 = ((g 2) * (g 15) * (g 20)) := by
  norm_num [atom0991, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0991_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (547518367872000 : Int) atom0991) := by
  rw [SparsePolynomial.eval_scale, eval_atom0991]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0992 : SparsePolynomial.Poly := [([2,15,21], 1)]
theorem eval_atom0992 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0992 = ((g 2) * (g 15) * (g 21)) := by
  norm_num [atom0992, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0992_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (434104999372800 : Int) atom0992) := by
  rw [SparsePolynomial.eval_scale, eval_atom0992]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 15) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0993 : SparsePolynomial.Poly := [([2,15,22], 1)]
theorem eval_atom0993 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0993 = ((g 2) * (g 15) * (g 22)) := by
  norm_num [atom0993, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0993_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (373035023424000 : Int) atom0993) := by
  rw [SparsePolynomial.eval_scale, eval_atom0993]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 15) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0994 : SparsePolynomial.Poly := [([2,15,23], 1)]
theorem eval_atom0994 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0994 = ((g 2) * (g 15) * (g 23)) := by
  norm_num [atom0994, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0994_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (415072942099200 : Int) atom0994) := by
  rw [SparsePolynomial.eval_scale, eval_atom0994]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 15) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0995 : SparsePolynomial.Poly := [([2,16,16], 1)]
theorem eval_atom0995 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0995 = ((g 2) * (g 16) * (g 16)) := by
  norm_num [atom0995, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0995_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (276961422528000 : Int) atom0995) := by
  rw [SparsePolynomial.eval_scale, eval_atom0995]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0996 : SparsePolynomial.Poly := [([2,16,17], 1)]
theorem eval_atom0996 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0996 = ((g 2) * (g 16) * (g 17)) := by
  norm_num [atom0996, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0996_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (495502930944000 : Int) atom0996) := by
  rw [SparsePolynomial.eval_scale, eval_atom0996]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0997 : SparsePolynomial.Poly := [([2,16,18], 1)]
theorem eval_atom0997 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0997 = ((g 2) * (g 16) * (g 18)) := by
  norm_num [atom0997, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0997_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (488973456921600 : Int) atom0997) := by
  rw [SparsePolynomial.eval_scale, eval_atom0997]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0998 : SparsePolynomial.Poly := [([2,16,19], 1)]
theorem eval_atom0998 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0998 = ((g 2) * (g 16) * (g 19)) := by
  norm_num [atom0998, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0998_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (378621866649600 : Int) atom0998) := by
  rw [SparsePolynomial.eval_scale, eval_atom0998]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0999 : SparsePolynomial.Poly := [([2,16,20], 1)]
theorem eval_atom0999 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0999 = ((g 2) * (g 16) * (g 20)) := by
  norm_num [atom0999, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0999_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (549953873280000 : Int) atom0999) := by
  rw [SparsePolynomial.eval_scale, eval_atom0999]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1000 : SparsePolynomial.Poly := [([2,16,21], 1)]
theorem eval_atom1000 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1000 = ((g 2) * (g 16) * (g 21)) := by
  norm_num [atom1000, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1000_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (439602283008000 : Int) atom1000) := by
  rw [SparsePolynomial.eval_scale, eval_atom1000]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 16) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1001 : SparsePolynomial.Poly := [([2,16,22], 1)]
theorem eval_atom1001 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1001 = ((g 2) * (g 16) * (g 22)) := by
  norm_num [atom1001, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1001_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (323801088307200 : Int) atom1001) := by
  rw [SparsePolynomial.eval_scale, eval_atom1001]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 16) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1002 : SparsePolynomial.Poly := [([2,16,23], 1)]
theorem eval_atom1002 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1002 = ((g 2) * (g 16) * (g 23)) := by
  norm_num [atom1002, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1002_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (445435576185600 : Int) atom1002) := by
  rw [SparsePolynomial.eval_scale, eval_atom1002]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 16) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1003 : SparsePolynomial.Poly := [([2,17,17], 1)]
theorem eval_atom1003 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1003 = ((g 2) * (g 17) * (g 17)) := by
  norm_num [atom1003, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1003_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (267182675020800 : Int) atom1003) := by
  rw [SparsePolynomial.eval_scale, eval_atom1003]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1004 : SparsePolynomial.Poly := [([2,17,18], 1)]
theorem eval_atom1004 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1004 = ((g 2) * (g 17) * (g 18)) := by
  norm_num [atom1004, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1004_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (505150882790400 : Int) atom1004) := by
  rw [SparsePolynomial.eval_scale, eval_atom1004]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1005 : SparsePolynomial.Poly := [([2,17,19], 1)]
theorem eval_atom1005 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1005 = ((g 2) * (g 17) * (g 19)) := by
  norm_num [atom1005, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1005_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (397861070745600 : Int) atom1005) := by
  rw [SparsePolynomial.eval_scale, eval_atom1005]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1006 : SparsePolynomial.Poly := [([2,17,20], 1)]
theorem eval_atom1006 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1006 = ((g 2) * (g 17) * (g 20)) := by
  norm_num [atom1006, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1006_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (572254855603200 : Int) atom1006) := by
  rw [SparsePolynomial.eval_scale, eval_atom1006]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1007 : SparsePolynomial.Poly := [([2,17,21], 1)]
theorem eval_atom1007 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1007 = ((g 2) * (g 17) * (g 21)) := by
  norm_num [atom1007, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1007_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (464965043558400 : Int) atom1007) := by
  rw [SparsePolynomial.eval_scale, eval_atom1007]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1008 : SparsePolynomial.Poly := [([2,17,22], 1)]
theorem eval_atom1008 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1008 = ((g 2) * (g 17) * (g 22)) := by
  norm_num [atom1008, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1008_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (351101944166400 : Int) atom1008) := by
  rw [SparsePolynomial.eval_scale, eval_atom1008]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block014 : SparsePolynomial.Poly := [([2,10,13], 403961087933568), ([2,10,14], 381526078906368), ([2,10,15], 373878076474368), ([2,10,16], 354407563795968), ([2,10,17], 344869789575168), ([2,10,18], 379974615939072), ([2,10,19], 329477914529280), ([2,10,20], 419823011570688), ([2,10,21], 399350123656704), ([2,10,22], 445024402859520), ([2,10,23], 523432068039936), ([2,11,11], 247082976765504), ([2,11,12], 484045607060928), ([2,11,13], 457120118911104), ([2,11,14], 426520367944704), ([2,11,15], 410707623573504), ([2,11,16], 386155409531904), ([2,11,17], 371535933947904), ([2,11,18], 413692392979008), ([2,11,19], 347494413911040), ([2,11,20], 444055027065408), ([2,11,21], 410230735782912), ([2,11,22], 452841657269760), ([2,11,23], 528185964734208), ([2,12,12], 284228831677824), ([2,12,13], 526699029124224), ([2,12,14], 493080024628224), ([2,12,15], 474248026727424), ([2,12,16], 443593518580224), ([2,12,17], 422871748890624), ([2,12,18], 484590100376448), ([2,12,19], 377389276323840), ([2,12,20], 521076290917248), ([2,12,21], 409448281347072), ([2,12,22], 433641756303360), ([2,12,23], 490568617237248), ([2,13,13], 289736398828800), ([2,13,14], 526404059596800), ([2,13,15], 497366134272000), ([2,13,16], 459588739276800), ([2,13,17], 431744082739200), ([2,13,18], 482321582265600), ([2,13,19], 377204281977600), ([2,13,20], 524931329260800), ([2,13,21], 405394404307200), ([2,13,22], 429382919750400), ([2,13,23], 486104821171200), ([2,14,14], 283933862150400), ([2,14,15], 525551462150400), ([2,14,16], 479630587564800), ([2,14,17], 443642451436800), ([2,14,18], 472704538521600), ([2,14,19], 375370378336800), ([2,14,20], 521437841971200), ([2,14,21], 404962695244800), ([2,14,22], 411634200146400), ([2,14,23], 463618871100000), ([2,15,15], 291966841958400), ([2,15,16], 515495981952000), ([2,15,17], 470343773491200), ([2,15,18], 492661507968000), ([2,15,19], 379248139468800), ([2,15,20], 547518367872000), ([2,15,21], 434104999372800), ([2,15,22], 373035023424000), ([2,15,23], 415072942099200), ([2,16,16], 276961422528000), ([2,16,17], 495502930944000), ([2,16,18], 488973456921600), ([2,16,19], 378621866649600), ([2,16,20], 549953873280000), ([2,16,21], 439602283008000), ([2,16,22], 323801088307200), ([2,16,23], 445435576185600), ([2,17,17], 267182675020800), ([2,17,18], 505150882790400), ([2,17,19], 397861070745600), ([2,17,20], 572254855603200), ([2,17,21], 464965043558400), ([2,17,22], 351101944166400)]
theorem block014_data : block014 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (403961087933568 : Int) atom0929) (SparsePolynomial.scale (381526078906368 : Int) atom0930)) (SparsePolynomial.merge (SparsePolynomial.scale (373878076474368 : Int) atom0931) (SparsePolynomial.merge (SparsePolynomial.scale (354407563795968 : Int) atom0932) (SparsePolynomial.scale (344869789575168 : Int) atom0933)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (379974615939072 : Int) atom0934) (SparsePolynomial.scale (329477914529280 : Int) atom0935)) (SparsePolynomial.merge (SparsePolynomial.scale (419823011570688 : Int) atom0936) (SparsePolynomial.merge (SparsePolynomial.scale (399350123656704 : Int) atom0937) (SparsePolynomial.scale (445024402859520 : Int) atom0938))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (523432068039936 : Int) atom0939) (SparsePolynomial.scale (247082976765504 : Int) atom0940)) (SparsePolynomial.merge (SparsePolynomial.scale (484045607060928 : Int) atom0941) (SparsePolynomial.merge (SparsePolynomial.scale (457120118911104 : Int) atom0942) (SparsePolynomial.scale (426520367944704 : Int) atom0943)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (410707623573504 : Int) atom0944) (SparsePolynomial.scale (386155409531904 : Int) atom0945)) (SparsePolynomial.merge (SparsePolynomial.scale (371535933947904 : Int) atom0946) (SparsePolynomial.merge (SparsePolynomial.scale (413692392979008 : Int) atom0947) (SparsePolynomial.scale (347494413911040 : Int) atom0948)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (444055027065408 : Int) atom0949) (SparsePolynomial.scale (410230735782912 : Int) atom0950)) (SparsePolynomial.merge (SparsePolynomial.scale (452841657269760 : Int) atom0951) (SparsePolynomial.merge (SparsePolynomial.scale (528185964734208 : Int) atom0952) (SparsePolynomial.scale (284228831677824 : Int) atom0953)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (526699029124224 : Int) atom0954) (SparsePolynomial.scale (493080024628224 : Int) atom0955)) (SparsePolynomial.merge (SparsePolynomial.scale (474248026727424 : Int) atom0956) (SparsePolynomial.merge (SparsePolynomial.scale (443593518580224 : Int) atom0957) (SparsePolynomial.scale (422871748890624 : Int) atom0958))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (484590100376448 : Int) atom0959) (SparsePolynomial.scale (377389276323840 : Int) atom0960)) (SparsePolynomial.merge (SparsePolynomial.scale (521076290917248 : Int) atom0961) (SparsePolynomial.merge (SparsePolynomial.scale (409448281347072 : Int) atom0962) (SparsePolynomial.scale (433641756303360 : Int) atom0963)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (490568617237248 : Int) atom0964) (SparsePolynomial.scale (289736398828800 : Int) atom0965)) (SparsePolynomial.merge (SparsePolynomial.scale (526404059596800 : Int) atom0966) (SparsePolynomial.merge (SparsePolynomial.scale (497366134272000 : Int) atom0967) (SparsePolynomial.scale (459588739276800 : Int) atom0968))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (431744082739200 : Int) atom0969) (SparsePolynomial.scale (482321582265600 : Int) atom0970)) (SparsePolynomial.merge (SparsePolynomial.scale (377204281977600 : Int) atom0971) (SparsePolynomial.merge (SparsePolynomial.scale (524931329260800 : Int) atom0972) (SparsePolynomial.scale (405394404307200 : Int) atom0973)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (429382919750400 : Int) atom0974) (SparsePolynomial.scale (486104821171200 : Int) atom0975)) (SparsePolynomial.merge (SparsePolynomial.scale (283933862150400 : Int) atom0976) (SparsePolynomial.merge (SparsePolynomial.scale (525551462150400 : Int) atom0977) (SparsePolynomial.scale (479630587564800 : Int) atom0978))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (443642451436800 : Int) atom0979) (SparsePolynomial.scale (472704538521600 : Int) atom0980)) (SparsePolynomial.merge (SparsePolynomial.scale (375370378336800 : Int) atom0981) (SparsePolynomial.merge (SparsePolynomial.scale (521437841971200 : Int) atom0982) (SparsePolynomial.scale (404962695244800 : Int) atom0983)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (411634200146400 : Int) atom0984) (SparsePolynomial.scale (463618871100000 : Int) atom0985)) (SparsePolynomial.merge (SparsePolynomial.scale (291966841958400 : Int) atom0986) (SparsePolynomial.merge (SparsePolynomial.scale (515495981952000 : Int) atom0987) (SparsePolynomial.scale (470343773491200 : Int) atom0988)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (492661507968000 : Int) atom0989) (SparsePolynomial.scale (379248139468800 : Int) atom0990)) (SparsePolynomial.merge (SparsePolynomial.scale (547518367872000 : Int) atom0991) (SparsePolynomial.merge (SparsePolynomial.scale (434104999372800 : Int) atom0992) (SparsePolynomial.scale (373035023424000 : Int) atom0993)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (415072942099200 : Int) atom0994) (SparsePolynomial.scale (276961422528000 : Int) atom0995)) (SparsePolynomial.merge (SparsePolynomial.scale (495502930944000 : Int) atom0996) (SparsePolynomial.merge (SparsePolynomial.scale (488973456921600 : Int) atom0997) (SparsePolynomial.scale (378621866649600 : Int) atom0998))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (549953873280000 : Int) atom0999) (SparsePolynomial.scale (439602283008000 : Int) atom1000)) (SparsePolynomial.merge (SparsePolynomial.scale (323801088307200 : Int) atom1001) (SparsePolynomial.merge (SparsePolynomial.scale (445435576185600 : Int) atom1002) (SparsePolynomial.scale (267182675020800 : Int) atom1003)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (505150882790400 : Int) atom1004) (SparsePolynomial.scale (397861070745600 : Int) atom1005)) (SparsePolynomial.merge (SparsePolynomial.scale (572254855603200 : Int) atom1006) (SparsePolynomial.merge (SparsePolynomial.scale (464965043558400 : Int) atom1007) (SparsePolynomial.scale (351101944166400 : Int) atom1008)))))))) := by decide +kernel
theorem block014_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block014 := by
  rw [block014_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0929_nonneg g hg hA hB) (atom0930_nonneg g hg hA hB)) (add_nonneg (atom0931_nonneg g hg hA hB) (add_nonneg (atom0932_nonneg g hg hA hB) (atom0933_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0934_nonneg g hg hA hB) (atom0935_nonneg g hg hA hB)) (add_nonneg (atom0936_nonneg g hg hA hB) (add_nonneg (atom0937_nonneg g hg hA hB) (atom0938_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0939_nonneg g hg hA hB) (atom0940_nonneg g hg hA hB)) (add_nonneg (atom0941_nonneg g hg hA hB) (add_nonneg (atom0942_nonneg g hg hA hB) (atom0943_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0944_nonneg g hg hA hB) (atom0945_nonneg g hg hA hB)) (add_nonneg (atom0946_nonneg g hg hA hB) (add_nonneg (atom0947_nonneg g hg hA hB) (atom0948_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0949_nonneg g hg hA hB) (atom0950_nonneg g hg hA hB)) (add_nonneg (atom0951_nonneg g hg hA hB) (add_nonneg (atom0952_nonneg g hg hA hB) (atom0953_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0954_nonneg g hg hA hB) (atom0955_nonneg g hg hA hB)) (add_nonneg (atom0956_nonneg g hg hA hB) (add_nonneg (atom0957_nonneg g hg hA hB) (atom0958_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0959_nonneg g hg hA hB) (atom0960_nonneg g hg hA hB)) (add_nonneg (atom0961_nonneg g hg hA hB) (add_nonneg (atom0962_nonneg g hg hA hB) (atom0963_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0964_nonneg g hg hA hB) (atom0965_nonneg g hg hA hB)) (add_nonneg (atom0966_nonneg g hg hA hB) (add_nonneg (atom0967_nonneg g hg hA hB) (atom0968_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0969_nonneg g hg hA hB) (atom0970_nonneg g hg hA hB)) (add_nonneg (atom0971_nonneg g hg hA hB) (add_nonneg (atom0972_nonneg g hg hA hB) (atom0973_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0974_nonneg g hg hA hB) (atom0975_nonneg g hg hA hB)) (add_nonneg (atom0976_nonneg g hg hA hB) (add_nonneg (atom0977_nonneg g hg hA hB) (atom0978_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0979_nonneg g hg hA hB) (atom0980_nonneg g hg hA hB)) (add_nonneg (atom0981_nonneg g hg hA hB) (add_nonneg (atom0982_nonneg g hg hA hB) (atom0983_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0984_nonneg g hg hA hB) (atom0985_nonneg g hg hA hB)) (add_nonneg (atom0986_nonneg g hg hA hB) (add_nonneg (atom0987_nonneg g hg hA hB) (atom0988_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0989_nonneg g hg hA hB) (atom0990_nonneg g hg hA hB)) (add_nonneg (atom0991_nonneg g hg hA hB) (add_nonneg (atom0992_nonneg g hg hA hB) (atom0993_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0994_nonneg g hg hA hB) (atom0995_nonneg g hg hA hB)) (add_nonneg (atom0996_nonneg g hg hA hB) (add_nonneg (atom0997_nonneg g hg hA hB) (atom0998_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0999_nonneg g hg hA hB) (atom1000_nonneg g hg hA hB)) (add_nonneg (atom1001_nonneg g hg hA hB) (add_nonneg (atom1002_nonneg g hg hA hB) (atom1003_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1004_nonneg g hg hA hB) (atom1005_nonneg g hg hA hB)) (add_nonneg (atom1006_nonneg g hg hA hB) (add_nonneg (atom1007_nonneg g hg hA hB) (atom1008_nonneg g hg hA hB))))))))

end APPT.Finite24
