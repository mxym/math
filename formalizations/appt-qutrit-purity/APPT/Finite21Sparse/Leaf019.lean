import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom1376 : SparsePolynomial.Poly := [([8,8,10], 1)]
theorem eval_atom1376 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1376 = ((g 8) * (g 8) * (g 10)) := by
  norm_num [atom1376, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1376_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (770276908800 : Int) atom1376) := by
  rw [SparsePolynomial.eval_scale, eval_atom1376]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 8) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1377 : SparsePolynomial.Poly := [([8,8,11], 1)]
theorem eval_atom1377 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1377 = ((g 8) * (g 8) * (g 11)) := by
  norm_num [atom1377, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1377_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (427179916800 : Int) atom1377) := by
  rw [SparsePolynomial.eval_scale, eval_atom1377]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1378 : SparsePolynomial.Poly := [([8,8,15], 1)]
theorem eval_atom1378 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1378 = ((g 8) * (g 8) * (g 15)) := by
  norm_num [atom1378, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1378_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3093893233200 : Int) atom1378) := by
  rw [SparsePolynomial.eval_scale, eval_atom1378]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1379 : SparsePolynomial.Poly := [([8,9,9], 1)]
theorem eval_atom1379 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1379 = ((g 8) * (g 9) * (g 9)) := by
  norm_num [atom1379, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1379_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1414429430400 : Int) atom1379) := by
  rw [SparsePolynomial.eval_scale, eval_atom1379]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 8) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1380 : SparsePolynomial.Poly := [([8,9,10], 1)]
theorem eval_atom1380 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1380 = ((g 8) * (g 9) * (g 10)) := by
  norm_num [atom1380, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1380_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (518028134400 : Int) atom1380) := by
  rw [SparsePolynomial.eval_scale, eval_atom1380]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 8) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1381 : SparsePolynomial.Poly := [([8,9,13], 1)]
theorem eval_atom1381 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1381 = ((g 8) * (g 9) * (g 13)) := by
  norm_num [atom1381, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1381_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (427179916800 : Int) atom1381) := by
  rw [SparsePolynomial.eval_scale, eval_atom1381]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1382 : SparsePolynomial.Poly := [([8,9,14], 1)]
theorem eval_atom1382 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1382 = ((g 8) * (g 9) * (g 14)) := by
  norm_num [atom1382, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1382_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (854359833600 : Int) atom1382) := by
  rw [SparsePolynomial.eval_scale, eval_atom1382]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1383 : SparsePolynomial.Poly := [([8,9,15], 1)]
theorem eval_atom1383 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1383 = ((g 8) * (g 9) * (g 15)) := by
  norm_num [atom1383, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1383_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5687746762320 : Int) atom1383) := by
  rw [SparsePolynomial.eval_scale, eval_atom1383]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1384 : SparsePolynomial.Poly := [([8,9,17], 1)]
theorem eval_atom1384 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1384 = ((g 8) * (g 9) * (g 17)) := by
  norm_num [atom1384, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1384_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2944323370800 : Int) atom1384) := by
  rw [SparsePolynomial.eval_scale, eval_atom1384]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1385 : SparsePolynomial.Poly := [([8,9,18], 1)]
theorem eval_atom1385 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1385 = ((g 8) * (g 9) * (g 18)) := by
  norm_num [atom1385, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1385_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5786258284800 : Int) atom1385) := by
  rw [SparsePolynomial.eval_scale, eval_atom1385]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 9) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1386 : SparsePolynomial.Poly := [([8,9,19], 1)]
theorem eval_atom1386 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1386 = ((g 8) * (g 9) * (g 19)) := by
  norm_num [atom1386, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1386_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11171238059520 : Int) atom1386) := by
  rw [SparsePolynomial.eval_scale, eval_atom1386]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 9) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1387 : SparsePolynomial.Poly := [([8,9,20], 1)]
theorem eval_atom1387 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1387 = ((g 8) * (g 9) * (g 20)) := by
  norm_num [atom1387, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1387_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17391151612800 : Int) atom1387) := by
  rw [SparsePolynomial.eval_scale, eval_atom1387]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 9) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1388 : SparsePolynomial.Poly := [([8,10,10], 1)]
theorem eval_atom1388 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1388 = ((g 8) * (g 10) * (g 10)) := by
  norm_num [atom1388, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1388_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1834844054400 : Int) atom1388) := by
  rw [SparsePolynomial.eval_scale, eval_atom1388]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 8) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1389 : SparsePolynomial.Poly := [([8,10,11], 1)]
theorem eval_atom1389 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1389 = ((g 8) * (g 10) * (g 11)) := by
  norm_num [atom1389, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1389_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2647162425600 : Int) atom1389) := by
  rw [SparsePolynomial.eval_scale, eval_atom1389]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1390 : SparsePolynomial.Poly := [([8,10,12], 1)]
theorem eval_atom1390 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1390 = ((g 8) * (g 10) * (g 12)) := by
  norm_num [atom1390, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1390_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2478996576000 : Int) atom1390) := by
  rw [SparsePolynomial.eval_scale, eval_atom1390]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 8) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1391 : SparsePolynomial.Poly := [([8,10,13], 1)]
theorem eval_atom1391 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1391 = ((g 8) * (g 10) * (g 13)) := by
  norm_num [atom1391, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1391_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3165190560000 : Int) atom1391) := by
  rw [SparsePolynomial.eval_scale, eval_atom1391]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1392 : SparsePolynomial.Poly := [([8,10,14], 1)]
theorem eval_atom1392 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1392 = ((g 8) * (g 10) * (g 14)) := by
  norm_num [atom1392, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1392_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3851384544000 : Int) atom1392) := by
  rw [SparsePolynomial.eval_scale, eval_atom1392]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1393 : SparsePolynomial.Poly := [([8,10,15], 1)]
theorem eval_atom1393 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1393 = ((g 8) * (g 10) * (g 15)) := by
  norm_num [atom1393, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1393_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7803362548800 : Int) atom1393) := by
  rw [SparsePolynomial.eval_scale, eval_atom1393]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1394 : SparsePolynomial.Poly := [([8,10,16], 1)]
theorem eval_atom1394 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1394 = ((g 8) * (g 10) * (g 16)) := by
  norm_num [atom1394, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1394_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2139543982800 : Int) atom1394) := by
  rw [SparsePolynomial.eval_scale, eval_atom1394]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1395 : SparsePolynomial.Poly := [([8,10,17], 1)]
theorem eval_atom1395 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1395 = ((g 8) * (g 10) * (g 17)) := by
  norm_num [atom1395, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1395_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9372338136000 : Int) atom1395) := by
  rw [SparsePolynomial.eval_scale, eval_atom1395]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1396 : SparsePolynomial.Poly := [([8,10,18], 1)]
theorem eval_atom1396 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1396 = ((g 8) * (g 10) * (g 18)) := by
  norm_num [atom1396, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1396_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11410652912400 : Int) atom1396) := by
  rw [SparsePolynomial.eval_scale, eval_atom1396]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1397 : SparsePolynomial.Poly := [([8,10,19], 1)]
theorem eval_atom1397 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1397 = ((g 8) * (g 10) * (g 19)) := by
  norm_num [atom1397, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1397_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20176096474800 : Int) atom1397) := by
  rw [SparsePolynomial.eval_scale, eval_atom1397]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1398 : SparsePolynomial.Poly := [([8,10,20], 1)]
theorem eval_atom1398 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1398 = ((g 8) * (g 10) * (g 20)) := by
  norm_num [atom1398, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1398_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30348257839200 : Int) atom1398) := by
  rw [SparsePolynomial.eval_scale, eval_atom1398]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 10) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1399 : SparsePolynomial.Poly := [([8,11,11], 1)]
theorem eval_atom1399 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1399 = ((g 8) * (g 11) * (g 11)) := by
  norm_num [atom1399, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1399_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3543563721600 : Int) atom1399) := by
  rw [SparsePolynomial.eval_scale, eval_atom1399]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1400 : SparsePolynomial.Poly := [([8,11,12], 1)]
theorem eval_atom1400 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1400 = ((g 8) * (g 11) * (g 12)) := by
  norm_num [atom1400, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1400_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5560104211200 : Int) atom1400) := by
  rw [SparsePolynomial.eval_scale, eval_atom1400]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 8) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1401 : SparsePolynomial.Poly := [([8,11,13], 1)]
theorem eval_atom1401 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1401 = ((g 8) * (g 11) * (g 13)) := by
  norm_num [atom1401, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1401_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6337146412800 : Int) atom1401) := by
  rw [SparsePolynomial.eval_scale, eval_atom1401]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1402 : SparsePolynomial.Poly := [([8,11,14], 1)]
theorem eval_atom1402 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1402 = ((g 8) * (g 11) * (g 14)) := by
  norm_num [atom1402, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1402_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7114188614400 : Int) atom1402) := by
  rw [SparsePolynomial.eval_scale, eval_atom1402]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1403 : SparsePolynomial.Poly := [([8,11,15], 1)]
theorem eval_atom1403 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1403 = ((g 8) * (g 11) * (g 15)) := by
  norm_num [atom1403, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1403_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12510442929600 : Int) atom1403) := by
  rw [SparsePolynomial.eval_scale, eval_atom1403]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1404 : SparsePolynomial.Poly := [([8,11,16], 1)]
theorem eval_atom1404 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1404 = ((g 8) * (g 11) * (g 16)) := by
  norm_num [atom1404, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1404_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8456065254000 : Int) atom1404) := by
  rw [SparsePolynomial.eval_scale, eval_atom1404]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1405 : SparsePolynomial.Poly := [([8,11,17], 1)]
theorem eval_atom1405 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1405 = ((g 8) * (g 11) * (g 17)) := by
  norm_num [atom1405, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1405_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19774108468800 : Int) atom1405) := by
  rw [SparsePolynomial.eval_scale, eval_atom1405]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1406 : SparsePolynomial.Poly := [([8,11,18], 1)]
theorem eval_atom1406 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1406 = ((g 8) * (g 11) * (g 18)) := by
  norm_num [atom1406, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1406_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20318281326000 : Int) atom1406) := by
  rw [SparsePolynomial.eval_scale, eval_atom1406]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1407 : SparsePolynomial.Poly := [([8,11,19], 1)]
theorem eval_atom1407 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1407 = ((g 8) * (g 11) * (g 19)) := by
  norm_num [atom1407, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1407_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30113920746000 : Int) atom1407) := by
  rw [SparsePolynomial.eval_scale, eval_atom1407]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1408 : SparsePolynomial.Poly := [([8,11,20], 1)]
theorem eval_atom1408 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1408 = ((g 8) * (g 11) * (g 20)) := by
  norm_num [atom1408, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1408_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40982814885600 : Int) atom1408) := by
  rw [SparsePolynomial.eval_scale, eval_atom1408]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1409 : SparsePolynomial.Poly := [([8,12,12], 1)]
theorem eval_atom1409 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1409 = ((g 8) * (g 12) * (g 12)) := by
  norm_num [atom1409, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1409_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5174965756800 : Int) atom1409) := by
  rw [SparsePolynomial.eval_scale, eval_atom1409]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 8) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1410 : SparsePolynomial.Poly := [([8,12,13], 1)]
theorem eval_atom1410 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1410 = ((g 8) * (g 12) * (g 13)) := by
  norm_num [atom1410, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1410_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10622476166400 : Int) atom1410) := by
  rw [SparsePolynomial.eval_scale, eval_atom1410]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1411 : SparsePolynomial.Poly := [([8,12,14], 1)]
theorem eval_atom1411 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1411 = ((g 8) * (g 12) * (g 14)) := by
  norm_num [atom1411, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1411_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11322200736000 : Int) atom1411) := by
  rw [SparsePolynomial.eval_scale, eval_atom1411]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1412 : SparsePolynomial.Poly := [([8,12,15], 1)]
theorem eval_atom1412 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1412 = ((g 8) * (g 12) * (g 15)) := by
  norm_num [atom1412, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1412_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14101152139200 : Int) atom1412) := by
  rw [SparsePolynomial.eval_scale, eval_atom1412]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1413 : SparsePolynomial.Poly := [([8,12,16], 1)]
theorem eval_atom1413 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1413 = ((g 8) * (g 12) * (g 16)) := by
  norm_num [atom1413, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1413_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13619552332400 : Int) atom1413) := by
  rw [SparsePolynomial.eval_scale, eval_atom1413]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1414 : SparsePolynomial.Poly := [([8,12,17], 1)]
theorem eval_atom1414 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1414 = ((g 8) * (g 12) * (g 17)) := by
  norm_num [atom1414, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1414_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25094037416000 : Int) atom1414) := by
  rw [SparsePolynomial.eval_scale, eval_atom1414]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1415 : SparsePolynomial.Poly := [([8,12,18], 1)]
theorem eval_atom1415 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1415 = ((g 8) * (g 12) * (g 18)) := by
  norm_num [atom1415, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1415_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27327261530800 : Int) atom1415) := by
  rw [SparsePolynomial.eval_scale, eval_atom1415]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1416 : SparsePolynomial.Poly := [([8,12,19], 1)]
theorem eval_atom1416 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1416 = ((g 8) * (g 12) * (g 19)) := by
  norm_num [atom1416, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1416_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37107275293200 : Int) atom1416) := by
  rw [SparsePolynomial.eval_scale, eval_atom1416]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1417 : SparsePolynomial.Poly := [([8,12,20], 1)]
theorem eval_atom1417 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1417 = ((g 8) * (g 12) * (g 20)) := by
  norm_num [atom1417, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1417_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48530465474400 : Int) atom1417) := by
  rw [SparsePolynomial.eval_scale, eval_atom1417]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1418 : SparsePolynomial.Poly := [([8,13,13], 1)]
theorem eval_atom1418 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1418 = ((g 8) * (g 13) * (g 13)) := by
  norm_num [atom1418, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1418_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8314429795200 : Int) atom1418) := by
  rw [SparsePolynomial.eval_scale, eval_atom1418]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1419 : SparsePolynomial.Poly := [([8,13,14], 1)]
theorem eval_atom1419 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1419 = ((g 8) * (g 13) * (g 14)) := by
  norm_num [atom1419, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1419_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15912566956800 : Int) atom1419) := by
  rw [SparsePolynomial.eval_scale, eval_atom1419]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1420 : SparsePolynomial.Poly := [([8,13,15], 1)]
theorem eval_atom1420 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1420 = ((g 8) * (g 13) * (g 15)) := by
  norm_num [atom1420, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1420_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19319098982400 : Int) atom1420) := by
  rw [SparsePolynomial.eval_scale, eval_atom1420]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1421 : SparsePolynomial.Poly := [([8,13,16], 1)]
theorem eval_atom1421 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1421 = ((g 8) * (g 13) * (g 16)) := by
  norm_num [atom1421, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1421_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19329077214000 : Int) atom1421) := by
  rw [SparsePolynomial.eval_scale, eval_atom1421]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1422 : SparsePolynomial.Poly := [([8,13,17], 1)]
theorem eval_atom1422 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1422 = ((g 8) * (g 13) * (g 17)) := by
  norm_num [atom1422, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1422_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34558073524800 : Int) atom1422) := by
  rw [SparsePolynomial.eval_scale, eval_atom1422]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1423 : SparsePolynomial.Poly := [([8,13,18], 1)]
theorem eval_atom1423 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1423 = ((g 8) * (g 13) * (g 18)) := by
  norm_num [atom1423, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1423_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38809323630000 : Int) atom1423) := by
  rw [SparsePolynomial.eval_scale, eval_atom1423]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1424 : SparsePolynomial.Poly := [([8,13,19], 1)]
theorem eval_atom1424 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1424 = ((g 8) * (g 13) * (g 19)) := by
  norm_num [atom1424, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1424_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42738457266000 : Int) atom1424) := by
  rw [SparsePolynomial.eval_scale, eval_atom1424]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1425 : SparsePolynomial.Poly := [([8,13,20], 1)]
theorem eval_atom1425 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1425 = ((g 8) * (g 13) * (g 20)) := by
  norm_num [atom1425, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1425_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (60582834597600 : Int) atom1425) := by
  rw [SparsePolynomial.eval_scale, eval_atom1425]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1426 : SparsePolynomial.Poly := [([8,14,14], 1)]
theorem eval_atom1426 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1426 = ((g 8) * (g 14) * (g 14)) := by
  norm_num [atom1426, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1426_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12733408598400 : Int) atom1426) := by
  rw [SparsePolynomial.eval_scale, eval_atom1426]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1427 : SparsePolynomial.Poly := [([8,14,15], 1)]
theorem eval_atom1427 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1427 = ((g 8) * (g 14) * (g 15)) := by
  norm_num [atom1427, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1427_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24425203723200 : Int) atom1427) := by
  rw [SparsePolynomial.eval_scale, eval_atom1427]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1428 : SparsePolynomial.Poly := [([8,14,16], 1)]
theorem eval_atom1428 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1428 = ((g 8) * (g 14) * (g 16)) := by
  norm_num [atom1428, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1428_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24919452658800 : Int) atom1428) := by
  rw [SparsePolynomial.eval_scale, eval_atom1428]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1429 : SparsePolynomial.Poly := [([8,14,17], 1)]
theorem eval_atom1429 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1429 = ((g 8) * (g 14) * (g 17)) := by
  norm_num [atom1429, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1429_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46215639489600 : Int) atom1429) := by
  rw [SparsePolynomial.eval_scale, eval_atom1429]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1430 : SparsePolynomial.Poly := [([8,14,18], 1)]
theorem eval_atom1430 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1430 = ((g 8) * (g 14) * (g 18)) := by
  norm_num [atom1430, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1430_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52704268570800 : Int) atom1430) := by
  rw [SparsePolynomial.eval_scale, eval_atom1430]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1431 : SparsePolynomial.Poly := [([8,14,19], 1)]
theorem eval_atom1431 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1431 = ((g 8) * (g 14) * (g 19)) := by
  norm_num [atom1431, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1431_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52820365827600 : Int) atom1431) := by
  rw [SparsePolynomial.eval_scale, eval_atom1431]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1432 : SparsePolynomial.Poly := [([8,14,20], 1)]
theorem eval_atom1432 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1432 = ((g 8) * (g 14) * (g 20)) := by
  norm_num [atom1432, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1432_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (77218206357600 : Int) atom1432) := by
  rw [SparsePolynomial.eval_scale, eval_atom1432]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1433 : SparsePolynomial.Poly := [([8,15,15], 1)]
theorem eval_atom1433 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1433 = ((g 8) * (g 15) * (g 15)) := by
  norm_num [atom1433, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1433_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19383530342400 : Int) atom1433) := by
  rw [SparsePolynomial.eval_scale, eval_atom1433]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1434 : SparsePolynomial.Poly := [([8,15,16], 1)]
theorem eval_atom1434 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1434 = ((g 8) * (g 15) * (g 16)) := by
  norm_num [atom1434, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1434_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39580818694200 : Int) atom1434) := by
  rw [SparsePolynomial.eval_scale, eval_atom1434]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1435 : SparsePolynomial.Poly := [([8,15,17], 1)]
theorem eval_atom1435 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1435 = ((g 8) * (g 15) * (g 17)) := by
  norm_num [atom1435, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1435_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (66724705152000 : Int) atom1435) := by
  rw [SparsePolynomial.eval_scale, eval_atom1435]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1436 : SparsePolynomial.Poly := [([8,15,18], 1)]
theorem eval_atom1436 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1436 = ((g 8) * (g 15) * (g 18)) := by
  norm_num [atom1436, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1436_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (71113667221800 : Int) atom1436) := by
  rw [SparsePolynomial.eval_scale, eval_atom1436]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1437 : SparsePolynomial.Poly := [([8,15,19], 1)]
theorem eval_atom1437 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1437 = ((g 8) * (g 15) * (g 19)) := by
  norm_num [atom1437, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1437_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53763791949000 : Int) atom1437) := by
  rw [SparsePolynomial.eval_scale, eval_atom1437]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1438 : SparsePolynomial.Poly := [([8,15,20], 1)]
theorem eval_atom1438 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1438 = ((g 8) * (g 15) * (g 20)) := by
  norm_num [atom1438, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1438_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (82935935850600 : Int) atom1438) := by
  rw [SparsePolynomial.eval_scale, eval_atom1438]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1439 : SparsePolynomial.Poly := [([8,16,16], 1)]
theorem eval_atom1439 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1439 = ((g 8) * (g 16) * (g 16)) := by
  norm_num [atom1439, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1439_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15952947010560 : Int) atom1439) := by
  rw [SparsePolynomial.eval_scale, eval_atom1439]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1440 : SparsePolynomial.Poly := [([8,16,17], 1)]
theorem eval_atom1440 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1440 = ((g 8) * (g 16) * (g 17)) := by
  norm_num [atom1440, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1440_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (56181592441800 : Int) atom1440) := by
  rw [SparsePolynomial.eval_scale, eval_atom1440]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1441 : SparsePolynomial.Poly := [([8,16,18], 1)]
theorem eval_atom1441 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1441 = ((g 8) * (g 16) * (g 18)) := by
  norm_num [atom1441, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1441_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (64310888457900 : Int) atom1441) := by
  rw [SparsePolynomial.eval_scale, eval_atom1441]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1442 : SparsePolynomial.Poly := [([8,16,19], 1)]
theorem eval_atom1442 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1442 = ((g 8) * (g 16) * (g 19)) := by
  norm_num [atom1442, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1442_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46815859734000 : Int) atom1442) := by
  rw [SparsePolynomial.eval_scale, eval_atom1442]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1443 : SparsePolynomial.Poly := [([8,16,20], 1)]
theorem eval_atom1443 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1443 = ((g 8) * (g 16) * (g 20)) := by
  norm_num [atom1443, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1443_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (61853161781250 : Int) atom1443) := by
  rw [SparsePolynomial.eval_scale, eval_atom1443]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1444 : SparsePolynomial.Poly := [([8,17,17], 1)]
theorem eval_atom1444 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1444 = ((g 8) * (g 17) * (g 17)) := by
  norm_num [atom1444, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1444_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41682593433600 : Int) atom1444) := by
  rw [SparsePolynomial.eval_scale, eval_atom1444]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1445 : SparsePolynomial.Poly := [([8,17,18], 1)]
theorem eval_atom1445 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1445 = ((g 8) * (g 17) * (g 18)) := by
  norm_num [atom1445, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1445_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (73028319197400 : Int) atom1445) := by
  rw [SparsePolynomial.eval_scale, eval_atom1445]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1446 : SparsePolynomial.Poly := [([8,17,19], 1)]
theorem eval_atom1446 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1446 = ((g 8) * (g 17) * (g 19)) := by
  norm_num [atom1446, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1446_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49453121621400 : Int) atom1446) := by
  rw [SparsePolynomial.eval_scale, eval_atom1446]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1447 : SparsePolynomial.Poly := [([8,17,20], 1)]
theorem eval_atom1447 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1447 = ((g 8) * (g 17) * (g 20)) := by
  norm_num [atom1447, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1447_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (54003049493400 : Int) atom1447) := by
  rw [SparsePolynomial.eval_scale, eval_atom1447]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1448 : SparsePolynomial.Poly := [([8,18,18], 1)]
theorem eval_atom1448 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1448 = ((g 8) * (g 18) * (g 18)) := by
  norm_num [atom1448, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1448_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25323261106500 : Int) atom1448) := by
  rw [SparsePolynomial.eval_scale, eval_atom1448]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1449 : SparsePolynomial.Poly := [([8,18,19], 1)]
theorem eval_atom1449 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1449 = ((g 8) * (g 18) * (g 19)) := by
  norm_num [atom1449, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1449_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30034904980500 : Int) atom1449) := by
  rw [SparsePolynomial.eval_scale, eval_atom1449]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1450 : SparsePolynomial.Poly := [([8,18,20], 1)]
theorem eval_atom1450 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1450 = ((g 8) * (g 18) * (g 20)) := by
  norm_num [atom1450, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1450_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36065647557450 : Int) atom1450) := by
  rw [SparsePolynomial.eval_scale, eval_atom1450]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1451 : SparsePolynomial.Poly := [([8,19,20], 1)]
theorem eval_atom1451 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1451 = ((g 8) * (g 19) * (g 20)) := by
  norm_num [atom1451, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1451_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5439574781550 : Int) atom1451) := by
  rw [SparsePolynomial.eval_scale, eval_atom1451]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1452 : SparsePolynomial.Poly := [([8,20,20], 1)]
theorem eval_atom1452 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1452 = ((g 8) * (g 20) * (g 20)) := by
  norm_num [atom1452, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1452_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3482925254550 : Int) atom1452) := by
  rw [SparsePolynomial.eval_scale, eval_atom1452]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1453 : SparsePolynomial.Poly := [([9,9,9], 1)]
theorem eval_atom1453 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1453 = ((g 9) * (g 9) * (g 9)) := by
  norm_num [atom1453, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1453_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (912670214400 : Int) atom1453) := by
  rw [SparsePolynomial.eval_scale, eval_atom1453]
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 9) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1454 : SparsePolynomial.Poly := [([9,9,10], 1)]
theorem eval_atom1454 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1454 = ((g 9) * (g 9) * (g 10)) := by
  norm_num [atom1454, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1454_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (602111059200 : Int) atom1454) := by
  rw [SparsePolynomial.eval_scale, eval_atom1454]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 9) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1455 : SparsePolynomial.Poly := [([9,9,15], 1)]
theorem eval_atom1455 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1455 = ((g 9) * (g 9) * (g 15)) := by
  norm_num [atom1455, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1455_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2995132039200 : Int) atom1455) := by
  rw [SparsePolynomial.eval_scale, eval_atom1455]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block019 : SparsePolynomial.Poly := [([8,8,10], 770276908800), ([8,8,11], 427179916800), ([8,8,15], 3093893233200), ([8,9,9], 1414429430400), ([8,9,10], 518028134400), ([8,9,13], 427179916800), ([8,9,14], 854359833600), ([8,9,15], 5687746762320), ([8,9,17], 2944323370800), ([8,9,18], 5786258284800), ([8,9,19], 11171238059520), ([8,9,20], 17391151612800), ([8,10,10], 1834844054400), ([8,10,11], 2647162425600), ([8,10,12], 2478996576000), ([8,10,13], 3165190560000), ([8,10,14], 3851384544000), ([8,10,15], 7803362548800), ([8,10,16], 2139543982800), ([8,10,17], 9372338136000), ([8,10,18], 11410652912400), ([8,10,19], 20176096474800), ([8,10,20], 30348257839200), ([8,11,11], 3543563721600), ([8,11,12], 5560104211200), ([8,11,13], 6337146412800), ([8,11,14], 7114188614400), ([8,11,15], 12510442929600), ([8,11,16], 8456065254000), ([8,11,17], 19774108468800), ([8,11,18], 20318281326000), ([8,11,19], 30113920746000), ([8,11,20], 40982814885600), ([8,12,12], 5174965756800), ([8,12,13], 10622476166400), ([8,12,14], 11322200736000), ([8,12,15], 14101152139200), ([8,12,16], 13619552332400), ([8,12,17], 25094037416000), ([8,12,18], 27327261530800), ([8,12,19], 37107275293200), ([8,12,20], 48530465474400), ([8,13,13], 8314429795200), ([8,13,14], 15912566956800), ([8,13,15], 19319098982400), ([8,13,16], 19329077214000), ([8,13,17], 34558073524800), ([8,13,18], 38809323630000), ([8,13,19], 42738457266000), ([8,13,20], 60582834597600), ([8,14,14], 12733408598400), ([8,14,15], 24425203723200), ([8,14,16], 24919452658800), ([8,14,17], 46215639489600), ([8,14,18], 52704268570800), ([8,14,19], 52820365827600), ([8,14,20], 77218206357600), ([8,15,15], 19383530342400), ([8,15,16], 39580818694200), ([8,15,17], 66724705152000), ([8,15,18], 71113667221800), ([8,15,19], 53763791949000), ([8,15,20], 82935935850600), ([8,16,16], 15952947010560), ([8,16,17], 56181592441800), ([8,16,18], 64310888457900), ([8,16,19], 46815859734000), ([8,16,20], 61853161781250), ([8,17,17], 41682593433600), ([8,17,18], 73028319197400), ([8,17,19], 49453121621400), ([8,17,20], 54003049493400), ([8,18,18], 25323261106500), ([8,18,19], 30034904980500), ([8,18,20], 36065647557450), ([8,19,20], 5439574781550), ([8,20,20], 3482925254550), ([9,9,9], 912670214400), ([9,9,10], 602111059200), ([9,9,15], 2995132039200)]
theorem block019_data : block019 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (770276908800 : Int) atom1376) (SparsePolynomial.scale (427179916800 : Int) atom1377)) (SparsePolynomial.merge (SparsePolynomial.scale (3093893233200 : Int) atom1378) (SparsePolynomial.merge (SparsePolynomial.scale (1414429430400 : Int) atom1379) (SparsePolynomial.scale (518028134400 : Int) atom1380)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (427179916800 : Int) atom1381) (SparsePolynomial.scale (854359833600 : Int) atom1382)) (SparsePolynomial.merge (SparsePolynomial.scale (5687746762320 : Int) atom1383) (SparsePolynomial.merge (SparsePolynomial.scale (2944323370800 : Int) atom1384) (SparsePolynomial.scale (5786258284800 : Int) atom1385))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (11171238059520 : Int) atom1386) (SparsePolynomial.scale (17391151612800 : Int) atom1387)) (SparsePolynomial.merge (SparsePolynomial.scale (1834844054400 : Int) atom1388) (SparsePolynomial.merge (SparsePolynomial.scale (2647162425600 : Int) atom1389) (SparsePolynomial.scale (2478996576000 : Int) atom1390)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3165190560000 : Int) atom1391) (SparsePolynomial.scale (3851384544000 : Int) atom1392)) (SparsePolynomial.merge (SparsePolynomial.scale (7803362548800 : Int) atom1393) (SparsePolynomial.merge (SparsePolynomial.scale (2139543982800 : Int) atom1394) (SparsePolynomial.scale (9372338136000 : Int) atom1395)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (11410652912400 : Int) atom1396) (SparsePolynomial.scale (20176096474800 : Int) atom1397)) (SparsePolynomial.merge (SparsePolynomial.scale (30348257839200 : Int) atom1398) (SparsePolynomial.merge (SparsePolynomial.scale (3543563721600 : Int) atom1399) (SparsePolynomial.scale (5560104211200 : Int) atom1400)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (6337146412800 : Int) atom1401) (SparsePolynomial.scale (7114188614400 : Int) atom1402)) (SparsePolynomial.merge (SparsePolynomial.scale (12510442929600 : Int) atom1403) (SparsePolynomial.merge (SparsePolynomial.scale (8456065254000 : Int) atom1404) (SparsePolynomial.scale (19774108468800 : Int) atom1405))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (20318281326000 : Int) atom1406) (SparsePolynomial.scale (30113920746000 : Int) atom1407)) (SparsePolynomial.merge (SparsePolynomial.scale (40982814885600 : Int) atom1408) (SparsePolynomial.merge (SparsePolynomial.scale (5174965756800 : Int) atom1409) (SparsePolynomial.scale (10622476166400 : Int) atom1410)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (11322200736000 : Int) atom1411) (SparsePolynomial.scale (14101152139200 : Int) atom1412)) (SparsePolynomial.merge (SparsePolynomial.scale (13619552332400 : Int) atom1413) (SparsePolynomial.merge (SparsePolynomial.scale (25094037416000 : Int) atom1414) (SparsePolynomial.scale (27327261530800 : Int) atom1415))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (37107275293200 : Int) atom1416) (SparsePolynomial.scale (48530465474400 : Int) atom1417)) (SparsePolynomial.merge (SparsePolynomial.scale (8314429795200 : Int) atom1418) (SparsePolynomial.merge (SparsePolynomial.scale (15912566956800 : Int) atom1419) (SparsePolynomial.scale (19319098982400 : Int) atom1420)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (19329077214000 : Int) atom1421) (SparsePolynomial.scale (34558073524800 : Int) atom1422)) (SparsePolynomial.merge (SparsePolynomial.scale (38809323630000 : Int) atom1423) (SparsePolynomial.merge (SparsePolynomial.scale (42738457266000 : Int) atom1424) (SparsePolynomial.scale (60582834597600 : Int) atom1425))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (12733408598400 : Int) atom1426) (SparsePolynomial.scale (24425203723200 : Int) atom1427)) (SparsePolynomial.merge (SparsePolynomial.scale (24919452658800 : Int) atom1428) (SparsePolynomial.merge (SparsePolynomial.scale (46215639489600 : Int) atom1429) (SparsePolynomial.scale (52704268570800 : Int) atom1430)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (52820365827600 : Int) atom1431) (SparsePolynomial.scale (77218206357600 : Int) atom1432)) (SparsePolynomial.merge (SparsePolynomial.scale (19383530342400 : Int) atom1433) (SparsePolynomial.merge (SparsePolynomial.scale (39580818694200 : Int) atom1434) (SparsePolynomial.scale (66724705152000 : Int) atom1435)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (71113667221800 : Int) atom1436) (SparsePolynomial.scale (53763791949000 : Int) atom1437)) (SparsePolynomial.merge (SparsePolynomial.scale (82935935850600 : Int) atom1438) (SparsePolynomial.merge (SparsePolynomial.scale (15952947010560 : Int) atom1439) (SparsePolynomial.scale (56181592441800 : Int) atom1440)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (64310888457900 : Int) atom1441) (SparsePolynomial.scale (46815859734000 : Int) atom1442)) (SparsePolynomial.merge (SparsePolynomial.scale (61853161781250 : Int) atom1443) (SparsePolynomial.merge (SparsePolynomial.scale (41682593433600 : Int) atom1444) (SparsePolynomial.scale (73028319197400 : Int) atom1445))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (49453121621400 : Int) atom1446) (SparsePolynomial.scale (54003049493400 : Int) atom1447)) (SparsePolynomial.merge (SparsePolynomial.scale (25323261106500 : Int) atom1448) (SparsePolynomial.merge (SparsePolynomial.scale (30034904980500 : Int) atom1449) (SparsePolynomial.scale (36065647557450 : Int) atom1450)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (5439574781550 : Int) atom1451) (SparsePolynomial.scale (3482925254550 : Int) atom1452)) (SparsePolynomial.merge (SparsePolynomial.scale (912670214400 : Int) atom1453) (SparsePolynomial.merge (SparsePolynomial.scale (602111059200 : Int) atom1454) (SparsePolynomial.scale (2995132039200 : Int) atom1455)))))))) := by decide +kernel
theorem block019_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block019 := by
  rw [block019_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1376_nonneg g hg hA hB) (atom1377_nonneg g hg hA hB)) (add_nonneg (atom1378_nonneg g hg hA hB) (add_nonneg (atom1379_nonneg g hg hA hB) (atom1380_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1381_nonneg g hg hA hB) (atom1382_nonneg g hg hA hB)) (add_nonneg (atom1383_nonneg g hg hA hB) (add_nonneg (atom1384_nonneg g hg hA hB) (atom1385_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1386_nonneg g hg hA hB) (atom1387_nonneg g hg hA hB)) (add_nonneg (atom1388_nonneg g hg hA hB) (add_nonneg (atom1389_nonneg g hg hA hB) (atom1390_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1391_nonneg g hg hA hB) (atom1392_nonneg g hg hA hB)) (add_nonneg (atom1393_nonneg g hg hA hB) (add_nonneg (atom1394_nonneg g hg hA hB) (atom1395_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1396_nonneg g hg hA hB) (atom1397_nonneg g hg hA hB)) (add_nonneg (atom1398_nonneg g hg hA hB) (add_nonneg (atom1399_nonneg g hg hA hB) (atom1400_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1401_nonneg g hg hA hB) (atom1402_nonneg g hg hA hB)) (add_nonneg (atom1403_nonneg g hg hA hB) (add_nonneg (atom1404_nonneg g hg hA hB) (atom1405_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1406_nonneg g hg hA hB) (atom1407_nonneg g hg hA hB)) (add_nonneg (atom1408_nonneg g hg hA hB) (add_nonneg (atom1409_nonneg g hg hA hB) (atom1410_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1411_nonneg g hg hA hB) (atom1412_nonneg g hg hA hB)) (add_nonneg (atom1413_nonneg g hg hA hB) (add_nonneg (atom1414_nonneg g hg hA hB) (atom1415_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1416_nonneg g hg hA hB) (atom1417_nonneg g hg hA hB)) (add_nonneg (atom1418_nonneg g hg hA hB) (add_nonneg (atom1419_nonneg g hg hA hB) (atom1420_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1421_nonneg g hg hA hB) (atom1422_nonneg g hg hA hB)) (add_nonneg (atom1423_nonneg g hg hA hB) (add_nonneg (atom1424_nonneg g hg hA hB) (atom1425_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1426_nonneg g hg hA hB) (atom1427_nonneg g hg hA hB)) (add_nonneg (atom1428_nonneg g hg hA hB) (add_nonneg (atom1429_nonneg g hg hA hB) (atom1430_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1431_nonneg g hg hA hB) (atom1432_nonneg g hg hA hB)) (add_nonneg (atom1433_nonneg g hg hA hB) (add_nonneg (atom1434_nonneg g hg hA hB) (atom1435_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1436_nonneg g hg hA hB) (atom1437_nonneg g hg hA hB)) (add_nonneg (atom1438_nonneg g hg hA hB) (add_nonneg (atom1439_nonneg g hg hA hB) (atom1440_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1441_nonneg g hg hA hB) (atom1442_nonneg g hg hA hB)) (add_nonneg (atom1443_nonneg g hg hA hB) (add_nonneg (atom1444_nonneg g hg hA hB) (atom1445_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1446_nonneg g hg hA hB) (atom1447_nonneg g hg hA hB)) (add_nonneg (atom1448_nonneg g hg hA hB) (add_nonneg (atom1449_nonneg g hg hA hB) (atom1450_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1451_nonneg g hg hA hB) (atom1452_nonneg g hg hA hB)) (add_nonneg (atom1453_nonneg g hg hA hB) (add_nonneg (atom1454_nonneg g hg hA hB) (atom1455_nonneg g hg hA hB))))))))

end APPT.Finite21
