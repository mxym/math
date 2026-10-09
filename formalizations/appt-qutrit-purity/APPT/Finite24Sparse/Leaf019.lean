import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom1329 : SparsePolynomial.Poly := [([4,8,14], 1)]
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
def atom1330 : SparsePolynomial.Poly := [([4,8,15], 1)]
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
def atom1331 : SparsePolynomial.Poly := [([4,8,16], 1)]
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
def atom1332 : SparsePolynomial.Poly := [([4,8,17], 1)]
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
def atom1333 : SparsePolynomial.Poly := [([4,8,18], 1)]
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
def atom1334 : SparsePolynomial.Poly := [([4,8,19], 1)]
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
def atom1335 : SparsePolynomial.Poly := [([4,8,20], 1)]
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
def atom1336 : SparsePolynomial.Poly := [([4,8,21], 1)]
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
def atom1337 : SparsePolynomial.Poly := [([4,8,22], 1)]
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
def atom1338 : SparsePolynomial.Poly := [([4,8,23], 1)]
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
def atom1339 : SparsePolynomial.Poly := [([4,9,9], 1)]
theorem eval_atom1339 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1339 = ((g 4) * (g 9) * (g 9)) := by
  norm_num [atom1339, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1339_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (69667045180128 : Int) atom1339) := by
  rw [SparsePolynomial.eval_scale, eval_atom1339]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1340 : SparsePolynomial.Poly := [([4,9,10], 1)]
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
def atom1341 : SparsePolynomial.Poly := [([4,9,11], 1)]
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
def atom1342 : SparsePolynomial.Poly := [([4,9,12], 1)]
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
def atom1343 : SparsePolynomial.Poly := [([4,9,13], 1)]
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
def atom1344 : SparsePolynomial.Poly := [([4,9,14], 1)]
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
def atom1345 : SparsePolynomial.Poly := [([4,9,15], 1)]
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
def atom1346 : SparsePolynomial.Poly := [([4,9,16], 1)]
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
def atom1347 : SparsePolynomial.Poly := [([4,9,17], 1)]
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
def atom1348 : SparsePolynomial.Poly := [([4,9,18], 1)]
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
def atom1349 : SparsePolynomial.Poly := [([4,9,19], 1)]
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
def atom1350 : SparsePolynomial.Poly := [([4,9,20], 1)]
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
def atom1351 : SparsePolynomial.Poly := [([4,9,21], 1)]
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
def atom1352 : SparsePolynomial.Poly := [([4,9,22], 1)]
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
def atom1353 : SparsePolynomial.Poly := [([4,9,23], 1)]
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
def atom1354 : SparsePolynomial.Poly := [([4,10,10], 1)]
theorem eval_atom1354 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1354 = ((g 4) * (g 10) * (g 10)) := by
  norm_num [atom1354, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1354_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (94497216108768 : Int) atom1354) := by
  rw [SparsePolynomial.eval_scale, eval_atom1354]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1355 : SparsePolynomial.Poly := [([4,10,11], 1)]
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
def atom1356 : SparsePolynomial.Poly := [([4,10,12], 1)]
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
def atom1357 : SparsePolynomial.Poly := [([4,10,13], 1)]
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
def atom1358 : SparsePolynomial.Poly := [([4,10,14], 1)]
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
def atom1359 : SparsePolynomial.Poly := [([4,10,15], 1)]
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
def atom1360 : SparsePolynomial.Poly := [([4,10,16], 1)]
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
def atom1361 : SparsePolynomial.Poly := [([4,10,17], 1)]
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
def atom1362 : SparsePolynomial.Poly := [([4,10,18], 1)]
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
def atom1363 : SparsePolynomial.Poly := [([4,10,19], 1)]
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
def atom1364 : SparsePolynomial.Poly := [([4,10,20], 1)]
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
def atom1365 : SparsePolynomial.Poly := [([4,10,21], 1)]
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
def atom1366 : SparsePolynomial.Poly := [([4,10,22], 1)]
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
def atom1367 : SparsePolynomial.Poly := [([4,10,23], 1)]
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
def atom1368 : SparsePolynomial.Poly := [([4,11,11], 1)]
theorem eval_atom1368 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1368 = ((g 4) * (g 11) * (g 11)) := by
  norm_num [atom1368, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1368_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (135328071472704 : Int) atom1368) := by
  rw [SparsePolynomial.eval_scale, eval_atom1368]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1369 : SparsePolynomial.Poly := [([4,11,12], 1)]
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
def atom1370 : SparsePolynomial.Poly := [([4,11,13], 1)]
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
def atom1371 : SparsePolynomial.Poly := [([4,11,14], 1)]
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
def atom1372 : SparsePolynomial.Poly := [([4,11,15], 1)]
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
def atom1373 : SparsePolynomial.Poly := [([4,11,16], 1)]
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
def atom1374 : SparsePolynomial.Poly := [([4,11,17], 1)]
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
def atom1375 : SparsePolynomial.Poly := [([4,11,18], 1)]
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
def atom1376 : SparsePolynomial.Poly := [([4,11,19], 1)]
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
def atom1377 : SparsePolynomial.Poly := [([4,11,20], 1)]
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
def atom1378 : SparsePolynomial.Poly := [([4,11,21], 1)]
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
def atom1379 : SparsePolynomial.Poly := [([4,11,22], 1)]
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
def atom1380 : SparsePolynomial.Poly := [([4,11,23], 1)]
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
def atom1381 : SparsePolynomial.Poly := [([4,12,12], 1)]
theorem eval_atom1381 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1381 = ((g 4) * (g 12) * (g 12)) := by
  norm_num [atom1381, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1381_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (176428723261824 : Int) atom1381) := by
  rw [SparsePolynomial.eval_scale, eval_atom1381]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1382 : SparsePolynomial.Poly := [([4,12,13], 1)]
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
def atom1383 : SparsePolynomial.Poly := [([4,12,14], 1)]
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
def atom1384 : SparsePolynomial.Poly := [([4,12,15], 1)]
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
def atom1385 : SparsePolynomial.Poly := [([4,12,16], 1)]
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
def atom1386 : SparsePolynomial.Poly := [([4,12,17], 1)]
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
def atom1387 : SparsePolynomial.Poly := [([4,12,18], 1)]
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
def atom1388 : SparsePolynomial.Poly := [([4,12,19], 1)]
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
def atom1389 : SparsePolynomial.Poly := [([4,12,20], 1)]
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
def atom1390 : SparsePolynomial.Poly := [([4,12,21], 1)]
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
def atom1391 : SparsePolynomial.Poly := [([4,12,22], 1)]
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
def atom1392 : SparsePolynomial.Poly := [([4,12,23], 1)]
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
def atom1393 : SparsePolynomial.Poly := [([4,13,13], 1)]
theorem eval_atom1393 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1393 = ((g 4) * (g 13) * (g 13)) := by
  norm_num [atom1393, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1393_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (187932272774400 : Int) atom1393) := by
  rw [SparsePolynomial.eval_scale, eval_atom1393]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1394 : SparsePolynomial.Poly := [([4,13,14], 1)]
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
def atom1395 : SparsePolynomial.Poly := [([4,13,15], 1)]
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
def atom1396 : SparsePolynomial.Poly := [([4,13,16], 1)]
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
def atom1397 : SparsePolynomial.Poly := [([4,13,17], 1)]
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
def atom1398 : SparsePolynomial.Poly := [([4,13,18], 1)]
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
def atom1399 : SparsePolynomial.Poly := [([4,13,19], 1)]
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
def atom1400 : SparsePolynomial.Poly := [([4,13,20], 1)]
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
def atom1401 : SparsePolynomial.Poly := [([4,13,21], 1)]
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
def atom1402 : SparsePolynomial.Poly := [([4,13,22], 1)]
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
def atom1403 : SparsePolynomial.Poly := [([4,13,23], 1)]
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
def atom1404 : SparsePolynomial.Poly := [([4,14,14], 1)]
theorem eval_atom1404 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1404 = ((g 4) * (g 14) * (g 14)) := by
  norm_num [atom1404, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1404_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (190166903942400 : Int) atom1404) := by
  rw [SparsePolynomial.eval_scale, eval_atom1404]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1405 : SparsePolynomial.Poly := [([4,14,15], 1)]
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
def atom1406 : SparsePolynomial.Poly := [([4,14,16], 1)]
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
def atom1407 : SparsePolynomial.Poly := [([4,14,17], 1)]
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
def atom1408 : SparsePolynomial.Poly := [([4,14,18], 1)]
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
def block019 : SparsePolynomial.Poly := [([4,8,14], 95552995507200), ([4,8,15], 99003939148800), ([4,8,16], 90632372544000), ([4,8,17], 96840978393600), ([4,8,18], 137461084992000), ([4,8,19], 157970956046400), ([4,8,20], 196654739198400), ([4,8,21], 267813699652800), ([4,8,22], 338972660107200), ([4,8,23], 410131620561600), ([4,9,9], 69667045180128), ([4,9,10], 129230222210496), ([4,9,11], 123772944236832), ([4,9,12], 151694926460352), ([4,9,13], 139950755353728), ([4,9,14], 127615362006528), ([4,9,15], 130066975254528), ([4,9,16], 120696078256128), ([4,9,17], 125905353712128), ([4,9,18], 167729597747712), ([4,9,19], 191647074070080), ([4,9,20], 233738462490048), ([4,9,21], 312711963873984), ([4,9,22], 391685465257920), ([4,9,23], 470658966641856), ([4,10,10], 94497216108768), ([4,10,11], 188725167351072), ([4,10,12], 211544185862592), ([4,10,13], 200863132195968), ([4,10,14], 186507815712768), ([4,10,15], 186939505824768), ([4,10,16], 175548685690368), ([4,10,17], 178738038010368), ([4,10,18], 217275122921472), ([4,10,19], 236638204130880), ([4,10,20], 274175197437888), ([4,10,21], 346059831731904), ([4,10,22], 417944466025920), ([4,10,23], 489829100319936), ([4,11,11], 135328071472704), ([4,11,12], 270656674504128), ([4,11,13], 253852064383104), ([4,11,14], 233373191445504), ([4,11,15], 227681325103104), ([4,11,16], 213249989090304), ([4,11,17], 213398825531904), ([4,11,18], 261028728595008), ([4,11,19], 266731717631040), ([4,11,20], 312525412535808), ([4,11,21], 373099828946112), ([4,11,22], 443962291008960), ([4,11,23], 514824753071808), ([4,12,12], 176428723261824), ([4,12,13], 323260875805824), ([4,12,14], 301803934823424), ([4,12,15], 295134000436224), ([4,12,16], 276641555802624), ([4,12,17], 272729283623424), ([4,12,18], 341962264626048), ([4,12,19], 308703594162240), ([4,12,20], 403664875990848), ([4,12,21], 388476759598272), ([4,12,22], 442962960615360), ([4,12,23], 497449161632448), ([4,13,13], 187932272774400), ([4,13,14], 336999056486400), ([4,13,15], 322164380160000), ([4,13,16], 298590234163200), ([4,13,17], 289596260620800), ([4,13,18], 349729575148800), ([4,13,19], 320595613934400), ([4,13,20], 421638113937600), ([4,13,21], 400582267646400), ([4,13,22], 456904694635200), ([4,13,23], 513227121624000), ([4,14,14], 190166903942400), ([4,14,15], 354261980217600), ([4,14,16], 324585540115200), ([4,14,17], 309489272467200), ([4,14,18], 350148360038400)]
theorem block019_data : block019 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (95552995507200 : Int) atom1329) (SparsePolynomial.scale (99003939148800 : Int) atom1330)) (SparsePolynomial.merge (SparsePolynomial.scale (90632372544000 : Int) atom1331) (SparsePolynomial.merge (SparsePolynomial.scale (96840978393600 : Int) atom1332) (SparsePolynomial.scale (137461084992000 : Int) atom1333)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (157970956046400 : Int) atom1334) (SparsePolynomial.scale (196654739198400 : Int) atom1335)) (SparsePolynomial.merge (SparsePolynomial.scale (267813699652800 : Int) atom1336) (SparsePolynomial.merge (SparsePolynomial.scale (338972660107200 : Int) atom1337) (SparsePolynomial.scale (410131620561600 : Int) atom1338))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (69667045180128 : Int) atom1339) (SparsePolynomial.scale (129230222210496 : Int) atom1340)) (SparsePolynomial.merge (SparsePolynomial.scale (123772944236832 : Int) atom1341) (SparsePolynomial.merge (SparsePolynomial.scale (151694926460352 : Int) atom1342) (SparsePolynomial.scale (139950755353728 : Int) atom1343)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (127615362006528 : Int) atom1344) (SparsePolynomial.scale (130066975254528 : Int) atom1345)) (SparsePolynomial.merge (SparsePolynomial.scale (120696078256128 : Int) atom1346) (SparsePolynomial.merge (SparsePolynomial.scale (125905353712128 : Int) atom1347) (SparsePolynomial.scale (167729597747712 : Int) atom1348)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (191647074070080 : Int) atom1349) (SparsePolynomial.scale (233738462490048 : Int) atom1350)) (SparsePolynomial.merge (SparsePolynomial.scale (312711963873984 : Int) atom1351) (SparsePolynomial.merge (SparsePolynomial.scale (391685465257920 : Int) atom1352) (SparsePolynomial.scale (470658966641856 : Int) atom1353)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (94497216108768 : Int) atom1354) (SparsePolynomial.scale (188725167351072 : Int) atom1355)) (SparsePolynomial.merge (SparsePolynomial.scale (211544185862592 : Int) atom1356) (SparsePolynomial.merge (SparsePolynomial.scale (200863132195968 : Int) atom1357) (SparsePolynomial.scale (186507815712768 : Int) atom1358))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (186939505824768 : Int) atom1359) (SparsePolynomial.scale (175548685690368 : Int) atom1360)) (SparsePolynomial.merge (SparsePolynomial.scale (178738038010368 : Int) atom1361) (SparsePolynomial.merge (SparsePolynomial.scale (217275122921472 : Int) atom1362) (SparsePolynomial.scale (236638204130880 : Int) atom1363)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (274175197437888 : Int) atom1364) (SparsePolynomial.scale (346059831731904 : Int) atom1365)) (SparsePolynomial.merge (SparsePolynomial.scale (417944466025920 : Int) atom1366) (SparsePolynomial.merge (SparsePolynomial.scale (489829100319936 : Int) atom1367) (SparsePolynomial.scale (135328071472704 : Int) atom1368))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (270656674504128 : Int) atom1369) (SparsePolynomial.scale (253852064383104 : Int) atom1370)) (SparsePolynomial.merge (SparsePolynomial.scale (233373191445504 : Int) atom1371) (SparsePolynomial.merge (SparsePolynomial.scale (227681325103104 : Int) atom1372) (SparsePolynomial.scale (213249989090304 : Int) atom1373)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (213398825531904 : Int) atom1374) (SparsePolynomial.scale (261028728595008 : Int) atom1375)) (SparsePolynomial.merge (SparsePolynomial.scale (266731717631040 : Int) atom1376) (SparsePolynomial.merge (SparsePolynomial.scale (312525412535808 : Int) atom1377) (SparsePolynomial.scale (373099828946112 : Int) atom1378))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (443962291008960 : Int) atom1379) (SparsePolynomial.scale (514824753071808 : Int) atom1380)) (SparsePolynomial.merge (SparsePolynomial.scale (176428723261824 : Int) atom1381) (SparsePolynomial.merge (SparsePolynomial.scale (323260875805824 : Int) atom1382) (SparsePolynomial.scale (301803934823424 : Int) atom1383)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (295134000436224 : Int) atom1384) (SparsePolynomial.scale (276641555802624 : Int) atom1385)) (SparsePolynomial.merge (SparsePolynomial.scale (272729283623424 : Int) atom1386) (SparsePolynomial.merge (SparsePolynomial.scale (341962264626048 : Int) atom1387) (SparsePolynomial.scale (308703594162240 : Int) atom1388)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (403664875990848 : Int) atom1389) (SparsePolynomial.scale (388476759598272 : Int) atom1390)) (SparsePolynomial.merge (SparsePolynomial.scale (442962960615360 : Int) atom1391) (SparsePolynomial.merge (SparsePolynomial.scale (497449161632448 : Int) atom1392) (SparsePolynomial.scale (187932272774400 : Int) atom1393)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (336999056486400 : Int) atom1394) (SparsePolynomial.scale (322164380160000 : Int) atom1395)) (SparsePolynomial.merge (SparsePolynomial.scale (298590234163200 : Int) atom1396) (SparsePolynomial.merge (SparsePolynomial.scale (289596260620800 : Int) atom1397) (SparsePolynomial.scale (349729575148800 : Int) atom1398))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (320595613934400 : Int) atom1399) (SparsePolynomial.scale (421638113937600 : Int) atom1400)) (SparsePolynomial.merge (SparsePolynomial.scale (400582267646400 : Int) atom1401) (SparsePolynomial.merge (SparsePolynomial.scale (456904694635200 : Int) atom1402) (SparsePolynomial.scale (513227121624000 : Int) atom1403)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (190166903942400 : Int) atom1404) (SparsePolynomial.scale (354261980217600 : Int) atom1405)) (SparsePolynomial.merge (SparsePolynomial.scale (324585540115200 : Int) atom1406) (SparsePolynomial.merge (SparsePolynomial.scale (309489272467200 : Int) atom1407) (SparsePolynomial.scale (350148360038400 : Int) atom1408)))))))) := by decide +kernel
theorem block019_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block019 := by
  rw [block019_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1329_nonneg g hg hA hB) (atom1330_nonneg g hg hA hB)) (add_nonneg (atom1331_nonneg g hg hA hB) (add_nonneg (atom1332_nonneg g hg hA hB) (atom1333_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1334_nonneg g hg hA hB) (atom1335_nonneg g hg hA hB)) (add_nonneg (atom1336_nonneg g hg hA hB) (add_nonneg (atom1337_nonneg g hg hA hB) (atom1338_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1339_nonneg g hg hA hB) (atom1340_nonneg g hg hA hB)) (add_nonneg (atom1341_nonneg g hg hA hB) (add_nonneg (atom1342_nonneg g hg hA hB) (atom1343_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1344_nonneg g hg hA hB) (atom1345_nonneg g hg hA hB)) (add_nonneg (atom1346_nonneg g hg hA hB) (add_nonneg (atom1347_nonneg g hg hA hB) (atom1348_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1349_nonneg g hg hA hB) (atom1350_nonneg g hg hA hB)) (add_nonneg (atom1351_nonneg g hg hA hB) (add_nonneg (atom1352_nonneg g hg hA hB) (atom1353_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1354_nonneg g hg hA hB) (atom1355_nonneg g hg hA hB)) (add_nonneg (atom1356_nonneg g hg hA hB) (add_nonneg (atom1357_nonneg g hg hA hB) (atom1358_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1359_nonneg g hg hA hB) (atom1360_nonneg g hg hA hB)) (add_nonneg (atom1361_nonneg g hg hA hB) (add_nonneg (atom1362_nonneg g hg hA hB) (atom1363_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1364_nonneg g hg hA hB) (atom1365_nonneg g hg hA hB)) (add_nonneg (atom1366_nonneg g hg hA hB) (add_nonneg (atom1367_nonneg g hg hA hB) (atom1368_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1369_nonneg g hg hA hB) (atom1370_nonneg g hg hA hB)) (add_nonneg (atom1371_nonneg g hg hA hB) (add_nonneg (atom1372_nonneg g hg hA hB) (atom1373_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1374_nonneg g hg hA hB) (atom1375_nonneg g hg hA hB)) (add_nonneg (atom1376_nonneg g hg hA hB) (add_nonneg (atom1377_nonneg g hg hA hB) (atom1378_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1379_nonneg g hg hA hB) (atom1380_nonneg g hg hA hB)) (add_nonneg (atom1381_nonneg g hg hA hB) (add_nonneg (atom1382_nonneg g hg hA hB) (atom1383_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1384_nonneg g hg hA hB) (atom1385_nonneg g hg hA hB)) (add_nonneg (atom1386_nonneg g hg hA hB) (add_nonneg (atom1387_nonneg g hg hA hB) (atom1388_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1389_nonneg g hg hA hB) (atom1390_nonneg g hg hA hB)) (add_nonneg (atom1391_nonneg g hg hA hB) (add_nonneg (atom1392_nonneg g hg hA hB) (atom1393_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1394_nonneg g hg hA hB) (atom1395_nonneg g hg hA hB)) (add_nonneg (atom1396_nonneg g hg hA hB) (add_nonneg (atom1397_nonneg g hg hA hB) (atom1398_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1399_nonneg g hg hA hB) (atom1400_nonneg g hg hA hB)) (add_nonneg (atom1401_nonneg g hg hA hB) (add_nonneg (atom1402_nonneg g hg hA hB) (atom1403_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1404_nonneg g hg hA hB) (atom1405_nonneg g hg hA hB)) (add_nonneg (atom1406_nonneg g hg hA hB) (add_nonneg (atom1407_nonneg g hg hA hB) (atom1408_nonneg g hg hA hB))))))))

end APPT.Finite24
