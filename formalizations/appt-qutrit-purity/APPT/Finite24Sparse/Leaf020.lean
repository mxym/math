import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom1409 : SparsePolynomial.Poly := [([4,14,19], 1)]
theorem eval_atom1409 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1409 = ((g 4) * (g 14) * (g 19)) := by
  norm_num [atom1409, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1409_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (330838724412000 : Int) atom1409) := by
  rw [SparsePolynomial.eval_scale, eval_atom1409]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1410 : SparsePolynomial.Poly := [([4,14,20], 1)]
theorem eval_atom1410 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1410 = ((g 4) * (g 14) * (g 20)) := by
  norm_num [atom1410, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1410_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (432262826251200 : Int) atom1410) := by
  rw [SparsePolynomial.eval_scale, eval_atom1410]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1411 : SparsePolynomial.Poly := [([4,14,21], 1)]
theorem eval_atom1411 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1411 = ((g 4) * (g 14) * (g 21)) := by
  norm_num [atom1411, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1411_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (416309943672000 : Int) atom1411) := by
  rw [SparsePolynomial.eval_scale, eval_atom1411]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 4) * (g 14) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1412 : SparsePolynomial.Poly := [([4,14,22], 1)]
theorem eval_atom1412 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1412 = ((g 4) * (g 14) * (g 22)) := by
  norm_num [atom1412, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1412_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (457356545604000 : Int) atom1412) := by
  rw [SparsePolynomial.eval_scale, eval_atom1412]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 4) * (g 14) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1413 : SparsePolynomial.Poly := [([4,14,23], 1)]
theorem eval_atom1413 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1413 = ((g 4) * (g 14) * (g 23)) := by
  norm_num [atom1413, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1413_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (510982927610400 : Int) atom1413) := by
  rw [SparsePolynomial.eval_scale, eval_atom1413]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 4) * (g 14) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1414 : SparsePolynomial.Poly := [([4,15,15], 1)]
theorem eval_atom1414 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1414 = ((g 4) * (g 15) * (g 15)) := by
  norm_num [atom1414, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1414_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (208278237081600 : Int) atom1414) := by
  rw [SparsePolynomial.eval_scale, eval_atom1414]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1415 : SparsePolynomial.Poly := [([4,15,16], 1)]
theorem eval_atom1415 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1415 = ((g 4) * (g 15) * (g 16)) := by
  norm_num [atom1415, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1415_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (366404392166400 : Int) atom1415) := by
  rw [SparsePolynomial.eval_scale, eval_atom1415]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1416 : SparsePolynomial.Poly := [([4,15,17], 1)]
theorem eval_atom1416 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1416 = ((g 4) * (g 15) * (g 17)) := by
  norm_num [atom1416, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1416_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (344185237670400 : Int) atom1416) := by
  rw [SparsePolynomial.eval_scale, eval_atom1416]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1417 : SparsePolynomial.Poly := [([4,15,18], 1)]
theorem eval_atom1417 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1417 = ((g 4) * (g 15) * (g 18)) := by
  norm_num [atom1417, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1417_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (380141158118400 : Int) atom1417) := by
  rw [SparsePolynomial.eval_scale, eval_atom1417]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1418 : SparsePolynomial.Poly := [([4,15,19], 1)]
theorem eval_atom1418 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1418 = ((g 4) * (g 15) * (g 19)) := by
  norm_num [atom1418, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1418_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (346793499662400 : Int) atom1418) := by
  rw [SparsePolynomial.eval_scale, eval_atom1418]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1419 : SparsePolynomial.Poly := [([4,15,20], 1)]
theorem eval_atom1419 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1419 = ((g 4) * (g 15) * (g 20)) := by
  norm_num [atom1419, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1419_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (472461551755200 : Int) atom1419) := by
  rw [SparsePolynomial.eval_scale, eval_atom1419]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1420 : SparsePolynomial.Poly := [([4,15,21], 1)]
theorem eval_atom1420 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1420 = ((g 4) * (g 15) * (g 21)) := by
  norm_num [atom1420, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1420_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (461611632888000 : Int) atom1420) := by
  rw [SparsePolynomial.eval_scale, eval_atom1420]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 4) * (g 15) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1421 : SparsePolynomial.Poly := [([4,15,22], 1)]
theorem eval_atom1421 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1421 = ((g 4) * (g 15) * (g 22)) := by
  norm_num [atom1421, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1421_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (436957939454400 : Int) atom1421) := by
  rw [SparsePolynomial.eval_scale, eval_atom1421]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 4) * (g 15) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1422 : SparsePolynomial.Poly := [([4,15,23], 1)]
theorem eval_atom1422 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1422 = ((g 4) * (g 15) * (g 23)) := by
  norm_num [atom1422, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1422_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (482678754667200 : Int) atom1422) := by
  rw [SparsePolynomial.eval_scale, eval_atom1422]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 4) * (g 15) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1423 : SparsePolynomial.Poly := [([4,16,16], 1)]
theorem eval_atom1423 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1423 = ((g 4) * (g 16) * (g 16)) := by
  norm_num [atom1423, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1423_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (205392356467200 : Int) atom1423) := by
  rw [SparsePolynomial.eval_scale, eval_atom1423]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1424 : SparsePolynomial.Poly := [([4,16,17], 1)]
theorem eval_atom1424 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1424 = ((g 4) * (g 16) * (g 17)) := by
  norm_num [atom1424, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1424_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (377339038272000 : Int) atom1424) := by
  rw [SparsePolynomial.eval_scale, eval_atom1424]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1425 : SparsePolynomial.Poly := [([4,16,18], 1)]
theorem eval_atom1425 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1425 = ((g 4) * (g 16) * (g 18)) := by
  norm_num [atom1425, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1425_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (386488935705600 : Int) atom1425) := by
  rw [SparsePolynomial.eval_scale, eval_atom1425]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1426 : SparsePolynomial.Poly := [([4,16,19], 1)]
theorem eval_atom1426 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1426 = ((g 4) * (g 16) * (g 19)) := by
  norm_num [atom1426, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1426_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (358244240961600 : Int) atom1426) := by
  rw [SparsePolynomial.eval_scale, eval_atom1426]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1427 : SparsePolynomial.Poly := [([4,16,20], 1)]
theorem eval_atom1427 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1427 = ((g 4) * (g 16) * (g 20)) := by
  norm_num [atom1427, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1427_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (489015256766400 : Int) atom1427) := by
  rw [SparsePolynomial.eval_scale, eval_atom1427]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1428 : SparsePolynomial.Poly := [([4,16,21], 1)]
theorem eval_atom1428 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1428 = ((g 4) * (g 16) * (g 21)) := by
  norm_num [atom1428, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1428_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (483268301611200 : Int) atom1428) := by
  rw [SparsePolynomial.eval_scale, eval_atom1428]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 4) * (g 16) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1429 : SparsePolynomial.Poly := [([4,16,22], 1)]
theorem eval_atom1429 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1429 = ((g 4) * (g 16) * (g 22)) := by
  norm_num [atom1429, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1429_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (405924574910400 : Int) atom1429) := by
  rw [SparsePolynomial.eval_scale, eval_atom1429]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 4) * (g 16) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1430 : SparsePolynomial.Poly := [([4,16,23], 1)]
theorem eval_atom1430 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1430 = ((g 4) * (g 16) * (g 23)) := by
  norm_num [atom1430, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1430_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (533283144811200 : Int) atom1430) := by
  rw [SparsePolynomial.eval_scale, eval_atom1430]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 4) * (g 16) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1431 : SparsePolynomial.Poly := [([4,17,17], 1)]
theorem eval_atom1431 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1431 = ((g 4) * (g 17) * (g 17)) := by
  norm_num [atom1431, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1431_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (214421767257600 : Int) atom1431) := by
  rw [SparsePolynomial.eval_scale, eval_atom1431]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1432 : SparsePolynomial.Poly := [([4,17,18], 1)]
theorem eval_atom1432 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1432 = ((g 4) * (g 17) * (g 18)) := by
  norm_num [atom1432, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1432_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (415025907206400 : Int) atom1432) := by
  rw [SparsePolynomial.eval_scale, eval_atom1432]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1433 : SparsePolynomial.Poly := [([4,17,19], 1)]
theorem eval_atom1433 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1433 = ((g 4) * (g 17) * (g 19)) := by
  norm_num [atom1433, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1433_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (389560459176000 : Int) atom1433) := by
  rw [SparsePolynomial.eval_scale, eval_atom1433]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1434 : SparsePolynomial.Poly := [([4,17,20], 1)]
theorem eval_atom1434 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1434 = ((g 4) * (g 17) * (g 20)) := by
  norm_num [atom1434, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1434_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (523110721694400 : Int) atom1434) := by
  rw [SparsePolynomial.eval_scale, eval_atom1434]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1435 : SparsePolynomial.Poly := [([4,17,21], 1)]
theorem eval_atom1435 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1435 = ((g 4) * (g 17) * (g 21)) := by
  norm_num [atom1435, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1435_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (521304871752000 : Int) atom1435) := by
  rw [SparsePolynomial.eval_scale, eval_atom1435]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 4) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1436 : SparsePolynomial.Poly := [([4,17,22], 1)]
theorem eval_atom1436 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1436 = ((g 4) * (g 17) * (g 22)) := by
  norm_num [atom1436, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1436_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (446778567345600 : Int) atom1436) := by
  rw [SparsePolynomial.eval_scale, eval_atom1436]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 4) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1437 : SparsePolynomial.Poly := [([4,17,23], 1)]
theorem eval_atom1437 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1437 = ((g 4) * (g 17) * (g 23)) := by
  norm_num [atom1437, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1437_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (578659171708800 : Int) atom1437) := by
  rw [SparsePolynomial.eval_scale, eval_atom1437]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 4) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1438 : SparsePolynomial.Poly := [([4,18,18], 1)]
theorem eval_atom1438 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1438 = ((g 4) * (g 18) * (g 18)) := by
  norm_num [atom1438, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1438_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (249088416192000 : Int) atom1438) := by
  rw [SparsePolynomial.eval_scale, eval_atom1438]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1439 : SparsePolynomial.Poly := [([4,18,19], 1)]
theorem eval_atom1439 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1439 = ((g 4) * (g 18) * (g 19)) := by
  norm_num [atom1439, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1439_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (449248020026400 : Int) atom1439) := by
  rw [SparsePolynomial.eval_scale, eval_atom1439]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1440 : SparsePolynomial.Poly := [([4,18,20], 1)]
theorem eval_atom1440 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1440 = ((g 4) * (g 18) * (g 20)) := by
  norm_num [atom1440, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1440_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (620668861394400 : Int) atom1440) := by
  rw [SparsePolynomial.eval_scale, eval_atom1440]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1441 : SparsePolynomial.Poly := [([4,18,21], 1)]
theorem eval_atom1441 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1441 = ((g 4) * (g 18) * (g 21)) := by
  norm_num [atom1441, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1441_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (582988918831200 : Int) atom1441) := by
  rw [SparsePolynomial.eval_scale, eval_atom1441]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 4) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1442 : SparsePolynomial.Poly := [([4,18,22], 1)]
theorem eval_atom1442 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1442 = ((g 4) * (g 18) * (g 22)) := by
  norm_num [atom1442, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1442_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (416071587909600 : Int) atom1442) := by
  rw [SparsePolynomial.eval_scale, eval_atom1442]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 4) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1443 : SparsePolynomial.Poly := [([4,18,23], 1)]
theorem eval_atom1443 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1443 = ((g 4) * (g 18) * (g 23)) := by
  norm_num [atom1443, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1443_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (578049932930400 : Int) atom1443) := by
  rw [SparsePolynomial.eval_scale, eval_atom1443]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 4) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1444 : SparsePolynomial.Poly := [([4,19,19], 1)]
theorem eval_atom1444 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1444 = ((g 4) * (g 19) * (g 19)) := by
  norm_num [atom1444, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1444_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (163652046243840 : Int) atom1444) := by
  rw [SparsePolynomial.eval_scale, eval_atom1444]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1445 : SparsePolynomial.Poly := [([4,19,20], 1)]
theorem eval_atom1445 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1445 = ((g 4) * (g 19) * (g 20)) := by
  norm_num [atom1445, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1445_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (483786370015200 : Int) atom1445) := by
  rw [SparsePolynomial.eval_scale, eval_atom1445]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1446 : SparsePolynomial.Poly := [([4,19,21], 1)]
theorem eval_atom1446 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1446 = ((g 4) * (g 19) * (g 21)) := by
  norm_num [atom1446, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1446_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (464046353038800 : Int) atom1446) := by
  rw [SparsePolynomial.eval_scale, eval_atom1446]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 4) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1447 : SparsePolynomial.Poly := [([4,19,22], 1)]
theorem eval_atom1447 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1447 = ((g 4) * (g 19) * (g 22)) := by
  norm_num [atom1447, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1447_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (352564509192000 : Int) atom1447) := by
  rw [SparsePolynomial.eval_scale, eval_atom1447]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 4) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1448 : SparsePolynomial.Poly := [([4,19,23], 1)]
theorem eval_atom1448 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1448 = ((g 4) * (g 19) * (g 23)) := by
  norm_num [atom1448, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1448_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (361867931119800 : Int) atom1448) := by
  rw [SparsePolynomial.eval_scale, eval_atom1448]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 4) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1449 : SparsePolynomial.Poly := [([4,20,20], 1)]
theorem eval_atom1449 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1449 = ((g 4) * (g 20) * (g 20)) := by
  norm_num [atom1449, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1449_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (344960709357600 : Int) atom1449) := by
  rw [SparsePolynomial.eval_scale, eval_atom1449]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1450 : SparsePolynomial.Poly := [([4,20,21], 1)]
theorem eval_atom1450 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1450 = ((g 4) * (g 20) * (g 21)) := by
  norm_num [atom1450, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1450_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (507525601237200 : Int) atom1450) := by
  rw [SparsePolynomial.eval_scale, eval_atom1450]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 4) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1451 : SparsePolynomial.Poly := [([4,20,22], 1)]
theorem eval_atom1451 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1451 = ((g 4) * (g 20) * (g 22)) := by
  norm_num [atom1451, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1451_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (377976761080800 : Int) atom1451) := by
  rw [SparsePolynomial.eval_scale, eval_atom1451]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 4) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1452 : SparsePolynomial.Poly := [([4,20,23], 1)]
theorem eval_atom1452 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1452 = ((g 4) * (g 20) * (g 23)) := by
  norm_num [atom1452, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1452_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (424529099908200 : Int) atom1452) := by
  rw [SparsePolynomial.eval_scale, eval_atom1452]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 4) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1453 : SparsePolynomial.Poly := [([4,21,21], 1)]
theorem eval_atom1453 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1453 = ((g 4) * (g 21) * (g 21)) := by
  norm_num [atom1453, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1453_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (126080231583600 : Int) atom1453) := by
  rw [SparsePolynomial.eval_scale, eval_atom1453]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 4) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1454 : SparsePolynomial.Poly := [([4,21,22], 1)]
theorem eval_atom1454 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1454 = ((g 4) * (g 21) * (g 22)) := by
  norm_num [atom1454, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1454_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (174744351860400 : Int) atom1454) := by
  rw [SparsePolynomial.eval_scale, eval_atom1454]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 4) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1455 : SparsePolynomial.Poly := [([4,21,23], 1)]
theorem eval_atom1455 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1455 = ((g 4) * (g 21) * (g 23)) := by
  norm_num [atom1455, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1455_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (211258137144600 : Int) atom1455) := by
  rw [SparsePolynomial.eval_scale, eval_atom1455]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 4) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1456 : SparsePolynomial.Poly := [([4,22,23], 1)]
theorem eval_atom1456 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1456 = ((g 4) * (g 22) * (g 23)) := by
  norm_num [atom1456, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1456_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6690481950600 : Int) atom1456) := by
  rw [SparsePolynomial.eval_scale, eval_atom1456]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 4) * (g 22) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1457 : SparsePolynomial.Poly := [([4,23,23], 1)]
theorem eval_atom1457 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1457 = ((g 4) * (g 23) * (g 23)) := by
  norm_num [atom1457, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1457_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (49057765684200 : Int) atom1457) := by
  rw [SparsePolynomial.eval_scale, eval_atom1457]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 4) * (g 23) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1458 : SparsePolynomial.Poly := [([5,5,5], 1)]
theorem eval_atom1458 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1458 = ((g 5) * (g 5) * (g 5)) := by
  norm_num [atom1458, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1458_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19631255212800 : Int) atom1458) := by
  rw [SparsePolynomial.eval_scale, eval_atom1458]
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 5) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1459 : SparsePolynomial.Poly := [([5,5,6], 1)]
theorem eval_atom1459 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1459 = ((g 5) * (g 5) * (g 6)) := by
  norm_num [atom1459, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1459_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (31325586960096 : Int) atom1459) := by
  rw [SparsePolynomial.eval_scale, eval_atom1459]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 5) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1460 : SparsePolynomial.Poly := [([5,5,7], 1)]
theorem eval_atom1460 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1460 = ((g 5) * (g 5) * (g 7)) := by
  norm_num [atom1460, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1460_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6649449936096 : Int) atom1460) := by
  rw [SparsePolynomial.eval_scale, eval_atom1460]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 5) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1461 : SparsePolynomial.Poly := [([5,5,8], 1)]
theorem eval_atom1461 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1461 = ((g 5) * (g 5) * (g 8)) := by
  norm_num [atom1461, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1461_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6533608444704 : Int) atom1461) := by
  rw [SparsePolynomial.eval_scale, eval_atom1461]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 5) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1462 : SparsePolynomial.Poly := [([5,5,9], 1)]
theorem eval_atom1462 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1462 = ((g 5) * (g 5) * (g 9)) := by
  norm_num [atom1462, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1462_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5725639190304 : Int) atom1462) := by
  rw [SparsePolynomial.eval_scale, eval_atom1462]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 5) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1463 : SparsePolynomial.Poly := [([5,5,11], 1)]
theorem eval_atom1463 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1463 = ((g 5) * (g 5) * (g 11)) := by
  norm_num [atom1463, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1463_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2642598614304 : Int) atom1463) := by
  rw [SparsePolynomial.eval_scale, eval_atom1463]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1464 : SparsePolynomial.Poly := [([5,5,12], 1)]
theorem eval_atom1464 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1464 = ((g 5) * (g 5) * (g 12)) := by
  norm_num [atom1464, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1464_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (27375228517824 : Int) atom1464) := by
  rw [SparsePolynomial.eval_scale, eval_atom1464]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1465 : SparsePolynomial.Poly := [([5,5,13], 1)]
theorem eval_atom1465 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1465 = ((g 5) * (g 5) * (g 13)) := by
  norm_num [atom1465, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1465_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (15524745667200 : Int) atom1465) := by
  rw [SparsePolynomial.eval_scale, eval_atom1465]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1466 : SparsePolynomial.Poly := [([5,5,18], 1)]
theorem eval_atom1466 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1466 = ((g 5) * (g 5) * (g 18)) := by
  norm_num [atom1466, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1466_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6709402022400 : Int) atom1466) := by
  rw [SparsePolynomial.eval_scale, eval_atom1466]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 5) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1467 : SparsePolynomial.Poly := [([5,6,6], 1)]
theorem eval_atom1467 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1467 = ((g 5) * (g 6) * (g 6)) := by
  norm_num [atom1467, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1467_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (34147372080096 : Int) atom1467) := by
  rw [SparsePolynomial.eval_scale, eval_atom1467]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 5) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1468 : SparsePolynomial.Poly := [([5,6,7], 1)]
theorem eval_atom1468 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1468 = ((g 5) * (g 6) * (g 7)) := by
  norm_num [atom1468, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1468_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (18942470112192 : Int) atom1468) := by
  rw [SparsePolynomial.eval_scale, eval_atom1468]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 5) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1469 : SparsePolynomial.Poly := [([5,6,12], 1)]
theorem eval_atom1469 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1469 = ((g 5) * (g 6) * (g 12)) := by
  norm_num [atom1469, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1469_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (25753222645920 : Int) atom1469) := by
  rw [SparsePolynomial.eval_scale, eval_atom1469]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1470 : SparsePolynomial.Poly := [([5,6,13], 1)]
theorem eval_atom1470 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1470 = ((g 5) * (g 6) * (g 13)) := by
  norm_num [atom1470, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1470_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (16985780371296 : Int) atom1470) := by
  rw [SparsePolynomial.eval_scale, eval_atom1470]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1471 : SparsePolynomial.Poly := [([5,6,14], 1)]
theorem eval_atom1471 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1471 = ((g 5) * (g 6) * (g 14)) := by
  norm_num [atom1471, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1471_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4544075280096 : Int) atom1471) := by
  rw [SparsePolynomial.eval_scale, eval_atom1471]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1472 : SparsePolynomial.Poly := [([5,6,15], 1)]
theorem eval_atom1472 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1472 = ((g 5) * (g 6) * (g 15)) := by
  norm_num [atom1472, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1472_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7627115856096 : Int) atom1472) := by
  rw [SparsePolynomial.eval_scale, eval_atom1472]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1473 : SparsePolynomial.Poly := [([5,6,16], 1)]
theorem eval_atom1473 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1473 = ((g 5) * (g 6) * (g 16)) := by
  norm_num [atom1473, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1473_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10710156432096 : Int) atom1473) := by
  rw [SparsePolynomial.eval_scale, eval_atom1473]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 6) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1474 : SparsePolynomial.Poly := [([5,6,17], 1)]
theorem eval_atom1474 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1474 = ((g 5) * (g 6) * (g 17)) := by
  norm_num [atom1474, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1474_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (13793197008096 : Int) atom1474) := by
  rw [SparsePolynomial.eval_scale, eval_atom1474]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1475 : SparsePolynomial.Poly := [([5,6,18], 1)]
theorem eval_atom1475 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1475 = ((g 5) * (g 6) * (g 18)) := by
  norm_num [atom1475, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1475_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10047950030448 : Int) atom1475) := by
  rw [SparsePolynomial.eval_scale, eval_atom1475]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 6) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1476 : SparsePolynomial.Poly := [([5,6,19], 1)]
theorem eval_atom1476 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1476 = ((g 5) * (g 6) * (g 19)) := by
  norm_num [atom1476, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1476_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5544496742400 : Int) atom1476) := by
  rw [SparsePolynomial.eval_scale, eval_atom1476]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 6) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1477 : SparsePolynomial.Poly := [([5,6,20], 1)]
theorem eval_atom1477 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1477 = ((g 5) * (g 6) * (g 20)) := by
  norm_num [atom1477, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1477_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7750445476752 : Int) atom1477) := by
  rw [SparsePolynomial.eval_scale, eval_atom1477]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 6) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1478 : SparsePolynomial.Poly := [([5,6,21], 1)]
theorem eval_atom1478 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1478 = ((g 5) * (g 6) * (g 21)) := by
  norm_num [atom1478, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1478_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (48376733335128 : Int) atom1478) := by
  rw [SparsePolynomial.eval_scale, eval_atom1478]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 5) * (g 6) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1479 : SparsePolynomial.Poly := [([5,6,22], 1)]
theorem eval_atom1479 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1479 = ((g 5) * (g 6) * (g 22)) := by
  norm_num [atom1479, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1479_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (89003021193504 : Int) atom1479) := by
  rw [SparsePolynomial.eval_scale, eval_atom1479]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 5) * (g 6) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1480 : SparsePolynomial.Poly := [([5,6,23], 1)]
theorem eval_atom1480 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1480 = ((g 5) * (g 6) * (g 23)) := by
  norm_num [atom1480, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1480_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (136178880879492 : Int) atom1480) := by
  rw [SparsePolynomial.eval_scale, eval_atom1480]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 5) * (g 6) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1481 : SparsePolynomial.Poly := [([5,7,7], 1)]
theorem eval_atom1481 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1481 = ((g 5) * (g 7) * (g 7)) := by
  norm_num [atom1481, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1481_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (12542463216096 : Int) atom1481) := by
  rw [SparsePolynomial.eval_scale, eval_atom1481]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 5) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1482 : SparsePolynomial.Poly := [([5,7,8], 1)]
theorem eval_atom1482 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1482 = ((g 5) * (g 7) * (g 8)) := by
  norm_num [atom1482, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1482_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (14392247654400 : Int) atom1482) := by
  rw [SparsePolynomial.eval_scale, eval_atom1482]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 5) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1483 : SparsePolynomial.Poly := [([5,7,11], 1)]
theorem eval_atom1483 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1483 = ((g 5) * (g 7) * (g 11)) := by
  norm_num [atom1483, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1483_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4124895667200 : Int) atom1483) := by
  rw [SparsePolynomial.eval_scale, eval_atom1483]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1484 : SparsePolynomial.Poly := [([5,7,12], 1)]
theorem eval_atom1484 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1484 = ((g 5) * (g 7) * (g 12)) := by
  norm_num [atom1484, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1484_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (34003013980320 : Int) atom1484) := by
  rw [SparsePolynomial.eval_scale, eval_atom1484]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1485 : SparsePolynomial.Poly := [([5,7,13], 1)]
theorem eval_atom1485 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1485 = ((g 5) * (g 7) * (g 13)) := by
  norm_num [atom1485, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1485_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (27298019539296 : Int) atom1485) := by
  rw [SparsePolynomial.eval_scale, eval_atom1485]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1486 : SparsePolynomial.Poly := [([5,7,14], 1)]
theorem eval_atom1486 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1486 = ((g 5) * (g 7) * (g 14)) := by
  norm_num [atom1486, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1486_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (16918762281696 : Int) atom1486) := by
  rw [SparsePolynomial.eval_scale, eval_atom1486]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1487 : SparsePolynomial.Poly := [([5,7,15], 1)]
theorem eval_atom1487 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1487 = ((g 5) * (g 7) * (g 15)) := by
  norm_num [atom1487, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1487_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (22064250691296 : Int) atom1487) := by
  rw [SparsePolynomial.eval_scale, eval_atom1487]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1488 : SparsePolynomial.Poly := [([5,7,16], 1)]
theorem eval_atom1488 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1488 = ((g 5) * (g 7) * (g 16)) := by
  norm_num [atom1488, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1488_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (27209739100896 : Int) atom1488) := by
  rw [SparsePolynomial.eval_scale, eval_atom1488]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block020 : SparsePolynomial.Poly := [([4,14,19], 330838724412000), ([4,14,20], 432262826251200), ([4,14,21], 416309943672000), ([4,14,22], 457356545604000), ([4,14,23], 510982927610400), ([4,15,15], 208278237081600), ([4,15,16], 366404392166400), ([4,15,17], 344185237670400), ([4,15,18], 380141158118400), ([4,15,19], 346793499662400), ([4,15,20], 472461551755200), ([4,15,21], 461611632888000), ([4,15,22], 436957939454400), ([4,15,23], 482678754667200), ([4,16,16], 205392356467200), ([4,16,17], 377339038272000), ([4,16,18], 386488935705600), ([4,16,19], 358244240961600), ([4,16,20], 489015256766400), ([4,16,21], 483268301611200), ([4,16,22], 405924574910400), ([4,16,23], 533283144811200), ([4,17,17], 214421767257600), ([4,17,18], 415025907206400), ([4,17,19], 389560459176000), ([4,17,20], 523110721694400), ([4,17,21], 521304871752000), ([4,17,22], 446778567345600), ([4,17,23], 578659171708800), ([4,18,18], 249088416192000), ([4,18,19], 449248020026400), ([4,18,20], 620668861394400), ([4,18,21], 582988918831200), ([4,18,22], 416071587909600), ([4,18,23], 578049932930400), ([4,19,19], 163652046243840), ([4,19,20], 483786370015200), ([4,19,21], 464046353038800), ([4,19,22], 352564509192000), ([4,19,23], 361867931119800), ([4,20,20], 344960709357600), ([4,20,21], 507525601237200), ([4,20,22], 377976761080800), ([4,20,23], 424529099908200), ([4,21,21], 126080231583600), ([4,21,22], 174744351860400), ([4,21,23], 211258137144600), ([4,22,23], 6690481950600), ([4,23,23], 49057765684200), ([5,5,5], 19631255212800), ([5,5,6], 31325586960096), ([5,5,7], 6649449936096), ([5,5,8], 6533608444704), ([5,5,9], 5725639190304), ([5,5,11], 2642598614304), ([5,5,12], 27375228517824), ([5,5,13], 15524745667200), ([5,5,18], 6709402022400), ([5,6,6], 34147372080096), ([5,6,7], 18942470112192), ([5,6,12], 25753222645920), ([5,6,13], 16985780371296), ([5,6,14], 4544075280096), ([5,6,15], 7627115856096), ([5,6,16], 10710156432096), ([5,6,17], 13793197008096), ([5,6,18], 10047950030448), ([5,6,19], 5544496742400), ([5,6,20], 7750445476752), ([5,6,21], 48376733335128), ([5,6,22], 89003021193504), ([5,6,23], 136178880879492), ([5,7,7], 12542463216096), ([5,7,8], 14392247654400), ([5,7,11], 4124895667200), ([5,7,12], 34003013980320), ([5,7,13], 27298019539296), ([5,7,14], 16918762281696), ([5,7,15], 22064250691296), ([5,7,16], 27209739100896)]
theorem block020_data : block020 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (330838724412000 : Int) atom1409) (SparsePolynomial.scale (432262826251200 : Int) atom1410)) (SparsePolynomial.merge (SparsePolynomial.scale (416309943672000 : Int) atom1411) (SparsePolynomial.merge (SparsePolynomial.scale (457356545604000 : Int) atom1412) (SparsePolynomial.scale (510982927610400 : Int) atom1413)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (208278237081600 : Int) atom1414) (SparsePolynomial.scale (366404392166400 : Int) atom1415)) (SparsePolynomial.merge (SparsePolynomial.scale (344185237670400 : Int) atom1416) (SparsePolynomial.merge (SparsePolynomial.scale (380141158118400 : Int) atom1417) (SparsePolynomial.scale (346793499662400 : Int) atom1418))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (472461551755200 : Int) atom1419) (SparsePolynomial.scale (461611632888000 : Int) atom1420)) (SparsePolynomial.merge (SparsePolynomial.scale (436957939454400 : Int) atom1421) (SparsePolynomial.merge (SparsePolynomial.scale (482678754667200 : Int) atom1422) (SparsePolynomial.scale (205392356467200 : Int) atom1423)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (377339038272000 : Int) atom1424) (SparsePolynomial.scale (386488935705600 : Int) atom1425)) (SparsePolynomial.merge (SparsePolynomial.scale (358244240961600 : Int) atom1426) (SparsePolynomial.merge (SparsePolynomial.scale (489015256766400 : Int) atom1427) (SparsePolynomial.scale (483268301611200 : Int) atom1428)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (405924574910400 : Int) atom1429) (SparsePolynomial.scale (533283144811200 : Int) atom1430)) (SparsePolynomial.merge (SparsePolynomial.scale (214421767257600 : Int) atom1431) (SparsePolynomial.merge (SparsePolynomial.scale (415025907206400 : Int) atom1432) (SparsePolynomial.scale (389560459176000 : Int) atom1433)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (523110721694400 : Int) atom1434) (SparsePolynomial.scale (521304871752000 : Int) atom1435)) (SparsePolynomial.merge (SparsePolynomial.scale (446778567345600 : Int) atom1436) (SparsePolynomial.merge (SparsePolynomial.scale (578659171708800 : Int) atom1437) (SparsePolynomial.scale (249088416192000 : Int) atom1438))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (449248020026400 : Int) atom1439) (SparsePolynomial.scale (620668861394400 : Int) atom1440)) (SparsePolynomial.merge (SparsePolynomial.scale (582988918831200 : Int) atom1441) (SparsePolynomial.merge (SparsePolynomial.scale (416071587909600 : Int) atom1442) (SparsePolynomial.scale (578049932930400 : Int) atom1443)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (163652046243840 : Int) atom1444) (SparsePolynomial.scale (483786370015200 : Int) atom1445)) (SparsePolynomial.merge (SparsePolynomial.scale (464046353038800 : Int) atom1446) (SparsePolynomial.merge (SparsePolynomial.scale (352564509192000 : Int) atom1447) (SparsePolynomial.scale (361867931119800 : Int) atom1448))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (344960709357600 : Int) atom1449) (SparsePolynomial.scale (507525601237200 : Int) atom1450)) (SparsePolynomial.merge (SparsePolynomial.scale (377976761080800 : Int) atom1451) (SparsePolynomial.merge (SparsePolynomial.scale (424529099908200 : Int) atom1452) (SparsePolynomial.scale (126080231583600 : Int) atom1453)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (174744351860400 : Int) atom1454) (SparsePolynomial.scale (211258137144600 : Int) atom1455)) (SparsePolynomial.merge (SparsePolynomial.scale (6690481950600 : Int) atom1456) (SparsePolynomial.merge (SparsePolynomial.scale (49057765684200 : Int) atom1457) (SparsePolynomial.scale (19631255212800 : Int) atom1458))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (31325586960096 : Int) atom1459) (SparsePolynomial.scale (6649449936096 : Int) atom1460)) (SparsePolynomial.merge (SparsePolynomial.scale (6533608444704 : Int) atom1461) (SparsePolynomial.merge (SparsePolynomial.scale (5725639190304 : Int) atom1462) (SparsePolynomial.scale (2642598614304 : Int) atom1463)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (27375228517824 : Int) atom1464) (SparsePolynomial.scale (15524745667200 : Int) atom1465)) (SparsePolynomial.merge (SparsePolynomial.scale (6709402022400 : Int) atom1466) (SparsePolynomial.merge (SparsePolynomial.scale (34147372080096 : Int) atom1467) (SparsePolynomial.scale (18942470112192 : Int) atom1468)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (25753222645920 : Int) atom1469) (SparsePolynomial.scale (16985780371296 : Int) atom1470)) (SparsePolynomial.merge (SparsePolynomial.scale (4544075280096 : Int) atom1471) (SparsePolynomial.merge (SparsePolynomial.scale (7627115856096 : Int) atom1472) (SparsePolynomial.scale (10710156432096 : Int) atom1473)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (13793197008096 : Int) atom1474) (SparsePolynomial.scale (10047950030448 : Int) atom1475)) (SparsePolynomial.merge (SparsePolynomial.scale (5544496742400 : Int) atom1476) (SparsePolynomial.merge (SparsePolynomial.scale (7750445476752 : Int) atom1477) (SparsePolynomial.scale (48376733335128 : Int) atom1478))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (89003021193504 : Int) atom1479) (SparsePolynomial.scale (136178880879492 : Int) atom1480)) (SparsePolynomial.merge (SparsePolynomial.scale (12542463216096 : Int) atom1481) (SparsePolynomial.merge (SparsePolynomial.scale (14392247654400 : Int) atom1482) (SparsePolynomial.scale (4124895667200 : Int) atom1483)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (34003013980320 : Int) atom1484) (SparsePolynomial.scale (27298019539296 : Int) atom1485)) (SparsePolynomial.merge (SparsePolynomial.scale (16918762281696 : Int) atom1486) (SparsePolynomial.merge (SparsePolynomial.scale (22064250691296 : Int) atom1487) (SparsePolynomial.scale (27209739100896 : Int) atom1488)))))))) := by decide +kernel
theorem block020_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block020 := by
  rw [block020_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1409_nonneg g hg hA hB) (atom1410_nonneg g hg hA hB)) (add_nonneg (atom1411_nonneg g hg hA hB) (add_nonneg (atom1412_nonneg g hg hA hB) (atom1413_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1414_nonneg g hg hA hB) (atom1415_nonneg g hg hA hB)) (add_nonneg (atom1416_nonneg g hg hA hB) (add_nonneg (atom1417_nonneg g hg hA hB) (atom1418_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1419_nonneg g hg hA hB) (atom1420_nonneg g hg hA hB)) (add_nonneg (atom1421_nonneg g hg hA hB) (add_nonneg (atom1422_nonneg g hg hA hB) (atom1423_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1424_nonneg g hg hA hB) (atom1425_nonneg g hg hA hB)) (add_nonneg (atom1426_nonneg g hg hA hB) (add_nonneg (atom1427_nonneg g hg hA hB) (atom1428_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1429_nonneg g hg hA hB) (atom1430_nonneg g hg hA hB)) (add_nonneg (atom1431_nonneg g hg hA hB) (add_nonneg (atom1432_nonneg g hg hA hB) (atom1433_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1434_nonneg g hg hA hB) (atom1435_nonneg g hg hA hB)) (add_nonneg (atom1436_nonneg g hg hA hB) (add_nonneg (atom1437_nonneg g hg hA hB) (atom1438_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1439_nonneg g hg hA hB) (atom1440_nonneg g hg hA hB)) (add_nonneg (atom1441_nonneg g hg hA hB) (add_nonneg (atom1442_nonneg g hg hA hB) (atom1443_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1444_nonneg g hg hA hB) (atom1445_nonneg g hg hA hB)) (add_nonneg (atom1446_nonneg g hg hA hB) (add_nonneg (atom1447_nonneg g hg hA hB) (atom1448_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1449_nonneg g hg hA hB) (atom1450_nonneg g hg hA hB)) (add_nonneg (atom1451_nonneg g hg hA hB) (add_nonneg (atom1452_nonneg g hg hA hB) (atom1453_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1454_nonneg g hg hA hB) (atom1455_nonneg g hg hA hB)) (add_nonneg (atom1456_nonneg g hg hA hB) (add_nonneg (atom1457_nonneg g hg hA hB) (atom1458_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1459_nonneg g hg hA hB) (atom1460_nonneg g hg hA hB)) (add_nonneg (atom1461_nonneg g hg hA hB) (add_nonneg (atom1462_nonneg g hg hA hB) (atom1463_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1464_nonneg g hg hA hB) (atom1465_nonneg g hg hA hB)) (add_nonneg (atom1466_nonneg g hg hA hB) (add_nonneg (atom1467_nonneg g hg hA hB) (atom1468_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1469_nonneg g hg hA hB) (atom1470_nonneg g hg hA hB)) (add_nonneg (atom1471_nonneg g hg hA hB) (add_nonneg (atom1472_nonneg g hg hA hB) (atom1473_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1474_nonneg g hg hA hB) (atom1475_nonneg g hg hA hB)) (add_nonneg (atom1476_nonneg g hg hA hB) (add_nonneg (atom1477_nonneg g hg hA hB) (atom1478_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1479_nonneg g hg hA hB) (atom1480_nonneg g hg hA hB)) (add_nonneg (atom1481_nonneg g hg hA hB) (add_nonneg (atom1482_nonneg g hg hA hB) (atom1483_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1484_nonneg g hg hA hB) (atom1485_nonneg g hg hA hB)) (add_nonneg (atom1486_nonneg g hg hA hB) (add_nonneg (atom1487_nonneg g hg hA hB) (atom1488_nonneg g hg hA hB))))))))

end APPT.Finite24
