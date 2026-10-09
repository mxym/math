import APPT.Finite24Sparse.Base05
import APPT.Finite24Sparse.Base06
import APPT.Finite24Sparse.Base07
import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom0049 : SparsePolynomial.Poly := [([0,0,16], -1), ([0,1,16], -2), ([0,2,16], -2), ([0,3,16], -2), ([0,4,16], -2), ([0,5,16], -2), ([0,6,16], -2), ([0,7,16], -2), ([0,8,16], -2), ([0,9,16], -2), ([0,10,16], -2), ([0,11,16], -2), ([0,12,16], -2), ([0,13,16], -2), ([0,14,16], -2), ([0,15,16], -2), ([0,16,16], -2), ([0,16,17], -2), ([0,16,18], -2), ([0,16,19], -2), ([0,16,20], -2), ([0,16,21], -2), ([1,1,16], -1), ([1,2,16], -2), ([1,3,16], -2), ([1,4,16], -2), ([1,5,16], -2), ([1,6,16], -2), ([1,7,16], -2), ([1,8,16], -2), ([1,9,16], -2), ([1,10,16], -2), ([1,11,16], -2), ([1,12,16], -2), ([1,13,16], -2), ([1,14,16], -2), ([1,15,16], -2), ([1,16,16], -2), ([1,16,17], -2), ([1,16,18], -2), ([1,16,19], -2), ([1,16,20], -2), ([1,16,21], -2), ([2,2,16], -1), ([2,3,16], -2), ([2,4,16], -2), ([2,5,16], -2), ([2,6,16], -2), ([2,7,16], -2), ([2,8,16], -2), ([2,9,16], -2), ([2,10,16], -2), ([2,11,16], -2), ([2,12,16], -2), ([2,13,16], -2), ([2,14,16], -2), ([2,15,16], -2), ([2,16,16], -2), ([2,16,17], -2), ([2,16,18], -2), ([2,16,19], -2), ([2,16,20], -2), ([2,16,21], -2), ([3,3,16], -1), ([3,4,16], -2), ([3,5,16], -2), ([3,6,16], -2), ([3,7,16], -2), ([3,8,16], -2), ([3,9,16], -2), ([3,10,16], -2), ([3,11,16], -2), ([3,12,16], -2), ([3,13,16], -2), ([3,14,16], -2), ([3,15,16], -2), ([3,16,16], -2), ([3,16,17], -2), ([3,16,18], -2), ([3,16,19], -2), ([3,16,20], -2), ([3,16,21], -2), ([4,4,16], -1), ([4,5,16], -2), ([4,6,16], -2), ([4,7,16], -2), ([4,8,16], -2), ([4,9,16], -2), ([4,10,16], -2), ([4,11,16], -2), ([4,12,16], -2), ([4,13,16], -2), ([4,14,16], -2), ([4,15,16], -2), ([4,16,16], -2), ([4,16,17], -2), ([4,16,18], -2), ([4,16,19], -2), ([4,16,20], -2), ([4,16,21], -2), ([5,5,16], -1), ([5,6,16], -2), ([5,7,16], -2), ([5,8,16], -2), ([5,9,16], -2), ([5,10,16], -2), ([5,11,16], -2), ([5,12,16], -2), ([5,13,16], -2), ([5,14,16], -2), ([5,15,16], -2), ([5,16,16], -2), ([5,16,17], -2), ([5,16,18], -2), ([5,16,19], -2), ([5,16,20], -2), ([5,16,21], -2), ([6,6,16], -1), ([6,7,16], -2), ([6,8,16], -2), ([6,9,16], -2), ([6,10,16], -2), ([6,11,16], -2), ([6,12,16], -2), ([6,13,16], -2), ([6,14,16], -2), ([6,15,16], -2), ([6,16,16], -2), ([6,16,17], -2), ([6,16,18], -2), ([6,16,19], -2), ([6,16,20], -2), ([6,16,21], -2), ([7,7,16], -1), ([7,8,16], -2), ([7,9,16], -2), ([7,10,16], -2), ([7,11,16], -2), ([7,12,16], -2), ([7,13,16], -2), ([7,14,16], -2), ([7,15,16], -2), ([7,16,16], -2), ([7,16,17], -2), ([7,16,18], -2), ([7,16,19], -2), ([7,16,20], -2), ([7,16,21], -2), ([8,8,16], -1), ([8,9,16], -2), ([8,10,16], -2), ([8,11,16], -2), ([8,12,16], -2), ([8,13,16], -2), ([8,14,16], -2), ([8,15,16], -2), ([8,16,16], -2), ([8,16,17], -2), ([8,16,18], -2), ([8,16,19], -2), ([8,16,20], -2), ([8,16,21], -2), ([9,9,16], -1), ([9,10,16], -2), ([9,11,16], -2), ([9,12,16], -2), ([9,13,16], -2), ([9,14,16], -2), ([9,15,16], -2), ([9,16,16], -2), ([9,16,17], -2), ([9,16,18], -2), ([9,16,19], -2), ([9,16,20], -2), ([9,16,21], -2), ([10,10,16], -1), ([10,11,16], -2), ([10,12,16], -2), ([10,13,16], -2), ([10,14,16], -2), ([10,15,16], -2), ([10,16,16], -2), ([10,16,17], -2), ([10,16,18], -2), ([10,16,19], -2), ([10,16,20], -2), ([10,16,21], -2), ([11,11,16], -1), ([11,12,16], -2), ([11,13,16], -2), ([11,14,16], -2), ([11,15,16], -2), ([11,16,16], -2), ([11,16,17], -2), ([11,16,18], -2), ([11,16,19], -2), ([11,16,20], -2), ([11,16,21], -2), ([12,12,16], -1), ([12,13,16], -2), ([12,14,16], -2), ([12,15,16], -2), ([12,16,16], -2), ([12,16,17], -2), ([12,16,18], -2), ([12,16,19], -2), ([12,16,20], -2), ([12,16,21], -2), ([13,13,16], -1), ([13,14,16], -2), ([13,15,16], -2), ([13,16,16], -2), ([13,16,17], -2), ([13,16,18], -2), ([13,16,19], -2), ([13,16,20], -2), ([13,16,21], -2), ([14,14,16], -1), ([14,15,16], -2), ([14,16,16], -2), ([14,16,17], -2), ([14,16,18], -2), ([14,16,19], -2), ([14,16,20], -2), ([14,16,21], -2), ([15,15,16], -1), ([15,16,16], -2), ([15,16,17], -2), ([15,16,18], -2), ([15,16,19], -2), ([15,16,20], -2), ([15,16,21], -2), ([16,16,16], -1), ([16,16,17], -2), ([16,16,18], -2), ([16,16,19], -2), ([16,16,20], -2), ([16,16,21], -2), ([16,17,17], -1), ([16,17,18], -2), ([16,17,19], -2), ([16,17,20], -2), ([16,17,21], -2), ([16,18,18], -1), ([16,18,19], -2), ([16,18,20], -2), ([16,18,21], -2), ([16,19,19], -1), ([16,19,20], -2), ([16,19,21], -2), ([16,20,20], -1), ([16,20,21], -2), ([16,20,23], 4), ([16,21,21], -1), ([16,21,23], 4), ([16,22,23], 4), ([16,23,23], 4)]
theorem atom0049_data : atom0049 = SparsePolynomial.monoTimes [16] 1 base05 := by decide +kernel
theorem eval_atom0049 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0049 = (minorB (outer g) 0 1 * g 16) := by
  rw [atom0049_data, SparsePolynomial.eval_monoTimes, eval_base05]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0049_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (39666522470400 : Int) atom0049) := by
  rw [SparsePolynomial.eval_scale, eval_atom0049]
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base05_nonneg g hg hA hB
  rw [eval_base05] at hb
  have ht : 0 ≤ (minorB (outer g) 0 1 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0050 : SparsePolynomial.Poly := [([0,0,17], -1), ([0,1,17], -2), ([0,2,17], -2), ([0,3,17], -2), ([0,4,17], -2), ([0,5,17], -2), ([0,6,17], -2), ([0,7,17], -2), ([0,8,17], -2), ([0,9,17], -2), ([0,10,17], -2), ([0,11,17], -2), ([0,12,17], -2), ([0,13,17], -2), ([0,14,17], -2), ([0,15,17], -2), ([0,16,17], -2), ([0,17,17], -2), ([0,17,18], -2), ([0,17,19], -2), ([0,17,20], -2), ([0,17,21], -2), ([1,1,17], -1), ([1,2,17], -2), ([1,3,17], -2), ([1,4,17], -2), ([1,5,17], -2), ([1,6,17], -2), ([1,7,17], -2), ([1,8,17], -2), ([1,9,17], -2), ([1,10,17], -2), ([1,11,17], -2), ([1,12,17], -2), ([1,13,17], -2), ([1,14,17], -2), ([1,15,17], -2), ([1,16,17], -2), ([1,17,17], -2), ([1,17,18], -2), ([1,17,19], -2), ([1,17,20], -2), ([1,17,21], -2), ([2,2,17], -1), ([2,3,17], -2), ([2,4,17], -2), ([2,5,17], -2), ([2,6,17], -2), ([2,7,17], -2), ([2,8,17], -2), ([2,9,17], -2), ([2,10,17], -2), ([2,11,17], -2), ([2,12,17], -2), ([2,13,17], -2), ([2,14,17], -2), ([2,15,17], -2), ([2,16,17], -2), ([2,17,17], -2), ([2,17,18], -2), ([2,17,19], -2), ([2,17,20], -2), ([2,17,21], -2), ([3,3,17], -1), ([3,4,17], -2), ([3,5,17], -2), ([3,6,17], -2), ([3,7,17], -2), ([3,8,17], -2), ([3,9,17], -2), ([3,10,17], -2), ([3,11,17], -2), ([3,12,17], -2), ([3,13,17], -2), ([3,14,17], -2), ([3,15,17], -2), ([3,16,17], -2), ([3,17,17], -2), ([3,17,18], -2), ([3,17,19], -2), ([3,17,20], -2), ([3,17,21], -2), ([4,4,17], -1), ([4,5,17], -2), ([4,6,17], -2), ([4,7,17], -2), ([4,8,17], -2), ([4,9,17], -2), ([4,10,17], -2), ([4,11,17], -2), ([4,12,17], -2), ([4,13,17], -2), ([4,14,17], -2), ([4,15,17], -2), ([4,16,17], -2), ([4,17,17], -2), ([4,17,18], -2), ([4,17,19], -2), ([4,17,20], -2), ([4,17,21], -2), ([5,5,17], -1), ([5,6,17], -2), ([5,7,17], -2), ([5,8,17], -2), ([5,9,17], -2), ([5,10,17], -2), ([5,11,17], -2), ([5,12,17], -2), ([5,13,17], -2), ([5,14,17], -2), ([5,15,17], -2), ([5,16,17], -2), ([5,17,17], -2), ([5,17,18], -2), ([5,17,19], -2), ([5,17,20], -2), ([5,17,21], -2), ([6,6,17], -1), ([6,7,17], -2), ([6,8,17], -2), ([6,9,17], -2), ([6,10,17], -2), ([6,11,17], -2), ([6,12,17], -2), ([6,13,17], -2), ([6,14,17], -2), ([6,15,17], -2), ([6,16,17], -2), ([6,17,17], -2), ([6,17,18], -2), ([6,17,19], -2), ([6,17,20], -2), ([6,17,21], -2), ([7,7,17], -1), ([7,8,17], -2), ([7,9,17], -2), ([7,10,17], -2), ([7,11,17], -2), ([7,12,17], -2), ([7,13,17], -2), ([7,14,17], -2), ([7,15,17], -2), ([7,16,17], -2), ([7,17,17], -2), ([7,17,18], -2), ([7,17,19], -2), ([7,17,20], -2), ([7,17,21], -2), ([8,8,17], -1), ([8,9,17], -2), ([8,10,17], -2), ([8,11,17], -2), ([8,12,17], -2), ([8,13,17], -2), ([8,14,17], -2), ([8,15,17], -2), ([8,16,17], -2), ([8,17,17], -2), ([8,17,18], -2), ([8,17,19], -2), ([8,17,20], -2), ([8,17,21], -2), ([9,9,17], -1), ([9,10,17], -2), ([9,11,17], -2), ([9,12,17], -2), ([9,13,17], -2), ([9,14,17], -2), ([9,15,17], -2), ([9,16,17], -2), ([9,17,17], -2), ([9,17,18], -2), ([9,17,19], -2), ([9,17,20], -2), ([9,17,21], -2), ([10,10,17], -1), ([10,11,17], -2), ([10,12,17], -2), ([10,13,17], -2), ([10,14,17], -2), ([10,15,17], -2), ([10,16,17], -2), ([10,17,17], -2), ([10,17,18], -2), ([10,17,19], -2), ([10,17,20], -2), ([10,17,21], -2), ([11,11,17], -1), ([11,12,17], -2), ([11,13,17], -2), ([11,14,17], -2), ([11,15,17], -2), ([11,16,17], -2), ([11,17,17], -2), ([11,17,18], -2), ([11,17,19], -2), ([11,17,20], -2), ([11,17,21], -2), ([12,12,17], -1), ([12,13,17], -2), ([12,14,17], -2), ([12,15,17], -2), ([12,16,17], -2), ([12,17,17], -2), ([12,17,18], -2), ([12,17,19], -2), ([12,17,20], -2), ([12,17,21], -2), ([13,13,17], -1), ([13,14,17], -2), ([13,15,17], -2), ([13,16,17], -2), ([13,17,17], -2), ([13,17,18], -2), ([13,17,19], -2), ([13,17,20], -2), ([13,17,21], -2), ([14,14,17], -1), ([14,15,17], -2), ([14,16,17], -2), ([14,17,17], -2), ([14,17,18], -2), ([14,17,19], -2), ([14,17,20], -2), ([14,17,21], -2), ([15,15,17], -1), ([15,16,17], -2), ([15,17,17], -2), ([15,17,18], -2), ([15,17,19], -2), ([15,17,20], -2), ([15,17,21], -2), ([16,16,17], -1), ([16,17,17], -2), ([16,17,18], -2), ([16,17,19], -2), ([16,17,20], -2), ([16,17,21], -2), ([17,17,17], -1), ([17,17,18], -2), ([17,17,19], -2), ([17,17,20], -2), ([17,17,21], -2), ([17,18,18], -1), ([17,18,19], -2), ([17,18,20], -2), ([17,18,21], -2), ([17,19,19], -1), ([17,19,20], -2), ([17,19,21], -2), ([17,20,20], -1), ([17,20,21], -2), ([17,20,23], 4), ([17,21,21], -1), ([17,21,23], 4), ([17,22,23], 4), ([17,23,23], 4)]
theorem atom0050_data : atom0050 = SparsePolynomial.monoTimes [17] 1 base05 := by decide +kernel
theorem eval_atom0050 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0050 = (minorB (outer g) 0 1 * g 17) := by
  rw [atom0050_data, SparsePolynomial.eval_monoTimes, eval_base05]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0050_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (40228363929600 : Int) atom0050) := by
  rw [SparsePolynomial.eval_scale, eval_atom0050]
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base05_nonneg g hg hA hB
  rw [eval_base05] at hb
  have ht : 0 ≤ (minorB (outer g) 0 1 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0051 : SparsePolynomial.Poly := [([0,0,22], -1), ([0,1,22], -2), ([0,2,22], -2), ([0,3,22], -2), ([0,4,22], -2), ([0,5,22], -2), ([0,6,22], -2), ([0,7,22], -2), ([0,8,22], -2), ([0,9,22], -2), ([0,10,22], -2), ([0,11,22], -2), ([0,12,22], -2), ([0,13,22], -2), ([0,14,22], -2), ([0,15,22], -2), ([0,16,22], -2), ([0,17,22], -2), ([0,18,22], -2), ([0,19,22], -2), ([0,20,22], -2), ([0,21,22], -2), ([1,1,22], -1), ([1,2,22], -2), ([1,3,22], -2), ([1,4,22], -2), ([1,5,22], -2), ([1,6,22], -2), ([1,7,22], -2), ([1,8,22], -2), ([1,9,22], -2), ([1,10,22], -2), ([1,11,22], -2), ([1,12,22], -2), ([1,13,22], -2), ([1,14,22], -2), ([1,15,22], -2), ([1,16,22], -2), ([1,17,22], -2), ([1,18,22], -2), ([1,19,22], -2), ([1,20,22], -2), ([1,21,22], -2), ([2,2,22], -1), ([2,3,22], -2), ([2,4,22], -2), ([2,5,22], -2), ([2,6,22], -2), ([2,7,22], -2), ([2,8,22], -2), ([2,9,22], -2), ([2,10,22], -2), ([2,11,22], -2), ([2,12,22], -2), ([2,13,22], -2), ([2,14,22], -2), ([2,15,22], -2), ([2,16,22], -2), ([2,17,22], -2), ([2,18,22], -2), ([2,19,22], -2), ([2,20,22], -2), ([2,21,22], -2), ([3,3,22], -1), ([3,4,22], -2), ([3,5,22], -2), ([3,6,22], -2), ([3,7,22], -2), ([3,8,22], -2), ([3,9,22], -2), ([3,10,22], -2), ([3,11,22], -2), ([3,12,22], -2), ([3,13,22], -2), ([3,14,22], -2), ([3,15,22], -2), ([3,16,22], -2), ([3,17,22], -2), ([3,18,22], -2), ([3,19,22], -2), ([3,20,22], -2), ([3,21,22], -2), ([4,4,22], -1), ([4,5,22], -2), ([4,6,22], -2), ([4,7,22], -2), ([4,8,22], -2), ([4,9,22], -2), ([4,10,22], -2), ([4,11,22], -2), ([4,12,22], -2), ([4,13,22], -2), ([4,14,22], -2), ([4,15,22], -2), ([4,16,22], -2), ([4,17,22], -2), ([4,18,22], -2), ([4,19,22], -2), ([4,20,22], -2), ([4,21,22], -2), ([5,5,22], -1), ([5,6,22], -2), ([5,7,22], -2), ([5,8,22], -2), ([5,9,22], -2), ([5,10,22], -2), ([5,11,22], -2), ([5,12,22], -2), ([5,13,22], -2), ([5,14,22], -2), ([5,15,22], -2), ([5,16,22], -2), ([5,17,22], -2), ([5,18,22], -2), ([5,19,22], -2), ([5,20,22], -2), ([5,21,22], -2), ([6,6,22], -1), ([6,7,22], -2), ([6,8,22], -2), ([6,9,22], -2), ([6,10,22], -2), ([6,11,22], -2), ([6,12,22], -2), ([6,13,22], -2), ([6,14,22], -2), ([6,15,22], -2), ([6,16,22], -2), ([6,17,22], -2), ([6,18,22], -2), ([6,19,22], -2), ([6,20,22], -2), ([6,21,22], -2), ([7,7,22], -1), ([7,8,22], -2), ([7,9,22], -2), ([7,10,22], -2), ([7,11,22], -2), ([7,12,22], -2), ([7,13,22], -2), ([7,14,22], -2), ([7,15,22], -2), ([7,16,22], -2), ([7,17,22], -2), ([7,18,22], -2), ([7,19,22], -2), ([7,20,22], -2), ([7,21,22], -2), ([8,8,22], -1), ([8,9,22], -2), ([8,10,22], -2), ([8,11,22], -2), ([8,12,22], -2), ([8,13,22], -2), ([8,14,22], -2), ([8,15,22], -2), ([8,16,22], -2), ([8,17,22], -2), ([8,18,22], -2), ([8,19,22], -2), ([8,20,22], -2), ([8,21,22], -2), ([9,9,22], -1), ([9,10,22], -2), ([9,11,22], -2), ([9,12,22], -2), ([9,13,22], -2), ([9,14,22], -2), ([9,15,22], -2), ([9,16,22], -2), ([9,17,22], -2), ([9,18,22], -2), ([9,19,22], -2), ([9,20,22], -2), ([9,21,22], -2), ([10,10,22], -1), ([10,11,22], -2), ([10,12,22], -2), ([10,13,22], -2), ([10,14,22], -2), ([10,15,22], -2), ([10,16,22], -2), ([10,17,22], -2), ([10,18,22], -2), ([10,19,22], -2), ([10,20,22], -2), ([10,21,22], -2), ([11,11,22], -1), ([11,12,22], -2), ([11,13,22], -2), ([11,14,22], -2), ([11,15,22], -2), ([11,16,22], -2), ([11,17,22], -2), ([11,18,22], -2), ([11,19,22], -2), ([11,20,22], -2), ([11,21,22], -2), ([12,12,22], -1), ([12,13,22], -2), ([12,14,22], -2), ([12,15,22], -2), ([12,16,22], -2), ([12,17,22], -2), ([12,18,22], -2), ([12,19,22], -2), ([12,20,22], -2), ([12,21,22], -2), ([13,13,22], -1), ([13,14,22], -2), ([13,15,22], -2), ([13,16,22], -2), ([13,17,22], -2), ([13,18,22], -2), ([13,19,22], -2), ([13,20,22], -2), ([13,21,22], -2), ([14,14,22], -1), ([14,15,22], -2), ([14,16,22], -2), ([14,17,22], -2), ([14,18,22], -2), ([14,19,22], -2), ([14,20,22], -2), ([14,21,22], -2), ([15,15,22], -1), ([15,16,22], -2), ([15,17,22], -2), ([15,18,22], -2), ([15,19,22], -2), ([15,20,22], -2), ([15,21,22], -2), ([16,16,22], -1), ([16,17,22], -2), ([16,18,22], -2), ([16,19,22], -2), ([16,20,22], -2), ([16,21,22], -2), ([17,17,22], -1), ([17,18,22], -2), ([17,19,22], -2), ([17,20,22], -2), ([17,21,22], -2), ([18,18,22], -1), ([18,19,22], -2), ([18,20,22], -2), ([18,21,22], -2), ([19,19,22], -1), ([19,20,22], -2), ([19,21,22], -2), ([20,20,22], -1), ([20,21,22], -2), ([20,22,23], 4), ([21,21,22], -1), ([21,22,23], 4), ([22,22,23], 4), ([22,23,23], 4)]
theorem atom0051_data : atom0051 = SparsePolynomial.monoTimes [22] 1 base05 := by decide +kernel
theorem eval_atom0051 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0051 = (minorB (outer g) 0 1 * g 22) := by
  rw [atom0051_data, SparsePolynomial.eval_monoTimes, eval_base05]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0051_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7675707916800 : Int) atom0051) := by
  rw [SparsePolynomial.eval_scale, eval_atom0051]
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base05_nonneg g hg hA hB
  rw [eval_base05] at hb
  have ht : 0 ≤ (minorB (outer g) 0 1 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0052 : SparsePolynomial.Poly := [([0,0,23], -2), ([0,1,23], -2), ([0,2,23], -2), ([0,3,23], -2), ([0,4,23], -2), ([0,5,23], -2), ([0,6,23], -2), ([0,7,23], -2), ([0,8,23], -2), ([0,9,23], -2), ([0,10,23], -2), ([0,11,23], -2), ([0,12,23], -2), ([0,13,23], -2), ([0,14,23], -2), ([0,15,23], -2), ([0,16,23], -2), ([0,17,23], -2), ([0,18,23], -2), ([0,19,23], -2), ([0,22,23], 2), ([0,23,23], 4)]
theorem atom0052_data : atom0052 = SparsePolynomial.monoTimes [0,23] 1 base06 := by decide +kernel
theorem eval_atom0052 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0052 = (quadB (outer g) ![1,1,0] * g 0 * g 23) := by
  rw [atom0052_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0052_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5379374246400 : Int) atom0052) := by
  rw [SparsePolynomial.eval_scale, eval_atom0052]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg23 : 0 ≤ g 23 := hg 23
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,1,0] * g 0 * g 23) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0053 : SparsePolynomial.Poly := [([0,2,22], -4), ([1,2,22], -8), ([2,2,22], -16), ([2,3,22], -16), ([2,4,22], -16), ([2,5,22], -16), ([2,6,22], -16), ([2,7,22], -16), ([2,8,22], -16), ([2,9,22], -16), ([2,10,22], -16), ([2,11,22], -16), ([2,12,22], -16), ([2,13,22], -16), ([2,14,22], -16), ([2,15,22], -16), ([2,16,22], -16), ([2,17,22], -16), ([2,18,22], -8), ([2,20,22], 8), ([2,21,22], 12), ([2,22,22], 16), ([2,22,23], 18)]
theorem atom0053_data : atom0053 = SparsePolynomial.monoTimes [2,22] 1 base07 := by decide +kernel
theorem eval_atom0053 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0053 = (quadB (outer g) ![1,2,2] * g 2 * g 22) := by
  rw [atom0053_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0053_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3650680857600 : Int) atom0053) := by
  rw [SparsePolynomial.eval_scale, eval_atom0053]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 2 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0054 : SparsePolynomial.Poly := [([0,3,19], -4), ([1,3,19], -8), ([2,3,19], -16), ([3,3,19], -16), ([3,4,19], -16), ([3,5,19], -16), ([3,6,19], -16), ([3,7,19], -16), ([3,8,19], -16), ([3,9,19], -16), ([3,10,19], -16), ([3,11,19], -16), ([3,12,19], -16), ([3,13,19], -16), ([3,14,19], -16), ([3,15,19], -16), ([3,16,19], -16), ([3,17,19], -16), ([3,18,19], -8), ([3,19,20], 8), ([3,19,21], 12), ([3,19,22], 16), ([3,19,23], 18)]
theorem atom0054_data : atom0054 = SparsePolynomial.monoTimes [3,19] 1 base07 := by decide +kernel
theorem eval_atom0054 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0054 = (quadB (outer g) ![1,2,2] * g 3 * g 19) := by
  rw [atom0054_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0054_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1743512601600 : Int) atom0054) := by
  rw [SparsePolynomial.eval_scale, eval_atom0054]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg19 : 0 ≤ g 19 := hg 19
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 3 * g 19) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0055 : SparsePolynomial.Poly := [([0,3,21], -4), ([1,3,21], -8), ([2,3,21], -16), ([3,3,21], -16), ([3,4,21], -16), ([3,5,21], -16), ([3,6,21], -16), ([3,7,21], -16), ([3,8,21], -16), ([3,9,21], -16), ([3,10,21], -16), ([3,11,21], -16), ([3,12,21], -16), ([3,13,21], -16), ([3,14,21], -16), ([3,15,21], -16), ([3,16,21], -16), ([3,17,21], -16), ([3,18,21], -8), ([3,20,21], 8), ([3,21,21], 12), ([3,21,22], 16), ([3,21,23], 18)]
theorem atom0055_data : atom0055 = SparsePolynomial.monoTimes [3,21] 1 base07 := by decide +kernel
theorem eval_atom0055 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0055 = (quadB (outer g) ![1,2,2] * g 3 * g 21) := by
  rw [atom0055_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0055_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2519588332800 : Int) atom0055) := by
  rw [SparsePolynomial.eval_scale, eval_atom0055]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg21 : 0 ≤ g 21 := hg 21
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 3 * g 21) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0056 : SparsePolynomial.Poly := [([0,3,22], -4), ([1,3,22], -8), ([2,3,22], -16), ([3,3,22], -16), ([3,4,22], -16), ([3,5,22], -16), ([3,6,22], -16), ([3,7,22], -16), ([3,8,22], -16), ([3,9,22], -16), ([3,10,22], -16), ([3,11,22], -16), ([3,12,22], -16), ([3,13,22], -16), ([3,14,22], -16), ([3,15,22], -16), ([3,16,22], -16), ([3,17,22], -16), ([3,18,22], -8), ([3,20,22], 8), ([3,21,22], 12), ([3,22,22], 16), ([3,22,23], 18)]
theorem atom0056_data : atom0056 = SparsePolynomial.monoTimes [3,22] 1 base07 := by decide +kernel
theorem eval_atom0056 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0056 = (quadB (outer g) ![1,2,2] * g 3 * g 22) := by
  rw [atom0056_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0056_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3501643068000 : Int) atom0056) := by
  rw [SparsePolynomial.eval_scale, eval_atom0056]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 3 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0057 : SparsePolynomial.Poly := [([0,3,23], -4), ([1,3,23], -8), ([2,3,23], -16), ([3,3,23], -16), ([3,4,23], -16), ([3,5,23], -16), ([3,6,23], -16), ([3,7,23], -16), ([3,8,23], -16), ([3,9,23], -16), ([3,10,23], -16), ([3,11,23], -16), ([3,12,23], -16), ([3,13,23], -16), ([3,14,23], -16), ([3,15,23], -16), ([3,16,23], -16), ([3,17,23], -16), ([3,18,23], -8), ([3,20,23], 8), ([3,21,23], 12), ([3,22,23], 16), ([3,23,23], 18)]
theorem atom0057_data : atom0057 = SparsePolynomial.monoTimes [3,23] 1 base07 := by decide +kernel
theorem eval_atom0057 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0057 = (quadB (outer g) ![1,2,2] * g 3 * g 23) := by
  rw [atom0057_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0057_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3295664064000 : Int) atom0057) := by
  rw [SparsePolynomial.eval_scale, eval_atom0057]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg23 : 0 ≤ g 23 := hg 23
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 3 * g 23) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0058 : SparsePolynomial.Poly := [([0,4,5], -4), ([1,4,5], -8), ([2,4,5], -16), ([3,4,5], -16), ([4,4,5], -16), ([4,5,5], -16), ([4,5,6], -16), ([4,5,7], -16), ([4,5,8], -16), ([4,5,9], -16), ([4,5,10], -16), ([4,5,11], -16), ([4,5,12], -16), ([4,5,13], -16), ([4,5,14], -16), ([4,5,15], -16), ([4,5,16], -16), ([4,5,17], -16), ([4,5,18], -8), ([4,5,20], 8), ([4,5,21], 12), ([4,5,22], 16), ([4,5,23], 18)]
theorem atom0058_data : atom0058 = SparsePolynomial.monoTimes [4,5] 1 base07 := by decide +kernel
theorem eval_atom0058 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0058 = (quadB (outer g) ![1,2,2] * g 4 * g 5) := by
  rw [atom0058_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0058_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (547889680206 : Int) atom0058) := by
  rw [SparsePolynomial.eval_scale, eval_atom0058]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 5) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0059 : SparsePolynomial.Poly := [([0,4,17], -4), ([1,4,17], -8), ([2,4,17], -16), ([3,4,17], -16), ([4,4,17], -16), ([4,5,17], -16), ([4,6,17], -16), ([4,7,17], -16), ([4,8,17], -16), ([4,9,17], -16), ([4,10,17], -16), ([4,11,17], -16), ([4,12,17], -16), ([4,13,17], -16), ([4,14,17], -16), ([4,15,17], -16), ([4,16,17], -16), ([4,17,17], -16), ([4,17,18], -8), ([4,17,20], 8), ([4,17,21], 12), ([4,17,22], 16), ([4,17,23], 18)]
theorem atom0059_data : atom0059 = SparsePolynomial.monoTimes [4,17] 1 base07 := by decide +kernel
theorem eval_atom0059 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0059 = (quadB (outer g) ![1,2,2] * g 4 * g 17) := by
  rw [atom0059_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0059_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (290464624800 : Int) atom0059) := by
  rw [SparsePolynomial.eval_scale, eval_atom0059]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0060 : SparsePolynomial.Poly := [([0,4,19], -4), ([1,4,19], -8), ([2,4,19], -16), ([3,4,19], -16), ([4,4,19], -16), ([4,5,19], -16), ([4,6,19], -16), ([4,7,19], -16), ([4,8,19], -16), ([4,9,19], -16), ([4,10,19], -16), ([4,11,19], -16), ([4,12,19], -16), ([4,13,19], -16), ([4,14,19], -16), ([4,15,19], -16), ([4,16,19], -16), ([4,17,19], -16), ([4,18,19], -8), ([4,19,20], 8), ([4,19,21], 12), ([4,19,22], 16), ([4,19,23], 18)]
theorem atom0060_data : atom0060 = SparsePolynomial.monoTimes [4,19] 1 base07 := by decide +kernel
theorem eval_atom0060 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0060 = (quadB (outer g) ![1,2,2] * g 4 * g 19) := by
  rw [atom0060_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0060_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3861255629700 : Int) atom0060) := by
  rw [SparsePolynomial.eval_scale, eval_atom0060]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg19 : 0 ≤ g 19 := hg 19
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 19) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0061 : SparsePolynomial.Poly := [([0,4,20], -4), ([1,4,20], -8), ([2,4,20], -16), ([3,4,20], -16), ([4,4,20], -16), ([4,5,20], -16), ([4,6,20], -16), ([4,7,20], -16), ([4,8,20], -16), ([4,9,20], -16), ([4,10,20], -16), ([4,11,20], -16), ([4,12,20], -16), ([4,13,20], -16), ([4,14,20], -16), ([4,15,20], -16), ([4,16,20], -16), ([4,17,20], -16), ([4,18,20], -8), ([4,20,20], 8), ([4,20,21], 12), ([4,20,22], 16), ([4,20,23], 18)]
theorem atom0061_data : atom0061 = SparsePolynomial.monoTimes [4,20] 1 base07 := by decide +kernel
theorem eval_atom0061 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0061 = (quadB (outer g) ![1,2,2] * g 4 * g 20) := by
  rw [atom0061_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0061_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (55768362300 : Int) atom0061) := by
  rw [SparsePolynomial.eval_scale, eval_atom0061]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg20 : 0 ≤ g 20 := hg 20
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 20) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0062 : SparsePolynomial.Poly := [([0,4,21], -4), ([1,4,21], -8), ([2,4,21], -16), ([3,4,21], -16), ([4,4,21], -16), ([4,5,21], -16), ([4,6,21], -16), ([4,7,21], -16), ([4,8,21], -16), ([4,9,21], -16), ([4,10,21], -16), ([4,11,21], -16), ([4,12,21], -16), ([4,13,21], -16), ([4,14,21], -16), ([4,15,21], -16), ([4,16,21], -16), ([4,17,21], -16), ([4,18,21], -8), ([4,20,21], 8), ([4,21,21], 12), ([4,21,22], 16), ([4,21,23], 18)]
theorem atom0062_data : atom0062 = SparsePolynomial.monoTimes [4,21] 1 base07 := by decide +kernel
theorem eval_atom0062 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0062 = (quadB (outer g) ![1,2,2] * g 4 * g 21) := by
  rw [atom0062_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0062_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5323132716300 : Int) atom0062) := by
  rw [SparsePolynomial.eval_scale, eval_atom0062]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg21 : 0 ≤ g 21 := hg 21
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 21) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0063 : SparsePolynomial.Poly := [([0,4,22], -4), ([1,4,22], -8), ([2,4,22], -16), ([3,4,22], -16), ([4,4,22], -16), ([4,5,22], -16), ([4,6,22], -16), ([4,7,22], -16), ([4,8,22], -16), ([4,9,22], -16), ([4,10,22], -16), ([4,11,22], -16), ([4,12,22], -16), ([4,13,22], -16), ([4,14,22], -16), ([4,15,22], -16), ([4,16,22], -16), ([4,17,22], -16), ([4,18,22], -8), ([4,20,22], 8), ([4,21,22], 12), ([4,22,22], 16), ([4,22,23], 18)]
theorem atom0063_data : atom0063 = SparsePolynomial.monoTimes [4,22] 1 base07 := by decide +kernel
theorem eval_atom0063 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0063 = (quadB (outer g) ![1,2,2] * g 4 * g 22) := by
  rw [atom0063_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0063_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1700123785500 : Int) atom0063) := by
  rw [SparsePolynomial.eval_scale, eval_atom0063]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0064 : SparsePolynomial.Poly := [([0,4,23], -4), ([1,4,23], -8), ([2,4,23], -16), ([3,4,23], -16), ([4,4,23], -16), ([4,5,23], -16), ([4,6,23], -16), ([4,7,23], -16), ([4,8,23], -16), ([4,9,23], -16), ([4,10,23], -16), ([4,11,23], -16), ([4,12,23], -16), ([4,13,23], -16), ([4,14,23], -16), ([4,15,23], -16), ([4,16,23], -16), ([4,17,23], -16), ([4,18,23], -8), ([4,20,23], 8), ([4,21,23], 12), ([4,22,23], 16), ([4,23,23], 18)]
theorem atom0064_data : atom0064 = SparsePolynomial.monoTimes [4,23] 1 base07 := by decide +kernel
theorem eval_atom0064 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0064 = (quadB (outer g) ![1,2,2] * g 4 * g 23) := by
  rw [atom0064_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0064_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7055249021100 : Int) atom0064) := by
  rw [SparsePolynomial.eval_scale, eval_atom0064]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg23 : 0 ≤ g 23 := hg 23
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 23) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0065 : SparsePolynomial.Poly := [([0,5,6], -4), ([1,5,6], -8), ([2,5,6], -16), ([3,5,6], -16), ([4,5,6], -16), ([5,5,6], -16), ([5,6,6], -16), ([5,6,7], -16), ([5,6,8], -16), ([5,6,9], -16), ([5,6,10], -16), ([5,6,11], -16), ([5,6,12], -16), ([5,6,13], -16), ([5,6,14], -16), ([5,6,15], -16), ([5,6,16], -16), ([5,6,17], -16), ([5,6,18], -8), ([5,6,20], 8), ([5,6,21], 12), ([5,6,22], 16), ([5,6,23], 18)]
theorem atom0065_data : atom0065 = SparsePolynomial.monoTimes [5,6] 1 base07 := by decide +kernel
theorem eval_atom0065 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0065 = (quadB (outer g) ![1,2,2] * g 5 * g 6) := by
  rw [atom0065_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0065_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3274785913806 : Int) atom0065) := by
  rw [SparsePolynomial.eval_scale, eval_atom0065]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 6) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0066 : SparsePolynomial.Poly := [([0,5,7], -4), ([1,5,7], -8), ([2,5,7], -16), ([3,5,7], -16), ([4,5,7], -16), ([5,5,7], -16), ([5,6,7], -16), ([5,7,7], -16), ([5,7,8], -16), ([5,7,9], -16), ([5,7,10], -16), ([5,7,11], -16), ([5,7,12], -16), ([5,7,13], -16), ([5,7,14], -16), ([5,7,15], -16), ([5,7,16], -16), ([5,7,17], -16), ([5,7,18], -8), ([5,7,20], 8), ([5,7,21], 12), ([5,7,22], 16), ([5,7,23], 18)]
theorem atom0066_data : atom0066 = SparsePolynomial.monoTimes [5,7] 1 base07 := by decide +kernel
theorem eval_atom0066 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0066 = (quadB (outer g) ![1,2,2] * g 5 * g 7) := by
  rw [atom0066_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0066_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1931861869806 : Int) atom0066) := by
  rw [SparsePolynomial.eval_scale, eval_atom0066]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0067 : SparsePolynomial.Poly := [([0,5,8], -4), ([1,5,8], -8), ([2,5,8], -16), ([3,5,8], -16), ([4,5,8], -16), ([5,5,8], -16), ([5,6,8], -16), ([5,7,8], -16), ([5,8,8], -16), ([5,8,9], -16), ([5,8,10], -16), ([5,8,11], -16), ([5,8,12], -16), ([5,8,13], -16), ([5,8,14], -16), ([5,8,15], -16), ([5,8,16], -16), ([5,8,17], -16), ([5,8,18], -8), ([5,8,20], 8), ([5,8,21], 12), ([5,8,22], 16), ([5,8,23], 18)]
theorem atom0067_data : atom0067 = SparsePolynomial.monoTimes [5,8] 1 base07 := by decide +kernel
theorem eval_atom0067 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0067 = (quadB (outer g) ![1,2,2] * g 5 * g 8) := by
  rw [atom0067_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0067_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2123956296594 : Int) atom0067) := by
  rw [SparsePolynomial.eval_scale, eval_atom0067]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0068 : SparsePolynomial.Poly := [([0,5,9], -4), ([1,5,9], -8), ([2,5,9], -16), ([3,5,9], -16), ([4,5,9], -16), ([5,5,9], -16), ([5,6,9], -16), ([5,7,9], -16), ([5,8,9], -16), ([5,9,9], -16), ([5,9,10], -16), ([5,9,11], -16), ([5,9,12], -16), ([5,9,13], -16), ([5,9,14], -16), ([5,9,15], -16), ([5,9,16], -16), ([5,9,17], -16), ([5,9,18], -8), ([5,9,20], 8), ([5,9,21], 12), ([5,9,22], 16), ([5,9,23], 18)]
theorem atom0068_data : atom0068 = SparsePolynomial.monoTimes [5,9] 1 base07 := by decide +kernel
theorem eval_atom0068 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0068 = (quadB (outer g) ![1,2,2] * g 5 * g 9) := by
  rw [atom0068_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0068_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1897056422811 : Int) atom0068) := by
  rw [SparsePolynomial.eval_scale, eval_atom0068]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0069 : SparsePolynomial.Poly := [([0,5,10], -4), ([1,5,10], -8), ([2,5,10], -16), ([3,5,10], -16), ([4,5,10], -16), ([5,5,10], -16), ([5,6,10], -16), ([5,7,10], -16), ([5,8,10], -16), ([5,9,10], -16), ([5,10,10], -16), ([5,10,11], -16), ([5,10,12], -16), ([5,10,13], -16), ([5,10,14], -16), ([5,10,15], -16), ([5,10,16], -16), ([5,10,17], -16), ([5,10,18], -8), ([5,10,20], 8), ([5,10,21], 12), ([5,10,22], 16), ([5,10,23], 18)]
theorem atom0069_data : atom0069 = SparsePolynomial.monoTimes [5,10] 1 base07 := by decide +kernel
theorem eval_atom0069 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0069 = (quadB (outer g) ![1,2,2] * g 5 * g 10) := by
  rw [atom0069_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0069_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (635819928777 : Int) atom0069) := by
  rw [SparsePolynomial.eval_scale, eval_atom0069]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0070 : SparsePolynomial.Poly := [([0,5,15], -4), ([1,5,15], -8), ([2,5,15], -16), ([3,5,15], -16), ([4,5,15], -16), ([5,5,15], -16), ([5,6,15], -16), ([5,7,15], -16), ([5,8,15], -16), ([5,9,15], -16), ([5,10,15], -16), ([5,11,15], -16), ([5,12,15], -16), ([5,13,15], -16), ([5,14,15], -16), ([5,15,15], -16), ([5,15,16], -16), ([5,15,17], -16), ([5,15,18], -8), ([5,15,20], 8), ([5,15,21], 12), ([5,15,22], 16), ([5,15,23], 18)]
theorem atom0070_data : atom0070 = SparsePolynomial.monoTimes [5,15] 1 base07 := by decide +kernel
theorem eval_atom0070 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0070 = (quadB (outer g) ![1,2,2] * g 5 * g 15) := by
  rw [atom0070_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0070_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (46108692000 : Int) atom0070) := by
  rw [SparsePolynomial.eval_scale, eval_atom0070]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0071 : SparsePolynomial.Poly := [([0,5,16], -4), ([1,5,16], -8), ([2,5,16], -16), ([3,5,16], -16), ([4,5,16], -16), ([5,5,16], -16), ([5,6,16], -16), ([5,7,16], -16), ([5,8,16], -16), ([5,9,16], -16), ([5,10,16], -16), ([5,11,16], -16), ([5,12,16], -16), ([5,13,16], -16), ([5,14,16], -16), ([5,15,16], -16), ([5,16,16], -16), ([5,16,17], -16), ([5,16,18], -8), ([5,16,20], 8), ([5,16,21], 12), ([5,16,22], 16), ([5,16,23], 18)]
theorem atom0071_data : atom0071 = SparsePolynomial.monoTimes [5,16] 1 base07 := by decide +kernel
theorem eval_atom0071 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0071 = (quadB (outer g) ![1,2,2] * g 5 * g 16) := by
  rw [atom0071_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0071_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (831124274400 : Int) atom0071) := by
  rw [SparsePolynomial.eval_scale, eval_atom0071]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0072 : SparsePolynomial.Poly := [([0,5,17], -4), ([1,5,17], -8), ([2,5,17], -16), ([3,5,17], -16), ([4,5,17], -16), ([5,5,17], -16), ([5,6,17], -16), ([5,7,17], -16), ([5,8,17], -16), ([5,9,17], -16), ([5,10,17], -16), ([5,11,17], -16), ([5,12,17], -16), ([5,13,17], -16), ([5,14,17], -16), ([5,15,17], -16), ([5,16,17], -16), ([5,17,17], -16), ([5,17,18], -8), ([5,17,20], 8), ([5,17,21], 12), ([5,17,22], 16), ([5,17,23], 18)]
theorem atom0072_data : atom0072 = SparsePolynomial.monoTimes [5,17] 1 base07 := by decide +kernel
theorem eval_atom0072 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0072 = (quadB (outer g) ![1,2,2] * g 5 * g 17) := by
  rw [atom0072_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0072_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (995343703200 : Int) atom0072) := by
  rw [SparsePolynomial.eval_scale, eval_atom0072]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0073 : SparsePolynomial.Poly := [([0,5,19], -4), ([1,5,19], -8), ([2,5,19], -16), ([3,5,19], -16), ([4,5,19], -16), ([5,5,19], -16), ([5,6,19], -16), ([5,7,19], -16), ([5,8,19], -16), ([5,9,19], -16), ([5,10,19], -16), ([5,11,19], -16), ([5,12,19], -16), ([5,13,19], -16), ([5,14,19], -16), ([5,15,19], -16), ([5,16,19], -16), ([5,17,19], -16), ([5,18,19], -8), ([5,19,20], 8), ([5,19,21], 12), ([5,19,22], 16), ([5,19,23], 18)]
theorem atom0073_data : atom0073 = SparsePolynomial.monoTimes [5,19] 1 base07 := by decide +kernel
theorem eval_atom0073 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0073 = (quadB (outer g) ![1,2,2] * g 5 * g 19) := by
  rw [atom0073_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0073_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4727338308000 : Int) atom0073) := by
  rw [SparsePolynomial.eval_scale, eval_atom0073]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg19 : 0 ≤ g 19 := hg 19
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 19) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0074 : SparsePolynomial.Poly := [([0,5,20], -4), ([1,5,20], -8), ([2,5,20], -16), ([3,5,20], -16), ([4,5,20], -16), ([5,5,20], -16), ([5,6,20], -16), ([5,7,20], -16), ([5,8,20], -16), ([5,9,20], -16), ([5,10,20], -16), ([5,11,20], -16), ([5,12,20], -16), ([5,13,20], -16), ([5,14,20], -16), ([5,15,20], -16), ([5,16,20], -16), ([5,17,20], -16), ([5,18,20], -8), ([5,20,20], 8), ([5,20,21], 12), ([5,20,22], 16), ([5,20,23], 18)]
theorem atom0074_data : atom0074 = SparsePolynomial.monoTimes [5,20] 1 base07 := by decide +kernel
theorem eval_atom0074 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0074 = (quadB (outer g) ![1,2,2] * g 5 * g 20) := by
  rw [atom0074_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0074_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1071401839200 : Int) atom0074) := by
  rw [SparsePolynomial.eval_scale, eval_atom0074]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 20) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0075 : SparsePolynomial.Poly := [([0,5,21], -4), ([1,5,21], -8), ([2,5,21], -16), ([3,5,21], -16), ([4,5,21], -16), ([5,5,21], -16), ([5,6,21], -16), ([5,7,21], -16), ([5,8,21], -16), ([5,9,21], -16), ([5,10,21], -16), ([5,11,21], -16), ([5,12,21], -16), ([5,13,21], -16), ([5,14,21], -16), ([5,15,21], -16), ([5,16,21], -16), ([5,17,21], -16), ([5,18,21], -8), ([5,20,21], 8), ([5,21,21], 12), ([5,21,22], 16), ([5,21,23], 18)]
theorem atom0075_data : atom0075 = SparsePolynomial.monoTimes [5,21] 1 base07 := by decide +kernel
theorem eval_atom0075 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0075 = (quadB (outer g) ![1,2,2] * g 5 * g 21) := by
  rw [atom0075_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0075_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6764112986400 : Int) atom0075) := by
  rw [SparsePolynomial.eval_scale, eval_atom0075]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg21 : 0 ≤ g 21 := hg 21
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 21) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0076 : SparsePolynomial.Poly := [([0,5,22], -4), ([1,5,22], -8), ([2,5,22], -16), ([3,5,22], -16), ([4,5,22], -16), ([5,5,22], -16), ([5,6,22], -16), ([5,7,22], -16), ([5,8,22], -16), ([5,9,22], -16), ([5,10,22], -16), ([5,11,22], -16), ([5,12,22], -16), ([5,13,22], -16), ([5,14,22], -16), ([5,15,22], -16), ([5,16,22], -16), ([5,17,22], -16), ([5,18,22], -8), ([5,20,22], 8), ([5,21,22], 12), ([5,22,22], 16), ([5,22,23], 18)]
theorem atom0076_data : atom0076 = SparsePolynomial.monoTimes [5,22] 1 base07 := by decide +kernel
theorem eval_atom0076 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0076 = (quadB (outer g) ![1,2,2] * g 5 * g 22) := by
  rw [atom0076_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0076_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (823397652000 : Int) atom0076) := by
  rw [SparsePolynomial.eval_scale, eval_atom0076]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0077 : SparsePolynomial.Poly := [([0,5,23], -4), ([1,5,23], -8), ([2,5,23], -16), ([3,5,23], -16), ([4,5,23], -16), ([5,5,23], -16), ([5,6,23], -16), ([5,7,23], -16), ([5,8,23], -16), ([5,9,23], -16), ([5,10,23], -16), ([5,11,23], -16), ([5,12,23], -16), ([5,13,23], -16), ([5,14,23], -16), ([5,15,23], -16), ([5,16,23], -16), ([5,17,23], -16), ([5,18,23], -8), ([5,20,23], 8), ([5,21,23], 12), ([5,22,23], 16), ([5,23,23], 18)]
theorem atom0077_data : atom0077 = SparsePolynomial.monoTimes [5,23] 1 base07 := by decide +kernel
theorem eval_atom0077 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0077 = (quadB (outer g) ![1,2,2] * g 5 * g 23) := by
  rw [atom0077_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0077_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (198278085600 : Int) atom0077) := by
  rw [SparsePolynomial.eval_scale, eval_atom0077]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg23 : 0 ≤ g 23 := hg 23
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 23) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0078 : SparsePolynomial.Poly := [([0,6,7], -4), ([1,6,7], -8), ([2,6,7], -16), ([3,6,7], -16), ([4,6,7], -16), ([5,6,7], -16), ([6,6,7], -16), ([6,7,7], -16), ([6,7,8], -16), ([6,7,9], -16), ([6,7,10], -16), ([6,7,11], -16), ([6,7,12], -16), ([6,7,13], -16), ([6,7,14], -16), ([6,7,15], -16), ([6,7,16], -16), ([6,7,17], -16), ([6,7,18], -8), ([6,7,20], 8), ([6,7,21], 12), ([6,7,22], 16), ([6,7,23], 18)]
theorem atom0078_data : atom0078 = SparsePolynomial.monoTimes [6,7] 1 base07 := by decide +kernel
theorem eval_atom0078 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0078 = (quadB (outer g) ![1,2,2] * g 6 * g 7) := by
  rw [atom0078_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0078_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3661110684000 : Int) atom0078) := by
  rw [SparsePolynomial.eval_scale, eval_atom0078]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0079 : SparsePolynomial.Poly := [([0,6,8], -4), ([1,6,8], -8), ([2,6,8], -16), ([3,6,8], -16), ([4,6,8], -16), ([5,6,8], -16), ([6,6,8], -16), ([6,7,8], -16), ([6,8,8], -16), ([6,8,9], -16), ([6,8,10], -16), ([6,8,11], -16), ([6,8,12], -16), ([6,8,13], -16), ([6,8,14], -16), ([6,8,15], -16), ([6,8,16], -16), ([6,8,17], -16), ([6,8,18], -8), ([6,8,20], 8), ([6,8,21], 12), ([6,8,22], 16), ([6,8,23], 18)]
theorem atom0079_data : atom0079 = SparsePolynomial.monoTimes [6,8] 1 base07 := by decide +kernel
theorem eval_atom0079 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0079 = (quadB (outer g) ![1,2,2] * g 6 * g 8) := by
  rw [atom0079_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0079_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5206617662400 : Int) atom0079) := by
  rw [SparsePolynomial.eval_scale, eval_atom0079]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0080 : SparsePolynomial.Poly := [([0,6,9], -4), ([1,6,9], -8), ([2,6,9], -16), ([3,6,9], -16), ([4,6,9], -16), ([5,6,9], -16), ([6,6,9], -16), ([6,7,9], -16), ([6,8,9], -16), ([6,9,9], -16), ([6,9,10], -16), ([6,9,11], -16), ([6,9,12], -16), ([6,9,13], -16), ([6,9,14], -16), ([6,9,15], -16), ([6,9,16], -16), ([6,9,17], -16), ([6,9,18], -8), ([6,9,20], 8), ([6,9,21], 12), ([6,9,22], 16), ([6,9,23], 18)]
theorem atom0080_data : atom0080 = SparsePolynomial.monoTimes [6,9] 1 base07 := by decide +kernel
theorem eval_atom0080 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0080 = (quadB (outer g) ![1,2,2] * g 6 * g 9) := by
  rw [atom0080_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0080_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4697991667017 : Int) atom0080) := by
  rw [SparsePolynomial.eval_scale, eval_atom0080]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0081 : SparsePolynomial.Poly := [([0,6,10], -4), ([1,6,10], -8), ([2,6,10], -16), ([3,6,10], -16), ([4,6,10], -16), ([5,6,10], -16), ([6,6,10], -16), ([6,7,10], -16), ([6,8,10], -16), ([6,9,10], -16), ([6,10,10], -16), ([6,10,11], -16), ([6,10,12], -16), ([6,10,13], -16), ([6,10,14], -16), ([6,10,15], -16), ([6,10,16], -16), ([6,10,17], -16), ([6,10,18], -8), ([6,10,20], 8), ([6,10,21], 12), ([6,10,22], 16), ([6,10,23], 18)]
theorem atom0081_data : atom0081 = SparsePolynomial.monoTimes [6,10] 1 base07 := by decide +kernel
theorem eval_atom0081 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0081 = (quadB (outer g) ![1,2,2] * g 6 * g 10) := by
  rw [atom0081_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0081_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3769737793371 : Int) atom0081) := by
  rw [SparsePolynomial.eval_scale, eval_atom0081]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0082 : SparsePolynomial.Poly := [([0,6,11], -4), ([1,6,11], -8), ([2,6,11], -16), ([3,6,11], -16), ([4,6,11], -16), ([5,6,11], -16), ([6,6,11], -16), ([6,7,11], -16), ([6,8,11], -16), ([6,9,11], -16), ([6,10,11], -16), ([6,11,11], -16), ([6,11,12], -16), ([6,11,13], -16), ([6,11,14], -16), ([6,11,15], -16), ([6,11,16], -16), ([6,11,17], -16), ([6,11,18], -8), ([6,11,20], 8), ([6,11,21], 12), ([6,11,22], 16), ([6,11,23], 18)]
theorem atom0082_data : atom0082 = SparsePolynomial.monoTimes [6,11] 1 base07 := by decide +kernel
theorem eval_atom0082 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0082 = (quadB (outer g) ![1,2,2] * g 6 * g 11) := by
  rw [atom0082_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0082_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2420870759406 : Int) atom0082) := by
  rw [SparsePolynomial.eval_scale, eval_atom0082]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0083 : SparsePolynomial.Poly := [([0,6,12], -4), ([1,6,12], -8), ([2,6,12], -16), ([3,6,12], -16), ([4,6,12], -16), ([5,6,12], -16), ([6,6,12], -16), ([6,7,12], -16), ([6,8,12], -16), ([6,9,12], -16), ([6,10,12], -16), ([6,11,12], -16), ([6,12,12], -16), ([6,12,13], -16), ([6,12,14], -16), ([6,12,15], -16), ([6,12,16], -16), ([6,12,17], -16), ([6,12,18], -8), ([6,12,20], 8), ([6,12,21], 12), ([6,12,22], 16), ([6,12,23], 18)]
theorem atom0083_data : atom0083 = SparsePolynomial.monoTimes [6,12] 1 base07 := by decide +kernel
theorem eval_atom0083 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0083 = (quadB (outer g) ![1,2,2] * g 6 * g 12) := by
  rw [atom0083_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0083_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (556146158436 : Int) atom0083) := by
  rw [SparsePolynomial.eval_scale, eval_atom0083]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0084 : SparsePolynomial.Poly := [([0,6,13], -4), ([1,6,13], -8), ([2,6,13], -16), ([3,6,13], -16), ([4,6,13], -16), ([5,6,13], -16), ([6,6,13], -16), ([6,7,13], -16), ([6,8,13], -16), ([6,9,13], -16), ([6,10,13], -16), ([6,11,13], -16), ([6,12,13], -16), ([6,13,13], -16), ([6,13,14], -16), ([6,13,15], -16), ([6,13,16], -16), ([6,13,17], -16), ([6,13,18], -8), ([6,13,20], 8), ([6,13,21], 12), ([6,13,22], 16), ([6,13,23], 18)]
theorem atom0084_data : atom0084 = SparsePolynomial.monoTimes [6,13] 1 base07 := by decide +kernel
theorem eval_atom0084 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0084 = (quadB (outer g) ![1,2,2] * g 6 * g 13) := by
  rw [atom0084_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0084_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1106769094200 : Int) atom0084) := by
  rw [SparsePolynomial.eval_scale, eval_atom0084]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0085 : SparsePolynomial.Poly := [([0,6,14], -4), ([1,6,14], -8), ([2,6,14], -16), ([3,6,14], -16), ([4,6,14], -16), ([5,6,14], -16), ([6,6,14], -16), ([6,7,14], -16), ([6,8,14], -16), ([6,9,14], -16), ([6,10,14], -16), ([6,11,14], -16), ([6,12,14], -16), ([6,13,14], -16), ([6,14,14], -16), ([6,14,15], -16), ([6,14,16], -16), ([6,14,17], -16), ([6,14,18], -8), ([6,14,20], 8), ([6,14,21], 12), ([6,14,22], 16), ([6,14,23], 18)]
theorem atom0085_data : atom0085 = SparsePolynomial.monoTimes [6,14] 1 base07 := by decide +kernel
theorem eval_atom0085 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0085 = (quadB (outer g) ![1,2,2] * g 6 * g 14) := by
  rw [atom0085_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0085_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1887033456000 : Int) atom0085) := by
  rw [SparsePolynomial.eval_scale, eval_atom0085]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0086 : SparsePolynomial.Poly := [([0,6,15], -4), ([1,6,15], -8), ([2,6,15], -16), ([3,6,15], -16), ([4,6,15], -16), ([5,6,15], -16), ([6,6,15], -16), ([6,7,15], -16), ([6,8,15], -16), ([6,9,15], -16), ([6,10,15], -16), ([6,11,15], -16), ([6,12,15], -16), ([6,13,15], -16), ([6,14,15], -16), ([6,15,15], -16), ([6,15,16], -16), ([6,15,17], -16), ([6,15,18], -8), ([6,15,20], 8), ([6,15,21], 12), ([6,15,22], 16), ([6,15,23], 18)]
theorem atom0086_data : atom0086 = SparsePolynomial.monoTimes [6,15] 1 base07 := by decide +kernel
theorem eval_atom0086 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0086 = (quadB (outer g) ![1,2,2] * g 6 * g 15) := by
  rw [atom0086_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0086_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1743109905600 : Int) atom0086) := by
  rw [SparsePolynomial.eval_scale, eval_atom0086]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0087 : SparsePolynomial.Poly := [([0,6,16], -4), ([1,6,16], -8), ([2,6,16], -16), ([3,6,16], -16), ([4,6,16], -16), ([5,6,16], -16), ([6,6,16], -16), ([6,7,16], -16), ([6,8,16], -16), ([6,9,16], -16), ([6,10,16], -16), ([6,11,16], -16), ([6,12,16], -16), ([6,13,16], -16), ([6,14,16], -16), ([6,15,16], -16), ([6,16,16], -16), ([6,16,17], -16), ([6,16,18], -8), ([6,16,20], 8), ([6,16,21], 12), ([6,16,22], 16), ([6,16,23], 18)]
theorem atom0087_data : atom0087 = SparsePolynomial.monoTimes [6,16] 1 base07 := by decide +kernel
theorem eval_atom0087 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0087 = (quadB (outer g) ![1,2,2] * g 6 * g 16) := by
  rw [atom0087_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0087_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2338093245600 : Int) atom0087) := by
  rw [SparsePolynomial.eval_scale, eval_atom0087]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0088 : SparsePolynomial.Poly := [([0,6,17], -4), ([1,6,17], -8), ([2,6,17], -16), ([3,6,17], -16), ([4,6,17], -16), ([5,6,17], -16), ([6,6,17], -16), ([6,7,17], -16), ([6,8,17], -16), ([6,9,17], -16), ([6,10,17], -16), ([6,11,17], -16), ([6,12,17], -16), ([6,13,17], -16), ([6,14,17], -16), ([6,15,17], -16), ([6,16,17], -16), ([6,17,17], -16), ([6,17,18], -8), ([6,17,20], 8), ([6,17,21], 12), ([6,17,22], 16), ([6,17,23], 18)]
theorem atom0088_data : atom0088 = SparsePolynomial.monoTimes [6,17] 1 base07 := by decide +kernel
theorem eval_atom0088 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0088 = (quadB (outer g) ![1,2,2] * g 6 * g 17) := by
  rw [atom0088_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0088_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2312280432000 : Int) atom0088) := by
  rw [SparsePolynomial.eval_scale, eval_atom0088]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0089 : SparsePolynomial.Poly := [([0,6,18], -4), ([1,6,18], -8), ([2,6,18], -16), ([3,6,18], -16), ([4,6,18], -16), ([5,6,18], -16), ([6,6,18], -16), ([6,7,18], -16), ([6,8,18], -16), ([6,9,18], -16), ([6,10,18], -16), ([6,11,18], -16), ([6,12,18], -16), ([6,13,18], -16), ([6,14,18], -16), ([6,15,18], -16), ([6,16,18], -16), ([6,17,18], -16), ([6,18,18], -8), ([6,18,20], 8), ([6,18,21], 12), ([6,18,22], 16), ([6,18,23], 18)]
theorem atom0089_data : atom0089 = SparsePolynomial.monoTimes [6,18] 1 base07 := by decide +kernel
theorem eval_atom0089 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0089 = (quadB (outer g) ![1,2,2] * g 6 * g 18) := by
  rw [atom0089_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0089_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (952819005600 : Int) atom0089) := by
  rw [SparsePolynomial.eval_scale, eval_atom0089]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 18) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0090 : SparsePolynomial.Poly := [([0,6,19], -4), ([1,6,19], -8), ([2,6,19], -16), ([3,6,19], -16), ([4,6,19], -16), ([5,6,19], -16), ([6,6,19], -16), ([6,7,19], -16), ([6,8,19], -16), ([6,9,19], -16), ([6,10,19], -16), ([6,11,19], -16), ([6,12,19], -16), ([6,13,19], -16), ([6,14,19], -16), ([6,15,19], -16), ([6,16,19], -16), ([6,17,19], -16), ([6,18,19], -8), ([6,19,20], 8), ([6,19,21], 12), ([6,19,22], 16), ([6,19,23], 18)]
theorem atom0090_data : atom0090 = SparsePolynomial.monoTimes [6,19] 1 base07 := by decide +kernel
theorem eval_atom0090 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0090 = (quadB (outer g) ![1,2,2] * g 6 * g 19) := by
  rw [atom0090_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0090_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6399966988800 : Int) atom0090) := by
  rw [SparsePolynomial.eval_scale, eval_atom0090]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 19) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0091 : SparsePolynomial.Poly := [([0,6,20], -4), ([1,6,20], -8), ([2,6,20], -16), ([3,6,20], -16), ([4,6,20], -16), ([5,6,20], -16), ([6,6,20], -16), ([6,7,20], -16), ([6,8,20], -16), ([6,9,20], -16), ([6,10,20], -16), ([6,11,20], -16), ([6,12,20], -16), ([6,13,20], -16), ([6,14,20], -16), ([6,15,20], -16), ([6,16,20], -16), ([6,17,20], -16), ([6,18,20], -8), ([6,20,20], 8), ([6,20,21], 12), ([6,20,22], 16), ([6,20,23], 18)]
theorem atom0091_data : atom0091 = SparsePolynomial.monoTimes [6,20] 1 base07 := by decide +kernel
theorem eval_atom0091 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0091 = (quadB (outer g) ![1,2,2] * g 6 * g 20) := by
  rw [atom0091_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0091_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3044502568800 : Int) atom0091) := by
  rw [SparsePolynomial.eval_scale, eval_atom0091]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 20) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0092 : SparsePolynomial.Poly := [([0,6,21], -4), ([1,6,21], -8), ([2,6,21], -16), ([3,6,21], -16), ([4,6,21], -16), ([5,6,21], -16), ([6,6,21], -16), ([6,7,21], -16), ([6,8,21], -16), ([6,9,21], -16), ([6,10,21], -16), ([6,11,21], -16), ([6,12,21], -16), ([6,13,21], -16), ([6,14,21], -16), ([6,15,21], -16), ([6,16,21], -16), ([6,17,21], -16), ([6,18,21], -8), ([6,20,21], 8), ([6,21,21], 12), ([6,21,22], 16), ([6,21,23], 18)]
theorem atom0092_data : atom0092 = SparsePolynomial.monoTimes [6,21] 1 base07 := by decide +kernel
theorem eval_atom0092 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0092 = (quadB (outer g) ![1,2,2] * g 6 * g 21) := by
  rw [atom0092_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0092_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (9528190056000 : Int) atom0092) := by
  rw [SparsePolynomial.eval_scale, eval_atom0092]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg21 : 0 ≤ g 21 := hg 21
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 21) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0093 : SparsePolynomial.Poly := [([0,6,23], -4), ([1,6,23], -8), ([2,6,23], -16), ([3,6,23], -16), ([4,6,23], -16), ([5,6,23], -16), ([6,6,23], -16), ([6,7,23], -16), ([6,8,23], -16), ([6,9,23], -16), ([6,10,23], -16), ([6,11,23], -16), ([6,12,23], -16), ([6,13,23], -16), ([6,14,23], -16), ([6,15,23], -16), ([6,16,23], -16), ([6,17,23], -16), ([6,18,23], -8), ([6,20,23], 8), ([6,21,23], 12), ([6,22,23], 16), ([6,23,23], 18)]
theorem atom0093_data : atom0093 = SparsePolynomial.monoTimes [6,23] 1 base07 := by decide +kernel
theorem eval_atom0093 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0093 = (quadB (outer g) ![1,2,2] * g 6 * g 23) := by
  rw [atom0093_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0093_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (943355649600 : Int) atom0093) := by
  rw [SparsePolynomial.eval_scale, eval_atom0093]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg23 : 0 ≤ g 23 := hg 23
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 23) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0094 : SparsePolynomial.Poly := [([0,7,9], -4), ([1,7,9], -8), ([2,7,9], -16), ([3,7,9], -16), ([4,7,9], -16), ([5,7,9], -16), ([6,7,9], -16), ([7,7,9], -16), ([7,8,9], -16), ([7,9,9], -16), ([7,9,10], -16), ([7,9,11], -16), ([7,9,12], -16), ([7,9,13], -16), ([7,9,14], -16), ([7,9,15], -16), ([7,9,16], -16), ([7,9,17], -16), ([7,9,18], -8), ([7,9,20], 8), ([7,9,21], 12), ([7,9,22], 16), ([7,9,23], 18)]
theorem atom0094_data : atom0094 = SparsePolynomial.monoTimes [7,9] 1 base07 := by decide +kernel
theorem eval_atom0094 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0094 = (quadB (outer g) ![1,2,2] * g 7 * g 9) := by
  rw [atom0094_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0094_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6848320131543 : Int) atom0094) := by
  rw [SparsePolynomial.eval_scale, eval_atom0094]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0095 : SparsePolynomial.Poly := [([0,7,10], -4), ([1,7,10], -8), ([2,7,10], -16), ([3,7,10], -16), ([4,7,10], -16), ([5,7,10], -16), ([6,7,10], -16), ([7,7,10], -16), ([7,8,10], -16), ([7,9,10], -16), ([7,10,10], -16), ([7,10,11], -16), ([7,10,12], -16), ([7,10,13], -16), ([7,10,14], -16), ([7,10,15], -16), ([7,10,16], -16), ([7,10,17], -16), ([7,10,18], -8), ([7,10,20], 8), ([7,10,21], 12), ([7,10,22], 16), ([7,10,23], 18)]
theorem atom0095_data : atom0095 = SparsePolynomial.monoTimes [7,10] 1 base07 := by decide +kernel
theorem eval_atom0095 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0095 = (quadB (outer g) ![1,2,2] * g 7 * g 10) := by
  rw [atom0095_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0095_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6292722195771 : Int) atom0095) := by
  rw [SparsePolynomial.eval_scale, eval_atom0095]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0096 : SparsePolynomial.Poly := [([0,7,11], -4), ([1,7,11], -8), ([2,7,11], -16), ([3,7,11], -16), ([4,7,11], -16), ([5,7,11], -16), ([6,7,11], -16), ([7,7,11], -16), ([7,8,11], -16), ([7,9,11], -16), ([7,10,11], -16), ([7,11,11], -16), ([7,11,12], -16), ([7,11,13], -16), ([7,11,14], -16), ([7,11,15], -16), ([7,11,16], -16), ([7,11,17], -16), ([7,11,18], -8), ([7,11,20], 8), ([7,11,21], 12), ([7,11,22], 16), ([7,11,23], 18)]
theorem atom0096_data : atom0096 = SparsePolynomial.monoTimes [7,11] 1 base07 := by decide +kernel
theorem eval_atom0096 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0096 = (quadB (outer g) ![1,2,2] * g 7 * g 11) := by
  rw [atom0096_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0096_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4818938862606 : Int) atom0096) := by
  rw [SparsePolynomial.eval_scale, eval_atom0096]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0097 : SparsePolynomial.Poly := [([0,7,12], -4), ([1,7,12], -8), ([2,7,12], -16), ([3,7,12], -16), ([4,7,12], -16), ([5,7,12], -16), ([6,7,12], -16), ([7,7,12], -16), ([7,8,12], -16), ([7,9,12], -16), ([7,10,12], -16), ([7,11,12], -16), ([7,12,12], -16), ([7,12,13], -16), ([7,12,14], -16), ([7,12,15], -16), ([7,12,16], -16), ([7,12,17], -16), ([7,12,18], -8), ([7,12,20], 8), ([7,12,21], 12), ([7,12,22], 16), ([7,12,23], 18)]
theorem atom0097_data : atom0097 = SparsePolynomial.monoTimes [7,12] 1 base07 := by decide +kernel
theorem eval_atom0097 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0097 = (quadB (outer g) ![1,2,2] * g 7 * g 12) := by
  rw [atom0097_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0097_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2829297962436 : Int) atom0097) := by
  rw [SparsePolynomial.eval_scale, eval_atom0097]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0098 : SparsePolynomial.Poly := [([0,7,13], -4), ([1,7,13], -8), ([2,7,13], -16), ([3,7,13], -16), ([4,7,13], -16), ([5,7,13], -16), ([6,7,13], -16), ([7,7,13], -16), ([7,8,13], -16), ([7,9,13], -16), ([7,10,13], -16), ([7,11,13], -16), ([7,12,13], -16), ([7,13,13], -16), ([7,13,14], -16), ([7,13,15], -16), ([7,13,16], -16), ([7,13,17], -16), ([7,13,18], -8), ([7,13,20], 8), ([7,13,21], 12), ([7,13,22], 16), ([7,13,23], 18)]
theorem atom0098_data : atom0098 = SparsePolynomial.monoTimes [7,13] 1 base07 := by decide +kernel
theorem eval_atom0098 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0098 = (quadB (outer g) ![1,2,2] * g 7 * g 13) := by
  rw [atom0098_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0098_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3126101609400 : Int) atom0098) := by
  rw [SparsePolynomial.eval_scale, eval_atom0098]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0099 : SparsePolynomial.Poly := [([0,7,14], -4), ([1,7,14], -8), ([2,7,14], -16), ([3,7,14], -16), ([4,7,14], -16), ([5,7,14], -16), ([6,7,14], -16), ([7,7,14], -16), ([7,8,14], -16), ([7,9,14], -16), ([7,10,14], -16), ([7,11,14], -16), ([7,12,14], -16), ([7,13,14], -16), ([7,14,14], -16), ([7,14,15], -16), ([7,14,16], -16), ([7,14,17], -16), ([7,14,18], -8), ([7,14,20], 8), ([7,14,21], 12), ([7,14,22], 16), ([7,14,23], 18)]
theorem atom0099_data : atom0099 = SparsePolynomial.monoTimes [7,14] 1 base07 := by decide +kernel
theorem eval_atom0099 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0099 = (quadB (outer g) ![1,2,2] * g 7 * g 14) := by
  rw [atom0099_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0099_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3652546682400 : Int) atom0099) := by
  rw [SparsePolynomial.eval_scale, eval_atom0099]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0100 : SparsePolynomial.Poly := [([0,7,15], -4), ([1,7,15], -8), ([2,7,15], -16), ([3,7,15], -16), ([4,7,15], -16), ([5,7,15], -16), ([6,7,15], -16), ([7,7,15], -16), ([7,8,15], -16), ([7,9,15], -16), ([7,10,15], -16), ([7,11,15], -16), ([7,12,15], -16), ([7,13,15], -16), ([7,14,15], -16), ([7,15,15], -16), ([7,15,16], -16), ([7,15,17], -16), ([7,15,18], -8), ([7,15,20], 8), ([7,15,21], 12), ([7,15,22], 16), ([7,15,23], 18)]
theorem atom0100_data : atom0100 = SparsePolynomial.monoTimes [7,15] 1 base07 := by decide +kernel
theorem eval_atom0100 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0100 = (quadB (outer g) ![1,2,2] * g 7 * g 15) := by
  rw [atom0100_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0100_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3254803843200 : Int) atom0100) := by
  rw [SparsePolynomial.eval_scale, eval_atom0100]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0101 : SparsePolynomial.Poly := [([0,7,16], -4), ([1,7,16], -8), ([2,7,16], -16), ([3,7,16], -16), ([4,7,16], -16), ([5,7,16], -16), ([6,7,16], -16), ([7,7,16], -16), ([7,8,16], -16), ([7,9,16], -16), ([7,10,16], -16), ([7,11,16], -16), ([7,12,16], -16), ([7,13,16], -16), ([7,14,16], -16), ([7,15,16], -16), ([7,16,16], -16), ([7,16,17], -16), ([7,16,18], -8), ([7,16,20], 8), ([7,16,21], 12), ([7,16,22], 16), ([7,16,23], 18)]
theorem atom0101_data : atom0101 = SparsePolynomial.monoTimes [7,16] 1 base07 := by decide +kernel
theorem eval_atom0101 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0101 = (quadB (outer g) ![1,2,2] * g 7 * g 16) := by
  rw [atom0101_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0101_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3595967894400 : Int) atom0101) := by
  rw [SparsePolynomial.eval_scale, eval_atom0101]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0102 : SparsePolynomial.Poly := [([0,7,17], -4), ([1,7,17], -8), ([2,7,17], -16), ([3,7,17], -16), ([4,7,17], -16), ([5,7,17], -16), ([6,7,17], -16), ([7,7,17], -16), ([7,8,17], -16), ([7,9,17], -16), ([7,10,17], -16), ([7,11,17], -16), ([7,12,17], -16), ([7,13,17], -16), ([7,14,17], -16), ([7,15,17], -16), ([7,16,17], -16), ([7,17,17], -16), ([7,17,18], -8), ([7,17,20], 8), ([7,17,21], 12), ([7,17,22], 16), ([7,17,23], 18)]
theorem atom0102_data : atom0102 = SparsePolynomial.monoTimes [7,17] 1 base07 := by decide +kernel
theorem eval_atom0102 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0102 = (quadB (outer g) ![1,2,2] * g 7 * g 17) := by
  rw [atom0102_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0102_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3316335792000 : Int) atom0102) := by
  rw [SparsePolynomial.eval_scale, eval_atom0102]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0103 : SparsePolynomial.Poly := [([0,7,18], -4), ([1,7,18], -8), ([2,7,18], -16), ([3,7,18], -16), ([4,7,18], -16), ([5,7,18], -16), ([6,7,18], -16), ([7,7,18], -16), ([7,8,18], -16), ([7,9,18], -16), ([7,10,18], -16), ([7,11,18], -16), ([7,12,18], -16), ([7,13,18], -16), ([7,14,18], -16), ([7,15,18], -16), ([7,16,18], -16), ([7,17,18], -16), ([7,18,18], -8), ([7,18,20], 8), ([7,18,21], 12), ([7,18,22], 16), ([7,18,23], 18)]
theorem atom0103_data : atom0103 = SparsePolynomial.monoTimes [7,18] 1 base07 := by decide +kernel
theorem eval_atom0103 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0103 = (quadB (outer g) ![1,2,2] * g 7 * g 18) := by
  rw [atom0103_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0103_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1848643104000 : Int) atom0103) := by
  rw [SparsePolynomial.eval_scale, eval_atom0103]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 18) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0104 : SparsePolynomial.Poly := [([0,7,19], -4), ([1,7,19], -8), ([2,7,19], -16), ([3,7,19], -16), ([4,7,19], -16), ([5,7,19], -16), ([6,7,19], -16), ([7,7,19], -16), ([7,8,19], -16), ([7,9,19], -16), ([7,10,19], -16), ([7,11,19], -16), ([7,12,19], -16), ([7,13,19], -16), ([7,14,19], -16), ([7,15,19], -16), ([7,16,19], -16), ([7,17,19], -16), ([7,18,19], -8), ([7,19,20], 8), ([7,19,21], 12), ([7,19,22], 16), ([7,19,23], 18)]
theorem atom0104_data : atom0104 = SparsePolynomial.monoTimes [7,19] 1 base07 := by decide +kernel
theorem eval_atom0104 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0104 = (quadB (outer g) ![1,2,2] * g 7 * g 19) := by
  rw [atom0104_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0104_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7333147852800 : Int) atom0104) := by
  rw [SparsePolynomial.eval_scale, eval_atom0104]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 19) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0105 : SparsePolynomial.Poly := [([0,7,20], -4), ([1,7,20], -8), ([2,7,20], -16), ([3,7,20], -16), ([4,7,20], -16), ([5,7,20], -16), ([6,7,20], -16), ([7,7,20], -16), ([7,8,20], -16), ([7,9,20], -16), ([7,10,20], -16), ([7,11,20], -16), ([7,12,20], -16), ([7,13,20], -16), ([7,14,20], -16), ([7,15,20], -16), ([7,16,20], -16), ([7,17,20], -16), ([7,18,20], -8), ([7,20,20], 8), ([7,20,21], 12), ([7,20,22], 16), ([7,20,23], 18)]
theorem atom0105_data : atom0105 = SparsePolynomial.monoTimes [7,20] 1 base07 := by decide +kernel
theorem eval_atom0105 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0105 = (quadB (outer g) ![1,2,2] * g 7 * g 20) := by
  rw [atom0105_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0105_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4015040198400 : Int) atom0105) := by
  rw [SparsePolynomial.eval_scale, eval_atom0105]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 20) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0106 : SparsePolynomial.Poly := [([0,7,21], -4), ([1,7,21], -8), ([2,7,21], -16), ([3,7,21], -16), ([4,7,21], -16), ([5,7,21], -16), ([6,7,21], -16), ([7,7,21], -16), ([7,8,21], -16), ([7,9,21], -16), ([7,10,21], -16), ([7,11,21], -16), ([7,12,21], -16), ([7,13,21], -16), ([7,14,21], -16), ([7,15,21], -16), ([7,16,21], -16), ([7,17,21], -16), ([7,18,21], -8), ([7,20,21], 8), ([7,21,21], 12), ([7,21,22], 16), ([7,21,23], 18)]
theorem atom0106_data : atom0106 = SparsePolynomial.monoTimes [7,21] 1 base07 := by decide +kernel
theorem eval_atom0106 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0106 = (quadB (outer g) ![1,2,2] * g 7 * g 21) := by
  rw [atom0106_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0106_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10827260505600 : Int) atom0106) := by
  rw [SparsePolynomial.eval_scale, eval_atom0106]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg21 : 0 ≤ g 21 := hg 21
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 21) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0107 : SparsePolynomial.Poly := [([0,7,22], -4), ([1,7,22], -8), ([2,7,22], -16), ([3,7,22], -16), ([4,7,22], -16), ([5,7,22], -16), ([6,7,22], -16), ([7,7,22], -16), ([7,8,22], -16), ([7,9,22], -16), ([7,10,22], -16), ([7,11,22], -16), ([7,12,22], -16), ([7,13,22], -16), ([7,14,22], -16), ([7,15,22], -16), ([7,16,22], -16), ([7,17,22], -16), ([7,18,22], -8), ([7,20,22], 8), ([7,21,22], 12), ([7,22,22], 16), ([7,22,23], 18)]
theorem atom0107_data : atom0107 = SparsePolynomial.monoTimes [7,22] 1 base07 := by decide +kernel
theorem eval_atom0107 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0107 = (quadB (outer g) ![1,2,2] * g 7 * g 22) := by
  rw [atom0107_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0107_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (955083052000 : Int) atom0107) := by
  rw [SparsePolynomial.eval_scale, eval_atom0107]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0108 : SparsePolynomial.Poly := [([0,7,23], -4), ([1,7,23], -8), ([2,7,23], -16), ([3,7,23], -16), ([4,7,23], -16), ([5,7,23], -16), ([6,7,23], -16), ([7,7,23], -16), ([7,8,23], -16), ([7,9,23], -16), ([7,10,23], -16), ([7,11,23], -16), ([7,12,23], -16), ([7,13,23], -16), ([7,14,23], -16), ([7,15,23], -16), ([7,16,23], -16), ([7,17,23], -16), ([7,18,23], -8), ([7,20,23], 8), ([7,21,23], 12), ([7,22,23], 16), ([7,23,23], 18)]
theorem atom0108_data : atom0108 = SparsePolynomial.monoTimes [7,23] 1 base07 := by decide +kernel
theorem eval_atom0108 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0108 = (quadB (outer g) ![1,2,2] * g 7 * g 23) := by
  rw [atom0108_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0108_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2850322557600 : Int) atom0108) := by
  rw [SparsePolynomial.eval_scale, eval_atom0108]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg23 : 0 ≤ g 23 := hg 23
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 23) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0109 : SparsePolynomial.Poly := [([0,8,10], -4), ([1,8,10], -8), ([2,8,10], -16), ([3,8,10], -16), ([4,8,10], -16), ([5,8,10], -16), ([6,8,10], -16), ([7,8,10], -16), ([8,8,10], -16), ([8,9,10], -16), ([8,10,10], -16), ([8,10,11], -16), ([8,10,12], -16), ([8,10,13], -16), ([8,10,14], -16), ([8,10,15], -16), ([8,10,16], -16), ([8,10,17], -16), ([8,10,18], -8), ([8,10,20], 8), ([8,10,21], 12), ([8,10,22], 16), ([8,10,23], 18)]
theorem atom0109_data : atom0109 = SparsePolynomial.monoTimes [8,10] 1 base07 := by decide +kernel
theorem eval_atom0109 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0109 = (quadB (outer g) ![1,2,2] * g 8 * g 10) := by
  rw [atom0109_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0109_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7194763474569 : Int) atom0109) := by
  rw [SparsePolynomial.eval_scale, eval_atom0109]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 8 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0110 : SparsePolynomial.Poly := [([0,8,11], -4), ([1,8,11], -8), ([2,8,11], -16), ([3,8,11], -16), ([4,8,11], -16), ([5,8,11], -16), ([6,8,11], -16), ([7,8,11], -16), ([8,8,11], -16), ([8,9,11], -16), ([8,10,11], -16), ([8,11,11], -16), ([8,11,12], -16), ([8,11,13], -16), ([8,11,14], -16), ([8,11,15], -16), ([8,11,16], -16), ([8,11,17], -16), ([8,11,18], -8), ([8,11,20], 8), ([8,11,21], 12), ([8,11,22], 16), ([8,11,23], 18)]
theorem atom0110_data : atom0110 = SparsePolynomial.monoTimes [8,11] 1 base07 := by decide +kernel
theorem eval_atom0110 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0110 = (quadB (outer g) ![1,2,2] * g 8 * g 11) := by
  rw [atom0110_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0110_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7109218669806 : Int) atom0110) := by
  rw [SparsePolynomial.eval_scale, eval_atom0110]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 8 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0111 : SparsePolynomial.Poly := [([0,8,12], -4), ([1,8,12], -8), ([2,8,12], -16), ([3,8,12], -16), ([4,8,12], -16), ([5,8,12], -16), ([6,8,12], -16), ([7,8,12], -16), ([8,8,12], -16), ([8,9,12], -16), ([8,10,12], -16), ([8,11,12], -16), ([8,12,12], -16), ([8,12,13], -16), ([8,12,14], -16), ([8,12,15], -16), ([8,12,16], -16), ([8,12,17], -16), ([8,12,18], -8), ([8,12,20], 8), ([8,12,21], 12), ([8,12,22], 16), ([8,12,23], 18)]
theorem atom0111_data : atom0111 = SparsePolynomial.monoTimes [8,12] 1 base07 := by decide +kernel
theorem eval_atom0111 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0111 = (quadB (outer g) ![1,2,2] * g 8 * g 12) := by
  rw [atom0111_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0111_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4609281398436 : Int) atom0111) := by
  rw [SparsePolynomial.eval_scale, eval_atom0111]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 8 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0112 : SparsePolynomial.Poly := [([0,8,13], -4), ([1,8,13], -8), ([2,8,13], -16), ([3,8,13], -16), ([4,8,13], -16), ([5,8,13], -16), ([6,8,13], -16), ([7,8,13], -16), ([8,8,13], -16), ([8,9,13], -16), ([8,10,13], -16), ([8,11,13], -16), ([8,12,13], -16), ([8,13,13], -16), ([8,13,14], -16), ([8,13,15], -16), ([8,13,16], -16), ([8,13,17], -16), ([8,13,18], -8), ([8,13,20], 8), ([8,13,21], 12), ([8,13,22], 16), ([8,13,23], 18)]
theorem atom0112_data : atom0112 = SparsePolynomial.monoTimes [8,13] 1 base07 := by decide +kernel
theorem eval_atom0112 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0112 = (quadB (outer g) ![1,2,2] * g 8 * g 13) := by
  rw [atom0112_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0112_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4588478710200 : Int) atom0112) := by
  rw [SparsePolynomial.eval_scale, eval_atom0112]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 8 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0113 : SparsePolynomial.Poly := [([0,8,14], -4), ([1,8,14], -8), ([2,8,14], -16), ([3,8,14], -16), ([4,8,14], -16), ([5,8,14], -16), ([6,8,14], -16), ([7,8,14], -16), ([8,8,14], -16), ([8,9,14], -16), ([8,10,14], -16), ([8,11,14], -16), ([8,12,14], -16), ([8,13,14], -16), ([8,14,14], -16), ([8,14,15], -16), ([8,14,16], -16), ([8,14,17], -16), ([8,14,18], -8), ([8,14,20], 8), ([8,14,21], 12), ([8,14,22], 16), ([8,14,23], 18)]
theorem atom0113_data : atom0113 = SparsePolynomial.monoTimes [8,14] 1 base07 := by decide +kernel
theorem eval_atom0113 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0113 = (quadB (outer g) ![1,2,2] * g 8 * g 14) := by
  rw [atom0113_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0113_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4797317448000 : Int) atom0113) := by
  rw [SparsePolynomial.eval_scale, eval_atom0113]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 8 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0114 : SparsePolynomial.Poly := [([0,8,15], -4), ([1,8,15], -8), ([2,8,15], -16), ([3,8,15], -16), ([4,8,15], -16), ([5,8,15], -16), ([6,8,15], -16), ([7,8,15], -16), ([8,8,15], -16), ([8,9,15], -16), ([8,10,15], -16), ([8,11,15], -16), ([8,12,15], -16), ([8,13,15], -16), ([8,14,15], -16), ([8,15,15], -16), ([8,15,16], -16), ([8,15,17], -16), ([8,15,18], -8), ([8,15,20], 8), ([8,15,21], 12), ([8,15,22], 16), ([8,15,23], 18)]
theorem atom0114_data : atom0114 = SparsePolynomial.monoTimes [8,15] 1 base07 := by decide +kernel
theorem eval_atom0114 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0114 = (quadB (outer g) ![1,2,2] * g 8 * g 15) := by
  rw [atom0114_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0114_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4081968273600 : Int) atom0114) := by
  rw [SparsePolynomial.eval_scale, eval_atom0114]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 8 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0115 : SparsePolynomial.Poly := [([0,8,16], -4), ([1,8,16], -8), ([2,8,16], -16), ([3,8,16], -16), ([4,8,16], -16), ([5,8,16], -16), ([6,8,16], -16), ([7,8,16], -16), ([8,8,16], -16), ([8,9,16], -16), ([8,10,16], -16), ([8,11,16], -16), ([8,12,16], -16), ([8,13,16], -16), ([8,14,16], -16), ([8,15,16], -16), ([8,16,16], -16), ([8,16,17], -16), ([8,16,18], -8), ([8,16,20], 8), ([8,16,21], 12), ([8,16,22], 16), ([8,16,23], 18)]
theorem atom0115_data : atom0115 = SparsePolynomial.monoTimes [8,16] 1 base07 := by decide +kernel
theorem eval_atom0115 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0115 = (quadB (outer g) ![1,2,2] * g 8 * g 16) := by
  rw [atom0115_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0115_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4105525989600 : Int) atom0115) := by
  rw [SparsePolynomial.eval_scale, eval_atom0115]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 8 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0116 : SparsePolynomial.Poly := [([0,8,17], -4), ([1,8,17], -8), ([2,8,17], -16), ([3,8,17], -16), ([4,8,17], -16), ([5,8,17], -16), ([6,8,17], -16), ([7,8,17], -16), ([8,8,17], -16), ([8,9,17], -16), ([8,10,17], -16), ([8,11,17], -16), ([8,12,17], -16), ([8,13,17], -16), ([8,14,17], -16), ([8,15,17], -16), ([8,16,17], -16), ([8,17,17], -16), ([8,17,18], -8), ([8,17,20], 8), ([8,17,21], 12), ([8,17,22], 16), ([8,17,23], 18)]
theorem atom0116_data : atom0116 = SparsePolynomial.monoTimes [8,17] 1 base07 := by decide +kernel
theorem eval_atom0116 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0116 = (quadB (outer g) ![1,2,2] * g 8 * g 17) := by
  rw [atom0116_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0116_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3508287552000 : Int) atom0116) := by
  rw [SparsePolynomial.eval_scale, eval_atom0116]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 8 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0117 : SparsePolynomial.Poly := [([0,8,18], -4), ([1,8,18], -8), ([2,8,18], -16), ([3,8,18], -16), ([4,8,18], -16), ([5,8,18], -16), ([6,8,18], -16), ([7,8,18], -16), ([8,8,18], -16), ([8,9,18], -16), ([8,10,18], -16), ([8,11,18], -16), ([8,12,18], -16), ([8,13,18], -16), ([8,14,18], -16), ([8,15,18], -16), ([8,16,18], -16), ([8,17,18], -16), ([8,18,18], -8), ([8,18,20], 8), ([8,18,21], 12), ([8,18,22], 16), ([8,18,23], 18)]
theorem atom0117_data : atom0117 = SparsePolynomial.monoTimes [8,18] 1 base07 := by decide +kernel
theorem eval_atom0117 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0117 = (quadB (outer g) ![1,2,2] * g 8 * g 18) := by
  rw [atom0117_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0117_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1938860431200 : Int) atom0117) := by
  rw [SparsePolynomial.eval_scale, eval_atom0117]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 8 * g 18) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0118 : SparsePolynomial.Poly := [([0,8,19], -4), ([1,8,19], -8), ([2,8,19], -16), ([3,8,19], -16), ([4,8,19], -16), ([5,8,19], -16), ([6,8,19], -16), ([7,8,19], -16), ([8,8,19], -16), ([8,9,19], -16), ([8,10,19], -16), ([8,11,19], -16), ([8,12,19], -16), ([8,13,19], -16), ([8,14,19], -16), ([8,15,19], -16), ([8,16,19], -16), ([8,17,19], -16), ([8,18,19], -8), ([8,19,20], 8), ([8,19,21], 12), ([8,19,22], 16), ([8,19,23], 18)]
theorem atom0118_data : atom0118 = SparsePolynomial.monoTimes [8,19] 1 base07 := by decide +kernel
theorem eval_atom0118 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0118 = (quadB (outer g) ![1,2,2] * g 8 * g 19) := by
  rw [atom0118_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0118_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7537502649600 : Int) atom0118) := by
  rw [SparsePolynomial.eval_scale, eval_atom0118]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 8 * g 19) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0119 : SparsePolynomial.Poly := [([0,8,20], -4), ([1,8,20], -8), ([2,8,20], -16), ([3,8,20], -16), ([4,8,20], -16), ([5,8,20], -16), ([6,8,20], -16), ([7,8,20], -16), ([8,8,20], -16), ([8,9,20], -16), ([8,10,20], -16), ([8,11,20], -16), ([8,12,20], -16), ([8,13,20], -16), ([8,14,20], -16), ([8,15,20], -16), ([8,16,20], -16), ([8,17,20], -16), ([8,18,20], -8), ([8,20,20], 8), ([8,20,21], 12), ([8,20,22], 16), ([8,20,23], 18)]
theorem atom0119_data : atom0119 = SparsePolynomial.monoTimes [8,20] 1 base07 := by decide +kernel
theorem eval_atom0119 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0119 = (quadB (outer g) ![1,2,2] * g 8 * g 20) := by
  rw [atom0119_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0119_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4333532464800 : Int) atom0119) := by
  rw [SparsePolynomial.eval_scale, eval_atom0119]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 8 * g 20) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0120 : SparsePolynomial.Poly := [([0,8,21], -4), ([1,8,21], -8), ([2,8,21], -16), ([3,8,21], -16), ([4,8,21], -16), ([5,8,21], -16), ([6,8,21], -16), ([7,8,21], -16), ([8,8,21], -16), ([8,9,21], -16), ([8,10,21], -16), ([8,11,21], -16), ([8,12,21], -16), ([8,13,21], -16), ([8,14,21], -16), ([8,15,21], -16), ([8,16,21], -16), ([8,17,21], -16), ([8,18,21], -8), ([8,20,21], 8), ([8,21,21], 12), ([8,21,22], 16), ([8,21,23], 18)]
theorem atom0120_data : atom0120 = SparsePolynomial.monoTimes [8,21] 1 base07 := by decide +kernel
theorem eval_atom0120 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0120 = (quadB (outer g) ![1,2,2] * g 8 * g 21) := by
  rw [atom0120_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0120_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (11691634046400 : Int) atom0120) := by
  rw [SparsePolynomial.eval_scale, eval_atom0120]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg21 : 0 ≤ g 21 := hg 21
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 8 * g 21) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0121 : SparsePolynomial.Poly := [([0,8,22], -4), ([1,8,22], -8), ([2,8,22], -16), ([3,8,22], -16), ([4,8,22], -16), ([5,8,22], -16), ([6,8,22], -16), ([7,8,22], -16), ([8,8,22], -16), ([8,9,22], -16), ([8,10,22], -16), ([8,11,22], -16), ([8,12,22], -16), ([8,13,22], -16), ([8,14,22], -16), ([8,15,22], -16), ([8,16,22], -16), ([8,17,22], -16), ([8,18,22], -8), ([8,20,22], 8), ([8,21,22], 12), ([8,22,22], 16), ([8,22,23], 18)]
theorem atom0121_data : atom0121 = SparsePolynomial.monoTimes [8,22] 1 base07 := by decide +kernel
theorem eval_atom0121 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0121 = (quadB (outer g) ![1,2,2] * g 8 * g 22) := by
  rw [atom0121_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0121_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2272413528000 : Int) atom0121) := by
  rw [SparsePolynomial.eval_scale, eval_atom0121]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 8 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0122 : SparsePolynomial.Poly := [([0,8,23], -4), ([1,8,23], -8), ([2,8,23], -16), ([3,8,23], -16), ([4,8,23], -16), ([5,8,23], -16), ([6,8,23], -16), ([7,8,23], -16), ([8,8,23], -16), ([8,9,23], -16), ([8,10,23], -16), ([8,11,23], -16), ([8,12,23], -16), ([8,13,23], -16), ([8,14,23], -16), ([8,15,23], -16), ([8,16,23], -16), ([8,17,23], -16), ([8,18,23], -8), ([8,20,23], 8), ([8,21,23], 12), ([8,22,23], 16), ([8,23,23], 18)]
theorem atom0122_data : atom0122 = SparsePolynomial.monoTimes [8,23] 1 base07 := by decide +kernel
theorem eval_atom0122 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0122 = (quadB (outer g) ![1,2,2] * g 8 * g 23) := by
  rw [atom0122_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0122_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5409334828800 : Int) atom0122) := by
  rw [SparsePolynomial.eval_scale, eval_atom0122]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg23 : 0 ≤ g 23 := hg 23
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 8 * g 23) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0123 : SparsePolynomial.Poly := [([0,9,10], -4), ([1,9,10], -8), ([2,9,10], -16), ([3,9,10], -16), ([4,9,10], -16), ([5,9,10], -16), ([6,9,10], -16), ([7,9,10], -16), ([8,9,10], -16), ([9,9,10], -16), ([9,10,10], -16), ([9,10,11], -16), ([9,10,12], -16), ([9,10,13], -16), ([9,10,14], -16), ([9,10,15], -16), ([9,10,16], -16), ([9,10,17], -16), ([9,10,18], -8), ([9,10,20], 8), ([9,10,21], 12), ([9,10,22], 16), ([9,10,23], 18)]
theorem atom0123_data : atom0123 = SparsePolynomial.monoTimes [9,10] 1 base07 := by decide +kernel
theorem eval_atom0123 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0123 = (quadB (outer g) ![1,2,2] * g 9 * g 10) := by
  rw [atom0123_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0123_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3618143020800 : Int) atom0123) := by
  rw [SparsePolynomial.eval_scale, eval_atom0123]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0124 : SparsePolynomial.Poly := [([0,9,11], -4), ([1,9,11], -8), ([2,9,11], -16), ([3,9,11], -16), ([4,9,11], -16), ([5,9,11], -16), ([6,9,11], -16), ([7,9,11], -16), ([8,9,11], -16), ([9,9,11], -16), ([9,10,11], -16), ([9,11,11], -16), ([9,11,12], -16), ([9,11,13], -16), ([9,11,14], -16), ([9,11,15], -16), ([9,11,16], -16), ([9,11,17], -16), ([9,11,18], -8), ([9,11,20], 8), ([9,11,21], 12), ([9,11,22], 16), ([9,11,23], 18)]
theorem atom0124_data : atom0124 = SparsePolynomial.monoTimes [9,11] 1 base07 := by decide +kernel
theorem eval_atom0124 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0124 = (quadB (outer g) ![1,2,2] * g 9 * g 11) := by
  rw [atom0124_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0124_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6481295472960 : Int) atom0124) := by
  rw [SparsePolynomial.eval_scale, eval_atom0124]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0125 : SparsePolynomial.Poly := [([0,9,12], -4), ([1,9,12], -8), ([2,9,12], -16), ([3,9,12], -16), ([4,9,12], -16), ([5,9,12], -16), ([6,9,12], -16), ([7,9,12], -16), ([8,9,12], -16), ([9,9,12], -16), ([9,10,12], -16), ([9,11,12], -16), ([9,12,12], -16), ([9,12,13], -16), ([9,12,14], -16), ([9,12,15], -16), ([9,12,16], -16), ([9,12,17], -16), ([9,12,18], -8), ([9,12,20], 8), ([9,12,21], 12), ([9,12,22], 16), ([9,12,23], 18)]
theorem atom0125_data : atom0125 = SparsePolynomial.monoTimes [9,12] 1 base07 := by decide +kernel
theorem eval_atom0125 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0125 = (quadB (outer g) ![1,2,2] * g 9 * g 12) := by
  rw [atom0125_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0125_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6524826177078 : Int) atom0125) := by
  rw [SparsePolynomial.eval_scale, eval_atom0125]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0126 : SparsePolynomial.Poly := [([0,9,13], -4), ([1,9,13], -8), ([2,9,13], -16), ([3,9,13], -16), ([4,9,13], -16), ([5,9,13], -16), ([6,9,13], -16), ([7,9,13], -16), ([8,9,13], -16), ([9,9,13], -16), ([9,10,13], -16), ([9,11,13], -16), ([9,12,13], -16), ([9,13,13], -16), ([9,13,14], -16), ([9,13,15], -16), ([9,13,16], -16), ([9,13,17], -16), ([9,13,18], -8), ([9,13,20], 8), ([9,13,21], 12), ([9,13,22], 16), ([9,13,23], 18)]
theorem atom0126_data : atom0126 = SparsePolynomial.monoTimes [9,13] 1 base07 := by decide +kernel
theorem eval_atom0126 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0126 = (quadB (outer g) ![1,2,2] * g 9 * g 13) := by
  rw [atom0126_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0126_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5929940071242 : Int) atom0126) := by
  rw [SparsePolynomial.eval_scale, eval_atom0126]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0127 : SparsePolynomial.Poly := [([0,9,14], -4), ([1,9,14], -8), ([2,9,14], -16), ([3,9,14], -16), ([4,9,14], -16), ([5,9,14], -16), ([6,9,14], -16), ([7,9,14], -16), ([8,9,14], -16), ([9,9,14], -16), ([9,10,14], -16), ([9,11,14], -16), ([9,12,14], -16), ([9,13,14], -16), ([9,14,14], -16), ([9,14,15], -16), ([9,14,16], -16), ([9,14,17], -16), ([9,14,18], -8), ([9,14,20], 8), ([9,14,21], 12), ([9,14,22], 16), ([9,14,23], 18)]
theorem atom0127_data : atom0127 = SparsePolynomial.monoTimes [9,14] 1 base07 := by decide +kernel
theorem eval_atom0127 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0127 = (quadB (outer g) ![1,2,2] * g 9 * g 14) := by
  rw [atom0127_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0127_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5757385427442 : Int) atom0127) := by
  rw [SparsePolynomial.eval_scale, eval_atom0127]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0128 : SparsePolynomial.Poly := [([0,9,15], -4), ([1,9,15], -8), ([2,9,15], -16), ([3,9,15], -16), ([4,9,15], -16), ([5,9,15], -16), ([6,9,15], -16), ([7,9,15], -16), ([8,9,15], -16), ([9,9,15], -16), ([9,10,15], -16), ([9,11,15], -16), ([9,12,15], -16), ([9,13,15], -16), ([9,14,15], -16), ([9,15,15], -16), ([9,15,16], -16), ([9,15,17], -16), ([9,15,18], -8), ([9,15,20], 8), ([9,15,21], 12), ([9,15,22], 16), ([9,15,23], 18)]
theorem atom0128_data : atom0128 = SparsePolynomial.monoTimes [9,15] 1 base07 := by decide +kernel
theorem eval_atom0128 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0128 = (quadB (outer g) ![1,2,2] * g 9 * g 15) := by
  rw [atom0128_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0128_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4660642871442 : Int) atom0128) := by
  rw [SparsePolynomial.eval_scale, eval_atom0128]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def block003 : SparsePolynomial.Poly := [([0,0,16], -39666522470400), ([0,0,17], -40228363929600), ([0,0,22], -7675707916800), ([0,0,23], -10758748492800), ([0,1,16], -79333044940800), ([0,1,17], -80456727859200), ([0,1,22], -15351415833600), ([0,1,23], -10758748492800), ([0,2,16], -79333044940800), ([0,2,17], -80456727859200), ([0,2,22], -29954139264000), ([0,2,23], -10758748492800), ([0,3,16], -79333044940800), ([0,3,17], -80456727859200), ([0,3,19], -6974050406400), ([0,3,21], -10078353331200), ([0,3,22], -29357988105600), ([0,3,23], -23941404748800), ([0,4,5], -2191558720824), ([0,4,16], -79333044940800), ([0,4,17], -81618586358400), ([0,4,19], -15445022518800), ([0,4,20], -223073449200), ([0,4,21], -21292530865200), ([0,4,22], -22151910975600), ([0,4,23], -38979744577200), ([0,5,6], -13099143655224), ([0,5,7], -7727447479224), ([0,5,8], -8495825186376), ([0,5,9], -7588225691244), ([0,5,10], -2543279715108), ([0,5,15], -184434768000), ([0,5,16], -82657542038400), ([0,5,17], -84438102672000), ([0,5,19], -18909353232000), ([0,5,20], -4285607356800), ([0,5,21], -27056451945600), ([0,5,22], -18645006441600), ([0,5,23], -11551860835200), ([0,6,7], -14644442736000), ([0,6,8], -20826470649600), ([0,6,9], -18791966668068), ([0,6,10], -15078951173484), ([0,6,11], -9683483037624), ([0,6,12], -2224584633744), ([0,6,13], -4427076376800), ([0,6,14], -7548133824000), ([0,6,15], -6972439622400), ([0,6,16], -88685417923200), ([0,6,17], -89705849587200), ([0,6,18], -3811276022400), ([0,6,19], -25599867955200), ([0,6,20], -12178010275200), ([0,6,21], -38112760224000), ([0,6,22], -15351415833600), ([0,6,23], -14532171091200), ([0,7,9], -27393280526172), ([0,7,10], -25170888783084), ([0,7,11], -19275755450424), ([0,7,12], -11317191849744), ([0,7,13], -12504406437600), ([0,7,14], -14610186729600), ([0,7,15], -13019215372800), ([0,7,16], -93716916518400), ([0,7,17], -93722071027200), ([0,7,18], -7394572416000), ([0,7,19], -29332591411200), ([0,7,20], -16060160793600), ([0,7,21], -43309042022400), ([0,7,22], -19171748041600), ([0,7,23], -22160038723200), ([0,8,10], -28779053898276), ([0,8,11], -28436874679224), ([0,8,12], -18437125593744), ([0,8,13], -18353914840800), ([0,8,14], -19189269792000), ([0,8,15], -16327873094400), ([0,8,16], -95755148899200), ([0,8,17], -94489878067200), ([0,8,18], -7755441724800), ([0,8,19], -30150010598400), ([0,8,20], -17334129859200), ([0,8,21], -46766536185600), ([0,8,22], -24441069945600), ([0,8,23], -32396087808000), ([0,9,10], -14472572083200), ([0,9,11], -25925181891840), ([0,9,12], -26099304708312), ([0,9,13], -23719760284968), ([0,9,14], -23029541709768), ([0,9,15], -18642571485768), ([0,9,16], -79333044940800), ([0,9,17], -80456727859200), ([0,9,22], -15351415833600), ([0,9,23], -10758748492800), ([0,10,16], -79333044940800), ([0,10,17], -80456727859200), ([0,10,22], -15351415833600), ([0,10,23], -10758748492800), ([0,11,16], -79333044940800), ([0,11,17], -80456727859200), ([0,11,22], -15351415833600), ([0,11,23], -10758748492800), ([0,12,16], -79333044940800), ([0,12,17], -80456727859200), ([0,12,22], -15351415833600), ([0,12,23], -10758748492800), ([0,13,16], -79333044940800), ([0,13,17], -80456727859200), ([0,13,22], -15351415833600), ([0,13,23], -10758748492800), ([0,14,16], -79333044940800), ([0,14,17], -80456727859200), ([0,14,22], -15351415833600), ([0,14,23], -10758748492800), ([0,15,16], -79333044940800), ([0,15,17], -80456727859200), ([0,15,22], -15351415833600), ([0,15,23], -10758748492800), ([0,16,16], -79333044940800), ([0,16,17], -159789772800000), ([0,16,18], -79333044940800), ([0,16,19], -79333044940800), ([0,16,20], -79333044940800), ([0,16,21], -79333044940800), ([0,16,22], -15351415833600), ([0,16,23], -10758748492800), ([0,17,17], -80456727859200), ([0,17,18], -80456727859200), ([0,17,19], -80456727859200), ([0,17,20], -80456727859200), ([0,17,21], -80456727859200), ([0,17,22], -15351415833600), ([0,17,23], -10758748492800), ([0,18,22], -15351415833600), ([0,18,23], -10758748492800), ([0,19,22], -15351415833600), ([0,19,23], -10758748492800), ([0,20,22], -15351415833600), ([0,21,22], -15351415833600), ([0,22,23], 10758748492800), ([0,23,23], 21517496985600), ([1,1,16], -39666522470400), ([1,1,17], -40228363929600), ([1,1,22], -7675707916800), ([1,2,16], -79333044940800), ([1,2,17], -80456727859200), ([1,2,22], -44556862694400), ([1,3,16], -79333044940800), ([1,3,17], -80456727859200), ([1,3,19], -13948100812800), ([1,3,21], -20156706662400), ([1,3,22], -43364560377600), ([1,3,23], -26365312512000), ([1,4,5], -4383117441648), ([1,4,16], -79333044940800), ([1,4,17], -82780444857600), ([1,4,19], -30890045037600), ([1,4,20], -446146898400), ([1,4,21], -42585061730400), ([1,4,22], -28952406117600), ([1,4,23], -56441992168800), ([1,5,6], -26198287310448), ([1,5,7], -15454894958448), ([1,5,8], -16991650372752), ([1,5,9], -15176451382488), ([1,5,10], -5086559430216), ([1,5,15], -368869536000), ([1,5,16], -85982039136000), ([1,5,17], -88419477484800), ([1,5,19], -37818706464000), ([1,5,20], -8571214713600), ([1,5,21], -54112903891200), ([1,5,22], -21938597049600), ([1,5,23], -1586224684800), ([1,6,7], -29288885472000), ([1,6,8], -41652941299200), ([1,6,9], -37583933336136), ([1,6,10], -30157902346968), ([1,6,11], -19366966075248), ([1,6,12], -4449169267488), ([1,6,13], -8854152753600), ([1,6,14], -15096267648000), ([1,6,15], -13944879244800), ([1,6,16], -98037790905600), ([1,6,17], -98954971315200), ([1,6,18], -7622552044800), ([1,6,19], -51199735910400), ([1,6,20], -24356020550400), ([1,6,21], -76225520448000), ([1,6,22], -15351415833600), ([1,6,23], -7546845196800), ([1,7,9], -54786561052344), ([1,7,10], -50341777566168), ([1,7,11], -38551510900848), ([1,7,12], -22634383699488), ([1,7,13], -25008812875200), ([1,7,14], -29220373459200), ([1,7,15], -26038430745600), ([1,7,16], -108100788096000), ([1,7,17], -106987414195200), ([1,7,18], -14789144832000), ([1,7,19], -58665182822400), ([1,7,20], -32120321587200), ([1,7,21], -86618084044800), ([1,7,22], -22992080249600), ([1,7,23], -22802580460800), ([1,8,10], -57558107796552), ([1,8,11], -56873749358448), ([1,8,12], -36874251187488), ([1,8,13], -36707829681600), ([1,8,14], -38378539584000), ([1,8,15], -32655746188800), ([1,8,16], -112177252857600), ([1,8,17], -108523028275200), ([1,8,18], -15510883449600), ([1,8,19], -60300021196800), ([1,8,20], -34668259718400), ([1,8,21], -93533072371200), ([1,8,22], -33530724057600), ([1,8,23], -43274678630400), ([1,9,10], -28945144166400), ([1,9,11], -51850363783680), ([1,9,12], -52198609416624), ([1,9,13], -47439520569936), ([1,9,14], -46059083419536), ([1,9,15], -37285142971536), ([1,9,16], -79333044940800), ([1,9,17], -80456727859200), ([1,9,22], -15351415833600), ([1,10,16], -79333044940800), ([1,10,17], -80456727859200), ([1,10,22], -15351415833600), ([1,11,16], -79333044940800), ([1,11,17], -80456727859200), ([1,11,22], -15351415833600), ([1,12,16], -79333044940800), ([1,12,17], -80456727859200), ([1,12,22], -15351415833600), ([1,13,16], -79333044940800), ([1,13,17], -80456727859200), ([1,13,22], -15351415833600), ([1,14,16], -79333044940800), ([1,14,17], -80456727859200), ([1,14,22], -15351415833600), ([1,15,16], -79333044940800), ([1,15,17], -80456727859200), ([1,15,22], -15351415833600), ([1,16,16], -79333044940800), ([1,16,17], -159789772800000), ([1,16,18], -79333044940800), ([1,16,19], -79333044940800), ([1,16,20], -79333044940800), ([1,16,21], -79333044940800), ([1,16,22], -15351415833600), ([1,17,17], -80456727859200), ([1,17,18], -80456727859200), ([1,17,19], -80456727859200), ([1,17,20], -80456727859200), ([1,17,21], -80456727859200), ([1,17,22], -15351415833600), ([1,18,22], -15351415833600), ([1,19,22], -15351415833600), ([1,20,22], -15351415833600), ([1,21,22], -15351415833600), ([2,2,16], -39666522470400), ([2,2,17], -40228363929600), ([2,2,22], -66086601638400), ([2,3,16], -79333044940800), ([2,3,17], -80456727859200), ([2,3,19], -27896201625600), ([2,3,21], -40313413324800), ([2,3,22], -129788598643200), ([2,3,23], -52730625024000), ([2,4,5], -8766234883296), ([2,4,16], -79333044940800), ([2,4,17], -85104161856000), ([2,4,19], -61780090075200), ([2,4,20], -892293796800), ([2,4,21], -85170123460800), ([2,4,22], -100964290123200), ([2,4,23], -112883984337600), ([2,5,6], -52396574620896), ([2,5,7], -30909789916896), ([2,5,8], -33983300745504), ([2,5,9], -30352902764976), ([2,5,10], -10173118860432), ([2,5,15], -737739072000), ([2,5,16], -92631033331200), ([2,5,17], -96382227110400), ([2,5,19], -75637412928000), ([2,5,20], -17142429427200), ([2,5,21], -108225807782400), ([2,5,22], -86936671987200), ([2,5,23], -3172449369600), ([2,6,7], -58577770944000), ([2,6,8], -83305882598400), ([2,6,9], -75167866672272), ([2,6,10], -60315804693936), ([2,6,11], -38733932150496), ([2,6,12], -8898338534976), ([2,6,13], -17708305507200), ([2,6,14], -30192535296000), ([2,6,15], -27889758489600), ([2,6,16], -116742536870400), ([2,6,17], -117453214771200), ([2,6,18], -15245104089600), ([2,6,19], -102399471820800), ([2,6,20], -48712041100800), ([2,6,21], -152451040896000), ([2,6,22], -73762309555200), ([2,6,23], -15093690393600), ([2,7,9], -109573122104688), ([2,7,10], -100683555132336), ([2,7,11], -77103021801696), ([2,7,12], -45268767398976), ([2,7,13], -50017625750400), ([2,7,14], -58440746918400), ([2,7,15], -52076861491200), ([2,7,16], -136868531251200), ([2,7,17], -133518100531200), ([2,7,18], -29578289664000), ([2,7,19], -117330365644800), ([2,7,20], -64240643174400), ([2,7,21], -173236168089600), ([2,7,22], -89043638387200), ([2,7,23], -45605160921600), ([2,8,10], -115116215593104), ([2,8,11], -113747498716896), ([2,8,12], -73748502374976), ([2,8,13], -73415659363200), ([2,8,14], -76757079168000), ([2,8,15], -65311492377600), ([2,8,16], -145021460774400), ([2,8,17], -136589328691200), ([2,8,18], -31021766899200), ([2,8,19], -120600042393600), ([2,8,20], -69336519436800), ([2,8,21], -187066144742400), ([2,8,22], -110120926003200), ([2,8,23], -86549357260800), ([2,9,10], -57890288332800), ([2,9,11], -103700727567360), ([2,9,12], -104397218833248), ([2,9,13], -94879041139872), ([2,9,14], -92118166839072), ([2,9,15], -74570285943072), ([2,9,16], -79333044940800), ([2,9,17], -80456727859200), ([2,9,22], -73762309555200), ([2,10,16], -79333044940800), ([2,10,17], -80456727859200), ([2,10,22], -73762309555200), ([2,11,16], -79333044940800), ([2,11,17], -80456727859200), ([2,11,22], -73762309555200), ([2,12,16], -79333044940800), ([2,12,17], -80456727859200), ([2,12,22], -73762309555200), ([2,13,16], -79333044940800), ([2,13,17], -80456727859200), ([2,13,22], -73762309555200), ([2,14,16], -79333044940800), ([2,14,17], -80456727859200), ([2,14,22], -73762309555200), ([2,15,16], -79333044940800), ([2,15,17], -80456727859200), ([2,15,22], -73762309555200), ([2,16,16], -79333044940800), ([2,16,17], -159789772800000), ([2,16,18], -79333044940800), ([2,16,19], -79333044940800), ([2,16,20], -79333044940800), ([2,16,21], -79333044940800), ([2,16,22], -73762309555200), ([2,17,17], -80456727859200), ([2,17,18], -80456727859200), ([2,17,19], -80456727859200), ([2,17,20], -80456727859200), ([2,17,21], -80456727859200), ([2,17,22], -73762309555200), ([2,18,22], -44556862694400), ([2,19,22], -15351415833600), ([2,20,22], 13854031027200), ([2,21,22], 28456754457600), ([2,22,22], 58410893721600), ([2,22,23], 65712255436800), ([3,3,16], -39666522470400), ([3,3,17], -40228363929600), ([3,3,19], -27896201625600), ([3,3,21], -40313413324800), ([3,3,22], -63701997004800), ([3,3,23], -52730625024000), ([3,4,5], -8766234883296), ([3,4,16], -79333044940800), ([3,4,17], -85104161856000), ([3,4,19], -89676291700800), ([3,4,20], -892293796800), ([3,4,21], -125483536785600), ([3,4,22], -98579685489600), ([3,4,23], -165614609361600), ([3,5,6], -52396574620896), ([3,5,7], -30909789916896), ([3,5,8], -33983300745504), ([3,5,9], -30352902764976), ([3,5,10], -10173118860432), ([3,5,15], -737739072000), ([3,5,16], -92631033331200), ([3,5,17], -96382227110400), ([3,5,19], -103533614553600), ([3,5,20], -17142429427200), ([3,5,21], -148539221107200), ([3,5,22], -84552067353600), ([3,5,23], -55903074393600), ([3,6,7], -58577770944000), ([3,6,8], -83305882598400), ([3,6,9], -75167866672272), ([3,6,10], -60315804693936), ([3,6,11], -38733932150496), ([3,6,12], -8898338534976), ([3,6,13], -17708305507200), ([3,6,14], -30192535296000), ([3,6,15], -27889758489600), ([3,6,16], -116742536870400), ([3,6,17], -117453214771200), ([3,6,18], -15245104089600), ([3,6,19], -130295673446400), ([3,6,20], -48712041100800), ([3,6,21], -192764454220800), ([3,6,22], -71377704921600), ([3,6,23], -67824315417600), ([3,7,9], -109573122104688), ([3,7,10], -100683555132336), ([3,7,11], -77103021801696), ([3,7,12], -45268767398976), ([3,7,13], -50017625750400), ([3,7,14], -58440746918400), ([3,7,15], -52076861491200), ([3,7,16], -136868531251200), ([3,7,17], -133518100531200), ([3,7,18], -29578289664000), ([3,7,19], -145226567270400), ([3,7,20], -64240643174400), ([3,7,21], -213549581414400), ([3,7,22], -86659033753600), ([3,7,23], -98335785945600), ([3,8,10], -115116215593104), ([3,8,11], -113747498716896), ([3,8,12], -73748502374976), ([3,8,13], -73415659363200), ([3,8,14], -76757079168000), ([3,8,15], -65311492377600), ([3,8,16], -145021460774400), ([3,8,17], -136589328691200), ([3,8,18], -31021766899200), ([3,8,19], -148496244019200), ([3,8,20], -69336519436800), ([3,8,21], -227379558067200), ([3,8,22], -107736321369600), ([3,8,23], -139279982284800), ([3,9,10], -57890288332800), ([3,9,11], -103700727567360), ([3,9,12], -104397218833248), ([3,9,13], -94879041139872), ([3,9,14], -92118166839072), ([3,9,15], -74570285943072), ([3,9,16], -79333044940800), ([3,9,17], -80456727859200), ([3,9,19], -27896201625600), ([3,9,21], -40313413324800), ([3,9,22], -71377704921600), ([3,9,23], -52730625024000), ([3,10,16], -79333044940800), ([3,10,17], -80456727859200), ([3,10,19], -27896201625600), ([3,10,21], -40313413324800), ([3,10,22], -71377704921600), ([3,10,23], -52730625024000), ([3,11,16], -79333044940800), ([3,11,17], -80456727859200), ([3,11,19], -27896201625600), ([3,11,21], -40313413324800), ([3,11,22], -71377704921600), ([3,11,23], -52730625024000), ([3,12,16], -79333044940800), ([3,12,17], -80456727859200), ([3,12,19], -27896201625600), ([3,12,21], -40313413324800), ([3,12,22], -71377704921600), ([3,12,23], -52730625024000), ([3,13,16], -79333044940800), ([3,13,17], -80456727859200), ([3,13,19], -27896201625600), ([3,13,21], -40313413324800), ([3,13,22], -71377704921600), ([3,13,23], -52730625024000), ([3,14,16], -79333044940800), ([3,14,17], -80456727859200), ([3,14,19], -27896201625600), ([3,14,21], -40313413324800), ([3,14,22], -71377704921600), ([3,14,23], -52730625024000), ([3,15,16], -79333044940800), ([3,15,17], -80456727859200), ([3,15,19], -27896201625600), ([3,15,21], -40313413324800), ([3,15,22], -71377704921600), ([3,15,23], -52730625024000), ([3,16,16], -79333044940800), ([3,16,17], -159789772800000), ([3,16,18], -79333044940800), ([3,16,19], -107229246566400), ([3,16,20], -79333044940800), ([3,16,21], -119646458265600), ([3,16,22], -71377704921600), ([3,16,23], -52730625024000), ([3,17,17], -80456727859200), ([3,17,18], -80456727859200), ([3,17,19], -108352929484800), ([3,17,20], -80456727859200), ([3,17,21], -120770141184000), ([3,17,22], -71377704921600), ([3,17,23], -52730625024000), ([3,18,19], -13948100812800), ([3,18,21], -20156706662400), ([3,18,22], -43364560377600), ([3,18,23], -26365312512000), ([3,19,20], 13948100812800), ([3,19,21], 20922151219200), ([3,19,22], 12544785792000), ([3,19,23], 31383226828800), ([3,20,21], 20156706662400), ([3,20,22], 12661728710400), ([3,20,23], 26365312512000), ([3,21,21], 30235059993600), ([3,21,22], 66981714307200), ([3,21,23], 84900558758400), ([3,22,22], 56026289088000), ([3,22,23], 115760200248000), ([3,23,23], 59321953152000), ([4,4,5], -8766234883296), ([4,4,16], -39666522470400), ([4,4,17], -44875797926400), ([4,4,19], -61780090075200), ([4,4,20], -892293796800), ([4,4,21], -85170123460800), ([4,4,22], -34877688484800), ([4,4,23], -112883984337600), ([4,5,5], -8766234883296), ([4,5,6], -61162809504192), ([4,5,7], -39676024800192), ([4,5,8], -42749535628800), ([4,5,9], -39119137648272), ([4,5,10], -18939353743728), ([4,5,11], -8766234883296), ([4,5,12], -8766234883296), ([4,5,13], -8766234883296), ([4,5,14], -8766234883296), ([4,5,15], -9503973955296), ([4,5,16], -101397268214496), ([4,5,17], -109795895990496), ([4,5,18], -4383117441648), ([4,5,19], -137417503003200), ([4,5,20], -13651605782352), ([4,5,21], -186821255080728), ([4,5,22], -46961523950304), ([4,5,23], -106194419463492), ([4,6,7], -58577770944000), ([4,6,8], -83305882598400), ([4,6,9], -75167866672272), ([4,6,10], -60315804693936), ([4,6,11], -38733932150496), ([4,6,12], -8898338534976), ([4,6,13], -17708305507200), ([4,6,14], -30192535296000), ([4,6,15], -27889758489600), ([4,6,16], -116742536870400), ([4,6,17], -122100648768000), ([4,6,18], -15245104089600), ([4,6,19], -164179561896000), ([4,6,20], -49604334897600), ([4,6,21], -237621164356800), ([4,6,22], -42553396401600), ([4,6,23], -127977674731200), ([4,7,9], -109573122104688), ([4,7,10], -100683555132336), ([4,7,11], -77103021801696), ([4,7,12], -45268767398976), ([4,7,13], -50017625750400), ([4,7,14], -58440746918400), ([4,7,15], -52076861491200), ([4,7,16], -136868531251200), ([4,7,17], -138165534528000), ([4,7,18], -29578289664000), ([4,7,19], -179110455720000), ([4,7,20], -65132936971200), ([4,7,21], -258406291550400), ([4,7,22], -57834725233600), ([4,7,23], -158489145259200), ([4,8,10], -115116215593104), ([4,8,11], -113747498716896), ([4,8,12], -73748502374976), ([4,8,13], -73415659363200), ([4,8,14], -76757079168000), ([4,8,15], -65311492377600), ([4,8,16], -145021460774400), ([4,8,17], -141236762688000), ([4,8,18], -31021766899200), ([4,8,19], -182380132468800), ([4,8,20], -70228813233600), ([4,8,21], -272236268203200), ([4,8,22], -78912012849600), ([4,8,23], -199433341598400), ([4,9,10], -57890288332800), ([4,9,11], -103700727567360), ([4,9,12], -104397218833248), ([4,9,13], -94879041139872), ([4,9,14], -92118166839072), ([4,9,15], -74570285943072), ([4,9,16], -79333044940800), ([4,9,17], -85104161856000), ([4,9,19], -61780090075200), ([4,9,20], -892293796800), ([4,9,21], -85170123460800), ([4,9,22], -42553396401600), ([4,9,23], -112883984337600), ([4,10,16], -79333044940800), ([4,10,17], -85104161856000), ([4,10,19], -61780090075200), ([4,10,20], -892293796800), ([4,10,21], -85170123460800), ([4,10,22], -42553396401600), ([4,10,23], -112883984337600), ([4,11,16], -79333044940800), ([4,11,17], -85104161856000), ([4,11,19], -61780090075200), ([4,11,20], -892293796800), ([4,11,21], -85170123460800), ([4,11,22], -42553396401600), ([4,11,23], -112883984337600), ([4,12,16], -79333044940800), ([4,12,17], -85104161856000), ([4,12,19], -61780090075200), ([4,12,20], -892293796800), ([4,12,21], -85170123460800), ([4,12,22], -42553396401600), ([4,12,23], -112883984337600), ([4,13,16], -79333044940800), ([4,13,17], -85104161856000), ([4,13,19], -61780090075200), ([4,13,20], -892293796800), ([4,13,21], -85170123460800), ([4,13,22], -42553396401600), ([4,13,23], -112883984337600), ([4,14,16], -79333044940800), ([4,14,17], -85104161856000), ([4,14,19], -61780090075200), ([4,14,20], -892293796800), ([4,14,21], -85170123460800), ([4,14,22], -42553396401600), ([4,14,23], -112883984337600), ([4,15,16], -79333044940800), ([4,15,17], -85104161856000), ([4,15,19], -61780090075200), ([4,15,20], -892293796800), ([4,15,21], -85170123460800), ([4,15,22], -42553396401600), ([4,15,23], -112883984337600), ([4,16,16], -79333044940800), ([4,16,17], -164437206796800), ([4,16,18], -79333044940800), ([4,16,19], -141113135016000), ([4,16,20], -80225338737600), ([4,16,21], -164503168401600), ([4,16,22], -42553396401600), ([4,16,23], -112883984337600), ([4,17,17], -85104161856000), ([4,17,18], -82780444857600), ([4,17,19], -142236817934400), ([4,17,20], -79025304657600), ([4,17,21], -162141275822400), ([4,17,22], -37905962404800), ([4,17,23], -107655621091200), ([4,18,19], -30890045037600), ([4,18,20], -446146898400), ([4,18,21], -42585061730400), ([4,18,22], -28952406117600), ([4,18,23], -56441992168800), ([4,19,20], 30890045037600), ([4,19,21], 46335067556400), ([4,19,22], 46428674241600), ([4,19,23], 69502601334600), ([4,20,20], 446146898400), ([4,20,21], 43254282078000), ([4,20,22], -858131752800), ([4,20,23], 57445822690200), ([4,21,21], 63877592595600), ([4,21,22], 90220193053200), ([4,21,23], 180479377146600), ([4,22,22], 27201980568000), ([4,22,23], 143486212476600), ([4,23,23], 126994482379800), ([5,5,6], -52396574620896), ([5,5,7], -30909789916896), ([5,5,8], -33983300745504), ([5,5,9], -30352902764976), ([5,5,10], -10173118860432), ([5,5,15], -737739072000), ([5,5,16], -52964510860800), ([5,5,17], -56153863180800), ([5,5,19], -75637412928000), ([5,5,20], -17142429427200), ([5,5,21], -108225807782400), ([5,5,22], -20850070348800), ([5,5,23], -3172449369600), ([5,6,6], -52396574620896), ([5,6,7], -141884135481792), ([5,6,8], -169685757964800), ([5,6,9], -157917344058144), ([5,6,10], -122885498175264), ([5,6,11], -91130506771392), ([5,6,12], -61294913155872), ([5,6,13], -70104880128096), ([5,6,14], -82589109916896), ([5,6,15], -81024072182496), ([5,6,16], -182437099881696), ([5,6,17], -185775288643296), ([5,6,18], -41443391400048), ([5,6,19], -178036884748800), ([5,6,20], -39656183217552), ([5,6,21], -221379417712728), ([5,6,22], 23870796355296), ([5,6,23], 40680006685308), ([5,7,7], -30909789916896), ([5,7,8], -64893090662400), ([5,7,9], -170835814786560), ([5,7,10], -141766463909664), ([5,7,11], -108012811718592), ([5,7,12], -76178557315872), ([5,7,13], -80927415667296), ([5,7,14], -89350536835296), ([5,7,15], -83724390480096), ([5,7,16], -181076309558496), ([5,7,17], -180353389699296), ([5,7,18], -45033184622448), ([5,7,19], -192967778572800), ([5,7,20], -65928177643152), ([5,7,21], -258279633434328), ([5,7,22], -12897317180704), ([5,7,23], -14004096634692), ([5,8,8], -33983300745504), ([5,8,9], -64336203510480), ([5,8,10], -159272635199040), ([5,8,11], -147730799462400), ([5,8,12], -107731803120480), ([5,8,13], -107398960108704), ([5,8,14], -110740379913504), ([5,8,15], -100032532195104), ([5,8,16], -192302749910304), ([5,8,17], -186498128687904), ([5,8,18], -48013417271952), ([5,8,19], -196237455321600), ([5,8,20], -69487298491248), ([5,8,21], -269804476965672), ([5,8,22], -30901093968096), ([5,8,23], -51490593291708), ([5,9,9], -30352902764976), ([5,9,10], -98416309958208), ([5,9,11], -134053630332336), ([5,9,12], -134750121598224), ([5,9,13], -125231943904848), ([5,9,14], -122471069604048), ([5,9,15], -105660927780048), ([5,9,16], -122983936096176), ([5,9,17], -126735129875376), ([5,9,18], -15176451382488), ([5,9,19], -75637412928000), ([5,9,20], -1965978044712), ([5,9,21], -85461130708668), ([5,9,22], 1827124499376), ([5,9,23], 30974566240998), ([5,10,10], -10173118860432), ([5,10,11], -10173118860432), ([5,10,12], -10173118860432), ([5,10,13], -10173118860432), ([5,10,14], -10173118860432), ([5,10,15], -10910857932432), ([5,10,16], -102804152191632), ([5,10,17], -106555345970832), ([5,10,18], -5086559430216), ([5,10,19], -75637412928000), ([5,10,20], -12055869996984), ([5,10,21], -100595968637076), ([5,10,22], -18352659405168), ([5,10,23], 8272309348386), ([5,11,15], -737739072000), ([5,11,16], -92631033331200), ([5,11,17], -96382227110400), ([5,11,19], -75637412928000), ([5,11,20], -17142429427200), ([5,11,21], -108225807782400), ([5,11,22], -28525778265600), ([5,11,23], -3172449369600), ([5,12,15], -737739072000), ([5,12,16], -92631033331200), ([5,12,17], -96382227110400), ([5,12,19], -75637412928000), ([5,12,20], -17142429427200), ([5,12,21], -108225807782400), ([5,12,22], -28525778265600), ([5,12,23], -3172449369600), ([5,13,15], -737739072000), ([5,13,16], -92631033331200), ([5,13,17], -96382227110400), ([5,13,19], -75637412928000), ([5,13,20], -17142429427200), ([5,13,21], -108225807782400), ([5,13,22], -28525778265600), ([5,13,23], -3172449369600), ([5,14,15], -737739072000), ([5,14,16], -92631033331200), ([5,14,17], -96382227110400), ([5,14,19], -75637412928000), ([5,14,20], -17142429427200), ([5,14,21], -108225807782400), ([5,14,22], -28525778265600), ([5,14,23], -3172449369600), ([5,15,15], -737739072000), ([5,15,16], -93368772403200), ([5,15,17], -97119966182400), ([5,15,18], -368869536000), ([5,15,19], -75637412928000), ([5,15,20], -16773559891200), ([5,15,21], -107672503478400), ([5,15,22], -27788039193600), ([5,15,23], -2342492913600), ([5,16,16], -92631033331200), ([5,16,17], -189013260441600), ([5,16,18], -85982039136000), ([5,16,19], -154970457868800), ([5,16,20], -89826480172800), ([5,16,21], -177585361430400), ([5,16,22], -15227789875200), ([5,16,23], 11787787569600), ([5,17,17], -96382227110400), ([5,17,18], -88419477484800), ([5,17,19], -156094140787200), ([5,17,20], -89636407660800), ([5,17,21], -176738411203200), ([5,17,22], -12600279014400), ([5,17,23], 14743737288000), ([5,18,19], -37818706464000), ([5,18,20], -8571214713600), ([5,18,21], -54112903891200), ([5,18,22], -21938597049600), ([5,18,23], -1586224684800), ([5,19,20], 37818706464000), ([5,19,21], 56728059696000), ([5,19,22], 60285997094400), ([5,19,23], 85092089544000), ([5,20,20], 8571214713600), ([5,20,21], 66969725961600), ([5,20,22], 8378194809600), ([5,20,23], 20871457790400), ([5,21,21], 81169355836800), ([5,21,22], 102755163772800), ([5,21,23], 124133370782400), ([5,22,22], 13174362432000), ([5,22,23], 17993607105600), ([5,23,23], 3569005540800), ([6,6,7], -58577770944000), ([6,6,8], -83305882598400), ([6,6,9], -75167866672272), ([6,6,10], -60315804693936), ([6,6,11], -38733932150496), ([6,6,12], -8898338534976), ([6,6,13], -17708305507200), ([6,6,14], -30192535296000), ([6,6,15], -27889758489600), ([6,6,16], -77076014400000), ([6,6,17], -77224850841600), ([6,6,18], -15245104089600), ([6,6,19], -102399471820800), ([6,6,20], -48712041100800), ([6,6,21], -152451040896000), ([6,6,22], -7675707916800), ([6,6,23], -15093690393600), ([6,7,7], -58577770944000), ([6,7,8], -141883653542400), ([6,7,9], -243318759720960), ([6,7,10], -219577130770272), ([6,7,11], -174414724896192), ([6,7,12], -112744876877952), ([6,7,13], -126303702201600), ([6,7,14], -147211053158400), ([6,7,15], -138544390924800), ([6,7,16], -232855794124800), ([6,7,17], -229092358387200), ([6,7,18], -74112279225600), ([6,7,19], -219729837465600), ([6,7,20], -83663798803200), ([6,7,21], -281753880777600), ([6,7,22], 27945026278400), ([6,7,23], 5201140996800), ([6,8,8], -83305882598400), ([6,8,9], -158473749270672), ([6,8,10], -258737902885440), ([6,8,11], -235787313465792), ([6,8,12], -165952723508352), ([6,8,13], -174429847468800), ([6,8,14], -190255497062400), ([6,8,15], -176507133465600), ([6,8,16], -265736835302400), ([6,8,17], -256891698201600), ([6,8,18], -87919812288000), ([6,8,19], -222999514214400), ([6,8,20], -76395619238400), ([6,8,21], -277037773689600), ([6,8,22], 31595850316800), ([6,8,23], -7923929731200), ([6,9,9], -75167866672272), ([6,9,10], -193373959699008), ([6,9,11], -217602526390128), ([6,9,12], -188463424040496), ([6,9,13], -187755213319344), ([6,9,14], -197478568807344), ([6,9,15], -177627911104944), ([6,9,16], -191910403542672), ([6,9,17], -192621081443472), ([6,9,18], -52829037425736), ([6,9,19], -102399471820800), ([6,9,20], -11128107764664), ([6,9,21], -96075140891796), ([6,9,22], 59816450838672), ([6,9,23], 69470159612706), ([6,10,10], -60315804693936), ([6,10,11], -99049736844432), ([6,10,12], -69214143228912), ([6,10,13], -78024110201136), ([6,10,14], -90508339989936), ([6,10,15], -88205563183536), ([6,10,16], -177058341564336), ([6,10,17], -177769019465136), ([6,10,18], -45403006436568), ([6,10,19], -102399471820800), ([6,10,20], -18554138753832), ([6,10,21], -107214187375548), ([6,10,22], 44964388860336), ([6,10,23], 52761589887078), ([6,11,11], -38733932150496), ([6,11,12], -47632270685472), ([6,11,13], -56442237657696), ([6,11,14], -68926467446496), ([6,11,15], -66623690640096), ([6,11,16], -155476469020896), ([6,11,17], -156187146921696), ([6,11,18], -34612070164848), ([6,11,19], -102399471820800), ([6,11,20], -29345075025552), ([6,11,21], -123400591783128), ([6,11,22], 23382516316896), ([6,11,23], 28481983275708), ([6,12,12], -8898338534976), ([6,12,13], -26606644042176), ([6,12,14], -39090873830976), ([6,12,15], -36788097024576), ([6,12,16], -125640875405376), ([6,12,17], -126351553306176), ([6,12,18], -19694273357088), ([6,12,19], -102399471820800), ([6,12,20], -44262871833312), ([6,12,21], -145777286994768), ([6,12,22], -6453077298624), ([6,12,23], -5083059541752), ([6,13,13], -17708305507200), ([6,13,14], -47900840803200), ([6,13,15], -45598063996800), ([6,13,16], -134450842377600), ([6,13,17], -135161520278400), ([6,13,18], -24099256843200), ([6,13,19], -102399471820800), ([6,13,20], -39857888347200), ([6,13,21], -139169811765600), ([6,13,22], 2356889673600), ([6,13,23], 4828153302000), ([6,14,14], -30192535296000), ([6,14,15], -58082293785600), ([6,14,16], -146935072166400), ([6,14,17], -147645750067200), ([6,14,18], -30341371737600), ([6,14,19], -102399471820800), ([6,14,20], -33615773452800), ([6,14,21], -129806639424000), ([6,14,22], 14841119462400), ([6,14,23], 18872911814400), ([6,15,15], -27889758489600), ([6,15,16], -144632295360000), ([6,15,17], -145342973260800), ([6,15,18], -29189983334400), ([6,15,19], -102399471820800), ([6,15,20], -34767161856000), ([6,15,21], -131533722028800), ([6,15,22], 12538342656000), ([6,15,23], 16282287907200), ([6,16,16], -116742536870400), ([6,16,17], -234195751641600), ([6,16,18], -113282894995200), ([6,16,19], -181732516761600), ([6,16,20], -109340340076800), ([6,16,21], -203726966889600), ([6,16,22], 22058076096000), ([6,16,23], 26991988027200), ([6,17,17], -117453214771200), ([6,17,18], -114200075404800), ([6,17,19], -182856199680000), ([6,17,20], -110670525504000), ([6,17,21], -205160403571200), ([6,17,22], 21645071078400), ([6,17,23], 26527357382400), ([6,18,18], -7622552044800), ([6,18,19], -51199735910400), ([6,18,20], -16733468505600), ([6,18,21], -64791692380800), ([6,18,22], -106311744000), ([6,18,23], 9603896904000), ([6,19,20], 51199735910400), ([6,19,21], 76799603865600), ([6,19,22], 87048055987200), ([6,19,23], 115199405798400), ([6,20,20], 24356020550400), ([6,20,21], 112759551273600), ([6,20,22], 33360625267200), ([6,20,23], 62347891435200), ([6,21,21], 114338280672000), ([6,21,22], 137099625062400), ([6,21,23], 182827688803200), ([6,22,23], 15093690393600), ([6,23,23], 16980401692800), ([7,7,9], -109573122104688), ([7,7,10], -100683555132336), ([7,7,11], -77103021801696), ([7,7,12], -45268767398976), ([7,7,13], -50017625750400), ([7,7,14], -58440746918400), ([7,7,15], -52076861491200), ([7,7,16], -97202008780800), ([7,7,17], -93289736601600), ([7,7,18], -29578289664000), ([7,7,19], -117330365644800), ([7,7,20], -64240643174400), ([7,7,21], -173236168089600), ([7,7,22], -22957036748800), ([7,7,23], -45605160921600), ([7,8,9], -109573122104688), ([7,8,10], -215799770725440), ([7,8,11], -190850520518592), ([7,8,12], -119017269773952), ([7,8,13], -123433285113600), ([7,8,14], -135197826086400), ([7,8,15], -117388353868800), ([7,8,16], -202556947084800), ([7,8,17], -189650701363200), ([7,8,18], -60600056563200), ([7,8,19], -237930408038400), ([7,8,20], -133577162611200), ([7,8,21], -360302312832000), ([7,8,22], -66991361113600), ([7,8,23], -132154518182400), ([7,9,9], -109573122104688), ([7,9,10], -268146965569824), ([7,9,11], -290376871473744), ([7,9,12], -259239108336912), ([7,9,13], -254469788994960), ([7,9,14], -260132035862160), ([7,9,15], -236220269538960), ([7,9,16], -246441653355888), ([7,9,17], -243091222635888), ([7,9,18], -84364850716344), ([7,9,19], -117330365644800), ([7,9,20], -9454082122056), ([7,9,21], -91056326511084), ([7,9,22], 78940377439088), ([7,9,23], 77664601446174), ([7,10,10], -100683555132336), ([7,10,11], -177786576934032), ([7,10,12], -145952322531312), ([7,10,13], -150701180882736), ([7,10,14], -159124302050736), ([7,10,15], -152760416623536), ([7,10,16], -237552086383536), ([7,10,17], -234201655663536), ([7,10,18], -79920067230168), ([7,10,19], -117330365644800), ([7,10,20], -13898865608232), ([7,10,21], -97723501740348), ([7,10,22], 70050810466736), ([7,10,23], 67663838602278), ([7,11,11], -77103021801696), ([7,11,12], -122371789200672), ([7,11,13], -127120647552096), ([7,11,14], -135543768720096), ([7,11,15], -129179883292896), ([7,11,16], -213971553052896), ([7,11,17], -210621122332896), ([7,11,18], -68129800564848), ([7,11,19], -117330365644800), ([7,11,20], -25689132273552), ([7,11,21], -115408901738328), ([7,11,22], 46470277136096), ([7,11,23], 41135738605308), ([7,12,12], -45268767398976), ([7,12,13], -95286393149376), ([7,12,14], -103709514317376), ([7,12,15], -97345628890176), ([7,12,16], -182137298650176), ([7,12,17], -178786867930176), ([7,12,18], -52212673363488), ([7,12,19], -117330365644800), ([7,12,20], -41606259474912), ([7,12,21], -139284592540368), ([7,12,22], 14636022733376), ([7,12,23], 5322202402248), ([7,13,13], -50017625750400), ([7,13,14], -108458372668800), ([7,13,15], -102094487241600), ([7,13,16], -186886157001600), ([7,13,17], -183535726281600), ([7,13,18], -54587102539200), ([7,13,19], -117330365644800), ([7,13,20], -39231830299200), ([7,13,21], -135722948776800), ([7,13,22], 19384881084800), ([7,13,23], 10664668047600), ([7,14,14], -58440746918400), ([7,14,15], -110517608409600), ([7,14,16], -195309278169600), ([7,14,17], -191958847449600), ([7,14,18], -58798663123200), ([7,14,19], -117330365644800), ([7,14,20], -35020269715200), ([7,14,21], -129405607900800), ([7,14,22], 27808002252800), ([7,14,23], 20140679361600), ([7,15,15], -52076861491200), ([7,15,16], -188945392742400), ([7,15,17], -185594962022400), ([7,15,18], -55616720409600), ([7,15,19], -117330365644800), ([7,15,20], -38202212428800), ([7,15,21], -134178521971200), ([7,15,22], 21444116825600), ([7,15,23], 12981308256000), ([7,16,16], -136868531251200), ([7,16,17], -270386631782400), ([7,16,18], -137679077760000), ([7,16,19], -196663410585600), ([7,16,20], -114805944960000), ([7,16,21], -209417598297600), ([7,16,22], 26902741644800), ([7,16,23], 19122261177600), ([7,17,17], -133518100531200), ([7,17,18], -136565703859200), ([7,17,19], -197787093504000), ([7,17,20], -118166684697600), ([7,17,21], -213896866444800), ([7,17,22], 22428628006400), ([7,17,23], 14088883334400), ([7,18,18], -14789144832000), ([7,18,19], -58665182822400), ([7,18,20], -17331176755200), ([7,18,21], -64434366796800), ([7,18,22], 6586209414400), ([7,18,23], 10472995411200), ([7,19,20], 58665182822400), ([7,19,21], 87997774233600), ([7,19,22], 101978949811200), ([7,19,23], 131996661350400), ([7,20,20], 32120321587200), ([7,20,21], 134798566425600), ([7,20,22], 56529891756800), ([7,20,23], 95073304032000), ([7,21,21], 129927126067200), ([7,21,22], 169345748880000), ([7,21,23], 229094559792000), ([7,22,22], 15281328832000), ([7,22,23], 62796655857600), ([7,23,23], 51305806036800), ([8,8,10], -115116215593104), ([8,8,11], -113747498716896), ([8,8,12], -73748502374976), ([8,8,13], -73415659363200), ([8,8,14], -76757079168000), ([8,8,15], -65311492377600), ([8,8,16], -105354938304000), ([8,8,17], -96360964761600), ([8,8,18], -31021766899200), ([8,8,19], -120600042393600), ([8,8,20], -69336519436800), ([8,8,21], -187066144742400), ([8,8,22], -44034324364800), ([8,8,23], -86549357260800), ([8,9,10], -173006503925904), ([8,9,11], -217448226284256), ([8,9,12], -178145721208224), ([8,9,13], -168294700503072), ([8,9,14], -168875246007072), ([8,9,15], -139881778320672), ([8,9,16], -145021460774400), ([8,9,17], -136589328691200), ([8,9,18], -31021766899200), ([8,9,19], -120600042393600), ([8,9,20], -69336519436800), ([8,9,21], -187066144742400), ([8,9,22], -51710032281600), ([8,9,23], -86549357260800), ([8,10,10], -115116215593104), ([8,10,11], -228863714310000), ([8,10,12], -188864717968080), ([8,10,13], -188531874956304), ([8,10,14], -191873294761104), ([8,10,15], -180427707970704), ([8,10,16], -260137676367504), ([8,10,17], -251705544284304), ([8,10,18], -88579874695752), ([8,10,19], -120600042393600), ([8,10,20], -11778411640248), ([8,10,21], -100728983047572), ([8,10,22], 63406183311504), ([8,10,23], 42956385281442), ([8,11,11], -113747498716896), ([8,11,12], -187496001091872), ([8,11,13], -187163158080096), ([8,11,14], -190504577884896), ([8,11,15], -179058991094496), ([8,11,16], -258768959491296), ([8,11,17], -250336827408096), ([8,11,18], -87895516257648), ([8,11,19], -120600042393600), ([8,11,20], -12462770078352), ([8,11,21], -101755520704728), ([8,11,22], 62037466435296), ([8,11,23], 41416578795708), ([8,12,12], -73748502374976), ([8,12,13], -147164161738176), ([8,12,14], -150505581542976), ([8,12,15], -139059994752576), ([8,12,16], -218769963149376), ([8,12,17], -210337831066176), ([8,12,18], -67896018086688), ([8,12,19], -120600042393600), ([8,12,20], -32462268249312), ([8,12,21], -131754767961168), ([8,12,22], 22038470093376), ([8,12,23], -3582292088952), ([8,13,13], -73415659363200), ([8,13,14], -150172738531200), ([8,13,15], -138727151740800), ([8,13,16], -218437120137600), ([8,13,17], -210004988054400), ([8,13,18], -67729596580800), ([8,13,19], -120600042393600), ([8,13,20], -32628689755200), ([8,13,21], -132004400220000), ([8,13,22], 21705627081600), ([8,13,23], -3956740477200), ([8,14,14], -76757079168000), ([8,14,15], -142068571545600), ([8,14,16], -221778539942400), ([8,14,17], -213346407859200), ([8,14,18], -69400306483200), ([8,14,19], -120600042393600), ([8,14,20], -30957979852800), ([8,14,21], -129498335366400), ([8,14,22], 25047046886400), ([8,14,23], -197643196800), ([8,15,15], -65311492377600), ([8,15,16], -210332953152000), ([8,15,17], -201900821068800), ([8,15,18], -63677513088000), ([8,15,19], -120600042393600), ([8,15,20], -36680773248000), ([8,15,21], -138082525459200), ([8,15,22], 13601460096000), ([8,15,23], -13073928336000), ([8,16,16], -145021460774400), ([8,16,17], -281610789465600), ([8,16,18], -143199019756800), ([8,16,19], -199933087334400), ([8,16,20], -115825356460800), ([8,16,21], -217132877808000), ([8,16,22], 13978383552000), ([8,16,23], -12649889448000), ([8,17,17], -136589328691200), ([8,17,18], -139544795174400), ([8,17,19], -201056770252800), ([8,17,20], -121726946880000), ([8,17,21], -225423421977600), ([8,17,22], 4422568550400), ([8,17,23], -23400181324800), ([8,18,18], -15510883449600), ([8,18,19], -60300021196800), ([8,18,20], -19157376268800), ([8,18,21], -70266747196800), ([8,18,22], -2508957158400), ([8,18,23], -8375190868800), ([8,19,20], 60300021196800), ([8,19,21], 90450031795200), ([8,19,22], 105248626560000), ([8,19,23], 135675047692800), ([8,20,20], 34668259718400), ([8,20,21], 145535461948800), ([8,20,22], 72164411827200), ([8,20,23], 121278262996800), ([8,21,21], 140299608556800), ([8,21,22], 198983691244800), ([8,21,23], 275361430780800), ([8,22,22], 36358616448000), ([8,22,23], 127452800764800), ([8,23,23], 97368026918400), ([9,9,10], -57890288332800), ([9,9,11], -103700727567360), ([9,9,12], -104397218833248), ([9,9,13], -94879041139872), ([9,9,14], -92118166839072), ([9,9,15], -74570285943072), ([9,9,16], -39666522470400), ([9,9,17], -40228363929600), ([9,9,22], -7675707916800), ([9,10,10], -57890288332800), ([9,10,11], -161591015900160), ([9,10,12], -162287507166048), ([9,10,13], -152769329472672), ([9,10,14], -150008455171872), ([9,10,15], -132460574275872), ([9,10,16], -137223333273600), ([9,10,17], -138347016192000), ([9,10,18], -28945144166400), ([9,10,20], 28945144166400), ([9,10,21], 43417716249600), ([9,10,22], 42538872499200), ([9,10,23], 65126574374400), ([9,11,11], -103700727567360), ([9,11,12], -208097946400608), ([9,11,13], -198579768707232), ([9,11,14], -195818894406432), ([9,11,15], -178271013510432), ([9,11,16], -183033772508160), ([9,11,17], -184157455426560), ([9,11,18], -51850363783680), ([9,11,20], 51850363783680), ([9,11,21], 77775545675520), ([9,11,22], 88349311733760), ([9,11,23], 116663318513280), ([9,12,12], -104397218833248), ([9,12,13], -199276259973120), ([9,12,14], -196515385672320), ([9,12,15], -178967504776320), ([9,12,16], -183730263774048), ([9,12,17], -184853946692448), ([9,12,18], -52198609416624), ([9,12,20], 52198609416624), ([9,12,21], 78297914124936), ([9,12,22], 89045802999648), ([9,12,23], 117446871187404), ([9,13,13], -94879041139872), ([9,13,14], -186997207978944), ([9,13,15], -169449327082944), ([9,13,16], -174212086080672), ([9,13,17], -175335768999072), ([9,13,18], -47439520569936), ([9,13,20], 47439520569936), ([9,13,21], 71159280854904), ([9,13,22], 79527625306272), ([9,13,23], 106738921282356), ([9,14,14], -92118166839072), ([9,14,15], -166688452782144), ([9,14,16], -171451211779872), ([9,14,17], -172574894698272), ([9,14,18], -46059083419536), ([9,14,20], 46059083419536), ([9,14,21], 69088625129304), ([9,14,22], 76766751005472), ([9,14,23], 103632937693956), ([9,15,15], -74570285943072), ([9,15,16], -153903330883872), ([9,15,17], -155027013802272), ([9,15,18], -37285142971536), ([9,15,20], 37285142971536), ([9,15,21], 55927714457304), ([9,15,22], 59218870109472), ([9,15,23], 83891571685956), ([9,16,16], -79333044940800), ([9,16,17], -159789772800000), ([9,16,18], -79333044940800), ([9,16,19], -79333044940800), ([9,16,20], -79333044940800), ([9,16,21], -79333044940800), ([9,16,22], -15351415833600), ([9,17,17], -80456727859200), ([9,17,18], -80456727859200), ([9,17,19], -80456727859200), ([9,17,20], -80456727859200), ([9,17,21], -80456727859200), ([9,17,22], -15351415833600), ([9,18,22], -15351415833600), ([9,19,22], -15351415833600), ([9,20,22], -15351415833600), ([9,21,22], -15351415833600), ([10,10,16], -39666522470400), ([10,10,17], -40228363929600), ([10,10,22], -7675707916800), ([10,11,16], -79333044940800), ([10,11,17], -80456727859200), ([10,11,22], -15351415833600), ([10,12,16], -79333044940800), ([10,12,17], -80456727859200), ([10,12,22], -15351415833600), ([10,13,16], -79333044940800), ([10,13,17], -80456727859200), ([10,13,22], -15351415833600), ([10,14,16], -79333044940800), ([10,14,17], -80456727859200), ([10,14,22], -15351415833600), ([10,15,16], -79333044940800), ([10,15,17], -80456727859200), ([10,15,22], -15351415833600), ([10,16,16], -79333044940800), ([10,16,17], -159789772800000), ([10,16,18], -79333044940800), ([10,16,19], -79333044940800), ([10,16,20], -79333044940800), ([10,16,21], -79333044940800), ([10,16,22], -15351415833600), ([10,17,17], -80456727859200), ([10,17,18], -80456727859200), ([10,17,19], -80456727859200), ([10,17,20], -80456727859200), ([10,17,21], -80456727859200), ([10,17,22], -15351415833600), ([10,18,22], -15351415833600), ([10,19,22], -15351415833600), ([10,20,22], -15351415833600), ([10,21,22], -15351415833600), ([11,11,16], -39666522470400), ([11,11,17], -40228363929600), ([11,11,22], -7675707916800), ([11,12,16], -79333044940800), ([11,12,17], -80456727859200), ([11,12,22], -15351415833600), ([11,13,16], -79333044940800), ([11,13,17], -80456727859200), ([11,13,22], -15351415833600), ([11,14,16], -79333044940800), ([11,14,17], -80456727859200), ([11,14,22], -15351415833600), ([11,15,16], -79333044940800), ([11,15,17], -80456727859200), ([11,15,22], -15351415833600), ([11,16,16], -79333044940800), ([11,16,17], -159789772800000), ([11,16,18], -79333044940800), ([11,16,19], -79333044940800), ([11,16,20], -79333044940800), ([11,16,21], -79333044940800), ([11,16,22], -15351415833600), ([11,17,17], -80456727859200), ([11,17,18], -80456727859200), ([11,17,19], -80456727859200), ([11,17,20], -80456727859200), ([11,17,21], -80456727859200), ([11,17,22], -15351415833600), ([11,18,22], -15351415833600), ([11,19,22], -15351415833600), ([11,20,22], -15351415833600), ([11,21,22], -15351415833600), ([12,12,16], -39666522470400), ([12,12,17], -40228363929600), ([12,12,22], -7675707916800), ([12,13,16], -79333044940800), ([12,13,17], -80456727859200), ([12,13,22], -15351415833600), ([12,14,16], -79333044940800), ([12,14,17], -80456727859200), ([12,14,22], -15351415833600), ([12,15,16], -79333044940800), ([12,15,17], -80456727859200), ([12,15,22], -15351415833600), ([12,16,16], -79333044940800), ([12,16,17], -159789772800000), ([12,16,18], -79333044940800), ([12,16,19], -79333044940800), ([12,16,20], -79333044940800), ([12,16,21], -79333044940800), ([12,16,22], -15351415833600), ([12,17,17], -80456727859200), ([12,17,18], -80456727859200), ([12,17,19], -80456727859200), ([12,17,20], -80456727859200), ([12,17,21], -80456727859200), ([12,17,22], -15351415833600), ([12,18,22], -15351415833600), ([12,19,22], -15351415833600), ([12,20,22], -15351415833600), ([12,21,22], -15351415833600), ([13,13,16], -39666522470400), ([13,13,17], -40228363929600), ([13,13,22], -7675707916800), ([13,14,16], -79333044940800), ([13,14,17], -80456727859200), ([13,14,22], -15351415833600), ([13,15,16], -79333044940800), ([13,15,17], -80456727859200), ([13,15,22], -15351415833600), ([13,16,16], -79333044940800), ([13,16,17], -159789772800000), ([13,16,18], -79333044940800), ([13,16,19], -79333044940800), ([13,16,20], -79333044940800), ([13,16,21], -79333044940800), ([13,16,22], -15351415833600), ([13,17,17], -80456727859200), ([13,17,18], -80456727859200), ([13,17,19], -80456727859200), ([13,17,20], -80456727859200), ([13,17,21], -80456727859200), ([13,17,22], -15351415833600), ([13,18,22], -15351415833600), ([13,19,22], -15351415833600), ([13,20,22], -15351415833600), ([13,21,22], -15351415833600), ([14,14,16], -39666522470400), ([14,14,17], -40228363929600), ([14,14,22], -7675707916800), ([14,15,16], -79333044940800), ([14,15,17], -80456727859200), ([14,15,22], -15351415833600), ([14,16,16], -79333044940800), ([14,16,17], -159789772800000), ([14,16,18], -79333044940800), ([14,16,19], -79333044940800), ([14,16,20], -79333044940800), ([14,16,21], -79333044940800), ([14,16,22], -15351415833600), ([14,17,17], -80456727859200), ([14,17,18], -80456727859200), ([14,17,19], -80456727859200), ([14,17,20], -80456727859200), ([14,17,21], -80456727859200), ([14,17,22], -15351415833600), ([14,18,22], -15351415833600), ([14,19,22], -15351415833600), ([14,20,22], -15351415833600), ([14,21,22], -15351415833600), ([15,15,16], -39666522470400), ([15,15,17], -40228363929600), ([15,15,22], -7675707916800), ([15,16,16], -79333044940800), ([15,16,17], -159789772800000), ([15,16,18], -79333044940800), ([15,16,19], -79333044940800), ([15,16,20], -79333044940800), ([15,16,21], -79333044940800), ([15,16,22], -15351415833600), ([15,17,17], -80456727859200), ([15,17,18], -80456727859200), ([15,17,19], -80456727859200), ([15,17,20], -80456727859200), ([15,17,21], -80456727859200), ([15,17,22], -15351415833600), ([15,18,22], -15351415833600), ([15,19,22], -15351415833600), ([15,20,22], -15351415833600), ([15,21,22], -15351415833600), ([16,16,16], -39666522470400), ([16,16,17], -119561408870400), ([16,16,18], -79333044940800), ([16,16,19], -79333044940800), ([16,16,20], -79333044940800), ([16,16,21], -79333044940800), ([16,16,22], -7675707916800), ([16,17,17], -120123250329600), ([16,17,18], -159789772800000), ([16,17,19], -159789772800000), ([16,17,20], -159789772800000), ([16,17,21], -159789772800000), ([16,17,22], -15351415833600), ([16,18,18], -39666522470400), ([16,18,19], -79333044940800), ([16,18,20], -79333044940800), ([16,18,21], -79333044940800), ([16,18,22], -15351415833600), ([16,19,19], -39666522470400), ([16,19,20], -79333044940800), ([16,19,21], -79333044940800), ([16,19,22], -15351415833600), ([16,20,20], -39666522470400), ([16,20,21], -79333044940800), ([16,20,22], -15351415833600), ([16,20,23], 158666089881600), ([16,21,21], -39666522470400), ([16,21,22], -15351415833600), ([16,21,23], 158666089881600), ([16,22,23], 158666089881600), ([16,23,23], 158666089881600), ([17,17,17], -40228363929600), ([17,17,18], -80456727859200), ([17,17,19], -80456727859200), ([17,17,20], -80456727859200), ([17,17,21], -80456727859200), ([17,17,22], -7675707916800), ([17,18,18], -40228363929600), ([17,18,19], -80456727859200), ([17,18,20], -80456727859200), ([17,18,21], -80456727859200), ([17,18,22], -15351415833600), ([17,19,19], -40228363929600), ([17,19,20], -80456727859200), ([17,19,21], -80456727859200), ([17,19,22], -15351415833600), ([17,20,20], -40228363929600), ([17,20,21], -80456727859200), ([17,20,22], -15351415833600), ([17,20,23], 160913455718400), ([17,21,21], -40228363929600), ([17,21,22], -15351415833600), ([17,21,23], 160913455718400), ([17,22,23], 160913455718400), ([17,23,23], 160913455718400), ([18,18,22], -7675707916800), ([18,19,22], -15351415833600), ([18,20,22], -15351415833600), ([18,21,22], -15351415833600), ([19,19,22], -7675707916800), ([19,20,22], -15351415833600), ([19,21,22], -15351415833600), ([20,20,22], -7675707916800), ([20,21,22], -15351415833600), ([20,22,23], 30702831667200), ([21,21,22], -7675707916800), ([21,22,23], 30702831667200), ([22,22,23], 30702831667200), ([22,23,23], 30702831667200)]
theorem block003_data : block003 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (39666522470400 : Int) atom0049) (SparsePolynomial.scale (40228363929600 : Int) atom0050)) (SparsePolynomial.merge (SparsePolynomial.scale (7675707916800 : Int) atom0051) (SparsePolynomial.merge (SparsePolynomial.scale (5379374246400 : Int) atom0052) (SparsePolynomial.scale (3650680857600 : Int) atom0053)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1743512601600 : Int) atom0054) (SparsePolynomial.scale (2519588332800 : Int) atom0055)) (SparsePolynomial.merge (SparsePolynomial.scale (3501643068000 : Int) atom0056) (SparsePolynomial.merge (SparsePolynomial.scale (3295664064000 : Int) atom0057) (SparsePolynomial.scale (547889680206 : Int) atom0058))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (290464624800 : Int) atom0059) (SparsePolynomial.scale (3861255629700 : Int) atom0060)) (SparsePolynomial.merge (SparsePolynomial.scale (55768362300 : Int) atom0061) (SparsePolynomial.merge (SparsePolynomial.scale (5323132716300 : Int) atom0062) (SparsePolynomial.scale (1700123785500 : Int) atom0063)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (7055249021100 : Int) atom0064) (SparsePolynomial.scale (3274785913806 : Int) atom0065)) (SparsePolynomial.merge (SparsePolynomial.scale (1931861869806 : Int) atom0066) (SparsePolynomial.merge (SparsePolynomial.scale (2123956296594 : Int) atom0067) (SparsePolynomial.scale (1897056422811 : Int) atom0068)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (635819928777 : Int) atom0069) (SparsePolynomial.scale (46108692000 : Int) atom0070)) (SparsePolynomial.merge (SparsePolynomial.scale (831124274400 : Int) atom0071) (SparsePolynomial.merge (SparsePolynomial.scale (995343703200 : Int) atom0072) (SparsePolynomial.scale (4727338308000 : Int) atom0073)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1071401839200 : Int) atom0074) (SparsePolynomial.scale (6764112986400 : Int) atom0075)) (SparsePolynomial.merge (SparsePolynomial.scale (823397652000 : Int) atom0076) (SparsePolynomial.merge (SparsePolynomial.scale (198278085600 : Int) atom0077) (SparsePolynomial.scale (3661110684000 : Int) atom0078))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (5206617662400 : Int) atom0079) (SparsePolynomial.scale (4697991667017 : Int) atom0080)) (SparsePolynomial.merge (SparsePolynomial.scale (3769737793371 : Int) atom0081) (SparsePolynomial.merge (SparsePolynomial.scale (2420870759406 : Int) atom0082) (SparsePolynomial.scale (556146158436 : Int) atom0083)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1106769094200 : Int) atom0084) (SparsePolynomial.scale (1887033456000 : Int) atom0085)) (SparsePolynomial.merge (SparsePolynomial.scale (1743109905600 : Int) atom0086) (SparsePolynomial.merge (SparsePolynomial.scale (2338093245600 : Int) atom0087) (SparsePolynomial.scale (2312280432000 : Int) atom0088))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (952819005600 : Int) atom0089) (SparsePolynomial.scale (6399966988800 : Int) atom0090)) (SparsePolynomial.merge (SparsePolynomial.scale (3044502568800 : Int) atom0091) (SparsePolynomial.merge (SparsePolynomial.scale (9528190056000 : Int) atom0092) (SparsePolynomial.scale (943355649600 : Int) atom0093)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (6848320131543 : Int) atom0094) (SparsePolynomial.scale (6292722195771 : Int) atom0095)) (SparsePolynomial.merge (SparsePolynomial.scale (4818938862606 : Int) atom0096) (SparsePolynomial.merge (SparsePolynomial.scale (2829297962436 : Int) atom0097) (SparsePolynomial.scale (3126101609400 : Int) atom0098))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3652546682400 : Int) atom0099) (SparsePolynomial.scale (3254803843200 : Int) atom0100)) (SparsePolynomial.merge (SparsePolynomial.scale (3595967894400 : Int) atom0101) (SparsePolynomial.merge (SparsePolynomial.scale (3316335792000 : Int) atom0102) (SparsePolynomial.scale (1848643104000 : Int) atom0103)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (7333147852800 : Int) atom0104) (SparsePolynomial.scale (4015040198400 : Int) atom0105)) (SparsePolynomial.merge (SparsePolynomial.scale (10827260505600 : Int) atom0106) (SparsePolynomial.merge (SparsePolynomial.scale (955083052000 : Int) atom0107) (SparsePolynomial.scale (2850322557600 : Int) atom0108)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (7194763474569 : Int) atom0109) (SparsePolynomial.scale (7109218669806 : Int) atom0110)) (SparsePolynomial.merge (SparsePolynomial.scale (4609281398436 : Int) atom0111) (SparsePolynomial.merge (SparsePolynomial.scale (4588478710200 : Int) atom0112) (SparsePolynomial.scale (4797317448000 : Int) atom0113)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (4081968273600 : Int) atom0114) (SparsePolynomial.scale (4105525989600 : Int) atom0115)) (SparsePolynomial.merge (SparsePolynomial.scale (3508287552000 : Int) atom0116) (SparsePolynomial.merge (SparsePolynomial.scale (1938860431200 : Int) atom0117) (SparsePolynomial.scale (7537502649600 : Int) atom0118))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (4333532464800 : Int) atom0119) (SparsePolynomial.scale (11691634046400 : Int) atom0120)) (SparsePolynomial.merge (SparsePolynomial.scale (2272413528000 : Int) atom0121) (SparsePolynomial.merge (SparsePolynomial.scale (5409334828800 : Int) atom0122) (SparsePolynomial.scale (3618143020800 : Int) atom0123)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (6481295472960 : Int) atom0124) (SparsePolynomial.scale (6524826177078 : Int) atom0125)) (SparsePolynomial.merge (SparsePolynomial.scale (5929940071242 : Int) atom0126) (SparsePolynomial.merge (SparsePolynomial.scale (5757385427442 : Int) atom0127) (SparsePolynomial.scale (4660642871442 : Int) atom0128)))))))) := by decide +kernel
theorem block003_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block003 := by
  rw [block003_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0049_nonneg g hg hA hB) (atom0050_nonneg g hg hA hB)) (add_nonneg (atom0051_nonneg g hg hA hB) (add_nonneg (atom0052_nonneg g hg hA hB) (atom0053_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0054_nonneg g hg hA hB) (atom0055_nonneg g hg hA hB)) (add_nonneg (atom0056_nonneg g hg hA hB) (add_nonneg (atom0057_nonneg g hg hA hB) (atom0058_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0059_nonneg g hg hA hB) (atom0060_nonneg g hg hA hB)) (add_nonneg (atom0061_nonneg g hg hA hB) (add_nonneg (atom0062_nonneg g hg hA hB) (atom0063_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0064_nonneg g hg hA hB) (atom0065_nonneg g hg hA hB)) (add_nonneg (atom0066_nonneg g hg hA hB) (add_nonneg (atom0067_nonneg g hg hA hB) (atom0068_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0069_nonneg g hg hA hB) (atom0070_nonneg g hg hA hB)) (add_nonneg (atom0071_nonneg g hg hA hB) (add_nonneg (atom0072_nonneg g hg hA hB) (atom0073_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0074_nonneg g hg hA hB) (atom0075_nonneg g hg hA hB)) (add_nonneg (atom0076_nonneg g hg hA hB) (add_nonneg (atom0077_nonneg g hg hA hB) (atom0078_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0079_nonneg g hg hA hB) (atom0080_nonneg g hg hA hB)) (add_nonneg (atom0081_nonneg g hg hA hB) (add_nonneg (atom0082_nonneg g hg hA hB) (atom0083_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0084_nonneg g hg hA hB) (atom0085_nonneg g hg hA hB)) (add_nonneg (atom0086_nonneg g hg hA hB) (add_nonneg (atom0087_nonneg g hg hA hB) (atom0088_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0089_nonneg g hg hA hB) (atom0090_nonneg g hg hA hB)) (add_nonneg (atom0091_nonneg g hg hA hB) (add_nonneg (atom0092_nonneg g hg hA hB) (atom0093_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0094_nonneg g hg hA hB) (atom0095_nonneg g hg hA hB)) (add_nonneg (atom0096_nonneg g hg hA hB) (add_nonneg (atom0097_nonneg g hg hA hB) (atom0098_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0099_nonneg g hg hA hB) (atom0100_nonneg g hg hA hB)) (add_nonneg (atom0101_nonneg g hg hA hB) (add_nonneg (atom0102_nonneg g hg hA hB) (atom0103_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0104_nonneg g hg hA hB) (atom0105_nonneg g hg hA hB)) (add_nonneg (atom0106_nonneg g hg hA hB) (add_nonneg (atom0107_nonneg g hg hA hB) (atom0108_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0109_nonneg g hg hA hB) (atom0110_nonneg g hg hA hB)) (add_nonneg (atom0111_nonneg g hg hA hB) (add_nonneg (atom0112_nonneg g hg hA hB) (atom0113_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0114_nonneg g hg hA hB) (atom0115_nonneg g hg hA hB)) (add_nonneg (atom0116_nonneg g hg hA hB) (add_nonneg (atom0117_nonneg g hg hA hB) (atom0118_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0119_nonneg g hg hA hB) (atom0120_nonneg g hg hA hB)) (add_nonneg (atom0121_nonneg g hg hA hB) (add_nonneg (atom0122_nonneg g hg hA hB) (atom0123_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0124_nonneg g hg hA hB) (atom0125_nonneg g hg hA hB)) (add_nonneg (atom0126_nonneg g hg hA hB) (add_nonneg (atom0127_nonneg g hg hA hB) (atom0128_nonneg g hg hA hB))))))))

end APPT.Finite24
