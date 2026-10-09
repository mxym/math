import APPT.Finite12Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def atom0000 : SparsePolynomial.Poly := [([0,0,6], 1)]
theorem eval_atom0000 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0000 = ((g 0) * (g 0) * (g 6)) := by
  norm_num [atom0000, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0000_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14208 : Int) atom0000) := by
  rw [SparsePolynomial.eval_scale, eval_atom0000]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 0) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0001 : SparsePolynomial.Poly := [([0,0,7], 1)]
theorem eval_atom0001 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0001 = ((g 0) * (g 0) * (g 7)) := by
  norm_num [atom0001, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0001_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10944 : Int) atom0001) := by
  rw [SparsePolynomial.eval_scale, eval_atom0001]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 0) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0002 : SparsePolynomial.Poly := [([0,0,8], 1)]
theorem eval_atom0002 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0002 = ((g 0) * (g 0) * (g 8)) := by
  norm_num [atom0002, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0002_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7680 : Int) atom0002) := by
  rw [SparsePolynomial.eval_scale, eval_atom0002]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 0) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0003 : SparsePolynomial.Poly := [([0,0,9], 1)]
theorem eval_atom0003 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0003 = ((g 0) * (g 0) * (g 9)) := by
  norm_num [atom0003, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0003_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4416 : Int) atom0003) := by
  rw [SparsePolynomial.eval_scale, eval_atom0003]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 0) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0004 : SparsePolynomial.Poly := [([0,1,1], 1)]
theorem eval_atom0004 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0004 = ((g 0) * (g 1) * (g 1)) := by
  norm_num [atom0004, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0004_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2976 : Int) atom0004) := by
  rw [SparsePolynomial.eval_scale, eval_atom0004]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have ht : 0 ≤ ((g 0) * (g 1) * (g 1)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0005 : SparsePolynomial.Poly := [([0,1,2], 1)]
theorem eval_atom0005 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0005 = ((g 0) * (g 1) * (g 2)) := by
  norm_num [atom0005, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0005_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28992 : Int) atom0005) := by
  rw [SparsePolynomial.eval_scale, eval_atom0005]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 0) * (g 1) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0006 : SparsePolynomial.Poly := [([0,1,3], 1)]
theorem eval_atom0006 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0006 = ((g 0) * (g 1) * (g 3)) := by
  norm_num [atom0006, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0006_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30240 : Int) atom0006) := by
  rw [SparsePolynomial.eval_scale, eval_atom0006]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 1) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0007 : SparsePolynomial.Poly := [([0,1,4], 1)]
theorem eval_atom0007 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0007 = ((g 0) * (g 1) * (g 4)) := by
  norm_num [atom0007, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0007_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31488 : Int) atom0007) := by
  rw [SparsePolynomial.eval_scale, eval_atom0007]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 1) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0008 : SparsePolynomial.Poly := [([0,1,5], 1)]
theorem eval_atom0008 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0008 = ((g 0) * (g 1) * (g 5)) := by
  norm_num [atom0008, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0008_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33248 : Int) atom0008) := by
  rw [SparsePolynomial.eval_scale, eval_atom0008]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 1) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0009 : SparsePolynomial.Poly := [([0,1,6], 1)]
theorem eval_atom0009 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0009 = ((g 0) * (g 1) * (g 6)) := by
  norm_num [atom0009, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0009_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (72432 : Int) atom0009) := by
  rw [SparsePolynomial.eval_scale, eval_atom0009]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 1) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0010 : SparsePolynomial.Poly := [([0,1,7], 1)]
theorem eval_atom0010 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0010 = ((g 0) * (g 1) * (g 7)) := by
  norm_num [atom0010, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0010_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32464 : Int) atom0010) := by
  rw [SparsePolynomial.eval_scale, eval_atom0010]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 1) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0011 : SparsePolynomial.Poly := [([0,1,8], 1)]
theorem eval_atom0011 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0011 = ((g 0) * (g 1) * (g 8)) := by
  norm_num [atom0011, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0011_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15888 : Int) atom0011) := by
  rw [SparsePolynomial.eval_scale, eval_atom0011]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 1) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0012 : SparsePolynomial.Poly := [([0,1,9], 1)]
theorem eval_atom0012 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0012 = ((g 0) * (g 1) * (g 9)) := by
  norm_num [atom0012, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0012_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8688 : Int) atom0012) := by
  rw [SparsePolynomial.eval_scale, eval_atom0012]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 1) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0013 : SparsePolynomial.Poly := [([0,1,10], 1)]
theorem eval_atom0013 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0013 = ((g 0) * (g 1) * (g 10)) := by
  norm_num [atom0013, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0013_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4592 : Int) atom0013) := by
  rw [SparsePolynomial.eval_scale, eval_atom0013]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 1) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0014 : SparsePolynomial.Poly := [([0,2,2], 1)]
theorem eval_atom0014 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0014 = ((g 0) * (g 2) * (g 2)) := by
  norm_num [atom0014, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0014_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34368 : Int) atom0014) := by
  rw [SparsePolynomial.eval_scale, eval_atom0014]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 0) * (g 2) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0015 : SparsePolynomial.Poly := [([0,2,3], 1)]
theorem eval_atom0015 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0015 = ((g 0) * (g 2) * (g 3)) := by
  norm_num [atom0015, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0015_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (74496 : Int) atom0015) := by
  rw [SparsePolynomial.eval_scale, eval_atom0015]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 2) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0016 : SparsePolynomial.Poly := [([0,2,4], 1)]
theorem eval_atom0016 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0016 = ((g 0) * (g 2) * (g 4)) := by
  norm_num [atom0016, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0016_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (80256 : Int) atom0016) := by
  rw [SparsePolynomial.eval_scale, eval_atom0016]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 2) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0017 : SparsePolynomial.Poly := [([0,2,5], 1)]
theorem eval_atom0017 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0017 = ((g 0) * (g 2) * (g 5)) := by
  norm_num [atom0017, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0017_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (86016 : Int) atom0017) := by
  rw [SparsePolynomial.eval_scale, eval_atom0017]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 2) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0018 : SparsePolynomial.Poly := [([0,2,6], 1)]
theorem eval_atom0018 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0018 = ((g 0) * (g 2) * (g 6)) := by
  norm_num [atom0018, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0018_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (117504 : Int) atom0018) := by
  rw [SparsePolynomial.eval_scale, eval_atom0018]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 2) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0019 : SparsePolynomial.Poly := [([0,2,7], 1)]
theorem eval_atom0019 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0019 = ((g 0) * (g 2) * (g 7)) := by
  norm_num [atom0019, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0019_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (73344 : Int) atom0019) := by
  rw [SparsePolynomial.eval_scale, eval_atom0019]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 2) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0020 : SparsePolynomial.Poly := [([0,2,8], 1)]
theorem eval_atom0020 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0020 = ((g 0) * (g 2) * (g 8)) := by
  norm_num [atom0020, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0020_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48768 : Int) atom0020) := by
  rw [SparsePolynomial.eval_scale, eval_atom0020]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 2) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0021 : SparsePolynomial.Poly := [([0,2,9], 1)]
theorem eval_atom0021 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0021 = ((g 0) * (g 2) * (g 9)) := by
  norm_num [atom0021, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0021_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17664 : Int) atom0021) := by
  rw [SparsePolynomial.eval_scale, eval_atom0021]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 2) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0022 : SparsePolynomial.Poly := [([0,2,10], 1)]
theorem eval_atom0022 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0022 = ((g 0) * (g 2) * (g 10)) := by
  norm_num [atom0022, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0022_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17616 : Int) atom0022) := by
  rw [SparsePolynomial.eval_scale, eval_atom0022]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 2) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0023 : SparsePolynomial.Poly := [([0,3,3], 1)]
theorem eval_atom0023 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0023 = ((g 0) * (g 3) * (g 3)) := by
  norm_num [atom0023, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0023_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39648 : Int) atom0023) := by
  rw [SparsePolynomial.eval_scale, eval_atom0023]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0024 : SparsePolynomial.Poly := [([0,3,4], 1)]
theorem eval_atom0024 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0024 = ((g 0) * (g 3) * (g 4)) := by
  norm_num [atom0024, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0024_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (83424 : Int) atom0024) := by
  rw [SparsePolynomial.eval_scale, eval_atom0024]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0025 : SparsePolynomial.Poly := [([0,3,5], 1)]
theorem eval_atom0025 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0025 = ((g 0) * (g 3) * (g 5)) := by
  norm_num [atom0025, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0025_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (91008 : Int) atom0025) := by
  rw [SparsePolynomial.eval_scale, eval_atom0025]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0026 : SparsePolynomial.Poly := [([0,3,6], 1)]
theorem eval_atom0026 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0026 = ((g 0) * (g 3) * (g 6)) := by
  norm_num [atom0026, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0026_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (124560 : Int) atom0026) := by
  rw [SparsePolynomial.eval_scale, eval_atom0026]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0027 : SparsePolynomial.Poly := [([0,3,7], 1)]
theorem eval_atom0027 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0027 = ((g 0) * (g 3) * (g 7)) := by
  norm_num [atom0027, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0027_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (81648 : Int) atom0027) := by
  rw [SparsePolynomial.eval_scale, eval_atom0027]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0028 : SparsePolynomial.Poly := [([0,3,8], 1)]
theorem eval_atom0028 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0028 = ((g 0) * (g 3) * (g 8)) := by
  norm_num [atom0028, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0028_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (56688 : Int) atom0028) := by
  rw [SparsePolynomial.eval_scale, eval_atom0028]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0029 : SparsePolynomial.Poly := [([0,3,9], 1)]
theorem eval_atom0029 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0029 = ((g 0) * (g 3) * (g 9)) := by
  norm_num [atom0029, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0029_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26832 : Int) atom0029) := by
  rw [SparsePolynomial.eval_scale, eval_atom0029]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0030 : SparsePolynomial.Poly := [([0,3,10], 1)]
theorem eval_atom0030 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0030 = ((g 0) * (g 3) * (g 10)) := by
  norm_num [atom0030, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0030_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29820 : Int) atom0030) := by
  rw [SparsePolynomial.eval_scale, eval_atom0030]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0031 : SparsePolynomial.Poly := [([0,3,11], 1)]
theorem eval_atom0031 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0031 = ((g 0) * (g 3) * (g 11)) := by
  norm_num [atom0031, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0031_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5136 : Int) atom0031) := by
  rw [SparsePolynomial.eval_scale, eval_atom0031]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0032 : SparsePolynomial.Poly := [([0,4,4], 1)]
theorem eval_atom0032 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0032 = ((g 0) * (g 4) * (g 4)) := by
  norm_num [atom0032, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0032_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52224 : Int) atom0032) := by
  rw [SparsePolynomial.eval_scale, eval_atom0032]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0033 : SparsePolynomial.Poly := [([0,4,5], 1)]
theorem eval_atom0033 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0033 = ((g 0) * (g 4) * (g 5)) := by
  norm_num [atom0033, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0033_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (102576 : Int) atom0033) := by
  rw [SparsePolynomial.eval_scale, eval_atom0033]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0034 : SparsePolynomial.Poly := [([0,4,6], 1)]
theorem eval_atom0034 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0034 = ((g 0) * (g 4) * (g 6)) := by
  norm_num [atom0034, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0034_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (131616 : Int) atom0034) := by
  rw [SparsePolynomial.eval_scale, eval_atom0034]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0035 : SparsePolynomial.Poly := [([0,4,7], 1)]
theorem eval_atom0035 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0035 = ((g 0) * (g 4) * (g 7)) := by
  norm_num [atom0035, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0035_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (92160 : Int) atom0035) := by
  rw [SparsePolynomial.eval_scale, eval_atom0035]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0036 : SparsePolynomial.Poly := [([0,4,8], 1)]
theorem eval_atom0036 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0036 = ((g 0) * (g 4) * (g 8)) := by
  norm_num [atom0036, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0036_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (64608 : Int) atom0036) := by
  rw [SparsePolynomial.eval_scale, eval_atom0036]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0037 : SparsePolynomial.Poly := [([0,4,9], 1)]
theorem eval_atom0037 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0037 = ((g 0) * (g 4) * (g 9)) := by
  norm_num [atom0037, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0037_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36000 : Int) atom0037) := by
  rw [SparsePolynomial.eval_scale, eval_atom0037]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0038 : SparsePolynomial.Poly := [([0,4,10], 1)]
theorem eval_atom0038 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0038 = ((g 0) * (g 4) * (g 10)) := by
  norm_num [atom0038, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0038_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38448 : Int) atom0038) := by
  rw [SparsePolynomial.eval_scale, eval_atom0038]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0039 : SparsePolynomial.Poly := [([0,4,11], 1)]
theorem eval_atom0039 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0039 = ((g 0) * (g 4) * (g 11)) := by
  norm_num [atom0039, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0039_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13536 : Int) atom0039) := by
  rw [SparsePolynomial.eval_scale, eval_atom0039]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0040 : SparsePolynomial.Poly := [([0,5,5], 1)]
theorem eval_atom0040 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0040 = ((g 0) * (g 5) * (g 5)) := by
  norm_num [atom0040, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0040_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (64320 : Int) atom0040) := by
  rw [SparsePolynomial.eval_scale, eval_atom0040]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0041 : SparsePolynomial.Poly := [([0,5,6], 1)]
theorem eval_atom0041 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0041 = ((g 0) * (g 5) * (g 6)) := by
  norm_num [atom0041, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0041_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (138672 : Int) atom0041) := by
  rw [SparsePolynomial.eval_scale, eval_atom0041]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0042 : SparsePolynomial.Poly := [([0,5,7], 1)]
theorem eval_atom0042 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0042 = ((g 0) * (g 5) * (g 7)) := by
  norm_num [atom0042, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0042_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (102864 : Int) atom0042) := by
  rw [SparsePolynomial.eval_scale, eval_atom0042]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0043 : SparsePolynomial.Poly := [([0,5,8], 1)]
theorem eval_atom0043 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0043 = ((g 0) * (g 5) * (g 8)) := by
  norm_num [atom0043, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0043_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (72528 : Int) atom0043) := by
  rw [SparsePolynomial.eval_scale, eval_atom0043]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0044 : SparsePolynomial.Poly := [([0,5,9], 1)]
theorem eval_atom0044 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0044 = ((g 0) * (g 5) * (g 9)) := by
  norm_num [atom0044, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0044_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (45168 : Int) atom0044) := by
  rw [SparsePolynomial.eval_scale, eval_atom0044]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0045 : SparsePolynomial.Poly := [([0,5,10], 1)]
theorem eval_atom0045 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0045 = ((g 0) * (g 5) * (g 10)) := by
  norm_num [atom0045, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0045_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43680 : Int) atom0045) := by
  rw [SparsePolynomial.eval_scale, eval_atom0045]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0046 : SparsePolynomial.Poly := [([0,5,11], 1)]
theorem eval_atom0046 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0046 = ((g 0) * (g 5) * (g 11)) := by
  norm_num [atom0046, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0046_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21936 : Int) atom0046) := by
  rw [SparsePolynomial.eval_scale, eval_atom0046]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0047 : SparsePolynomial.Poly := [([0,6,6], 1)]
theorem eval_atom0047 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0047 = ((g 0) * (g 6) * (g 6)) := by
  norm_num [atom0047, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0047_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (90048 : Int) atom0047) := by
  rw [SparsePolynomial.eval_scale, eval_atom0047]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0048 : SparsePolynomial.Poly := [([0,6,7], 1)]
theorem eval_atom0048 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0048 = ((g 0) * (g 6) * (g 7)) := by
  norm_num [atom0048, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0048_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (152832 : Int) atom0048) := by
  rw [SparsePolynomial.eval_scale, eval_atom0048]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0049 : SparsePolynomial.Poly := [([0,6,8], 1)]
theorem eval_atom0049 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0049 = ((g 0) * (g 6) * (g 8)) := by
  norm_num [atom0049, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0049_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (150528 : Int) atom0049) := by
  rw [SparsePolynomial.eval_scale, eval_atom0049]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0050 : SparsePolynomial.Poly := [([0,6,9], 1)]
theorem eval_atom0050 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0050 = ((g 0) * (g 6) * (g 9)) := by
  norm_num [atom0050, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0050_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (136320 : Int) atom0050) := by
  rw [SparsePolynomial.eval_scale, eval_atom0050]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0051 : SparsePolynomial.Poly := [([0,6,10], 1)]
theorem eval_atom0051 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0051 = ((g 0) * (g 6) * (g 10)) := by
  norm_num [atom0051, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0051_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (75360 : Int) atom0051) := by
  rw [SparsePolynomial.eval_scale, eval_atom0051]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0052 : SparsePolynomial.Poly := [([0,6,11], 1)]
theorem eval_atom0052 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0052 = ((g 0) * (g 6) * (g 11)) := by
  norm_num [atom0052, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0052_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (83904 : Int) atom0052) := by
  rw [SparsePolynomial.eval_scale, eval_atom0052]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0053 : SparsePolynomial.Poly := [([0,7,7], 1)]
theorem eval_atom0053 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0053 = ((g 0) * (g 7) * (g 7)) := by
  norm_num [atom0053, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0053_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (73344 : Int) atom0053) := by
  rw [SparsePolynomial.eval_scale, eval_atom0053]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0054 : SparsePolynomial.Poly := [([0,7,8], 1)]
theorem eval_atom0054 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0054 = ((g 0) * (g 7) * (g 8)) := by
  norm_num [atom0054, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0054_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (132672 : Int) atom0054) := by
  rw [SparsePolynomial.eval_scale, eval_atom0054]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0055 : SparsePolynomial.Poly := [([0,7,9], 1)]
theorem eval_atom0055 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0055 = ((g 0) * (g 7) * (g 9)) := by
  norm_num [atom0055, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0055_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (146304 : Int) atom0055) := by
  rw [SparsePolynomial.eval_scale, eval_atom0055]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0056 : SparsePolynomial.Poly := [([0,7,10], 1)]
theorem eval_atom0056 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0056 = ((g 0) * (g 7) * (g 10)) := by
  norm_num [atom0056, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0056_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (84576 : Int) atom0056) := by
  rw [SparsePolynomial.eval_scale, eval_atom0056]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0057 : SparsePolynomial.Poly := [([0,7,11], 1)]
theorem eval_atom0057 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0057 = ((g 0) * (g 7) * (g 11)) := by
  norm_num [atom0057, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0057_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (99648 : Int) atom0057) := by
  rw [SparsePolynomial.eval_scale, eval_atom0057]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0058 : SparsePolynomial.Poly := [([0,8,8], 1)]
theorem eval_atom0058 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0058 = ((g 0) * (g 8) * (g 8)) := by
  norm_num [atom0058, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0058_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (69888 : Int) atom0058) := by
  rw [SparsePolynomial.eval_scale, eval_atom0058]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0059 : SparsePolynomial.Poly := [([0,8,9], 1)]
theorem eval_atom0059 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0059 = ((g 0) * (g 8) * (g 9)) := by
  norm_num [atom0059, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0059_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (156288 : Int) atom0059) := by
  rw [SparsePolynomial.eval_scale, eval_atom0059]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0060 : SparsePolynomial.Poly := [([0,8,10], 1)]
theorem eval_atom0060 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0060 = ((g 0) * (g 8) * (g 10)) := by
  norm_num [atom0060, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0060_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (90144 : Int) atom0060) := by
  rw [SparsePolynomial.eval_scale, eval_atom0060]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0061 : SparsePolynomial.Poly := [([0,8,11], 1)]
theorem eval_atom0061 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0061 = ((g 0) * (g 8) * (g 11)) := by
  norm_num [atom0061, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0061_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (87936 : Int) atom0061) := by
  rw [SparsePolynomial.eval_scale, eval_atom0061]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0062 : SparsePolynomial.Poly := [([0,9,9], 1)]
theorem eval_atom0062 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0062 = ((g 0) * (g 9) * (g 9)) := by
  norm_num [atom0062, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0062_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (83136 : Int) atom0062) := by
  rw [SparsePolynomial.eval_scale, eval_atom0062]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0063 : SparsePolynomial.Poly := [([0,9,10], 1)]
theorem eval_atom0063 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0063 = ((g 0) * (g 9) * (g 10)) := by
  norm_num [atom0063, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0063_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (99360 : Int) atom0063) := by
  rw [SparsePolynomial.eval_scale, eval_atom0063]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0064 : SparsePolynomial.Poly := [([0,9,11], 1)]
theorem eval_atom0064 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0064 = ((g 0) * (g 9) * (g 11)) := by
  norm_num [atom0064, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0064_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (103680 : Int) atom0064) := by
  rw [SparsePolynomial.eval_scale, eval_atom0064]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0065 : SparsePolynomial.Poly := [([0,10,10], 1)]
theorem eval_atom0065 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0065 = ((g 0) * (g 10) * (g 10)) := by
  norm_num [atom0065, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0065_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9888 : Int) atom0065) := by
  rw [SparsePolynomial.eval_scale, eval_atom0065]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0066 : SparsePolynomial.Poly := [([0,10,11], 1)]
theorem eval_atom0066 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0066 = ((g 0) * (g 10) * (g 11)) := by
  norm_num [atom0066, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0066_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16416 : Int) atom0066) := by
  rw [SparsePolynomial.eval_scale, eval_atom0066]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0067 : SparsePolynomial.Poly := [([1,1,2], 1)]
theorem eval_atom0067 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0067 = ((g 1) * (g 1) * (g 2)) := by
  norm_num [atom0067, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0067_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9408 : Int) atom0067) := by
  rw [SparsePolynomial.eval_scale, eval_atom0067]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 1) * (g 1) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0068 : SparsePolynomial.Poly := [([1,1,3], 1)]
theorem eval_atom0068 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0068 = ((g 1) * (g 1) * (g 3)) := by
  norm_num [atom0068, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0068_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5760 : Int) atom0068) := by
  rw [SparsePolynomial.eval_scale, eval_atom0068]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 1) * (g 1) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0069 : SparsePolynomial.Poly := [([1,1,4], 1)]
theorem eval_atom0069 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0069 = ((g 1) * (g 1) * (g 4)) := by
  norm_num [atom0069, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0069_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2112 : Int) atom0069) := by
  rw [SparsePolynomial.eval_scale, eval_atom0069]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 1) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0070 : SparsePolynomial.Poly := [([1,1,6], 1)]
theorem eval_atom0070 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0070 = ((g 1) * (g 1) * (g 6)) := by
  norm_num [atom0070, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0070_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30336 : Int) atom0070) := by
  rw [SparsePolynomial.eval_scale, eval_atom0070]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 1) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0071 : SparsePolynomial.Poly := [([1,2,2], 1)]
theorem eval_atom0071 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0071 = ((g 1) * (g 2) * (g 2)) := by
  norm_num [atom0071, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0071_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17280 : Int) atom0071) := by
  rw [SparsePolynomial.eval_scale, eval_atom0071]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 1) * (g 2) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0072 : SparsePolynomial.Poly := [([1,2,3], 1)]
theorem eval_atom0072 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0072 = ((g 1) * (g 2) * (g 3)) := by
  norm_num [atom0072, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0072_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33024 : Int) atom0072) := by
  rw [SparsePolynomial.eval_scale, eval_atom0072]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 1) * (g 2) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0073 : SparsePolynomial.Poly := [([1,2,4], 1)]
theorem eval_atom0073 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0073 = ((g 1) * (g 2) * (g 4)) := by
  norm_num [atom0073, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0073_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31488 : Int) atom0073) := by
  rw [SparsePolynomial.eval_scale, eval_atom0073]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 2) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0074 : SparsePolynomial.Poly := [([1,2,5], 1)]
theorem eval_atom0074 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0074 = ((g 1) * (g 2) * (g 5)) := by
  norm_num [atom0074, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0074_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32000 : Int) atom0074) := by
  rw [SparsePolynomial.eval_scale, eval_atom0074]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 2) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0075 : SparsePolynomial.Poly := [([1,2,6], 1)]
theorem eval_atom0075 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0075 = ((g 1) * (g 2) * (g 6)) := by
  norm_num [atom0075, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0075_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (104448 : Int) atom0075) := by
  rw [SparsePolynomial.eval_scale, eval_atom0075]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 2) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0076 : SparsePolynomial.Poly := [([1,2,7], 1)]
theorem eval_atom0076 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0076 = ((g 1) * (g 2) * (g 7)) := by
  norm_num [atom0076, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0076_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48640 : Int) atom0076) := by
  rw [SparsePolynomial.eval_scale, eval_atom0076]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 2) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0077 : SparsePolynomial.Poly := [([1,2,8], 1)]
theorem eval_atom0077 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0077 = ((g 1) * (g 2) * (g 8)) := by
  norm_num [atom0077, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0077_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (62208 : Int) atom0077) := by
  rw [SparsePolynomial.eval_scale, eval_atom0077]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 2) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0078 : SparsePolynomial.Poly := [([1,2,9], 1)]
theorem eval_atom0078 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0078 = ((g 1) * (g 2) * (g 9)) := by
  norm_num [atom0078, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0078_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (62592 : Int) atom0078) := by
  rw [SparsePolynomial.eval_scale, eval_atom0078]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 2) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0079 : SparsePolynomial.Poly := [([1,2,10], 1)]
theorem eval_atom0079 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0079 = ((g 1) * (g 2) * (g 10)) := by
  norm_num [atom0079, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0079_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (51872 : Int) atom0079) := by
  rw [SparsePolynomial.eval_scale, eval_atom0079]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 2) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block000 : SparsePolynomial.Poly := [([0,0,6], 14208), ([0,0,7], 10944), ([0,0,8], 7680), ([0,0,9], 4416), ([0,1,1], 2976), ([0,1,2], 28992), ([0,1,3], 30240), ([0,1,4], 31488), ([0,1,5], 33248), ([0,1,6], 72432), ([0,1,7], 32464), ([0,1,8], 15888), ([0,1,9], 8688), ([0,1,10], 4592), ([0,2,2], 34368), ([0,2,3], 74496), ([0,2,4], 80256), ([0,2,5], 86016), ([0,2,6], 117504), ([0,2,7], 73344), ([0,2,8], 48768), ([0,2,9], 17664), ([0,2,10], 17616), ([0,3,3], 39648), ([0,3,4], 83424), ([0,3,5], 91008), ([0,3,6], 124560), ([0,3,7], 81648), ([0,3,8], 56688), ([0,3,9], 26832), ([0,3,10], 29820), ([0,3,11], 5136), ([0,4,4], 52224), ([0,4,5], 102576), ([0,4,6], 131616), ([0,4,7], 92160), ([0,4,8], 64608), ([0,4,9], 36000), ([0,4,10], 38448), ([0,4,11], 13536), ([0,5,5], 64320), ([0,5,6], 138672), ([0,5,7], 102864), ([0,5,8], 72528), ([0,5,9], 45168), ([0,5,10], 43680), ([0,5,11], 21936), ([0,6,6], 90048), ([0,6,7], 152832), ([0,6,8], 150528), ([0,6,9], 136320), ([0,6,10], 75360), ([0,6,11], 83904), ([0,7,7], 73344), ([0,7,8], 132672), ([0,7,9], 146304), ([0,7,10], 84576), ([0,7,11], 99648), ([0,8,8], 69888), ([0,8,9], 156288), ([0,8,10], 90144), ([0,8,11], 87936), ([0,9,9], 83136), ([0,9,10], 99360), ([0,9,11], 103680), ([0,10,10], 9888), ([0,10,11], 16416), ([1,1,2], 9408), ([1,1,3], 5760), ([1,1,4], 2112), ([1,1,6], 30336), ([1,2,2], 17280), ([1,2,3], 33024), ([1,2,4], 31488), ([1,2,5], 32000), ([1,2,6], 104448), ([1,2,7], 48640), ([1,2,8], 62208), ([1,2,9], 62592), ([1,2,10], 51872)]
theorem block000_data : block000 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (14208 : Int) atom0000) (SparsePolynomial.scale (10944 : Int) atom0001)) (SparsePolynomial.merge (SparsePolynomial.scale (7680 : Int) atom0002) (SparsePolynomial.merge (SparsePolynomial.scale (4416 : Int) atom0003) (SparsePolynomial.scale (2976 : Int) atom0004)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (28992 : Int) atom0005) (SparsePolynomial.scale (30240 : Int) atom0006)) (SparsePolynomial.merge (SparsePolynomial.scale (31488 : Int) atom0007) (SparsePolynomial.merge (SparsePolynomial.scale (33248 : Int) atom0008) (SparsePolynomial.scale (72432 : Int) atom0009))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (32464 : Int) atom0010) (SparsePolynomial.scale (15888 : Int) atom0011)) (SparsePolynomial.merge (SparsePolynomial.scale (8688 : Int) atom0012) (SparsePolynomial.merge (SparsePolynomial.scale (4592 : Int) atom0013) (SparsePolynomial.scale (34368 : Int) atom0014)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (74496 : Int) atom0015) (SparsePolynomial.scale (80256 : Int) atom0016)) (SparsePolynomial.merge (SparsePolynomial.scale (86016 : Int) atom0017) (SparsePolynomial.merge (SparsePolynomial.scale (117504 : Int) atom0018) (SparsePolynomial.scale (73344 : Int) atom0019)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (48768 : Int) atom0020) (SparsePolynomial.scale (17664 : Int) atom0021)) (SparsePolynomial.merge (SparsePolynomial.scale (17616 : Int) atom0022) (SparsePolynomial.merge (SparsePolynomial.scale (39648 : Int) atom0023) (SparsePolynomial.scale (83424 : Int) atom0024)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (91008 : Int) atom0025) (SparsePolynomial.scale (124560 : Int) atom0026)) (SparsePolynomial.merge (SparsePolynomial.scale (81648 : Int) atom0027) (SparsePolynomial.merge (SparsePolynomial.scale (56688 : Int) atom0028) (SparsePolynomial.scale (26832 : Int) atom0029))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (29820 : Int) atom0030) (SparsePolynomial.scale (5136 : Int) atom0031)) (SparsePolynomial.merge (SparsePolynomial.scale (52224 : Int) atom0032) (SparsePolynomial.merge (SparsePolynomial.scale (102576 : Int) atom0033) (SparsePolynomial.scale (131616 : Int) atom0034)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (92160 : Int) atom0035) (SparsePolynomial.scale (64608 : Int) atom0036)) (SparsePolynomial.merge (SparsePolynomial.scale (36000 : Int) atom0037) (SparsePolynomial.merge (SparsePolynomial.scale (38448 : Int) atom0038) (SparsePolynomial.scale (13536 : Int) atom0039))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (64320 : Int) atom0040) (SparsePolynomial.scale (138672 : Int) atom0041)) (SparsePolynomial.merge (SparsePolynomial.scale (102864 : Int) atom0042) (SparsePolynomial.merge (SparsePolynomial.scale (72528 : Int) atom0043) (SparsePolynomial.scale (45168 : Int) atom0044)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (43680 : Int) atom0045) (SparsePolynomial.scale (21936 : Int) atom0046)) (SparsePolynomial.merge (SparsePolynomial.scale (90048 : Int) atom0047) (SparsePolynomial.merge (SparsePolynomial.scale (152832 : Int) atom0048) (SparsePolynomial.scale (150528 : Int) atom0049))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (136320 : Int) atom0050) (SparsePolynomial.scale (75360 : Int) atom0051)) (SparsePolynomial.merge (SparsePolynomial.scale (83904 : Int) atom0052) (SparsePolynomial.merge (SparsePolynomial.scale (73344 : Int) atom0053) (SparsePolynomial.scale (132672 : Int) atom0054)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (146304 : Int) atom0055) (SparsePolynomial.scale (84576 : Int) atom0056)) (SparsePolynomial.merge (SparsePolynomial.scale (99648 : Int) atom0057) (SparsePolynomial.merge (SparsePolynomial.scale (69888 : Int) atom0058) (SparsePolynomial.scale (156288 : Int) atom0059)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (90144 : Int) atom0060) (SparsePolynomial.scale (87936 : Int) atom0061)) (SparsePolynomial.merge (SparsePolynomial.scale (83136 : Int) atom0062) (SparsePolynomial.merge (SparsePolynomial.scale (99360 : Int) atom0063) (SparsePolynomial.scale (103680 : Int) atom0064)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (9888 : Int) atom0065) (SparsePolynomial.scale (16416 : Int) atom0066)) (SparsePolynomial.merge (SparsePolynomial.scale (9408 : Int) atom0067) (SparsePolynomial.merge (SparsePolynomial.scale (5760 : Int) atom0068) (SparsePolynomial.scale (2112 : Int) atom0069))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (30336 : Int) atom0070) (SparsePolynomial.scale (17280 : Int) atom0071)) (SparsePolynomial.merge (SparsePolynomial.scale (33024 : Int) atom0072) (SparsePolynomial.merge (SparsePolynomial.scale (31488 : Int) atom0073) (SparsePolynomial.scale (32000 : Int) atom0074)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (104448 : Int) atom0075) (SparsePolynomial.scale (48640 : Int) atom0076)) (SparsePolynomial.merge (SparsePolynomial.scale (62208 : Int) atom0077) (SparsePolynomial.merge (SparsePolynomial.scale (62592 : Int) atom0078) (SparsePolynomial.scale (51872 : Int) atom0079)))))))) := by decide +kernel
theorem block000_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block000 := by
  rw [block000_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0000_nonneg g hg hA hB) (atom0001_nonneg g hg hA hB)) (add_nonneg (atom0002_nonneg g hg hA hB) (add_nonneg (atom0003_nonneg g hg hA hB) (atom0004_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0005_nonneg g hg hA hB) (atom0006_nonneg g hg hA hB)) (add_nonneg (atom0007_nonneg g hg hA hB) (add_nonneg (atom0008_nonneg g hg hA hB) (atom0009_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0010_nonneg g hg hA hB) (atom0011_nonneg g hg hA hB)) (add_nonneg (atom0012_nonneg g hg hA hB) (add_nonneg (atom0013_nonneg g hg hA hB) (atom0014_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0015_nonneg g hg hA hB) (atom0016_nonneg g hg hA hB)) (add_nonneg (atom0017_nonneg g hg hA hB) (add_nonneg (atom0018_nonneg g hg hA hB) (atom0019_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0020_nonneg g hg hA hB) (atom0021_nonneg g hg hA hB)) (add_nonneg (atom0022_nonneg g hg hA hB) (add_nonneg (atom0023_nonneg g hg hA hB) (atom0024_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0025_nonneg g hg hA hB) (atom0026_nonneg g hg hA hB)) (add_nonneg (atom0027_nonneg g hg hA hB) (add_nonneg (atom0028_nonneg g hg hA hB) (atom0029_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0030_nonneg g hg hA hB) (atom0031_nonneg g hg hA hB)) (add_nonneg (atom0032_nonneg g hg hA hB) (add_nonneg (atom0033_nonneg g hg hA hB) (atom0034_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0035_nonneg g hg hA hB) (atom0036_nonneg g hg hA hB)) (add_nonneg (atom0037_nonneg g hg hA hB) (add_nonneg (atom0038_nonneg g hg hA hB) (atom0039_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0040_nonneg g hg hA hB) (atom0041_nonneg g hg hA hB)) (add_nonneg (atom0042_nonneg g hg hA hB) (add_nonneg (atom0043_nonneg g hg hA hB) (atom0044_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0045_nonneg g hg hA hB) (atom0046_nonneg g hg hA hB)) (add_nonneg (atom0047_nonneg g hg hA hB) (add_nonneg (atom0048_nonneg g hg hA hB) (atom0049_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0050_nonneg g hg hA hB) (atom0051_nonneg g hg hA hB)) (add_nonneg (atom0052_nonneg g hg hA hB) (add_nonneg (atom0053_nonneg g hg hA hB) (atom0054_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0055_nonneg g hg hA hB) (atom0056_nonneg g hg hA hB)) (add_nonneg (atom0057_nonneg g hg hA hB) (add_nonneg (atom0058_nonneg g hg hA hB) (atom0059_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0060_nonneg g hg hA hB) (atom0061_nonneg g hg hA hB)) (add_nonneg (atom0062_nonneg g hg hA hB) (add_nonneg (atom0063_nonneg g hg hA hB) (atom0064_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0065_nonneg g hg hA hB) (atom0066_nonneg g hg hA hB)) (add_nonneg (atom0067_nonneg g hg hA hB) (add_nonneg (atom0068_nonneg g hg hA hB) (atom0069_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0070_nonneg g hg hA hB) (atom0071_nonneg g hg hA hB)) (add_nonneg (atom0072_nonneg g hg hA hB) (add_nonneg (atom0073_nonneg g hg hA hB) (atom0074_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0075_nonneg g hg hA hB) (atom0076_nonneg g hg hA hB)) (add_nonneg (atom0077_nonneg g hg hA hB) (add_nonneg (atom0078_nonneg g hg hA hB) (atom0079_nonneg g hg hA hB))))))))

end APPT.Finite12
