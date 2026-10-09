import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def atom0975 : SparsePolynomial.Poly := [([8,12,12], 1)]
theorem eval_atom0975 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0975 = ((g 8) * (g 12) * (g 12)) := by
  norm_num [atom0975, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0975_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1914984960 : Int) atom0975) := by
  rw [SparsePolynomial.eval_scale, eval_atom0975]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 8) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0976 : SparsePolynomial.Poly := [([8,12,13], 1)]
theorem eval_atom0976 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0976 = ((g 8) * (g 12) * (g 13)) := by
  norm_num [atom0976, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0976_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4619473920 : Int) atom0976) := by
  rw [SparsePolynomial.eval_scale, eval_atom0976]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0977 : SparsePolynomial.Poly := [([8,12,14], 1)]
theorem eval_atom0977 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0977 = ((g 8) * (g 12) * (g 14)) := by
  norm_num [atom0977, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0977_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10744620960 : Int) atom0977) := by
  rw [SparsePolynomial.eval_scale, eval_atom0977]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0978 : SparsePolynomial.Poly := [([8,12,15], 1)]
theorem eval_atom0978 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0978 = ((g 8) * (g 12) * (g 15)) := by
  norm_num [atom0978, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0978_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11856384000 : Int) atom0978) := by
  rw [SparsePolynomial.eval_scale, eval_atom0978]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0979 : SparsePolynomial.Poly := [([8,12,16], 1)]
theorem eval_atom0979 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0979 = ((g 8) * (g 12) * (g 16)) := by
  norm_num [atom0979, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0979_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9369254400 : Int) atom0979) := by
  rw [SparsePolynomial.eval_scale, eval_atom0979]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0980 : SparsePolynomial.Poly := [([8,12,17], 1)]
theorem eval_atom0980 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0980 = ((g 8) * (g 12) * (g 17)) := by
  norm_num [atom0980, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0980_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15816660480 : Int) atom0980) := by
  rw [SparsePolynomial.eval_scale, eval_atom0980]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0981 : SparsePolynomial.Poly := [([8,13,13], 1)]
theorem eval_atom0981 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0981 = ((g 8) * (g 13) * (g 13)) := by
  norm_num [atom0981, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0981_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1790734848 : Int) atom0981) := by
  rw [SparsePolynomial.eval_scale, eval_atom0981]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0982 : SparsePolynomial.Poly := [([8,13,14], 1)]
theorem eval_atom0982 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0982 = ((g 8) * (g 13) * (g 14)) := by
  norm_num [atom0982, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0982_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8615461560 : Int) atom0982) := by
  rw [SparsePolynomial.eval_scale, eval_atom0982]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0983 : SparsePolynomial.Poly := [([8,13,15], 1)]
theorem eval_atom0983 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0983 = ((g 8) * (g 13) * (g 15)) := by
  norm_num [atom0983, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0983_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10629073920 : Int) atom0983) := by
  rw [SparsePolynomial.eval_scale, eval_atom0983]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0984 : SparsePolynomial.Poly := [([8,13,16], 1)]
theorem eval_atom0984 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0984 = ((g 8) * (g 13) * (g 16)) := by
  norm_num [atom0984, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0984_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8825487360 : Int) atom0984) := by
  rw [SparsePolynomial.eval_scale, eval_atom0984]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0985 : SparsePolynomial.Poly := [([8,13,17], 1)]
theorem eval_atom0985 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0985 = ((g 8) * (g 13) * (g 17)) := by
  norm_num [atom0985, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0985_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12648821760 : Int) atom0985) := by
  rw [SparsePolynomial.eval_scale, eval_atom0985]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0986 : SparsePolynomial.Poly := [([8,14,14], 1)]
theorem eval_atom0986 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0986 = ((g 8) * (g 14) * (g 14)) := by
  norm_num [atom0986, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0986_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7466756280 : Int) atom0986) := by
  rw [SparsePolynomial.eval_scale, eval_atom0986]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0987 : SparsePolynomial.Poly := [([8,14,15], 1)]
theorem eval_atom0987 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0987 = ((g 8) * (g 14) * (g 15)) := by
  norm_num [atom0987, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0987_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13350688440 : Int) atom0987) := by
  rw [SparsePolynomial.eval_scale, eval_atom0987]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0988 : SparsePolynomial.Poly := [([8,14,16], 1)]
theorem eval_atom0988 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0988 = ((g 8) * (g 14) * (g 16)) := by
  norm_num [atom0988, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0988_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11285680080 : Int) atom0988) := by
  rw [SparsePolynomial.eval_scale, eval_atom0988]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0989 : SparsePolynomial.Poly := [([8,14,17], 1)]
theorem eval_atom0989 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0989 = ((g 8) * (g 14) * (g 17)) := by
  norm_num [atom0989, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0989_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16222276560 : Int) atom0989) := by
  rw [SparsePolynomial.eval_scale, eval_atom0989]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0990 : SparsePolynomial.Poly := [([8,15,15], 1)]
theorem eval_atom0990 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0990 = ((g 8) * (g 15) * (g 15)) := by
  norm_num [atom0990, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0990_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4506685440 : Int) atom0990) := by
  rw [SparsePolynomial.eval_scale, eval_atom0990]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0991 : SparsePolynomial.Poly := [([8,15,16], 1)]
theorem eval_atom0991 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0991 = ((g 8) * (g 15) * (g 16)) := by
  norm_num [atom0991, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0991_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8103102720 : Int) atom0991) := by
  rw [SparsePolynomial.eval_scale, eval_atom0991]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0992 : SparsePolynomial.Poly := [([8,15,17], 1)]
theorem eval_atom0992 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0992 = ((g 8) * (g 15) * (g 17)) := by
  norm_num [atom0992, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0992_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13606763520 : Int) atom0992) := by
  rw [SparsePolynomial.eval_scale, eval_atom0992]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0993 : SparsePolynomial.Poly := [([8,16,16], 1)]
theorem eval_atom0993 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0993 = ((g 8) * (g 16) * (g 16)) := by
  norm_num [atom0993, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0993_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2134348800 : Int) atom0993) := by
  rw [SparsePolynomial.eval_scale, eval_atom0993]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0994 : SparsePolynomial.Poly := [([8,16,17], 1)]
theorem eval_atom0994 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0994 = ((g 8) * (g 16) * (g 17)) := by
  norm_num [atom0994, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0994_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10271395200 : Int) atom0994) := by
  rw [SparsePolynomial.eval_scale, eval_atom0994]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0995 : SparsePolynomial.Poly := [([8,17,17], 1)]
theorem eval_atom0995 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0995 = ((g 8) * (g 17) * (g 17)) := by
  norm_num [atom0995, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0995_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7369979520 : Int) atom0995) := by
  rw [SparsePolynomial.eval_scale, eval_atom0995]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0996 : SparsePolynomial.Poly := [([9,9,9], 1)]
theorem eval_atom0996 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0996 = ((g 9) * (g 9) * (g 9)) := by
  norm_num [atom0996, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0996_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (116904960 : Int) atom0996) := by
  rw [SparsePolynomial.eval_scale, eval_atom0996]
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 9) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0997 : SparsePolynomial.Poly := [([9,9,14], 1)]
theorem eval_atom0997 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0997 = ((g 9) * (g 9) * (g 14)) := by
  norm_num [atom0997, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0997_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16292880 : Int) atom0997) := by
  rw [SparsePolynomial.eval_scale, eval_atom0997]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0998 : SparsePolynomial.Poly := [([9,10,10], 1)]
theorem eval_atom0998 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0998 = ((g 9) * (g 10) * (g 10)) := by
  norm_num [atom0998, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0998_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (115061760 : Int) atom0998) := by
  rw [SparsePolynomial.eval_scale, eval_atom0998]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 9) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0999 : SparsePolynomial.Poly := [([9,10,13], 1)]
theorem eval_atom0999 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0999 = ((g 9) * (g 10) * (g 13)) := by
  norm_num [atom0999, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0999_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (285358080 : Int) atom0999) := by
  rw [SparsePolynomial.eval_scale, eval_atom0999]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 9) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1000 : SparsePolynomial.Poly := [([9,10,14], 1)]
theorem eval_atom1000 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1000 = ((g 9) * (g 10) * (g 14)) := by
  norm_num [atom1000, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1000_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1766186400 : Int) atom1000) := by
  rw [SparsePolynomial.eval_scale, eval_atom1000]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1001 : SparsePolynomial.Poly := [([9,10,15], 1)]
theorem eval_atom1001 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1001 = ((g 9) * (g 10) * (g 15)) := by
  norm_num [atom1001, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1001_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1621401600 : Int) atom1001) := by
  rw [SparsePolynomial.eval_scale, eval_atom1001]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1002 : SparsePolynomial.Poly := [([9,10,16], 1)]
theorem eval_atom1002 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1002 = ((g 9) * (g 10) * (g 16)) := by
  norm_num [atom1002, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1002_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2672087040 : Int) atom1002) := by
  rw [SparsePolynomial.eval_scale, eval_atom1002]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1003 : SparsePolynomial.Poly := [([9,10,17], 1)]
theorem eval_atom1003 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1003 = ((g 9) * (g 10) * (g 17)) := by
  norm_num [atom1003, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1003_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4110834240 : Int) atom1003) := by
  rw [SparsePolynomial.eval_scale, eval_atom1003]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1004 : SparsePolynomial.Poly := [([9,11,11], 1)]
theorem eval_atom1004 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1004 = ((g 9) * (g 11) * (g 11)) := by
  norm_num [atom1004, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1004_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (684334080 : Int) atom1004) := by
  rw [SparsePolynomial.eval_scale, eval_atom1004]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 9) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1005 : SparsePolynomial.Poly := [([9,11,13], 1)]
theorem eval_atom1005 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1005 = ((g 9) * (g 11) * (g 13)) := by
  norm_num [atom1005, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1005_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (279352320 : Int) atom1005) := by
  rw [SparsePolynomial.eval_scale, eval_atom1005]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 9) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1006 : SparsePolynomial.Poly := [([9,11,14], 1)]
theorem eval_atom1006 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1006 = ((g 9) * (g 11) * (g 14)) := by
  norm_num [atom1006, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1006_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3051218400 : Int) atom1006) := by
  rw [SparsePolynomial.eval_scale, eval_atom1006]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1007 : SparsePolynomial.Poly := [([9,11,15], 1)]
theorem eval_atom1007 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1007 = ((g 9) * (g 11) * (g 15)) := by
  norm_num [atom1007, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1007_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3584509440 : Int) atom1007) := by
  rw [SparsePolynomial.eval_scale, eval_atom1007]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1008 : SparsePolynomial.Poly := [([9,11,16], 1)]
theorem eval_atom1008 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1008 = ((g 9) * (g 11) * (g 16)) := by
  norm_num [atom1008, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1008_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4543349760 : Int) atom1008) := by
  rw [SparsePolynomial.eval_scale, eval_atom1008]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1009 : SparsePolynomial.Poly := [([9,11,17], 1)]
theorem eval_atom1009 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1009 = ((g 9) * (g 11) * (g 17)) := by
  norm_num [atom1009, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1009_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9320682240 : Int) atom1009) := by
  rw [SparsePolynomial.eval_scale, eval_atom1009]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1010 : SparsePolynomial.Poly := [([9,12,12], 1)]
theorem eval_atom1010 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1010 = ((g 9) * (g 12) * (g 12)) := by
  norm_num [atom1010, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1010_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1234574880 : Int) atom1010) := by
  rw [SparsePolynomial.eval_scale, eval_atom1010]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 9) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1011 : SparsePolynomial.Poly := [([9,12,13], 1)]
theorem eval_atom1011 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1011 = ((g 9) * (g 12) * (g 13)) := by
  norm_num [atom1011, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1011_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3395495520 : Int) atom1011) := by
  rw [SparsePolynomial.eval_scale, eval_atom1011]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 9) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1012 : SparsePolynomial.Poly := [([9,12,14], 1)]
theorem eval_atom1012 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1012 = ((g 9) * (g 12) * (g 14)) := by
  norm_num [atom1012, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1012_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9850293120 : Int) atom1012) := by
  rw [SparsePolynomial.eval_scale, eval_atom1012]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1013 : SparsePolynomial.Poly := [([9,12,15], 1)]
theorem eval_atom1013 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1013 = ((g 9) * (g 12) * (g 15)) := by
  norm_num [atom1013, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1013_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10984189680 : Int) atom1013) := by
  rw [SparsePolynomial.eval_scale, eval_atom1013]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1014 : SparsePolynomial.Poly := [([9,12,16], 1)]
theorem eval_atom1014 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1014 = ((g 9) * (g 12) * (g 16)) := by
  norm_num [atom1014, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1014_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8721034080 : Int) atom1014) := by
  rw [SparsePolynomial.eval_scale, eval_atom1014]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1015 : SparsePolynomial.Poly := [([9,12,17], 1)]
theorem eval_atom1015 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1015 = ((g 9) * (g 12) * (g 17)) := by
  norm_num [atom1015, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1015_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15410525400 : Int) atom1015) := by
  rw [SparsePolynomial.eval_scale, eval_atom1015]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1016 : SparsePolynomial.Poly := [([9,13,13], 1)]
theorem eval_atom1016 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1016 = ((g 9) * (g 13) * (g 13)) := by
  norm_num [atom1016, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1016_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1293992448 : Int) atom1016) := by
  rw [SparsePolynomial.eval_scale, eval_atom1016]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 9) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1017 : SparsePolynomial.Poly := [([9,13,14], 1)]
theorem eval_atom1017 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1017 = ((g 9) * (g 13) * (g 14)) := by
  norm_num [atom1017, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1017_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8110518360 : Int) atom1017) := by
  rw [SparsePolynomial.eval_scale, eval_atom1017]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1018 : SparsePolynomial.Poly := [([9,13,15], 1)]
theorem eval_atom1018 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1018 = ((g 9) * (g 13) * (g 15)) := by
  norm_num [atom1018, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1018_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10591613040 : Int) atom1018) := by
  rw [SparsePolynomial.eval_scale, eval_atom1018]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1019 : SparsePolynomial.Poly := [([9,13,16], 1)]
theorem eval_atom1019 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1019 = ((g 9) * (g 13) * (g 16)) := by
  norm_num [atom1019, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1019_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9273572160 : Int) atom1019) := by
  rw [SparsePolynomial.eval_scale, eval_atom1019]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1020 : SparsePolynomial.Poly := [([9,13,17], 1)]
theorem eval_atom1020 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1020 = ((g 9) * (g 13) * (g 17)) := by
  norm_num [atom1020, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1020_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13553859240 : Int) atom1020) := by
  rw [SparsePolynomial.eval_scale, eval_atom1020]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1021 : SparsePolynomial.Poly := [([9,14,14], 1)]
theorem eval_atom1021 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1021 = ((g 9) * (g 14) * (g 14)) := by
  norm_num [atom1021, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1021_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7312572600 : Int) atom1021) := by
  rw [SparsePolynomial.eval_scale, eval_atom1021]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1022 : SparsePolynomial.Poly := [([9,14,15], 1)]
theorem eval_atom1022 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1022 = ((g 9) * (g 14) * (g 15)) := by
  norm_num [atom1022, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1022_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13858747800 : Int) atom1022) := by
  rw [SparsePolynomial.eval_scale, eval_atom1022]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1023 : SparsePolynomial.Poly := [([9,14,16], 1)]
theorem eval_atom1023 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1023 = ((g 9) * (g 14) * (g 16)) := by
  norm_num [atom1023, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1023_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12444452400 : Int) atom1023) := by
  rw [SparsePolynomial.eval_scale, eval_atom1023]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1024 : SparsePolynomial.Poly := [([9,14,17], 1)]
theorem eval_atom1024 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1024 = ((g 9) * (g 14) * (g 17)) := by
  norm_num [atom1024, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1024_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18040793520 : Int) atom1024) := by
  rw [SparsePolynomial.eval_scale, eval_atom1024]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1025 : SparsePolynomial.Poly := [([9,15,15], 1)]
theorem eval_atom1025 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1025 = ((g 9) * (g 15) * (g 15)) := by
  norm_num [atom1025, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1025_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5224906320 : Int) atom1025) := by
  rw [SparsePolynomial.eval_scale, eval_atom1025]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1026 : SparsePolynomial.Poly := [([9,15,16], 1)]
theorem eval_atom1026 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1026 = ((g 9) * (g 15) * (g 16)) := by
  norm_num [atom1026, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1026_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10468372560 : Int) atom1026) := by
  rw [SparsePolynomial.eval_scale, eval_atom1026]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1027 : SparsePolynomial.Poly := [([9,15,17], 1)]
theorem eval_atom1027 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1027 = ((g 9) * (g 15) * (g 17)) := by
  norm_num [atom1027, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1027_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16825456200 : Int) atom1027) := by
  rw [SparsePolynomial.eval_scale, eval_atom1027]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1028 : SparsePolynomial.Poly := [([9,16,16], 1)]
theorem eval_atom1028 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1028 = ((g 9) * (g 16) * (g 16)) := by
  norm_num [atom1028, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1028_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3736455360 : Int) atom1028) := by
  rw [SparsePolynomial.eval_scale, eval_atom1028]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1029 : SparsePolynomial.Poly := [([9,16,17], 1)]
theorem eval_atom1029 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1029 = ((g 9) * (g 16) * (g 17)) := by
  norm_num [atom1029, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1029_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14476765080 : Int) atom1029) := by
  rw [SparsePolynomial.eval_scale, eval_atom1029]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1030 : SparsePolynomial.Poly := [([9,17,17], 1)]
theorem eval_atom1030 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1030 = ((g 9) * (g 17) * (g 17)) := by
  norm_num [atom1030, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1030_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9901097400 : Int) atom1030) := by
  rw [SparsePolynomial.eval_scale, eval_atom1030]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1031 : SparsePolynomial.Poly := [([10,10,10], 1)]
theorem eval_atom1031 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1031 = ((g 10) * (g 10) * (g 10)) := by
  norm_num [atom1031, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1031_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (111329280 : Int) atom1031) := by
  rw [SparsePolynomial.eval_scale, eval_atom1031]
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 10) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1032 : SparsePolynomial.Poly := [([10,10,14], 1)]
theorem eval_atom1032 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1032 = ((g 10) * (g 10) * (g 14)) := by
  norm_num [atom1032, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1032_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (608461200 : Int) atom1032) := by
  rw [SparsePolynomial.eval_scale, eval_atom1032]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 10) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1033 : SparsePolynomial.Poly := [([10,10,17], 1)]
theorem eval_atom1033 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1033 = ((g 10) * (g 10) * (g 17)) := by
  norm_num [atom1033, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1033_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (290756160 : Int) atom1033) := by
  rw [SparsePolynomial.eval_scale, eval_atom1033]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1034 : SparsePolynomial.Poly := [([10,11,11], 1)]
theorem eval_atom1034 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1034 = ((g 10) * (g 11) * (g 11)) := by
  norm_num [atom1034, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1034_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (361543680 : Int) atom1034) := by
  rw [SparsePolynomial.eval_scale, eval_atom1034]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 10) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1035 : SparsePolynomial.Poly := [([10,11,13], 1)]
theorem eval_atom1035 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1035 = ((g 10) * (g 11) * (g 13)) := by
  norm_num [atom1035, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1035_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (563374080 : Int) atom1035) := by
  rw [SparsePolynomial.eval_scale, eval_atom1035]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 10) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1036 : SparsePolynomial.Poly := [([10,11,14], 1)]
theorem eval_atom1036 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1036 = ((g 10) * (g 11) * (g 14)) := by
  norm_num [atom1036, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1036_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3488312160 : Int) atom1036) := by
  rw [SparsePolynomial.eval_scale, eval_atom1036]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 10) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1037 : SparsePolynomial.Poly := [([10,11,15], 1)]
theorem eval_atom1037 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1037 = ((g 10) * (g 11) * (g 15)) := by
  norm_num [atom1037, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1037_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3183114240 : Int) atom1037) := by
  rw [SparsePolynomial.eval_scale, eval_atom1037]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 10) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1038 : SparsePolynomial.Poly := [([10,11,16], 1)]
theorem eval_atom1038 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1038 = ((g 10) * (g 11) * (g 16)) := by
  norm_num [atom1038, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1038_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3172515840 : Int) atom1038) := by
  rw [SparsePolynomial.eval_scale, eval_atom1038]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 10) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1039 : SparsePolynomial.Poly := [([10,11,17], 1)]
theorem eval_atom1039 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1039 = ((g 10) * (g 11) * (g 17)) := by
  norm_num [atom1039, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1039_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7005994560 : Int) atom1039) := by
  rw [SparsePolynomial.eval_scale, eval_atom1039]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1040 : SparsePolynomial.Poly := [([10,12,12], 1)]
theorem eval_atom1040 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1040 = ((g 10) * (g 12) * (g 12)) := by
  norm_num [atom1040, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1040_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (607054560 : Int) atom1040) := by
  rw [SparsePolynomial.eval_scale, eval_atom1040]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 10) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1041 : SparsePolynomial.Poly := [([10,12,13], 1)]
theorem eval_atom1041 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1041 = ((g 10) * (g 12) * (g 13)) := by
  norm_num [atom1041, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1041_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2189573280 : Int) atom1041) := by
  rw [SparsePolynomial.eval_scale, eval_atom1041]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 10) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1042 : SparsePolynomial.Poly := [([10,12,14], 1)]
theorem eval_atom1042 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1042 = ((g 10) * (g 12) * (g 14)) := by
  norm_num [atom1042, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1042_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8978554560 : Int) atom1042) := by
  rw [SparsePolynomial.eval_scale, eval_atom1042]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 10) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1043 : SparsePolynomial.Poly := [([10,12,15], 1)]
theorem eval_atom1043 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1043 = ((g 10) * (g 12) * (g 15)) := by
  norm_num [atom1043, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1043_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9933636240 : Int) atom1043) := by
  rw [SparsePolynomial.eval_scale, eval_atom1043]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 10) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1044 : SparsePolynomial.Poly := [([10,12,16], 1)]
theorem eval_atom1044 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1044 = ((g 10) * (g 12) * (g 16)) := by
  norm_num [atom1044, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1044_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7760603040 : Int) atom1044) := by
  rw [SparsePolynomial.eval_scale, eval_atom1044]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 10) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1045 : SparsePolynomial.Poly := [([10,12,17], 1)]
theorem eval_atom1045 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1045 = ((g 10) * (g 12) * (g 17)) := by
  norm_num [atom1045, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1045_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14735798280 : Int) atom1045) := by
  rw [SparsePolynomial.eval_scale, eval_atom1045]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1046 : SparsePolynomial.Poly := [([10,13,13], 1)]
theorem eval_atom1046 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1046 = ((g 10) * (g 13) * (g 13)) := by
  norm_num [atom1046, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1046_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (822409728 : Int) atom1046) := by
  rw [SparsePolynomial.eval_scale, eval_atom1046]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 10) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1047 : SparsePolynomial.Poly := [([10,13,14], 1)]
theorem eval_atom1047 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1047 = ((g 10) * (g 13) * (g 14)) := by
  norm_num [atom1047, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1047_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7688157720 : Int) atom1047) := by
  rw [SparsePolynomial.eval_scale, eval_atom1047]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 10) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1048 : SparsePolynomial.Poly := [([10,13,15], 1)]
theorem eval_atom1048 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1048 = ((g 10) * (g 13) * (g 15)) := by
  norm_num [atom1048, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1048_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10652866320 : Int) atom1048) := by
  rw [SparsePolynomial.eval_scale, eval_atom1048]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 10) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1049 : SparsePolynomial.Poly := [([10,13,16], 1)]
theorem eval_atom1049 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1049 = ((g 10) * (g 13) * (g 16)) := by
  norm_num [atom1049, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1049_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9786183360 : Int) atom1049) := by
  rw [SparsePolynomial.eval_scale, eval_atom1049]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 10) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1050 : SparsePolynomial.Poly := [([10,13,17], 1)]
theorem eval_atom1050 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1050 = ((g 10) * (g 13) * (g 17)) := by
  norm_num [atom1050, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1050_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14531488920 : Int) atom1050) := by
  rw [SparsePolynomial.eval_scale, eval_atom1050]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1051 : SparsePolynomial.Poly := [([10,14,14], 1)]
theorem eval_atom1051 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1051 = ((g 10) * (g 14) * (g 14)) := by
  norm_num [atom1051, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1051_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7183548600 : Int) atom1051) := by
  rw [SparsePolynomial.eval_scale, eval_atom1051]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 10) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1052 : SparsePolynomial.Poly := [([10,14,15], 1)]
theorem eval_atom1052 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1052 = ((g 10) * (g 14) * (g 15)) := by
  norm_num [atom1052, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1052_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14604209880 : Int) atom1052) := by
  rw [SparsePolynomial.eval_scale, eval_atom1052]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 10) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1053 : SparsePolynomial.Poly := [([10,14,16], 1)]
theorem eval_atom1053 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1053 = ((g 10) * (g 14) * (g 16)) := by
  norm_num [atom1053, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1053_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13859975280 : Int) atom1053) := by
  rw [SparsePolynomial.eval_scale, eval_atom1053]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 10) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1054 : SparsePolynomial.Poly := [([10,14,17], 1)]
theorem eval_atom1054 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1054 = ((g 10) * (g 14) * (g 17)) := by
  norm_num [atom1054, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1054_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19964871120 : Int) atom1054) := by
  rw [SparsePolynomial.eval_scale, eval_atom1054]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block013 : SparsePolynomial.Poly := [([8,12,12], 1914984960), ([8,12,13], 4619473920), ([8,12,14], 10744620960), ([8,12,15], 11856384000), ([8,12,16], 9369254400), ([8,12,17], 15816660480), ([8,13,13], 1790734848), ([8,13,14], 8615461560), ([8,13,15], 10629073920), ([8,13,16], 8825487360), ([8,13,17], 12648821760), ([8,14,14], 7466756280), ([8,14,15], 13350688440), ([8,14,16], 11285680080), ([8,14,17], 16222276560), ([8,15,15], 4506685440), ([8,15,16], 8103102720), ([8,15,17], 13606763520), ([8,16,16], 2134348800), ([8,16,17], 10271395200), ([8,17,17], 7369979520), ([9,9,9], 116904960), ([9,9,14], 16292880), ([9,10,10], 115061760), ([9,10,13], 285358080), ([9,10,14], 1766186400), ([9,10,15], 1621401600), ([9,10,16], 2672087040), ([9,10,17], 4110834240), ([9,11,11], 684334080), ([9,11,13], 279352320), ([9,11,14], 3051218400), ([9,11,15], 3584509440), ([9,11,16], 4543349760), ([9,11,17], 9320682240), ([9,12,12], 1234574880), ([9,12,13], 3395495520), ([9,12,14], 9850293120), ([9,12,15], 10984189680), ([9,12,16], 8721034080), ([9,12,17], 15410525400), ([9,13,13], 1293992448), ([9,13,14], 8110518360), ([9,13,15], 10591613040), ([9,13,16], 9273572160), ([9,13,17], 13553859240), ([9,14,14], 7312572600), ([9,14,15], 13858747800), ([9,14,16], 12444452400), ([9,14,17], 18040793520), ([9,15,15], 5224906320), ([9,15,16], 10468372560), ([9,15,17], 16825456200), ([9,16,16], 3736455360), ([9,16,17], 14476765080), ([9,17,17], 9901097400), ([10,10,10], 111329280), ([10,10,14], 608461200), ([10,10,17], 290756160), ([10,11,11], 361543680), ([10,11,13], 563374080), ([10,11,14], 3488312160), ([10,11,15], 3183114240), ([10,11,16], 3172515840), ([10,11,17], 7005994560), ([10,12,12], 607054560), ([10,12,13], 2189573280), ([10,12,14], 8978554560), ([10,12,15], 9933636240), ([10,12,16], 7760603040), ([10,12,17], 14735798280), ([10,13,13], 822409728), ([10,13,14], 7688157720), ([10,13,15], 10652866320), ([10,13,16], 9786183360), ([10,13,17], 14531488920), ([10,14,14], 7183548600), ([10,14,15], 14604209880), ([10,14,16], 13859975280), ([10,14,17], 19964871120)]
theorem block013_data : block013 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1914984960 : Int) atom0975) (SparsePolynomial.scale (4619473920 : Int) atom0976)) (SparsePolynomial.merge (SparsePolynomial.scale (10744620960 : Int) atom0977) (SparsePolynomial.merge (SparsePolynomial.scale (11856384000 : Int) atom0978) (SparsePolynomial.scale (9369254400 : Int) atom0979)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (15816660480 : Int) atom0980) (SparsePolynomial.scale (1790734848 : Int) atom0981)) (SparsePolynomial.merge (SparsePolynomial.scale (8615461560 : Int) atom0982) (SparsePolynomial.merge (SparsePolynomial.scale (10629073920 : Int) atom0983) (SparsePolynomial.scale (8825487360 : Int) atom0984))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (12648821760 : Int) atom0985) (SparsePolynomial.scale (7466756280 : Int) atom0986)) (SparsePolynomial.merge (SparsePolynomial.scale (13350688440 : Int) atom0987) (SparsePolynomial.merge (SparsePolynomial.scale (11285680080 : Int) atom0988) (SparsePolynomial.scale (16222276560 : Int) atom0989)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (4506685440 : Int) atom0990) (SparsePolynomial.scale (8103102720 : Int) atom0991)) (SparsePolynomial.merge (SparsePolynomial.scale (13606763520 : Int) atom0992) (SparsePolynomial.merge (SparsePolynomial.scale (2134348800 : Int) atom0993) (SparsePolynomial.scale (10271395200 : Int) atom0994)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (7369979520 : Int) atom0995) (SparsePolynomial.scale (116904960 : Int) atom0996)) (SparsePolynomial.merge (SparsePolynomial.scale (16292880 : Int) atom0997) (SparsePolynomial.merge (SparsePolynomial.scale (115061760 : Int) atom0998) (SparsePolynomial.scale (285358080 : Int) atom0999)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1766186400 : Int) atom1000) (SparsePolynomial.scale (1621401600 : Int) atom1001)) (SparsePolynomial.merge (SparsePolynomial.scale (2672087040 : Int) atom1002) (SparsePolynomial.merge (SparsePolynomial.scale (4110834240 : Int) atom1003) (SparsePolynomial.scale (684334080 : Int) atom1004))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (279352320 : Int) atom1005) (SparsePolynomial.scale (3051218400 : Int) atom1006)) (SparsePolynomial.merge (SparsePolynomial.scale (3584509440 : Int) atom1007) (SparsePolynomial.merge (SparsePolynomial.scale (4543349760 : Int) atom1008) (SparsePolynomial.scale (9320682240 : Int) atom1009)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1234574880 : Int) atom1010) (SparsePolynomial.scale (3395495520 : Int) atom1011)) (SparsePolynomial.merge (SparsePolynomial.scale (9850293120 : Int) atom1012) (SparsePolynomial.merge (SparsePolynomial.scale (10984189680 : Int) atom1013) (SparsePolynomial.scale (8721034080 : Int) atom1014))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (15410525400 : Int) atom1015) (SparsePolynomial.scale (1293992448 : Int) atom1016)) (SparsePolynomial.merge (SparsePolynomial.scale (8110518360 : Int) atom1017) (SparsePolynomial.merge (SparsePolynomial.scale (10591613040 : Int) atom1018) (SparsePolynomial.scale (9273572160 : Int) atom1019)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (13553859240 : Int) atom1020) (SparsePolynomial.scale (7312572600 : Int) atom1021)) (SparsePolynomial.merge (SparsePolynomial.scale (13858747800 : Int) atom1022) (SparsePolynomial.merge (SparsePolynomial.scale (12444452400 : Int) atom1023) (SparsePolynomial.scale (18040793520 : Int) atom1024))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (5224906320 : Int) atom1025) (SparsePolynomial.scale (10468372560 : Int) atom1026)) (SparsePolynomial.merge (SparsePolynomial.scale (16825456200 : Int) atom1027) (SparsePolynomial.merge (SparsePolynomial.scale (3736455360 : Int) atom1028) (SparsePolynomial.scale (14476765080 : Int) atom1029)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (9901097400 : Int) atom1030) (SparsePolynomial.scale (111329280 : Int) atom1031)) (SparsePolynomial.merge (SparsePolynomial.scale (608461200 : Int) atom1032) (SparsePolynomial.merge (SparsePolynomial.scale (290756160 : Int) atom1033) (SparsePolynomial.scale (361543680 : Int) atom1034)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (563374080 : Int) atom1035) (SparsePolynomial.scale (3488312160 : Int) atom1036)) (SparsePolynomial.merge (SparsePolynomial.scale (3183114240 : Int) atom1037) (SparsePolynomial.merge (SparsePolynomial.scale (3172515840 : Int) atom1038) (SparsePolynomial.scale (7005994560 : Int) atom1039)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (607054560 : Int) atom1040) (SparsePolynomial.scale (2189573280 : Int) atom1041)) (SparsePolynomial.merge (SparsePolynomial.scale (8978554560 : Int) atom1042) (SparsePolynomial.merge (SparsePolynomial.scale (9933636240 : Int) atom1043) (SparsePolynomial.scale (7760603040 : Int) atom1044))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (14735798280 : Int) atom1045) (SparsePolynomial.scale (822409728 : Int) atom1046)) (SparsePolynomial.merge (SparsePolynomial.scale (7688157720 : Int) atom1047) (SparsePolynomial.merge (SparsePolynomial.scale (10652866320 : Int) atom1048) (SparsePolynomial.scale (9786183360 : Int) atom1049)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (14531488920 : Int) atom1050) (SparsePolynomial.scale (7183548600 : Int) atom1051)) (SparsePolynomial.merge (SparsePolynomial.scale (14604209880 : Int) atom1052) (SparsePolynomial.merge (SparsePolynomial.scale (13859975280 : Int) atom1053) (SparsePolynomial.scale (19964871120 : Int) atom1054)))))))) := by decide +kernel
theorem block013_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block013 := by
  rw [block013_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0975_nonneg g hg hA hB) (atom0976_nonneg g hg hA hB)) (add_nonneg (atom0977_nonneg g hg hA hB) (add_nonneg (atom0978_nonneg g hg hA hB) (atom0979_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0980_nonneg g hg hA hB) (atom0981_nonneg g hg hA hB)) (add_nonneg (atom0982_nonneg g hg hA hB) (add_nonneg (atom0983_nonneg g hg hA hB) (atom0984_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0985_nonneg g hg hA hB) (atom0986_nonneg g hg hA hB)) (add_nonneg (atom0987_nonneg g hg hA hB) (add_nonneg (atom0988_nonneg g hg hA hB) (atom0989_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0990_nonneg g hg hA hB) (atom0991_nonneg g hg hA hB)) (add_nonneg (atom0992_nonneg g hg hA hB) (add_nonneg (atom0993_nonneg g hg hA hB) (atom0994_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0995_nonneg g hg hA hB) (atom0996_nonneg g hg hA hB)) (add_nonneg (atom0997_nonneg g hg hA hB) (add_nonneg (atom0998_nonneg g hg hA hB) (atom0999_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1000_nonneg g hg hA hB) (atom1001_nonneg g hg hA hB)) (add_nonneg (atom1002_nonneg g hg hA hB) (add_nonneg (atom1003_nonneg g hg hA hB) (atom1004_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1005_nonneg g hg hA hB) (atom1006_nonneg g hg hA hB)) (add_nonneg (atom1007_nonneg g hg hA hB) (add_nonneg (atom1008_nonneg g hg hA hB) (atom1009_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1010_nonneg g hg hA hB) (atom1011_nonneg g hg hA hB)) (add_nonneg (atom1012_nonneg g hg hA hB) (add_nonneg (atom1013_nonneg g hg hA hB) (atom1014_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1015_nonneg g hg hA hB) (atom1016_nonneg g hg hA hB)) (add_nonneg (atom1017_nonneg g hg hA hB) (add_nonneg (atom1018_nonneg g hg hA hB) (atom1019_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1020_nonneg g hg hA hB) (atom1021_nonneg g hg hA hB)) (add_nonneg (atom1022_nonneg g hg hA hB) (add_nonneg (atom1023_nonneg g hg hA hB) (atom1024_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1025_nonneg g hg hA hB) (atom1026_nonneg g hg hA hB)) (add_nonneg (atom1027_nonneg g hg hA hB) (add_nonneg (atom1028_nonneg g hg hA hB) (atom1029_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1030_nonneg g hg hA hB) (atom1031_nonneg g hg hA hB)) (add_nonneg (atom1032_nonneg g hg hA hB) (add_nonneg (atom1033_nonneg g hg hA hB) (atom1034_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1035_nonneg g hg hA hB) (atom1036_nonneg g hg hA hB)) (add_nonneg (atom1037_nonneg g hg hA hB) (add_nonneg (atom1038_nonneg g hg hA hB) (atom1039_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1040_nonneg g hg hA hB) (atom1041_nonneg g hg hA hB)) (add_nonneg (atom1042_nonneg g hg hA hB) (add_nonneg (atom1043_nonneg g hg hA hB) (atom1044_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1045_nonneg g hg hA hB) (atom1046_nonneg g hg hA hB)) (add_nonneg (atom1047_nonneg g hg hA hB) (add_nonneg (atom1048_nonneg g hg hA hB) (atom1049_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1050_nonneg g hg hA hB) (atom1051_nonneg g hg hA hB)) (add_nonneg (atom1052_nonneg g hg hA hB) (add_nonneg (atom1053_nonneg g hg hA hB) (atom1054_nonneg g hg hA hB))))))))

end APPT.Finite18
