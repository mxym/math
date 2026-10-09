import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom0976 : SparsePolynomial.Poly := [([4,7,20], 1)]
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
def atom0977 : SparsePolynomial.Poly := [([4,8,8], 1)]
theorem eval_atom0977 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0977 = ((g 4) * (g 8) * (g 8)) := by
  norm_num [atom0977, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0977_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8316316713600 : Int) atom0977) := by
  rw [SparsePolynomial.eval_scale, eval_atom0977]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0978 : SparsePolynomial.Poly := [([4,8,9], 1)]
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
def atom0979 : SparsePolynomial.Poly := [([4,8,10], 1)]
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
def atom0980 : SparsePolynomial.Poly := [([4,8,11], 1)]
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
def atom0981 : SparsePolynomial.Poly := [([4,8,12], 1)]
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
def atom0982 : SparsePolynomial.Poly := [([4,8,13], 1)]
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
def atom0983 : SparsePolynomial.Poly := [([4,8,14], 1)]
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
def atom0984 : SparsePolynomial.Poly := [([4,8,15], 1)]
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
def atom0985 : SparsePolynomial.Poly := [([4,8,16], 1)]
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
def atom0986 : SparsePolynomial.Poly := [([4,8,17], 1)]
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
def atom0987 : SparsePolynomial.Poly := [([4,8,18], 1)]
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
def atom0988 : SparsePolynomial.Poly := [([4,8,19], 1)]
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
def atom0989 : SparsePolynomial.Poly := [([4,8,20], 1)]
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
def atom0990 : SparsePolynomial.Poly := [([4,9,9], 1)]
theorem eval_atom0990 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0990 = ((g 4) * (g 9) * (g 9)) := by
  norm_num [atom0990, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0990_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10739741241600 : Int) atom0990) := by
  rw [SparsePolynomial.eval_scale, eval_atom0990]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0991 : SparsePolynomial.Poly := [([4,9,10], 1)]
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
def atom0992 : SparsePolynomial.Poly := [([4,9,11], 1)]
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
def atom0993 : SparsePolynomial.Poly := [([4,9,12], 1)]
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
def atom0994 : SparsePolynomial.Poly := [([4,9,13], 1)]
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
def atom0995 : SparsePolynomial.Poly := [([4,9,14], 1)]
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
def atom0996 : SparsePolynomial.Poly := [([4,9,15], 1)]
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
def atom0997 : SparsePolynomial.Poly := [([4,9,16], 1)]
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
def atom0998 : SparsePolynomial.Poly := [([4,9,17], 1)]
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
def atom0999 : SparsePolynomial.Poly := [([4,9,18], 1)]
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
def atom1000 : SparsePolynomial.Poly := [([4,9,19], 1)]
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
def atom1001 : SparsePolynomial.Poly := [([4,9,20], 1)]
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
def atom1002 : SparsePolynomial.Poly := [([4,10,10], 1)]
theorem eval_atom1002 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1002 = ((g 4) * (g 10) * (g 10)) := by
  norm_num [atom1002, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1002_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13470986592000 : Int) atom1002) := by
  rw [SparsePolynomial.eval_scale, eval_atom1002]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1003 : SparsePolynomial.Poly := [([4,10,11], 1)]
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
def atom1004 : SparsePolynomial.Poly := [([4,10,12], 1)]
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
def atom1005 : SparsePolynomial.Poly := [([4,10,13], 1)]
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
def atom1006 : SparsePolynomial.Poly := [([4,10,14], 1)]
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
def atom1007 : SparsePolynomial.Poly := [([4,10,15], 1)]
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
def atom1008 : SparsePolynomial.Poly := [([4,10,16], 1)]
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
def atom1009 : SparsePolynomial.Poly := [([4,10,17], 1)]
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
def atom1010 : SparsePolynomial.Poly := [([4,10,18], 1)]
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
def atom1011 : SparsePolynomial.Poly := [([4,10,19], 1)]
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
def atom1012 : SparsePolynomial.Poly := [([4,10,20], 1)]
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
def atom1013 : SparsePolynomial.Poly := [([4,11,11], 1)]
theorem eval_atom1013 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1013 = ((g 4) * (g 11) * (g 11)) := by
  norm_num [atom1013, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1013_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16246935936000 : Int) atom1013) := by
  rw [SparsePolynomial.eval_scale, eval_atom1013]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1014 : SparsePolynomial.Poly := [([4,11,12], 1)]
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
def atom1015 : SparsePolynomial.Poly := [([4,11,13], 1)]
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
def atom1016 : SparsePolynomial.Poly := [([4,11,14], 1)]
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
def atom1017 : SparsePolynomial.Poly := [([4,11,15], 1)]
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
def atom1018 : SparsePolynomial.Poly := [([4,11,16], 1)]
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
def atom1019 : SparsePolynomial.Poly := [([4,11,17], 1)]
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
def atom1020 : SparsePolynomial.Poly := [([4,11,18], 1)]
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
def atom1021 : SparsePolynomial.Poly := [([4,11,19], 1)]
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
def atom1022 : SparsePolynomial.Poly := [([4,11,20], 1)]
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
def atom1023 : SparsePolynomial.Poly := [([4,12,12], 1)]
theorem eval_atom1023 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1023 = ((g 4) * (g 12) * (g 12)) := by
  norm_num [atom1023, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1023_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17118445881600 : Int) atom1023) := by
  rw [SparsePolynomial.eval_scale, eval_atom1023]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1024 : SparsePolynomial.Poly := [([4,12,13], 1)]
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
def atom1025 : SparsePolynomial.Poly := [([4,12,14], 1)]
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
def atom1026 : SparsePolynomial.Poly := [([4,12,15], 1)]
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
def atom1027 : SparsePolynomial.Poly := [([4,12,16], 1)]
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
def atom1028 : SparsePolynomial.Poly := [([4,12,17], 1)]
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
def atom1029 : SparsePolynomial.Poly := [([4,12,18], 1)]
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
def atom1030 : SparsePolynomial.Poly := [([4,12,19], 1)]
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
def atom1031 : SparsePolynomial.Poly := [([4,12,20], 1)]
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
def atom1032 : SparsePolynomial.Poly := [([4,13,13], 1)]
theorem eval_atom1032 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1032 = ((g 4) * (g 13) * (g 13)) := by
  norm_num [atom1032, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1032_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19975700563200 : Int) atom1032) := by
  rw [SparsePolynomial.eval_scale, eval_atom1032]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1033 : SparsePolynomial.Poly := [([4,13,14], 1)]
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
def atom1034 : SparsePolynomial.Poly := [([4,13,15], 1)]
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
def atom1035 : SparsePolynomial.Poly := [([4,13,16], 1)]
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
def atom1036 : SparsePolynomial.Poly := [([4,13,17], 1)]
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
def atom1037 : SparsePolynomial.Poly := [([4,13,18], 1)]
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
def atom1038 : SparsePolynomial.Poly := [([4,13,19], 1)]
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
def atom1039 : SparsePolynomial.Poly := [([4,13,20], 1)]
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
def atom1040 : SparsePolynomial.Poly := [([4,14,14], 1)]
theorem eval_atom1040 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1040 = ((g 4) * (g 14) * (g 14)) := by
  norm_num [atom1040, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1040_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23439806611200 : Int) atom1040) := by
  rw [SparsePolynomial.eval_scale, eval_atom1040]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1041 : SparsePolynomial.Poly := [([4,14,15], 1)]
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
def atom1042 : SparsePolynomial.Poly := [([4,14,16], 1)]
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
def atom1043 : SparsePolynomial.Poly := [([4,14,17], 1)]
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
def atom1044 : SparsePolynomial.Poly := [([4,14,18], 1)]
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
def atom1045 : SparsePolynomial.Poly := [([4,14,19], 1)]
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
def atom1046 : SparsePolynomial.Poly := [([4,14,20], 1)]
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
def atom1047 : SparsePolynomial.Poly := [([4,15,15], 1)]
theorem eval_atom1047 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1047 = ((g 4) * (g 15) * (g 15)) := by
  norm_num [atom1047, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1047_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27544406400000 : Int) atom1047) := by
  rw [SparsePolynomial.eval_scale, eval_atom1047]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1048 : SparsePolynomial.Poly := [([4,15,16], 1)]
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
def atom1049 : SparsePolynomial.Poly := [([4,15,17], 1)]
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
def atom1050 : SparsePolynomial.Poly := [([4,15,18], 1)]
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
def atom1051 : SparsePolynomial.Poly := [([4,15,19], 1)]
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
def atom1052 : SparsePolynomial.Poly := [([4,15,20], 1)]
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
def atom1053 : SparsePolynomial.Poly := [([4,16,16], 1)]
theorem eval_atom1053 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1053 = ((g 4) * (g 16) * (g 16)) := by
  norm_num [atom1053, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1053_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19150031093760 : Int) atom1053) := by
  rw [SparsePolynomial.eval_scale, eval_atom1053]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1054 : SparsePolynomial.Poly := [([4,16,17], 1)]
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
def atom1055 : SparsePolynomial.Poly := [([4,16,18], 1)]
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
def block014 : SparsePolynomial.Poly := [([4,7,20], 37738841800608), ([4,8,8], 8316316713600), ([4,8,9], 14616092937600), ([4,8,10], 14686645276800), ([4,8,11], 14704288099200), ([4,8,12], 13399306704000), ([4,8,13], 14099031273600), ([4,8,14], 14798755843200), ([4,8,15], 23245546060800), ([4,8,16], 20719776344400), ([4,8,17], 26086557772800), ([4,8,18], 31162368207600), ([4,8,19], 37890854593200), ([4,8,20], 44619340978800), ([4,9,9], 10739741241600), ([4,9,10], 19770762816000), ([4,9,11], 19283908089600), ([4,9,12], 18160623129600), ([4,9,13], 18614864217600), ([4,9,14], 19069105305600), ([4,9,15], 27327917030400), ([4,9,16], 24967957392000), ([4,9,17], 31850587238400), ([4,9,18], 35857179388800), ([4,9,19], 42965247024000), ([4,9,20], 50073314659200), ([4,10,10], 13470986592000), ([4,10,11], 25277957510400), ([4,10,12], 23313843302400), ([4,10,13], 23354435059200), ([4,10,14], 23395026816000), ([4,10,15], 31410288000000), ([4,10,16], 28735500628800), ([4,10,17], 37614616704000), ([4,10,18], 39335264740800), ([4,10,19], 46388243563200), ([4,10,20], 53441222385600), ([4,11,11], 16246935936000), ([4,11,12], 28498236883200), ([4,11,13], 27957013459200), ([4,11,14], 27415790035200), ([4,11,15], 34868811801600), ([4,11,16], 31796949592800), ([4,11,17], 42754799001600), ([4,11,18], 41641715556000), ([4,11,19], 48385300672800), ([4,11,20], 55128885789600), ([4,12,12], 17118445881600), ([4,12,13], 32518507392000), ([4,12,14], 31227302937600), ([4,12,15], 34633735248000), ([4,12,16], 33705364364000), ([4,12,17], 43390369097600), ([4,12,18], 42915361938400), ([4,12,19], 48592346426400), ([4,12,20], 55028408400000), ([4,13,13], 19975700563200), ([4,13,14], 36571516070400), ([4,13,15], 38601069393600), ([4,13,16], 36159816938400), ([4,13,17], 47594873289600), ([4,13,18], 47799330616800), ([4,13,19], 46286873474400), ([4,13,20], 58138510147200), ([4,14,14], 23439806611200), ([4,14,15], 42456561436800), ([4,14,16], 38495120076000), ([4,14,17], 53992907337600), ([4,14,18], 55096182136800), ([4,14,19], 48432127111200), ([4,14,20], 65831614531200), ([4,15,15], 27544406400000), ([4,15,16], 49565736486000), ([4,15,17], 69701433984000), ([4,15,18], 67506930565200), ([4,15,19], 46776865338000), ([4,15,20], 68668144750800), ([4,16,16], 19150031093760), ([4,16,17], 54894908250000), ([4,16,18], 55511190567000)]
theorem block014_data : block014 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (37738841800608 : Int) atom0976) (SparsePolynomial.scale (8316316713600 : Int) atom0977)) (SparsePolynomial.merge (SparsePolynomial.scale (14616092937600 : Int) atom0978) (SparsePolynomial.merge (SparsePolynomial.scale (14686645276800 : Int) atom0979) (SparsePolynomial.scale (14704288099200 : Int) atom0980)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (13399306704000 : Int) atom0981) (SparsePolynomial.scale (14099031273600 : Int) atom0982)) (SparsePolynomial.merge (SparsePolynomial.scale (14798755843200 : Int) atom0983) (SparsePolynomial.merge (SparsePolynomial.scale (23245546060800 : Int) atom0984) (SparsePolynomial.scale (20719776344400 : Int) atom0985))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (26086557772800 : Int) atom0986) (SparsePolynomial.scale (31162368207600 : Int) atom0987)) (SparsePolynomial.merge (SparsePolynomial.scale (37890854593200 : Int) atom0988) (SparsePolynomial.merge (SparsePolynomial.scale (44619340978800 : Int) atom0989) (SparsePolynomial.scale (10739741241600 : Int) atom0990)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (19770762816000 : Int) atom0991) (SparsePolynomial.scale (19283908089600 : Int) atom0992)) (SparsePolynomial.merge (SparsePolynomial.scale (18160623129600 : Int) atom0993) (SparsePolynomial.merge (SparsePolynomial.scale (18614864217600 : Int) atom0994) (SparsePolynomial.scale (19069105305600 : Int) atom0995)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (27327917030400 : Int) atom0996) (SparsePolynomial.scale (24967957392000 : Int) atom0997)) (SparsePolynomial.merge (SparsePolynomial.scale (31850587238400 : Int) atom0998) (SparsePolynomial.merge (SparsePolynomial.scale (35857179388800 : Int) atom0999) (SparsePolynomial.scale (42965247024000 : Int) atom1000)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (50073314659200 : Int) atom1001) (SparsePolynomial.scale (13470986592000 : Int) atom1002)) (SparsePolynomial.merge (SparsePolynomial.scale (25277957510400 : Int) atom1003) (SparsePolynomial.merge (SparsePolynomial.scale (23313843302400 : Int) atom1004) (SparsePolynomial.scale (23354435059200 : Int) atom1005))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (23395026816000 : Int) atom1006) (SparsePolynomial.scale (31410288000000 : Int) atom1007)) (SparsePolynomial.merge (SparsePolynomial.scale (28735500628800 : Int) atom1008) (SparsePolynomial.merge (SparsePolynomial.scale (37614616704000 : Int) atom1009) (SparsePolynomial.scale (39335264740800 : Int) atom1010)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (46388243563200 : Int) atom1011) (SparsePolynomial.scale (53441222385600 : Int) atom1012)) (SparsePolynomial.merge (SparsePolynomial.scale (16246935936000 : Int) atom1013) (SparsePolynomial.merge (SparsePolynomial.scale (28498236883200 : Int) atom1014) (SparsePolynomial.scale (27957013459200 : Int) atom1015))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (27415790035200 : Int) atom1016) (SparsePolynomial.scale (34868811801600 : Int) atom1017)) (SparsePolynomial.merge (SparsePolynomial.scale (31796949592800 : Int) atom1018) (SparsePolynomial.merge (SparsePolynomial.scale (42754799001600 : Int) atom1019) (SparsePolynomial.scale (41641715556000 : Int) atom1020)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (48385300672800 : Int) atom1021) (SparsePolynomial.scale (55128885789600 : Int) atom1022)) (SparsePolynomial.merge (SparsePolynomial.scale (17118445881600 : Int) atom1023) (SparsePolynomial.merge (SparsePolynomial.scale (32518507392000 : Int) atom1024) (SparsePolynomial.scale (31227302937600 : Int) atom1025))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (34633735248000 : Int) atom1026) (SparsePolynomial.scale (33705364364000 : Int) atom1027)) (SparsePolynomial.merge (SparsePolynomial.scale (43390369097600 : Int) atom1028) (SparsePolynomial.merge (SparsePolynomial.scale (42915361938400 : Int) atom1029) (SparsePolynomial.scale (48592346426400 : Int) atom1030)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (55028408400000 : Int) atom1031) (SparsePolynomial.scale (19975700563200 : Int) atom1032)) (SparsePolynomial.merge (SparsePolynomial.scale (36571516070400 : Int) atom1033) (SparsePolynomial.merge (SparsePolynomial.scale (38601069393600 : Int) atom1034) (SparsePolynomial.scale (36159816938400 : Int) atom1035)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (47594873289600 : Int) atom1036) (SparsePolynomial.scale (47799330616800 : Int) atom1037)) (SparsePolynomial.merge (SparsePolynomial.scale (46286873474400 : Int) atom1038) (SparsePolynomial.merge (SparsePolynomial.scale (58138510147200 : Int) atom1039) (SparsePolynomial.scale (23439806611200 : Int) atom1040)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (42456561436800 : Int) atom1041) (SparsePolynomial.scale (38495120076000 : Int) atom1042)) (SparsePolynomial.merge (SparsePolynomial.scale (53992907337600 : Int) atom1043) (SparsePolynomial.merge (SparsePolynomial.scale (55096182136800 : Int) atom1044) (SparsePolynomial.scale (48432127111200 : Int) atom1045))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (65831614531200 : Int) atom1046) (SparsePolynomial.scale (27544406400000 : Int) atom1047)) (SparsePolynomial.merge (SparsePolynomial.scale (49565736486000 : Int) atom1048) (SparsePolynomial.merge (SparsePolynomial.scale (69701433984000 : Int) atom1049) (SparsePolynomial.scale (67506930565200 : Int) atom1050)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (46776865338000 : Int) atom1051) (SparsePolynomial.scale (68668144750800 : Int) atom1052)) (SparsePolynomial.merge (SparsePolynomial.scale (19150031093760 : Int) atom1053) (SparsePolynomial.merge (SparsePolynomial.scale (54894908250000 : Int) atom1054) (SparsePolynomial.scale (55511190567000 : Int) atom1055)))))))) := by decide +kernel
theorem block014_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block014 := by
  rw [block014_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0976_nonneg g hg hA hB) (atom0977_nonneg g hg hA hB)) (add_nonneg (atom0978_nonneg g hg hA hB) (add_nonneg (atom0979_nonneg g hg hA hB) (atom0980_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0981_nonneg g hg hA hB) (atom0982_nonneg g hg hA hB)) (add_nonneg (atom0983_nonneg g hg hA hB) (add_nonneg (atom0984_nonneg g hg hA hB) (atom0985_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0986_nonneg g hg hA hB) (atom0987_nonneg g hg hA hB)) (add_nonneg (atom0988_nonneg g hg hA hB) (add_nonneg (atom0989_nonneg g hg hA hB) (atom0990_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0991_nonneg g hg hA hB) (atom0992_nonneg g hg hA hB)) (add_nonneg (atom0993_nonneg g hg hA hB) (add_nonneg (atom0994_nonneg g hg hA hB) (atom0995_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0996_nonneg g hg hA hB) (atom0997_nonneg g hg hA hB)) (add_nonneg (atom0998_nonneg g hg hA hB) (add_nonneg (atom0999_nonneg g hg hA hB) (atom1000_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1001_nonneg g hg hA hB) (atom1002_nonneg g hg hA hB)) (add_nonneg (atom1003_nonneg g hg hA hB) (add_nonneg (atom1004_nonneg g hg hA hB) (atom1005_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1006_nonneg g hg hA hB) (atom1007_nonneg g hg hA hB)) (add_nonneg (atom1008_nonneg g hg hA hB) (add_nonneg (atom1009_nonneg g hg hA hB) (atom1010_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1011_nonneg g hg hA hB) (atom1012_nonneg g hg hA hB)) (add_nonneg (atom1013_nonneg g hg hA hB) (add_nonneg (atom1014_nonneg g hg hA hB) (atom1015_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1016_nonneg g hg hA hB) (atom1017_nonneg g hg hA hB)) (add_nonneg (atom1018_nonneg g hg hA hB) (add_nonneg (atom1019_nonneg g hg hA hB) (atom1020_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1021_nonneg g hg hA hB) (atom1022_nonneg g hg hA hB)) (add_nonneg (atom1023_nonneg g hg hA hB) (add_nonneg (atom1024_nonneg g hg hA hB) (atom1025_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1026_nonneg g hg hA hB) (atom1027_nonneg g hg hA hB)) (add_nonneg (atom1028_nonneg g hg hA hB) (add_nonneg (atom1029_nonneg g hg hA hB) (atom1030_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1031_nonneg g hg hA hB) (atom1032_nonneg g hg hA hB)) (add_nonneg (atom1033_nonneg g hg hA hB) (add_nonneg (atom1034_nonneg g hg hA hB) (atom1035_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1036_nonneg g hg hA hB) (atom1037_nonneg g hg hA hB)) (add_nonneg (atom1038_nonneg g hg hA hB) (add_nonneg (atom1039_nonneg g hg hA hB) (atom1040_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1041_nonneg g hg hA hB) (atom1042_nonneg g hg hA hB)) (add_nonneg (atom1043_nonneg g hg hA hB) (add_nonneg (atom1044_nonneg g hg hA hB) (atom1045_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1046_nonneg g hg hA hB) (atom1047_nonneg g hg hA hB)) (add_nonneg (atom1048_nonneg g hg hA hB) (add_nonneg (atom1049_nonneg g hg hA hB) (atom1050_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1051_nonneg g hg hA hB) (atom1052_nonneg g hg hA hB)) (add_nonneg (atom1053_nonneg g hg hA hB) (add_nonneg (atom1054_nonneg g hg hA hB) (atom1055_nonneg g hg hA hB))))))))

end APPT.Finite21
