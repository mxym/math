import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom1969 : SparsePolynomial.Poly := [([8,13,23], 1)]
theorem eval_atom1969 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1969 = ((g 8) * (g 13) * (g 23)) := by
  norm_num [atom1969, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1969_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (476282593155600 : Int) atom1969) := by
  rw [SparsePolynomial.eval_scale, eval_atom1969]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 8) * (g 13) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1970 : SparsePolynomial.Poly := [([8,14,14], 1)]
theorem eval_atom1970 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1970 = ((g 8) * (g 14) * (g 14)) := by
  norm_num [atom1970, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1970_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (79390066694400 : Int) atom1970) := by
  rw [SparsePolynomial.eval_scale, eval_atom1970]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1971 : SparsePolynomial.Poly := [([8,14,15], 1)]
theorem eval_atom1971 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1971 = ((g 8) * (g 14) * (g 15)) := by
  norm_num [atom1971, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1971_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (153751587897600 : Int) atom1971) := by
  rw [SparsePolynomial.eval_scale, eval_atom1971]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1972 : SparsePolynomial.Poly := [([8,14,16], 1)]
theorem eval_atom1972 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1972 = ((g 8) * (g 14) * (g 16)) := by
  norm_num [atom1972, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1972_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (156940940217600 : Int) atom1972) := by
  rw [SparsePolynomial.eval_scale, eval_atom1972]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1973 : SparsePolynomial.Poly := [([8,14,17], 1)]
theorem eval_atom1973 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1973 = ((g 8) * (g 14) * (g 17)) := by
  norm_num [atom1973, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1973_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (160130292537600 : Int) atom1973) := by
  rw [SparsePolynomial.eval_scale, eval_atom1973]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1974 : SparsePolynomial.Poly := [([8,14,18], 1)]
theorem eval_atom1974 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1974 = ((g 8) * (g 14) * (g 18)) := by
  norm_num [atom1974, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1974_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (174436309555200 : Int) atom1974) := by
  rw [SparsePolynomial.eval_scale, eval_atom1974]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1975 : SparsePolynomial.Poly := [([8,14,19], 1)]
theorem eval_atom1975 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1975 = ((g 8) * (g 14) * (g 19)) := by
  norm_num [atom1975, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1975_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (177035188730400 : Int) atom1975) := by
  rw [SparsePolynomial.eval_scale, eval_atom1975]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1976 : SparsePolynomial.Poly := [([8,14,20], 1)]
theorem eval_atom1976 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1976 = ((g 8) * (g 14) * (g 20)) := by
  norm_num [atom1976, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1976_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (282193893273600 : Int) atom1976) := by
  rw [SparsePolynomial.eval_scale, eval_atom1976]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1977 : SparsePolynomial.Poly := [([8,14,21], 1)]
theorem eval_atom1977 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1977 = ((g 8) * (g 14) * (g 21)) := by
  norm_num [atom1977, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1977_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (312992405510400 : Int) atom1977) := by
  rw [SparsePolynomial.eval_scale, eval_atom1977]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 8) * (g 14) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1978 : SparsePolynomial.Poly := [([8,14,22], 1)]
theorem eval_atom1978 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1978 = ((g 8) * (g 14) * (g 22)) := by
  norm_num [atom1978, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1978_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (400790402258400 : Int) atom1978) := by
  rw [SparsePolynomial.eval_scale, eval_atom1978]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 8) * (g 14) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1979 : SparsePolynomial.Poly := [([8,14,23], 1)]
theorem eval_atom1979 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1979 = ((g 8) * (g 14) * (g 23)) := by
  norm_num [atom1979, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1979_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (510762813976800 : Int) atom1979) := by
  rw [SparsePolynomial.eval_scale, eval_atom1979]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 8) * (g 14) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1980 : SparsePolynomial.Poly := [([8,15,15], 1)]
theorem eval_atom1980 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1980 = ((g 8) * (g 15) * (g 15)) := by
  norm_num [atom1980, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1980_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (106212519705600 : Int) atom1980) := by
  rw [SparsePolynomial.eval_scale, eval_atom1980]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1981 : SparsePolynomial.Poly := [([8,15,16], 1)]
theorem eval_atom1981 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1981 = ((g 8) * (g 15) * (g 16)) := by
  norm_num [atom1981, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1981_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (199221120806400 : Int) atom1981) := by
  rw [SparsePolynomial.eval_scale, eval_atom1981]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1982 : SparsePolynomial.Poly := [([8,15,17], 1)]
theorem eval_atom1982 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1982 = ((g 8) * (g 15) * (g 17)) := by
  norm_num [atom1982, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1982_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (199369957248000 : Int) atom1982) := by
  rw [SparsePolynomial.eval_scale, eval_atom1982]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1983 : SparsePolynomial.Poly := [([8,15,18], 1)]
theorem eval_atom1983 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1983 = ((g 8) * (g 15) * (g 18)) := by
  norm_num [atom1983, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1983_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (218777971507200 : Int) atom1983) := by
  rw [SparsePolynomial.eval_scale, eval_atom1983]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1984 : SparsePolynomial.Poly := [([8,15,19], 1)]
theorem eval_atom1984 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1984 = ((g 8) * (g 15) * (g 19)) := by
  norm_num [atom1984, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1984_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (217143992217600 : Int) atom1984) := by
  rw [SparsePolynomial.eval_scale, eval_atom1984]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1985 : SparsePolynomial.Poly := [([8,15,20], 1)]
theorem eval_atom1985 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1985 = ((g 8) * (g 15) * (g 20)) := by
  norm_num [atom1985, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1985_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (356351811379200 : Int) atom1985) := by
  rw [SparsePolynomial.eval_scale, eval_atom1985]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1986 : SparsePolynomial.Poly := [([8,15,21], 1)]
theorem eval_atom1986 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1986 = ((g 8) * (g 15) * (g 21)) := by
  norm_num [atom1986, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1986_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (399197054995200 : Int) atom1986) := by
  rw [SparsePolynomial.eval_scale, eval_atom1986]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 8) * (g 15) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1987 : SparsePolynomial.Poly := [([8,15,22], 1)]
theorem eval_atom1987 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1987 = ((g 8) * (g 15) * (g 22)) := by
  norm_num [atom1987, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1987_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (428238524044800 : Int) atom1987) := by
  rw [SparsePolynomial.eval_scale, eval_atom1987]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 8) * (g 15) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1988 : SparsePolynomial.Poly := [([8,15,23], 1)]
theorem eval_atom1988 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1988 = ((g 8) * (g 15) * (g 23)) := by
  norm_num [atom1988, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1988_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (535818438288000 : Int) atom1988) := by
  rw [SparsePolynomial.eval_scale, eval_atom1988]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 8) * (g 15) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1989 : SparsePolynomial.Poly := [([8,16,16], 1)]
theorem eval_atom1989 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1989 = ((g 8) * (g 16) * (g 16)) := by
  norm_num [atom1989, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1989_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (127942640179200 : Int) atom1989) := by
  rw [SparsePolynomial.eval_scale, eval_atom1989]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1990 : SparsePolynomial.Poly := [([8,16,17], 1)]
theorem eval_atom1990 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1990 = ((g 8) * (g 16) * (g 17)) := by
  norm_num [atom1990, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1990_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (248889967603200 : Int) atom1990) := by
  rw [SparsePolynomial.eval_scale, eval_atom1990]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1991 : SparsePolynomial.Poly := [([8,16,18], 1)]
theorem eval_atom1991 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1991 = ((g 8) * (g 16) * (g 18)) := by
  norm_num [atom1991, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1991_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (245385868089600 : Int) atom1991) := by
  rw [SparsePolynomial.eval_scale, eval_atom1991]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1992 : SparsePolynomial.Poly := [([8,16,19], 1)]
theorem eval_atom1992 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1992 = ((g 8) * (g 16) * (g 19)) := by
  norm_num [atom1992, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1992_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (252748761753600 : Int) atom1992) := by
  rw [SparsePolynomial.eval_scale, eval_atom1992]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1993 : SparsePolynomial.Poly := [([8,16,20], 1)]
theorem eval_atom1993 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1993 = ((g 8) * (g 16) * (g 20)) := by
  norm_num [atom1993, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1993_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (400953453868800 : Int) atom1993) := by
  rw [SparsePolynomial.eval_scale, eval_atom1993]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1994 : SparsePolynomial.Poly := [([8,16,21], 1)]
theorem eval_atom1994 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1994 = ((g 8) * (g 16) * (g 21)) := by
  norm_num [atom1994, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1994_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (452889801302400 : Int) atom1994) := by
  rw [SparsePolynomial.eval_scale, eval_atom1994]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 8) * (g 16) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1995 : SparsePolynomial.Poly := [([8,16,22], 1)]
theorem eval_atom1995 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1995 = ((g 8) * (g 16) * (g 22)) := by
  norm_num [atom1995, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1995_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (433229377190400 : Int) atom1995) := by
  rw [SparsePolynomial.eval_scale, eval_atom1995]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 8) * (g 16) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1996 : SparsePolynomial.Poly := [([8,16,23], 1)]
theorem eval_atom1996 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1996 = ((g 8) * (g 16) * (g 23)) := by
  norm_num [atom1996, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1996_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (626482301659200 : Int) atom1996) := by
  rw [SparsePolynomial.eval_scale, eval_atom1996]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 8) * (g 16) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1997 : SparsePolynomial.Poly := [([8,17,17], 1)]
theorem eval_atom1997 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1997 = ((g 8) * (g 17) * (g 17)) := by
  norm_num [atom1997, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1997_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (151090250572800 : Int) atom1997) := by
  rw [SparsePolynomial.eval_scale, eval_atom1997]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1998 : SparsePolynomial.Poly := [([8,17,18], 1)]
theorem eval_atom1998 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1998 = ((g 8) * (g 17) * (g 18)) := by
  norm_num [atom1998, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1998_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (286892872358400 : Int) atom1998) := by
  rw [SparsePolynomial.eval_scale, eval_atom1998]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1999 : SparsePolynomial.Poly := [([8,17,19], 1)]
theorem eval_atom1999 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1999 = ((g 8) * (g 17) * (g 19)) := by
  norm_num [atom1999, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1999_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (308219008204800 : Int) atom1999) := by
  rw [SparsePolynomial.eval_scale, eval_atom1999]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2000 : SparsePolynomial.Poly := [([8,17,20], 1)]
theorem eval_atom2000 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2000 = ((g 8) * (g 17) * (g 20)) := by
  norm_num [atom2000, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2000_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (470386942502400 : Int) atom2000) := by
  rw [SparsePolynomial.eval_scale, eval_atom2000]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2001 : SparsePolynomial.Poly := [([8,17,21], 1)]
theorem eval_atom2001 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2001 = ((g 8) * (g 17) * (g 21)) := by
  norm_num [atom2001, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2001_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (533897578368000 : Int) atom2001) := by
  rw [SparsePolynomial.eval_scale, eval_atom2001]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 8) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2002 : SparsePolynomial.Poly := [([8,17,22], 1)]
theorem eval_atom2002 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2002 = ((g 8) * (g 17) * (g 22)) := by
  norm_num [atom2002, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2002_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (524687759769600 : Int) atom2002) := by
  rw [SparsePolynomial.eval_scale, eval_atom2002]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 8) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2003 : SparsePolynomial.Poly := [([8,17,23], 1)]
theorem eval_atom2003 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2003 = ((g 8) * (g 17) * (g 23)) := by
  norm_num [atom2003, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2003_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (728320495795200 : Int) atom2003) := by
  rw [SparsePolynomial.eval_scale, eval_atom2003]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 8) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2004 : SparsePolynomial.Poly := [([8,18,18], 1)]
theorem eval_atom2004 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2004 = ((g 8) * (g 18) * (g 18)) := by
  norm_num [atom2004, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2004_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (182186435692800 : Int) atom2004) := by
  rw [SparsePolynomial.eval_scale, eval_atom2004]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2005 : SparsePolynomial.Poly := [([8,18,19], 1)]
theorem eval_atom2005 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2005 = ((g 8) * (g 18) * (g 19)) := by
  norm_num [atom2005, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2005_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (362650621132800 : Int) atom2005) := by
  rw [SparsePolynomial.eval_scale, eval_atom2005]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2006 : SparsePolynomial.Poly := [([8,18,20], 1)]
theorem eval_atom2006 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2006 = ((g 8) * (g 18) * (g 20)) := by
  norm_num [atom2006, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2006_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (572191068556800 : Int) atom2006) := by
  rw [SparsePolynomial.eval_scale, eval_atom2006]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2007 : SparsePolynomial.Poly := [([8,18,21], 1)]
theorem eval_atom2007 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2007 = ((g 8) * (g 18) * (g 21)) := by
  norm_num [atom2007, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2007_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (592299934934400 : Int) atom2007) := by
  rw [SparsePolynomial.eval_scale, eval_atom2007]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 8) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2008 : SparsePolynomial.Poly := [([8,18,22], 1)]
theorem eval_atom2008 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2008 = ((g 8) * (g 18) * (g 22)) := by
  norm_num [atom2008, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2008_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (483171412953600 : Int) atom2008) := by
  rw [SparsePolynomial.eval_scale, eval_atom2008]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 8) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2009 : SparsePolynomial.Poly := [([8,18,23], 1)]
theorem eval_atom2009 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2009 = ((g 8) * (g 18) * (g 23)) := by
  norm_num [atom2009, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2009_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (706816287777600 : Int) atom2009) := by
  rw [SparsePolynomial.eval_scale, eval_atom2009]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 8) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2010 : SparsePolynomial.Poly := [([8,19,19], 1)]
theorem eval_atom2010 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2010 = ((g 8) * (g 19) * (g 19)) := by
  norm_num [atom2010, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2010_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (117725372835840 : Int) atom2010) := by
  rw [SparsePolynomial.eval_scale, eval_atom2010]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2011 : SparsePolynomial.Poly := [([8,19,20], 1)]
theorem eval_atom2011 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2011 = ((g 8) * (g 19) * (g 20)) := by
  norm_num [atom2011, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2011_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (415423770854400 : Int) atom2011) := by
  rw [SparsePolynomial.eval_scale, eval_atom2011]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2012 : SparsePolynomial.Poly := [([8,19,21], 1)]
theorem eval_atom2012 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2012 = ((g 8) * (g 19) * (g 21)) := by
  norm_num [atom2012, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2012_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (433879489612800 : Int) atom2012) := by
  rw [SparsePolynomial.eval_scale, eval_atom2012]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 8) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2013 : SparsePolynomial.Poly := [([8,19,22], 1)]
theorem eval_atom2013 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2013 = ((g 8) * (g 19) * (g 22)) := by
  norm_num [atom2013, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2013_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (392141176761600 : Int) atom2013) := by
  rw [SparsePolynomial.eval_scale, eval_atom2013]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 8) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2014 : SparsePolynomial.Poly := [([8,19,23], 1)]
theorem eval_atom2014 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2014 = ((g 8) * (g 19) * (g 23)) := by
  norm_num [atom2014, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2014_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (464228593113600 : Int) atom2014) := by
  rw [SparsePolynomial.eval_scale, eval_atom2014]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 8) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2015 : SparsePolynomial.Poly := [([8,20,20], 1)]
theorem eval_atom2015 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2015 = ((g 8) * (g 20) * (g 20)) := by
  norm_num [atom2015, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2015_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (305380484640000 : Int) atom2015) := by
  rw [SparsePolynomial.eval_scale, eval_atom2015]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2016 : SparsePolynomial.Poly := [([8,20,21], 1)]
theorem eval_atom2016 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2016 = ((g 8) * (g 20) * (g 21)) := by
  norm_num [atom2016, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2016_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (451511292355200 : Int) atom2016) := by
  rw [SparsePolynomial.eval_scale, eval_atom2016]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 8) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2017 : SparsePolynomial.Poly := [([8,20,22], 1)]
theorem eval_atom2017 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2017 = ((g 8) * (g 20) * (g 22)) := by
  norm_num [atom2017, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2017_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (376656388012800 : Int) atom2017) := by
  rw [SparsePolynomial.eval_scale, eval_atom2017]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 8) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2018 : SparsePolynomial.Poly := [([8,20,23], 1)]
theorem eval_atom2018 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2018 = ((g 8) * (g 20) * (g 23)) := by
  norm_num [atom2018, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2018_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (472146160248000 : Int) atom2018) := by
  rw [SparsePolynomial.eval_scale, eval_atom2018]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 8) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2019 : SparsePolynomial.Poly := [([8,21,21], 1)]
theorem eval_atom2019 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2019 = ((g 8) * (g 21) * (g 21)) := by
  norm_num [atom2019, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2019_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (88951036204800 : Int) atom2019) := by
  rw [SparsePolynomial.eval_scale, eval_atom2019]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 8) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2020 : SparsePolynomial.Poly := [([8,21,22], 1)]
theorem eval_atom2020 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2020 = ((g 8) * (g 21) * (g 22)) := by
  norm_num [atom2020, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2020_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (158310267696000 : Int) atom2020) := by
  rw [SparsePolynomial.eval_scale, eval_atom2020]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 8) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2021 : SparsePolynomial.Poly := [([8,21,23], 1)]
theorem eval_atom2021 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2021 = ((g 8) * (g 21) * (g 23)) := by
  norm_num [atom2021, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2021_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (243917316316800 : Int) atom2021) := by
  rw [SparsePolynomial.eval_scale, eval_atom2021]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 8) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2022 : SparsePolynomial.Poly := [([9,9,9], 1)]
theorem eval_atom2022 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2022 = ((g 9) * (g 9) * (g 9)) := by
  norm_num [atom2022, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2022_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17430917842800 : Int) atom2022) := by
  rw [SparsePolynomial.eval_scale, eval_atom2022]
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 9) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2023 : SparsePolynomial.Poly := [([9,9,10], 1)]
theorem eval_atom2023 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2023 = ((g 9) * (g 9) * (g 10)) := by
  norm_num [atom2023, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2023_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24545388344400 : Int) atom2023) := by
  rw [SparsePolynomial.eval_scale, eval_atom2023]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 9) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2024 : SparsePolynomial.Poly := [([9,9,11], 1)]
theorem eval_atom2024 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2024 = ((g 9) * (g 9) * (g 11)) := by
  norm_num [atom2024, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2024_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3083040576000 : Int) atom2024) := by
  rw [SparsePolynomial.eval_scale, eval_atom2024]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 9) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2025 : SparsePolynomial.Poly := [([9,9,12], 1)]
theorem eval_atom2025 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2025 = ((g 9) * (g 9) * (g 12)) := by
  norm_num [atom2025, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2025_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3083040576000 : Int) atom2025) := by
  rw [SparsePolynomial.eval_scale, eval_atom2025]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 9) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2026 : SparsePolynomial.Poly := [([9,10,10], 1)]
theorem eval_atom2026 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2026 = ((g 9) * (g 10) * (g 10)) := by
  norm_num [atom2026, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2026_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16316859358800 : Int) atom2026) := by
  rw [SparsePolynomial.eval_scale, eval_atom2026]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 9) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2027 : SparsePolynomial.Poly := [([9,10,14], 1)]
theorem eval_atom2027 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2027 = ((g 9) * (g 10) * (g 14)) := by
  norm_num [atom2027, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2027_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3083040576000 : Int) atom2027) := by
  rw [SparsePolynomial.eval_scale, eval_atom2027]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2028 : SparsePolynomial.Poly := [([9,10,15], 1)]
theorem eval_atom2028 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2028 = ((g 9) * (g 10) * (g 15)) := by
  norm_num [atom2028, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2028_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6166081152000 : Int) atom2028) := by
  rw [SparsePolynomial.eval_scale, eval_atom2028]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2029 : SparsePolynomial.Poly := [([9,10,16], 1)]
theorem eval_atom2029 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2029 = ((g 9) * (g 10) * (g 16)) := by
  norm_num [atom2029, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2029_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9249121728000 : Int) atom2029) := by
  rw [SparsePolynomial.eval_scale, eval_atom2029]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2030 : SparsePolynomial.Poly := [([9,10,17], 1)]
theorem eval_atom2030 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2030 = ((g 9) * (g 10) * (g 17)) := by
  norm_num [atom2030, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2030_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12332162304000 : Int) atom2030) := by
  rw [SparsePolynomial.eval_scale, eval_atom2030]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2031 : SparsePolynomial.Poly := [([9,10,19], 1)]
theorem eval_atom2031 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2031 = ((g 9) * (g 10) * (g 19)) := by
  norm_num [atom2031, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2031_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1197778982400 : Int) atom2031) := by
  rw [SparsePolynomial.eval_scale, eval_atom2031]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2032 : SparsePolynomial.Poly := [([9,10,21], 1)]
theorem eval_atom2032 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2032 = ((g 9) * (g 10) * (g 21)) := by
  norm_num [atom2032, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2032_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (45125791603200 : Int) atom2032) := by
  rw [SparsePolynomial.eval_scale, eval_atom2032]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 9) * (g 10) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2033 : SparsePolynomial.Poly := [([9,10,22], 1)]
theorem eval_atom2033 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2033 = ((g 9) * (g 10) * (g 22)) := by
  norm_num [atom2033, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2033_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (87856025241600 : Int) atom2033) := by
  rw [SparsePolynomial.eval_scale, eval_atom2033]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 9) * (g 10) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2034 : SparsePolynomial.Poly := [([9,10,23], 1)]
theorem eval_atom2034 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2034 = ((g 9) * (g 10) * (g 23)) := by
  norm_num [atom2034, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2034_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (137822544921600 : Int) atom2034) := by
  rw [SparsePolynomial.eval_scale, eval_atom2034]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 9) * (g 10) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2035 : SparsePolynomial.Poly := [([9,11,11], 1)]
theorem eval_atom2035 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2035 = ((g 9) * (g 11) * (g 11)) := by
  norm_num [atom2035, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2035_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9368057991600 : Int) atom2035) := by
  rw [SparsePolynomial.eval_scale, eval_atom2035]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 9) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2036 : SparsePolynomial.Poly := [([9,11,12], 1)]
theorem eval_atom2036 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2036 = ((g 9) * (g 11) * (g 12)) := by
  norm_num [atom2036, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2036_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1020592742400 : Int) atom2036) := by
  rw [SparsePolynomial.eval_scale, eval_atom2036]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 9) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2037 : SparsePolynomial.Poly := [([9,11,14], 1)]
theorem eval_atom2037 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2037 = ((g 9) * (g 11) * (g 14)) := by
  norm_num [atom2037, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2037_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2062447833600 : Int) atom2037) := by
  rw [SparsePolynomial.eval_scale, eval_atom2037]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2038 : SparsePolynomial.Poly := [([9,11,15], 1)]
theorem eval_atom2038 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2038 = ((g 9) * (g 11) * (g 15)) := by
  norm_num [atom2038, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2038_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4124895667200 : Int) atom2038) := by
  rw [SparsePolynomial.eval_scale, eval_atom2038]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2039 : SparsePolynomial.Poly := [([9,11,16], 1)]
theorem eval_atom2039 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2039 = ((g 9) * (g 11) * (g 16)) := by
  norm_num [atom2039, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2039_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9270384076800 : Int) atom2039) := by
  rw [SparsePolynomial.eval_scale, eval_atom2039]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2040 : SparsePolynomial.Poly := [([9,11,17], 1)]
theorem eval_atom2040 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2040 = ((g 9) * (g 11) * (g 17)) := by
  norm_num [atom2040, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2040_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14415872486400 : Int) atom2040) := by
  rw [SparsePolynomial.eval_scale, eval_atom2040]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2041 : SparsePolynomial.Poly := [([9,11,18], 1)]
theorem eval_atom2041 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2041 = ((g 9) * (g 11) * (g 18)) := by
  norm_num [atom2041, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2041_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5671037984832 : Int) atom2041) := by
  rw [SparsePolynomial.eval_scale, eval_atom2041]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2042 : SparsePolynomial.Poly := [([9,11,20], 1)]
theorem eval_atom2042 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2042 = ((g 9) * (g 11) * (g 20)) := by
  norm_num [atom2042, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2042_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5317070501952 : Int) atom2042) := by
  rw [SparsePolynomial.eval_scale, eval_atom2042]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2043 : SparsePolynomial.Poly := [([9,11,21], 1)]
theorem eval_atom2043 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2043 = ((g 9) * (g 11) * (g 21)) := by
  norm_num [atom2043, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2043_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (90503187667200 : Int) atom2043) := by
  rw [SparsePolynomial.eval_scale, eval_atom2043]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 9) * (g 11) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2044 : SparsePolynomial.Poly := [([9,11,22], 1)]
theorem eval_atom2044 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2044 = ((g 9) * (g 11) * (g 22)) := by
  norm_num [atom2044, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2044_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (175048665200640 : Int) atom2044) := by
  rw [SparsePolynomial.eval_scale, eval_atom2044]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 9) * (g 11) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2045 : SparsePolynomial.Poly := [([9,11,23], 1)]
theorem eval_atom2045 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2045 = ((g 9) * (g 11) * (g 23)) := by
  norm_num [atom2045, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2045_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (272556733680000 : Int) atom2045) := by
  rw [SparsePolynomial.eval_scale, eval_atom2045]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 9) * (g 11) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2046 : SparsePolynomial.Poly := [([9,12,12], 1)]
theorem eval_atom2046 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2046 = ((g 9) * (g 12) * (g 12)) := by
  norm_num [atom2046, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2046_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17337452101200 : Int) atom2046) := by
  rw [SparsePolynomial.eval_scale, eval_atom2046]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 9) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2047 : SparsePolynomial.Poly := [([9,12,13], 1)]
theorem eval_atom2047 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2047 = ((g 9) * (g 12) * (g 13)) := by
  norm_num [atom2047, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2047_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25965314575200 : Int) atom2047) := by
  rw [SparsePolynomial.eval_scale, eval_atom2047]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 9) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2048 : SparsePolynomial.Poly := [([9,12,14], 1)]
theorem eval_atom2048 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2048 = ((g 9) * (g 12) * (g 14)) := by
  norm_num [atom2048, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2048_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32152658076000 : Int) atom2048) := by
  rw [SparsePolynomial.eval_scale, eval_atom2048]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block027 : SparsePolynomial.Poly := [([8,13,23], 476282593155600), ([8,14,14], 79390066694400), ([8,14,15], 153751587897600), ([8,14,16], 156940940217600), ([8,14,17], 160130292537600), ([8,14,18], 174436309555200), ([8,14,19], 177035188730400), ([8,14,20], 282193893273600), ([8,14,21], 312992405510400), ([8,14,22], 400790402258400), ([8,14,23], 510762813976800), ([8,15,15], 106212519705600), ([8,15,16], 199221120806400), ([8,15,17], 199369957248000), ([8,15,18], 218777971507200), ([8,15,19], 217143992217600), ([8,15,20], 356351811379200), ([8,15,21], 399197054995200), ([8,15,22], 428238524044800), ([8,15,23], 535818438288000), ([8,16,16], 127942640179200), ([8,16,17], 248889967603200), ([8,16,18], 245385868089600), ([8,16,19], 252748761753600), ([8,16,20], 400953453868800), ([8,16,21], 452889801302400), ([8,16,22], 433229377190400), ([8,16,23], 626482301659200), ([8,17,17], 151090250572800), ([8,17,18], 286892872358400), ([8,17,19], 308219008204800), ([8,17,20], 470386942502400), ([8,17,21], 533897578368000), ([8,17,22], 524687759769600), ([8,17,23], 728320495795200), ([8,18,18], 182186435692800), ([8,18,19], 362650621132800), ([8,18,20], 572191068556800), ([8,18,21], 592299934934400), ([8,18,22], 483171412953600), ([8,18,23], 706816287777600), ([8,19,19], 117725372835840), ([8,19,20], 415423770854400), ([8,19,21], 433879489612800), ([8,19,22], 392141176761600), ([8,19,23], 464228593113600), ([8,20,20], 305380484640000), ([8,20,21], 451511292355200), ([8,20,22], 376656388012800), ([8,20,23], 472146160248000), ([8,21,21], 88951036204800), ([8,21,22], 158310267696000), ([8,21,23], 243917316316800), ([9,9,9], 17430917842800), ([9,9,10], 24545388344400), ([9,9,11], 3083040576000), ([9,9,12], 3083040576000), ([9,10,10], 16316859358800), ([9,10,14], 3083040576000), ([9,10,15], 6166081152000), ([9,10,16], 9249121728000), ([9,10,17], 12332162304000), ([9,10,19], 1197778982400), ([9,10,21], 45125791603200), ([9,10,22], 87856025241600), ([9,10,23], 137822544921600), ([9,11,11], 9368057991600), ([9,11,12], 1020592742400), ([9,11,14], 2062447833600), ([9,11,15], 4124895667200), ([9,11,16], 9270384076800), ([9,11,17], 14415872486400), ([9,11,18], 5671037984832), ([9,11,20], 5317070501952), ([9,11,21], 90503187667200), ([9,11,22], 175048665200640), ([9,11,23], 272556733680000), ([9,12,12], 17337452101200), ([9,12,13], 25965314575200), ([9,12,14], 32152658076000)]
theorem block027_data : block027 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (476282593155600 : Int) atom1969) (SparsePolynomial.scale (79390066694400 : Int) atom1970)) (SparsePolynomial.merge (SparsePolynomial.scale (153751587897600 : Int) atom1971) (SparsePolynomial.merge (SparsePolynomial.scale (156940940217600 : Int) atom1972) (SparsePolynomial.scale (160130292537600 : Int) atom1973)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (174436309555200 : Int) atom1974) (SparsePolynomial.scale (177035188730400 : Int) atom1975)) (SparsePolynomial.merge (SparsePolynomial.scale (282193893273600 : Int) atom1976) (SparsePolynomial.merge (SparsePolynomial.scale (312992405510400 : Int) atom1977) (SparsePolynomial.scale (400790402258400 : Int) atom1978))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (510762813976800 : Int) atom1979) (SparsePolynomial.scale (106212519705600 : Int) atom1980)) (SparsePolynomial.merge (SparsePolynomial.scale (199221120806400 : Int) atom1981) (SparsePolynomial.merge (SparsePolynomial.scale (199369957248000 : Int) atom1982) (SparsePolynomial.scale (218777971507200 : Int) atom1983)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (217143992217600 : Int) atom1984) (SparsePolynomial.scale (356351811379200 : Int) atom1985)) (SparsePolynomial.merge (SparsePolynomial.scale (399197054995200 : Int) atom1986) (SparsePolynomial.merge (SparsePolynomial.scale (428238524044800 : Int) atom1987) (SparsePolynomial.scale (535818438288000 : Int) atom1988)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (127942640179200 : Int) atom1989) (SparsePolynomial.scale (248889967603200 : Int) atom1990)) (SparsePolynomial.merge (SparsePolynomial.scale (245385868089600 : Int) atom1991) (SparsePolynomial.merge (SparsePolynomial.scale (252748761753600 : Int) atom1992) (SparsePolynomial.scale (400953453868800 : Int) atom1993)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (452889801302400 : Int) atom1994) (SparsePolynomial.scale (433229377190400 : Int) atom1995)) (SparsePolynomial.merge (SparsePolynomial.scale (626482301659200 : Int) atom1996) (SparsePolynomial.merge (SparsePolynomial.scale (151090250572800 : Int) atom1997) (SparsePolynomial.scale (286892872358400 : Int) atom1998))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (308219008204800 : Int) atom1999) (SparsePolynomial.scale (470386942502400 : Int) atom2000)) (SparsePolynomial.merge (SparsePolynomial.scale (533897578368000 : Int) atom2001) (SparsePolynomial.merge (SparsePolynomial.scale (524687759769600 : Int) atom2002) (SparsePolynomial.scale (728320495795200 : Int) atom2003)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (182186435692800 : Int) atom2004) (SparsePolynomial.scale (362650621132800 : Int) atom2005)) (SparsePolynomial.merge (SparsePolynomial.scale (572191068556800 : Int) atom2006) (SparsePolynomial.merge (SparsePolynomial.scale (592299934934400 : Int) atom2007) (SparsePolynomial.scale (483171412953600 : Int) atom2008))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (706816287777600 : Int) atom2009) (SparsePolynomial.scale (117725372835840 : Int) atom2010)) (SparsePolynomial.merge (SparsePolynomial.scale (415423770854400 : Int) atom2011) (SparsePolynomial.merge (SparsePolynomial.scale (433879489612800 : Int) atom2012) (SparsePolynomial.scale (392141176761600 : Int) atom2013)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (464228593113600 : Int) atom2014) (SparsePolynomial.scale (305380484640000 : Int) atom2015)) (SparsePolynomial.merge (SparsePolynomial.scale (451511292355200 : Int) atom2016) (SparsePolynomial.merge (SparsePolynomial.scale (376656388012800 : Int) atom2017) (SparsePolynomial.scale (472146160248000 : Int) atom2018))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (88951036204800 : Int) atom2019) (SparsePolynomial.scale (158310267696000 : Int) atom2020)) (SparsePolynomial.merge (SparsePolynomial.scale (243917316316800 : Int) atom2021) (SparsePolynomial.merge (SparsePolynomial.scale (17430917842800 : Int) atom2022) (SparsePolynomial.scale (24545388344400 : Int) atom2023)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3083040576000 : Int) atom2024) (SparsePolynomial.scale (3083040576000 : Int) atom2025)) (SparsePolynomial.merge (SparsePolynomial.scale (16316859358800 : Int) atom2026) (SparsePolynomial.merge (SparsePolynomial.scale (3083040576000 : Int) atom2027) (SparsePolynomial.scale (6166081152000 : Int) atom2028)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (9249121728000 : Int) atom2029) (SparsePolynomial.scale (12332162304000 : Int) atom2030)) (SparsePolynomial.merge (SparsePolynomial.scale (1197778982400 : Int) atom2031) (SparsePolynomial.merge (SparsePolynomial.scale (45125791603200 : Int) atom2032) (SparsePolynomial.scale (87856025241600 : Int) atom2033)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (137822544921600 : Int) atom2034) (SparsePolynomial.scale (9368057991600 : Int) atom2035)) (SparsePolynomial.merge (SparsePolynomial.scale (1020592742400 : Int) atom2036) (SparsePolynomial.merge (SparsePolynomial.scale (2062447833600 : Int) atom2037) (SparsePolynomial.scale (4124895667200 : Int) atom2038))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (9270384076800 : Int) atom2039) (SparsePolynomial.scale (14415872486400 : Int) atom2040)) (SparsePolynomial.merge (SparsePolynomial.scale (5671037984832 : Int) atom2041) (SparsePolynomial.merge (SparsePolynomial.scale (5317070501952 : Int) atom2042) (SparsePolynomial.scale (90503187667200 : Int) atom2043)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (175048665200640 : Int) atom2044) (SparsePolynomial.scale (272556733680000 : Int) atom2045)) (SparsePolynomial.merge (SparsePolynomial.scale (17337452101200 : Int) atom2046) (SparsePolynomial.merge (SparsePolynomial.scale (25965314575200 : Int) atom2047) (SparsePolynomial.scale (32152658076000 : Int) atom2048)))))))) := by decide +kernel
theorem block027_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block027 := by
  rw [block027_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1969_nonneg g hg hA hB) (atom1970_nonneg g hg hA hB)) (add_nonneg (atom1971_nonneg g hg hA hB) (add_nonneg (atom1972_nonneg g hg hA hB) (atom1973_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1974_nonneg g hg hA hB) (atom1975_nonneg g hg hA hB)) (add_nonneg (atom1976_nonneg g hg hA hB) (add_nonneg (atom1977_nonneg g hg hA hB) (atom1978_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1979_nonneg g hg hA hB) (atom1980_nonneg g hg hA hB)) (add_nonneg (atom1981_nonneg g hg hA hB) (add_nonneg (atom1982_nonneg g hg hA hB) (atom1983_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1984_nonneg g hg hA hB) (atom1985_nonneg g hg hA hB)) (add_nonneg (atom1986_nonneg g hg hA hB) (add_nonneg (atom1987_nonneg g hg hA hB) (atom1988_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1989_nonneg g hg hA hB) (atom1990_nonneg g hg hA hB)) (add_nonneg (atom1991_nonneg g hg hA hB) (add_nonneg (atom1992_nonneg g hg hA hB) (atom1993_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1994_nonneg g hg hA hB) (atom1995_nonneg g hg hA hB)) (add_nonneg (atom1996_nonneg g hg hA hB) (add_nonneg (atom1997_nonneg g hg hA hB) (atom1998_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1999_nonneg g hg hA hB) (atom2000_nonneg g hg hA hB)) (add_nonneg (atom2001_nonneg g hg hA hB) (add_nonneg (atom2002_nonneg g hg hA hB) (atom2003_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2004_nonneg g hg hA hB) (atom2005_nonneg g hg hA hB)) (add_nonneg (atom2006_nonneg g hg hA hB) (add_nonneg (atom2007_nonneg g hg hA hB) (atom2008_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2009_nonneg g hg hA hB) (atom2010_nonneg g hg hA hB)) (add_nonneg (atom2011_nonneg g hg hA hB) (add_nonneg (atom2012_nonneg g hg hA hB) (atom2013_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2014_nonneg g hg hA hB) (atom2015_nonneg g hg hA hB)) (add_nonneg (atom2016_nonneg g hg hA hB) (add_nonneg (atom2017_nonneg g hg hA hB) (atom2018_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2019_nonneg g hg hA hB) (atom2020_nonneg g hg hA hB)) (add_nonneg (atom2021_nonneg g hg hA hB) (add_nonneg (atom2022_nonneg g hg hA hB) (atom2023_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2024_nonneg g hg hA hB) (atom2025_nonneg g hg hA hB)) (add_nonneg (atom2026_nonneg g hg hA hB) (add_nonneg (atom2027_nonneg g hg hA hB) (atom2028_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2029_nonneg g hg hA hB) (atom2030_nonneg g hg hA hB)) (add_nonneg (atom2031_nonneg g hg hA hB) (add_nonneg (atom2032_nonneg g hg hA hB) (atom2033_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2034_nonneg g hg hA hB) (atom2035_nonneg g hg hA hB)) (add_nonneg (atom2036_nonneg g hg hA hB) (add_nonneg (atom2037_nonneg g hg hA hB) (atom2038_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2039_nonneg g hg hA hB) (atom2040_nonneg g hg hA hB)) (add_nonneg (atom2041_nonneg g hg hA hB) (add_nonneg (atom2042_nonneg g hg hA hB) (atom2043_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2044_nonneg g hg hA hB) (atom2045_nonneg g hg hA hB)) (add_nonneg (atom2046_nonneg g hg hA hB) (add_nonneg (atom2047_nonneg g hg hA hB) (atom2048_nonneg g hg hA hB))))))))

end APPT.Finite24
