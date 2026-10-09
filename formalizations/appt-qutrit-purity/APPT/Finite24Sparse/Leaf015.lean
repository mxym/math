import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom1009 : SparsePolynomial.Poly := [([2,17,23], 1)]
theorem eval_atom1009 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1009 = ((g 2) * (g 17) * (g 23)) := by
  norm_num [atom1009, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1009_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (475798210272000 : Int) atom1009) := by
  rw [SparsePolynomial.eval_scale, eval_atom1009]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1010 : SparsePolynomial.Poly := [([2,18,18], 1)]
theorem eval_atom1010 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1010 = ((g 2) * (g 18) * (g 18)) := by
  norm_num [atom1010, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1010_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (290294848166400 : Int) atom1010) := by
  rw [SparsePolynomial.eval_scale, eval_atom1010]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1011 : SparsePolynomial.Poly := [([2,18,19], 1)]
theorem eval_atom1011 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1011 = ((g 2) * (g 18) * (g 19)) := by
  norm_num [atom1011, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1011_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (476361662515200 : Int) atom1011) := by
  rw [SparsePolynomial.eval_scale, eval_atom1011]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1012 : SparsePolynomial.Poly := [([2,18,20], 1)]
theorem eval_atom1012 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1012 = ((g 2) * (g 18) * (g 20)) := by
  norm_num [atom1012, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1012_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (653817225600000 : Int) atom1012) := by
  rw [SparsePolynomial.eval_scale, eval_atom1012]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1013 : SparsePolynomial.Poly := [([2,18,21], 1)]
theorem eval_atom1013 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1013 = ((g 2) * (g 18) * (g 21)) := by
  norm_num [atom1013, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1013_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (549589191782400 : Int) atom1013) := by
  rw [SparsePolynomial.eval_scale, eval_atom1013]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1014 : SparsePolynomial.Poly := [([2,18,22], 1)]
theorem eval_atom1014 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1014 = ((g 2) * (g 18) * (g 22)) := by
  norm_num [atom1014, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1014_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (349197353164800 : Int) atom1014) := by
  rw [SparsePolynomial.eval_scale, eval_atom1014]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1015 : SparsePolynomial.Poly := [([2,18,23], 1)]
theorem eval_atom1015 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1015 = ((g 2) * (g 18) * (g 23)) := by
  norm_num [atom1015, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1015_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (503137604138400 : Int) atom1015) := by
  rw [SparsePolynomial.eval_scale, eval_atom1015]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1016 : SparsePolynomial.Poly := [([2,19,19], 1)]
theorem eval_atom1016 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1016 = ((g 2) * (g 19) * (g 19)) := by
  norm_num [atom1016, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1016_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (186615382947840 : Int) atom1016) := by
  rw [SparsePolynomial.eval_scale, eval_atom1016]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1017 : SparsePolynomial.Poly := [([2,19,20], 1)]
theorem eval_atom1017 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1017 = ((g 2) * (g 19) * (g 20)) := by
  norm_num [atom1017, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1017_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (534152726553600 : Int) atom1017) := by
  rw [SparsePolynomial.eval_scale, eval_atom1017]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1018 : SparsePolynomial.Poly := [([2,19,21], 1)]
theorem eval_atom1018 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1018 = ((g 2) * (g 19) * (g 21)) := by
  norm_num [atom1018, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1018_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (503407370188800 : Int) atom1018) := by
  rw [SparsePolynomial.eval_scale, eval_atom1018]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1019 : SparsePolynomial.Poly := [([2,19,22], 1)]
theorem eval_atom1019 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1019 = ((g 2) * (g 19) * (g 22)) := by
  norm_num [atom1019, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1019_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (347292762163200 : Int) atom1019) := by
  rw [SparsePolynomial.eval_scale, eval_atom1019]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1020 : SparsePolynomial.Poly := [([2,19,23], 1)]
theorem eval_atom1020 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1020 = ((g 2) * (g 19) * (g 23)) := by
  norm_num [atom1020, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1020_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (386611959333600 : Int) atom1020) := by
  rw [SparsePolynomial.eval_scale, eval_atom1020]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1021 : SparsePolynomial.Poly := [([2,20,20], 1)]
theorem eval_atom1021 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1021 = ((g 2) * (g 20) * (g 20)) := by
  norm_num [atom1021, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1021_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (348085912204800 : Int) atom1021) := by
  rw [SparsePolynomial.eval_scale, eval_atom1021]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1022 : SparsePolynomial.Poly := [([2,20,21], 1)]
theorem eval_atom1022 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1022 = ((g 2) * (g 20) * (g 21)) := by
  norm_num [atom1022, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1022_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (527646447820800 : Int) atom1022) := by
  rw [SparsePolynomial.eval_scale, eval_atom1022]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1023 : SparsePolynomial.Poly := [([2,20,22], 1)]
theorem eval_atom1023 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1023 = ((g 2) * (g 20) * (g 22)) := by
  norm_num [atom1023, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1023_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (345267040204800 : Int) atom1023) := by
  rw [SparsePolynomial.eval_scale, eval_atom1023]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1024 : SparsePolynomial.Poly := [([2,20,23], 1)]
theorem eval_atom1024 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1024 = ((g 2) * (g 20) * (g 23)) := by
  norm_num [atom1024, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1024_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (404881632540000 : Int) atom1024) := by
  rw [SparsePolynomial.eval_scale, eval_atom1024]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1025 : SparsePolynomial.Poly := [([2,21,21], 1)]
theorem eval_atom1025 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1025 = ((g 2) * (g 21) * (g 21)) := by
  norm_num [atom1025, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1025_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (170311413888000 : Int) atom1025) := by
  rw [SparsePolynomial.eval_scale, eval_atom1025]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1026 : SparsePolynomial.Poly := [([2,21,22], 1)]
theorem eval_atom1026 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1026 = ((g 2) * (g 21) * (g 22)) := by
  norm_num [atom1026, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1026_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (217123374182400 : Int) atom1026) := by
  rw [SparsePolynomial.eval_scale, eval_atom1026]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1027 : SparsePolynomial.Poly := [([2,21,23], 1)]
theorem eval_atom1027 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1027 = ((g 2) * (g 21) * (g 23)) := by
  norm_num [atom1027, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1027_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (288355987735200 : Int) atom1027) := by
  rw [SparsePolynomial.eval_scale, eval_atom1027]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1028 : SparsePolynomial.Poly := [([2,22,22], 1)]
theorem eval_atom1028 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1028 = ((g 2) * (g 22) * (g 22)) := by
  norm_num [atom1028, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1028_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8846586806400 : Int) atom1028) := by
  rw [SparsePolynomial.eval_scale, eval_atom1028]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 22) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1029 : SparsePolynomial.Poly := [([2,22,23], 1)]
theorem eval_atom1029 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1029 = ((g 2) * (g 22) * (g 23)) := by
  norm_num [atom1029, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1029_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (100071607053600 : Int) atom1029) := by
  rw [SparsePolynomial.eval_scale, eval_atom1029]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 22) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1030 : SparsePolynomial.Poly := [([2,23,23], 1)]
theorem eval_atom1030 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1030 = ((g 2) * (g 23) * (g 23)) := by
  norm_num [atom1030, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1030_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (78422186858400 : Int) atom1030) := by
  rw [SparsePolynomial.eval_scale, eval_atom1030]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 23) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1031 : SparsePolynomial.Poly := [([3,3,3], 1)]
theorem eval_atom1031 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1031 = ((g 3) * (g 3) * (g 3)) := by
  norm_num [atom1031, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1031_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23813830656000 : Int) atom1031) := by
  rw [SparsePolynomial.eval_scale, eval_atom1031]
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 3) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1032 : SparsePolynomial.Poly := [([3,3,4], 1)]
theorem eval_atom1032 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1032 = ((g 3) * (g 3) * (g 4)) := by
  norm_num [atom1032, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1032_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65232886118400 : Int) atom1032) := by
  rw [SparsePolynomial.eval_scale, eval_atom1032]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 3) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1033 : SparsePolynomial.Poly := [([3,3,5], 1)]
theorem eval_atom1033 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1033 = ((g 3) * (g 3) * (g 5)) := by
  norm_num [atom1033, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1033_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65907174009600 : Int) atom1033) := by
  rw [SparsePolynomial.eval_scale, eval_atom1033]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1034 : SparsePolynomial.Poly := [([3,3,6], 1)]
theorem eval_atom1034 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1034 = ((g 3) * (g 3) * (g 6)) := by
  norm_num [atom1034, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1034_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52815674419200 : Int) atom1034) := by
  rw [SparsePolynomial.eval_scale, eval_atom1034]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1035 : SparsePolynomial.Poly := [([3,3,7], 1)]
theorem eval_atom1035 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1035 = ((g 3) * (g 3) * (g 7)) := by
  norm_num [atom1035, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1035_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46607068569600 : Int) atom1035) := by
  rw [SparsePolynomial.eval_scale, eval_atom1035]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1036 : SparsePolynomial.Poly := [([3,3,8], 1)]
theorem eval_atom1036 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1036 = ((g 3) * (g 3) * (g 8)) := by
  norm_num [atom1036, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1036_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40398462720000 : Int) atom1036) := by
  rw [SparsePolynomial.eval_scale, eval_atom1036]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1037 : SparsePolynomial.Poly := [([3,3,9], 1)]
theorem eval_atom1037 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1037 = ((g 3) * (g 3) * (g 9)) := by
  norm_num [atom1037, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1037_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40201637916528 : Int) atom1037) := by
  rw [SparsePolynomial.eval_scale, eval_atom1037]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1038 : SparsePolynomial.Poly := [([3,3,10], 1)]
theorem eval_atom1038 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1038 = ((g 3) * (g 3) * (g 10)) := by
  norm_num [atom1038, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1038_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (51636529101168 : Int) atom1038) := by
  rw [SparsePolynomial.eval_scale, eval_atom1038]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1039 : SparsePolynomial.Poly := [([3,3,11], 1)]
theorem eval_atom1039 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1039 = ((g 3) * (g 3) * (g 11)) := by
  norm_num [atom1039, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1039_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (61432993046304 : Int) atom1039) := by
  rw [SparsePolynomial.eval_scale, eval_atom1039]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1040 : SparsePolynomial.Poly := [([3,3,12], 1)]
theorem eval_atom1040 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1040 = ((g 3) * (g 3) * (g 12)) := by
  norm_num [atom1040, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1040_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (83146369420224 : Int) atom1040) := by
  rw [SparsePolynomial.eval_scale, eval_atom1040]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 3) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1041 : SparsePolynomial.Poly := [([3,3,13], 1)]
theorem eval_atom1041 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1041 = ((g 3) * (g 3) * (g 13)) := by
  norm_num [atom1041, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1041_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (68276633040000 : Int) atom1041) := by
  rw [SparsePolynomial.eval_scale, eval_atom1041]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 3) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1042 : SparsePolynomial.Poly := [([3,3,14], 1)]
theorem eval_atom1042 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1042 = ((g 3) * (g 3) * (g 14)) := by
  norm_num [atom1042, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1042_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49732633843200 : Int) atom1042) := by
  rw [SparsePolynomial.eval_scale, eval_atom1042]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 3) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1043 : SparsePolynomial.Poly := [([3,3,15], 1)]
theorem eval_atom1043 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1043 = ((g 3) * (g 3) * (g 15)) := by
  norm_num [atom1043, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1043_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (45975641241600 : Int) atom1043) := by
  rw [SparsePolynomial.eval_scale, eval_atom1043]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 3) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1044 : SparsePolynomial.Poly := [([3,3,16], 1)]
theorem eval_atom1044 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1044 = ((g 3) * (g 3) * (g 16)) := by
  norm_num [atom1044, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1044_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30396138393600 : Int) atom1044) := by
  rw [SparsePolynomial.eval_scale, eval_atom1044]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 3) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1045 : SparsePolynomial.Poly := [([3,3,17], 1)]
theorem eval_atom1045 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1045 = ((g 3) * (g 3) * (g 17)) := by
  norm_num [atom1045, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1045_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24749374003200 : Int) atom1045) := by
  rw [SparsePolynomial.eval_scale, eval_atom1045]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 3) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1046 : SparsePolynomial.Poly := [([3,3,18], 1)]
theorem eval_atom1046 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1046 = ((g 3) * (g 3) * (g 18)) := by
  norm_num [atom1046, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1046_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48733303449600 : Int) atom1046) := by
  rw [SparsePolynomial.eval_scale, eval_atom1046]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 3) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1047 : SparsePolynomial.Poly := [([3,3,20], 1)]
theorem eval_atom1047 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1047 = ((g 3) * (g 3) * (g 20)) := by
  norm_num [atom1047, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1047_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36316091750400 : Int) atom1047) := by
  rw [SparsePolynomial.eval_scale, eval_atom1047]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 3) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1048 : SparsePolynomial.Poly := [([3,4,4], 1)]
theorem eval_atom1048 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1048 = ((g 3) * (g 4) * (g 4)) := by
  norm_num [atom1048, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1048_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (63987427929600 : Int) atom1048) := by
  rw [SparsePolynomial.eval_scale, eval_atom1048]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 3) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1049 : SparsePolynomial.Poly := [([3,4,5], 1)]
theorem eval_atom1049 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1049 = ((g 3) * (g 4) * (g 5)) := by
  norm_num [atom1049, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1049_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (107581417564896 : Int) atom1049) := by
  rw [SparsePolynomial.eval_scale, eval_atom1049]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1050 : SparsePolynomial.Poly := [([3,4,6], 1)]
theorem eval_atom1050 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1050 = ((g 3) * (g 4) * (g 6)) := by
  norm_num [atom1050, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1050_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (76714554470400 : Int) atom1050) := by
  rw [SparsePolynomial.eval_scale, eval_atom1050]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1051 : SparsePolynomial.Poly := [([3,4,7], 1)]
theorem eval_atom1051 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1051 = ((g 3) * (g 4) * (g 7)) := by
  norm_num [atom1051, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1051_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (68379713740800 : Int) atom1051) := by
  rw [SparsePolynomial.eval_scale, eval_atom1051]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1052 : SparsePolynomial.Poly := [([3,4,8], 1)]
theorem eval_atom1052 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1052 = ((g 3) * (g 4) * (g 8)) := by
  norm_num [atom1052, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1052_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (60044873011200 : Int) atom1052) := by
  rw [SparsePolynomial.eval_scale, eval_atom1052]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1053 : SparsePolynomial.Poly := [([3,4,9], 1)]
theorem eval_atom1053 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1053 = ((g 3) * (g 4) * (g 9)) := by
  norm_num [atom1053, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1053_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (63733594373856 : Int) atom1053) := by
  rw [SparsePolynomial.eval_scale, eval_atom1053]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1054 : SparsePolynomial.Poly := [([3,4,10], 1)]
theorem eval_atom1054 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1054 = ((g 3) * (g 4) * (g 10)) := by
  norm_num [atom1054, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1054_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (90685747712736 : Int) atom1054) := by
  rw [SparsePolynomial.eval_scale, eval_atom1054]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1055 : SparsePolynomial.Poly := [([3,4,11], 1)]
theorem eval_atom1055 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1055 = ((g 3) * (g 4) * (g 11)) := by
  norm_num [atom1055, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1055_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (114361046572608 : Int) atom1055) := by
  rw [SparsePolynomial.eval_scale, eval_atom1055]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1056 : SparsePolynomial.Poly := [([3,4,12], 1)]
theorem eval_atom1056 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1056 = ((g 3) * (g 4) * (g 12)) := by
  norm_num [atom1056, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1056_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (161870170290048 : Int) atom1056) := by
  rw [SparsePolynomial.eval_scale, eval_atom1056]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1057 : SparsePolynomial.Poly := [([3,4,13], 1)]
theorem eval_atom1057 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1057 = ((g 3) * (g 4) * (g 13)) := by
  norm_num [atom1057, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1057_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (136213068499200 : Int) atom1057) := by
  rw [SparsePolynomial.eval_scale, eval_atom1057]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 4) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1058 : SparsePolynomial.Poly := [([3,4,14], 1)]
theorem eval_atom1058 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1058 = ((g 3) * (g 4) * (g 14)) := by
  norm_num [atom1058, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1058_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (103207441075200 : Int) atom1058) := by
  rw [SparsePolynomial.eval_scale, eval_atom1058]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1059 : SparsePolynomial.Poly := [([3,4,15], 1)]
theorem eval_atom1059 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1059 = ((g 3) * (g 4) * (g 15)) := by
  norm_num [atom1059, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1059_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (99775826841600 : Int) atom1059) := by
  rw [SparsePolynomial.eval_scale, eval_atom1059]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 4) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1060 : SparsePolynomial.Poly := [([3,4,16], 1)]
theorem eval_atom1060 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1060 = ((g 3) * (g 4) * (g 16)) := by
  norm_num [atom1060, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1060_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (72699192115200 : Int) atom1060) := by
  rw [SparsePolynomial.eval_scale, eval_atom1060]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 4) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1061 : SparsePolynomial.Poly := [([3,4,17], 1)]
theorem eval_atom1061 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1061 = ((g 3) * (g 4) * (g 17)) := by
  norm_num [atom1061, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1061_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (70135468300800 : Int) atom1061) := by
  rw [SparsePolynomial.eval_scale, eval_atom1061]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 4) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1062 : SparsePolynomial.Poly := [([3,4,18], 1)]
theorem eval_atom1062 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1062 = ((g 3) * (g 4) * (g 18)) := by
  norm_num [atom1062, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1062_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (117538264166400 : Int) atom1062) := by
  rw [SparsePolynomial.eval_scale, eval_atom1062]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 4) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1063 : SparsePolynomial.Poly := [([3,4,19], 1)]
theorem eval_atom1063 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1063 = ((g 3) * (g 4) * (g 19)) := by
  norm_num [atom1063, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1063_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (58037916686400 : Int) atom1063) := by
  rw [SparsePolynomial.eval_scale, eval_atom1063]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 4) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1064 : SparsePolynomial.Poly := [([3,4,20], 1)]
theorem eval_atom1064 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1064 = ((g 3) * (g 4) * (g 20)) := by
  norm_num [atom1064, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1064_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (101760876504000 : Int) atom1064) := by
  rw [SparsePolynomial.eval_scale, eval_atom1064]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 4) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1065 : SparsePolynomial.Poly := [([3,4,21], 1)]
theorem eval_atom1065 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1065 = ((g 3) * (g 4) * (g 21)) := by
  norm_num [atom1065, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1065_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (77175480312000 : Int) atom1065) := by
  rw [SparsePolynomial.eval_scale, eval_atom1065]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 4) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1066 : SparsePolynomial.Poly := [([3,4,22], 1)]
theorem eval_atom1066 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1066 = ((g 3) * (g 4) * (g 22)) := by
  norm_num [atom1066, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1066_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (88906175870400 : Int) atom1066) := by
  rw [SparsePolynomial.eval_scale, eval_atom1066]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 4) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1067 : SparsePolynomial.Poly := [([3,4,23], 1)]
theorem eval_atom1067 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1067 = ((g 3) * (g 4) * (g 23)) := by
  norm_num [atom1067, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1067_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (100636871428800 : Int) atom1067) := by
  rw [SparsePolynomial.eval_scale, eval_atom1067]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 4) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1068 : SparsePolynomial.Poly := [([3,5,5], 1)]
theorem eval_atom1068 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1068 = ((g 3) * (g 5) * (g 5)) := by
  norm_num [atom1068, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1068_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (74737156032000 : Int) atom1068) := by
  rw [SparsePolynomial.eval_scale, eval_atom1068]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1069 : SparsePolynomial.Poly := [([3,5,6], 1)]
theorem eval_atom1069 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1069 = ((g 3) * (g 5) * (g 6)) := by
  norm_num [atom1069, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1069_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (113960122204896 : Int) atom1069) := by
  rw [SparsePolynomial.eval_scale, eval_atom1069]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1070 : SparsePolynomial.Poly := [([3,5,7], 1)]
theorem eval_atom1070 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1070 = ((g 3) * (g 5) * (g 7)) := by
  norm_num [atom1070, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1070_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (88220867740896 : Int) atom1070) := by
  rw [SparsePolynomial.eval_scale, eval_atom1070]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1071 : SparsePolynomial.Poly := [([3,5,8], 1)]
theorem eval_atom1071 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1071 = ((g 3) * (g 5) * (g 8)) := by
  norm_num [atom1071, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1071_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (87041908809504 : Int) atom1071) := by
  rw [SparsePolynomial.eval_scale, eval_atom1071]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1072 : SparsePolynomial.Poly := [([3,5,9], 1)]
theorem eval_atom1072 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1072 = ((g 3) * (g 5) * (g 9)) := by
  norm_num [atom1072, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1072_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (91182603161232 : Int) atom1072) := by
  rw [SparsePolynomial.eval_scale, eval_atom1072]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1073 : SparsePolynomial.Poly := [([3,5,10], 1)]
theorem eval_atom1073 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1073 = ((g 3) * (g 5) * (g 10)) := by
  norm_num [atom1073, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1073_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (102037343565168 : Int) atom1073) := by
  rw [SparsePolynomial.eval_scale, eval_atom1073]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1074 : SparsePolynomial.Poly := [([3,5,11], 1)]
theorem eval_atom1074 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1074 = ((g 3) * (g 5) * (g 11)) := by
  norm_num [atom1074, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1074_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (119621894534208 : Int) atom1074) := by
  rw [SparsePolynomial.eval_scale, eval_atom1074]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1075 : SparsePolynomial.Poly := [([3,5,12], 1)]
theorem eval_atom1075 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1075 = ((g 3) * (g 5) * (g 12)) := by
  norm_num [atom1075, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1075_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (171213389221248 : Int) atom1075) := by
  rw [SparsePolynomial.eval_scale, eval_atom1075]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1076 : SparsePolynomial.Poly := [([3,5,13], 1)]
theorem eval_atom1076 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1076 = ((g 3) * (g 5) * (g 13)) := by
  norm_num [atom1076, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1076_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (149638658400000 : Int) atom1076) := by
  rw [SparsePolynomial.eval_scale, eval_atom1076]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1077 : SparsePolynomial.Poly := [([3,5,14], 1)]
theorem eval_atom1077 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1077 = ((g 3) * (g 5) * (g 14)) := by
  norm_num [atom1077, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1077_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (120715401945600 : Int) atom1077) := by
  rw [SparsePolynomial.eval_scale, eval_atom1077]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1078 : SparsePolynomial.Poly := [([3,5,15], 1)]
theorem eval_atom1078 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1078 = ((g 3) * (g 5) * (g 15)) := by
  norm_num [atom1078, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1078_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (122103897753600 : Int) atom1078) := by
  rw [SparsePolynomial.eval_scale, eval_atom1078]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 5) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1079 : SparsePolynomial.Poly := [([3,5,16], 1)]
theorem eval_atom1079 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1079 = ((g 3) * (g 5) * (g 16)) := by
  norm_num [atom1079, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1079_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (111669883315200 : Int) atom1079) := by
  rw [SparsePolynomial.eval_scale, eval_atom1079]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 5) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1080 : SparsePolynomial.Poly := [([3,5,17], 1)]
theorem eval_atom1080 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1080 = ((g 3) * (g 5) * (g 17)) := by
  norm_num [atom1080, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1080_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (111168607334400 : Int) atom1080) := by
  rw [SparsePolynomial.eval_scale, eval_atom1080]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 5) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1081 : SparsePolynomial.Poly := [([3,5,18], 1)]
theorem eval_atom1081 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1081 = ((g 3) * (g 5) * (g 18)) := by
  norm_num [atom1081, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1081_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (151375708915200 : Int) atom1081) := by
  rw [SparsePolynomial.eval_scale, eval_atom1081]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 5) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1082 : SparsePolynomial.Poly := [([3,5,19], 1)]
theorem eval_atom1082 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1082 = ((g 3) * (g 5) * (g 19)) := by
  norm_num [atom1082, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1082_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (109815055257600 : Int) atom1082) := by
  rw [SparsePolynomial.eval_scale, eval_atom1082]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 5) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1083 : SparsePolynomial.Poly := [([3,5,20], 1)]
theorem eval_atom1083 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1083 = ((g 3) * (g 5) * (g 20)) := by
  norm_num [atom1083, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1083_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (160013198822400 : Int) atom1083) := by
  rw [SparsePolynomial.eval_scale, eval_atom1083]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 5) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1084 : SparsePolynomial.Poly := [([3,5,21], 1)]
theorem eval_atom1084 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1084 = ((g 3) * (g 5) * (g 21)) := by
  norm_num [atom1084, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1084_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (146315722291200 : Int) atom1084) := by
  rw [SparsePolynomial.eval_scale, eval_atom1084]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 5) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1085 : SparsePolynomial.Poly := [([3,5,22], 1)]
theorem eval_atom1085 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1085 = ((g 3) * (g 5) * (g 22)) := by
  norm_num [atom1085, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1085_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (168934337510400 : Int) atom1085) := by
  rw [SparsePolynomial.eval_scale, eval_atom1085]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 5) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1086 : SparsePolynomial.Poly := [([3,5,23], 1)]
theorem eval_atom1086 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1086 = ((g 3) * (g 5) * (g 23)) := by
  norm_num [atom1086, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1086_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (191552952729600 : Int) atom1086) := by
  rw [SparsePolynomial.eval_scale, eval_atom1086]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 5) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1087 : SparsePolynomial.Poly := [([3,6,6], 1)]
theorem eval_atom1087 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1087 = ((g 3) * (g 6) * (g 6)) := by
  norm_num [atom1087, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1087_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (75779011123200 : Int) atom1087) := by
  rw [SparsePolynomial.eval_scale, eval_atom1087]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1088 : SparsePolynomial.Poly := [([3,6,7], 1)]
theorem eval_atom1088 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1088 = ((g 3) * (g 6) * (g 7)) := by
  norm_num [atom1088, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1088_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (123777582297600 : Int) atom1088) := by
  rw [SparsePolynomial.eval_scale, eval_atom1088]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block015 : SparsePolynomial.Poly := [([2,17,23], 475798210272000), ([2,18,18], 290294848166400), ([2,18,19], 476361662515200), ([2,18,20], 653817225600000), ([2,18,21], 549589191782400), ([2,18,22], 349197353164800), ([2,18,23], 503137604138400), ([2,19,19], 186615382947840), ([2,19,20], 534152726553600), ([2,19,21], 503407370188800), ([2,19,22], 347292762163200), ([2,19,23], 386611959333600), ([2,20,20], 348085912204800), ([2,20,21], 527646447820800), ([2,20,22], 345267040204800), ([2,20,23], 404881632540000), ([2,21,21], 170311413888000), ([2,21,22], 217123374182400), ([2,21,23], 288355987735200), ([2,22,22], 8846586806400), ([2,22,23], 100071607053600), ([2,23,23], 78422186858400), ([3,3,3], 23813830656000), ([3,3,4], 65232886118400), ([3,3,5], 65907174009600), ([3,3,6], 52815674419200), ([3,3,7], 46607068569600), ([3,3,8], 40398462720000), ([3,3,9], 40201637916528), ([3,3,10], 51636529101168), ([3,3,11], 61432993046304), ([3,3,12], 83146369420224), ([3,3,13], 68276633040000), ([3,3,14], 49732633843200), ([3,3,15], 45975641241600), ([3,3,16], 30396138393600), ([3,3,17], 24749374003200), ([3,3,18], 48733303449600), ([3,3,20], 36316091750400), ([3,4,4], 63987427929600), ([3,4,5], 107581417564896), ([3,4,6], 76714554470400), ([3,4,7], 68379713740800), ([3,4,8], 60044873011200), ([3,4,9], 63733594373856), ([3,4,10], 90685747712736), ([3,4,11], 114361046572608), ([3,4,12], 161870170290048), ([3,4,13], 136213068499200), ([3,4,14], 103207441075200), ([3,4,15], 99775826841600), ([3,4,16], 72699192115200), ([3,4,17], 70135468300800), ([3,4,18], 117538264166400), ([3,4,19], 58037916686400), ([3,4,20], 101760876504000), ([3,4,21], 77175480312000), ([3,4,22], 88906175870400), ([3,4,23], 100636871428800), ([3,5,5], 74737156032000), ([3,5,6], 113960122204896), ([3,5,7], 88220867740896), ([3,5,8], 87041908809504), ([3,5,9], 91182603161232), ([3,5,10], 102037343565168), ([3,5,11], 119621894534208), ([3,5,12], 171213389221248), ([3,5,13], 149638658400000), ([3,5,14], 120715401945600), ([3,5,15], 122103897753600), ([3,5,16], 111669883315200), ([3,5,17], 111168607334400), ([3,5,18], 151375708915200), ([3,5,19], 109815055257600), ([3,5,20], 160013198822400), ([3,5,21], 146315722291200), ([3,5,22], 168934337510400), ([3,5,23], 191552952729600), ([3,6,6], 75779011123200), ([3,6,7], 123777582297600)]
theorem block015_data : block015 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (475798210272000 : Int) atom1009) (SparsePolynomial.scale (290294848166400 : Int) atom1010)) (SparsePolynomial.merge (SparsePolynomial.scale (476361662515200 : Int) atom1011) (SparsePolynomial.merge (SparsePolynomial.scale (653817225600000 : Int) atom1012) (SparsePolynomial.scale (549589191782400 : Int) atom1013)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (349197353164800 : Int) atom1014) (SparsePolynomial.scale (503137604138400 : Int) atom1015)) (SparsePolynomial.merge (SparsePolynomial.scale (186615382947840 : Int) atom1016) (SparsePolynomial.merge (SparsePolynomial.scale (534152726553600 : Int) atom1017) (SparsePolynomial.scale (503407370188800 : Int) atom1018))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (347292762163200 : Int) atom1019) (SparsePolynomial.scale (386611959333600 : Int) atom1020)) (SparsePolynomial.merge (SparsePolynomial.scale (348085912204800 : Int) atom1021) (SparsePolynomial.merge (SparsePolynomial.scale (527646447820800 : Int) atom1022) (SparsePolynomial.scale (345267040204800 : Int) atom1023)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (404881632540000 : Int) atom1024) (SparsePolynomial.scale (170311413888000 : Int) atom1025)) (SparsePolynomial.merge (SparsePolynomial.scale (217123374182400 : Int) atom1026) (SparsePolynomial.merge (SparsePolynomial.scale (288355987735200 : Int) atom1027) (SparsePolynomial.scale (8846586806400 : Int) atom1028)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (100071607053600 : Int) atom1029) (SparsePolynomial.scale (78422186858400 : Int) atom1030)) (SparsePolynomial.merge (SparsePolynomial.scale (23813830656000 : Int) atom1031) (SparsePolynomial.merge (SparsePolynomial.scale (65232886118400 : Int) atom1032) (SparsePolynomial.scale (65907174009600 : Int) atom1033)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (52815674419200 : Int) atom1034) (SparsePolynomial.scale (46607068569600 : Int) atom1035)) (SparsePolynomial.merge (SparsePolynomial.scale (40398462720000 : Int) atom1036) (SparsePolynomial.merge (SparsePolynomial.scale (40201637916528 : Int) atom1037) (SparsePolynomial.scale (51636529101168 : Int) atom1038))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (61432993046304 : Int) atom1039) (SparsePolynomial.scale (83146369420224 : Int) atom1040)) (SparsePolynomial.merge (SparsePolynomial.scale (68276633040000 : Int) atom1041) (SparsePolynomial.merge (SparsePolynomial.scale (49732633843200 : Int) atom1042) (SparsePolynomial.scale (45975641241600 : Int) atom1043)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (30396138393600 : Int) atom1044) (SparsePolynomial.scale (24749374003200 : Int) atom1045)) (SparsePolynomial.merge (SparsePolynomial.scale (48733303449600 : Int) atom1046) (SparsePolynomial.merge (SparsePolynomial.scale (36316091750400 : Int) atom1047) (SparsePolynomial.scale (63987427929600 : Int) atom1048))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (107581417564896 : Int) atom1049) (SparsePolynomial.scale (76714554470400 : Int) atom1050)) (SparsePolynomial.merge (SparsePolynomial.scale (68379713740800 : Int) atom1051) (SparsePolynomial.merge (SparsePolynomial.scale (60044873011200 : Int) atom1052) (SparsePolynomial.scale (63733594373856 : Int) atom1053)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (90685747712736 : Int) atom1054) (SparsePolynomial.scale (114361046572608 : Int) atom1055)) (SparsePolynomial.merge (SparsePolynomial.scale (161870170290048 : Int) atom1056) (SparsePolynomial.merge (SparsePolynomial.scale (136213068499200 : Int) atom1057) (SparsePolynomial.scale (103207441075200 : Int) atom1058))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (99775826841600 : Int) atom1059) (SparsePolynomial.scale (72699192115200 : Int) atom1060)) (SparsePolynomial.merge (SparsePolynomial.scale (70135468300800 : Int) atom1061) (SparsePolynomial.merge (SparsePolynomial.scale (117538264166400 : Int) atom1062) (SparsePolynomial.scale (58037916686400 : Int) atom1063)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (101760876504000 : Int) atom1064) (SparsePolynomial.scale (77175480312000 : Int) atom1065)) (SparsePolynomial.merge (SparsePolynomial.scale (88906175870400 : Int) atom1066) (SparsePolynomial.merge (SparsePolynomial.scale (100636871428800 : Int) atom1067) (SparsePolynomial.scale (74737156032000 : Int) atom1068)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (113960122204896 : Int) atom1069) (SparsePolynomial.scale (88220867740896 : Int) atom1070)) (SparsePolynomial.merge (SparsePolynomial.scale (87041908809504 : Int) atom1071) (SparsePolynomial.merge (SparsePolynomial.scale (91182603161232 : Int) atom1072) (SparsePolynomial.scale (102037343565168 : Int) atom1073)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (119621894534208 : Int) atom1074) (SparsePolynomial.scale (171213389221248 : Int) atom1075)) (SparsePolynomial.merge (SparsePolynomial.scale (149638658400000 : Int) atom1076) (SparsePolynomial.merge (SparsePolynomial.scale (120715401945600 : Int) atom1077) (SparsePolynomial.scale (122103897753600 : Int) atom1078))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (111669883315200 : Int) atom1079) (SparsePolynomial.scale (111168607334400 : Int) atom1080)) (SparsePolynomial.merge (SparsePolynomial.scale (151375708915200 : Int) atom1081) (SparsePolynomial.merge (SparsePolynomial.scale (109815055257600 : Int) atom1082) (SparsePolynomial.scale (160013198822400 : Int) atom1083)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (146315722291200 : Int) atom1084) (SparsePolynomial.scale (168934337510400 : Int) atom1085)) (SparsePolynomial.merge (SparsePolynomial.scale (191552952729600 : Int) atom1086) (SparsePolynomial.merge (SparsePolynomial.scale (75779011123200 : Int) atom1087) (SparsePolynomial.scale (123777582297600 : Int) atom1088)))))))) := by decide +kernel
theorem block015_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block015 := by
  rw [block015_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1009_nonneg g hg hA hB) (atom1010_nonneg g hg hA hB)) (add_nonneg (atom1011_nonneg g hg hA hB) (add_nonneg (atom1012_nonneg g hg hA hB) (atom1013_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1014_nonneg g hg hA hB) (atom1015_nonneg g hg hA hB)) (add_nonneg (atom1016_nonneg g hg hA hB) (add_nonneg (atom1017_nonneg g hg hA hB) (atom1018_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1019_nonneg g hg hA hB) (atom1020_nonneg g hg hA hB)) (add_nonneg (atom1021_nonneg g hg hA hB) (add_nonneg (atom1022_nonneg g hg hA hB) (atom1023_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1024_nonneg g hg hA hB) (atom1025_nonneg g hg hA hB)) (add_nonneg (atom1026_nonneg g hg hA hB) (add_nonneg (atom1027_nonneg g hg hA hB) (atom1028_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1029_nonneg g hg hA hB) (atom1030_nonneg g hg hA hB)) (add_nonneg (atom1031_nonneg g hg hA hB) (add_nonneg (atom1032_nonneg g hg hA hB) (atom1033_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1034_nonneg g hg hA hB) (atom1035_nonneg g hg hA hB)) (add_nonneg (atom1036_nonneg g hg hA hB) (add_nonneg (atom1037_nonneg g hg hA hB) (atom1038_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1039_nonneg g hg hA hB) (atom1040_nonneg g hg hA hB)) (add_nonneg (atom1041_nonneg g hg hA hB) (add_nonneg (atom1042_nonneg g hg hA hB) (atom1043_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1044_nonneg g hg hA hB) (atom1045_nonneg g hg hA hB)) (add_nonneg (atom1046_nonneg g hg hA hB) (add_nonneg (atom1047_nonneg g hg hA hB) (atom1048_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1049_nonneg g hg hA hB) (atom1050_nonneg g hg hA hB)) (add_nonneg (atom1051_nonneg g hg hA hB) (add_nonneg (atom1052_nonneg g hg hA hB) (atom1053_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1054_nonneg g hg hA hB) (atom1055_nonneg g hg hA hB)) (add_nonneg (atom1056_nonneg g hg hA hB) (add_nonneg (atom1057_nonneg g hg hA hB) (atom1058_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1059_nonneg g hg hA hB) (atom1060_nonneg g hg hA hB)) (add_nonneg (atom1061_nonneg g hg hA hB) (add_nonneg (atom1062_nonneg g hg hA hB) (atom1063_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1064_nonneg g hg hA hB) (atom1065_nonneg g hg hA hB)) (add_nonneg (atom1066_nonneg g hg hA hB) (add_nonneg (atom1067_nonneg g hg hA hB) (atom1068_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1069_nonneg g hg hA hB) (atom1070_nonneg g hg hA hB)) (add_nonneg (atom1071_nonneg g hg hA hB) (add_nonneg (atom1072_nonneg g hg hA hB) (atom1073_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1074_nonneg g hg hA hB) (atom1075_nonneg g hg hA hB)) (add_nonneg (atom1076_nonneg g hg hA hB) (add_nonneg (atom1077_nonneg g hg hA hB) (atom1078_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1079_nonneg g hg hA hB) (atom1080_nonneg g hg hA hB)) (add_nonneg (atom1081_nonneg g hg hA hB) (add_nonneg (atom1082_nonneg g hg hA hB) (atom1083_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1084_nonneg g hg hA hB) (atom1085_nonneg g hg hA hB)) (add_nonneg (atom1086_nonneg g hg hA hB) (add_nonneg (atom1087_nonneg g hg hA hB) (atom1088_nonneg g hg hA hB))))))))

end APPT.Finite24
