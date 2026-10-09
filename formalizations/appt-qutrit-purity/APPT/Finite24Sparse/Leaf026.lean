import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom1889 : SparsePolynomial.Poly := [([7,17,23], 1)]
theorem eval_atom1889 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1889 = ((g 7) * (g 17) * (g 23)) := by
  norm_num [atom1889, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1889_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (690781818988800 : Int) atom1889) := by
  rw [SparsePolynomial.eval_scale, eval_atom1889]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 7) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1890 : SparsePolynomial.Poly := [([7,18,18], 1)]
theorem eval_atom1890 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1890 = ((g 7) * (g 18) * (g 18)) := by
  norm_num [atom1890, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1890_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (202067913062400 : Int) atom1890) := by
  rw [SparsePolynomial.eval_scale, eval_atom1890]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1891 : SparsePolynomial.Poly := [([7,18,19], 1)]
theorem eval_atom1891 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1891 = ((g 7) * (g 18) * (g 19)) := by
  norm_num [atom1891, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1891_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (390017626521600 : Int) atom1891) := by
  rw [SparsePolynomial.eval_scale, eval_atom1891]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1892 : SparsePolynomial.Poly := [([7,18,20], 1)]
theorem eval_atom1892 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1892 = ((g 7) * (g 18) * (g 20)) := by
  norm_num [atom1892, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1892_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (587162124595200 : Int) atom1892) := by
  rw [SparsePolynomial.eval_scale, eval_atom1892]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1893 : SparsePolynomial.Poly := [([7,18,21], 1)]
theorem eval_atom1893 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1893 = ((g 7) * (g 18) * (g 21)) := by
  norm_num [atom1893, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1893_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (591060221875200 : Int) atom1893) := by
  rw [SparsePolynomial.eval_scale, eval_atom1893]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 7) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1894 : SparsePolynomial.Poly := [([7,18,22], 1)]
theorem eval_atom1894 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1894 = ((g 7) * (g 18) * (g 22)) := by
  norm_num [atom1894, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1894_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (465720930796800 : Int) atom1894) := by
  rw [SparsePolynomial.eval_scale, eval_atom1894]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 7) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1895 : SparsePolynomial.Poly := [([7,18,23], 1)]
theorem eval_atom1895 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1895 = ((g 7) * (g 18) * (g 23)) := by
  norm_num [atom1895, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1895_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (672974601868800 : Int) atom1895) := by
  rw [SparsePolynomial.eval_scale, eval_atom1895]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 7) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1896 : SparsePolynomial.Poly := [([7,19,19], 1)]
theorem eval_atom1896 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1896 = ((g 7) * (g 19) * (g 19)) := by
  norm_num [atom1896, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1896_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (129207041187840 : Int) atom1896) := by
  rw [SparsePolynomial.eval_scale, eval_atom1896]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1897 : SparsePolynomial.Poly := [([7,19,20], 1)]
theorem eval_atom1897 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1897 = ((g 7) * (g 19) * (g 20)) := by
  norm_num [atom1897, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1897_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (426796764979200 : Int) atom1897) := by
  rw [SparsePolynomial.eval_scale, eval_atom1897]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1898 : SparsePolynomial.Poly := [([7,19,21], 1)]
theorem eval_atom1898 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1898 = ((g 7) * (g 19) * (g 21)) := by
  norm_num [atom1898, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1898_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (432844721971200 : Int) atom1898) := by
  rw [SparsePolynomial.eval_scale, eval_atom1898]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 7) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1899 : SparsePolynomial.Poly := [([7,19,22], 1)]
theorem eval_atom1899 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1899 = ((g 7) * (g 19) * (g 22)) := by
  norm_num [atom1899, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1899_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (378326949996800 : Int) atom1899) := by
  rw [SparsePolynomial.eval_scale, eval_atom1899]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 7) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1900 : SparsePolynomial.Poly := [([7,19,23], 1)]
theorem eval_atom1900 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1900 = ((g 7) * (g 19) * (g 23)) := by
  norm_num [atom1900, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1900_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (440381097072000 : Int) atom1900) := by
  rw [SparsePolynomial.eval_scale, eval_atom1900]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 7) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1901 : SparsePolynomial.Poly := [([7,20,20], 1)]
theorem eval_atom1901 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1901 = ((g 7) * (g 20) * (g 20)) := by
  norm_num [atom1901, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1901_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (309267950745600 : Int) atom1901) := by
  rw [SparsePolynomial.eval_scale, eval_atom1901]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1902 : SparsePolynomial.Poly := [([7,20,21], 1)]
theorem eval_atom1902 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1902 = ((g 7) * (g 20) * (g 21)) := by
  norm_num [atom1902, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1902_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (450681470131200 : Int) atom1902) := by
  rw [SparsePolynomial.eval_scale, eval_atom1902]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 7) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1903 : SparsePolynomial.Poly := [([7,20,22], 1)]
theorem eval_atom1903 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1903 = ((g 7) * (g 20) * (g 22)) := by
  norm_num [atom1903, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1903_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (366850113996800 : Int) atom1903) := by
  rw [SparsePolynomial.eval_scale, eval_atom1903]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 7) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1904 : SparsePolynomial.Poly := [([7,20,23], 1)]
theorem eval_atom1904 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1904 = ((g 7) * (g 20) * (g 23)) := by
  norm_num [atom1904, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1904_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (455881349347200 : Int) atom1904) := by
  rw [SparsePolynomial.eval_scale, eval_atom1904]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 7) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1905 : SparsePolynomial.Poly := [([7,21,21], 1)]
theorem eval_atom1905 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1905 = ((g 7) * (g 21) * (g 21)) := by
  norm_num [atom1905, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1905_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (89500313548800 : Int) atom1905) := by
  rw [SparsePolynomial.eval_scale, eval_atom1905]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 7) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1906 : SparsePolynomial.Poly := [([7,21,22], 1)]
theorem eval_atom1906 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1906 = ((g 7) * (g 21) * (g 22)) := by
  norm_num [atom1906, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1906_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (153592979366400 : Int) atom1906) := by
  rw [SparsePolynomial.eval_scale, eval_atom1906]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 7) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1907 : SparsePolynomial.Poly := [([7,21,23], 1)]
theorem eval_atom1907 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1907 = ((g 7) * (g 21) * (g 23)) := by
  norm_num [atom1907, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1907_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (236387787048000 : Int) atom1907) := by
  rw [SparsePolynomial.eval_scale, eval_atom1907]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 7) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1908 : SparsePolynomial.Poly := [([8,8,8], 1)]
theorem eval_atom1908 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1908 = ((g 8) * (g 8) * (g 8)) := by
  norm_num [atom1908, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1908_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15968023948800 : Int) atom1908) := by
  rw [SparsePolynomial.eval_scale, eval_atom1908]
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 8) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1909 : SparsePolynomial.Poly := [([8,8,9], 1)]
theorem eval_atom1909 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1909 = ((g 8) * (g 8) * (g 9)) := by
  norm_num [atom1909, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1909_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30188327122800 : Int) atom1909) := by
  rw [SparsePolynomial.eval_scale, eval_atom1909]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 8) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1910 : SparsePolynomial.Poly := [([8,8,10], 1)]
theorem eval_atom1910 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1910 = ((g 8) * (g 8) * (g 10)) := by
  norm_num [atom1910, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1910_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2502889795296 : Int) atom1910) := by
  rw [SparsePolynomial.eval_scale, eval_atom1910]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 8) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1911 : SparsePolynomial.Poly := [([8,8,11], 1)]
theorem eval_atom1911 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1911 = ((g 8) * (g 8) * (g 11)) := by
  norm_num [atom1911, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1911_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3083040576000 : Int) atom1911) := by
  rw [SparsePolynomial.eval_scale, eval_atom1911]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1912 : SparsePolynomial.Poly := [([8,9,9], 1)]
theorem eval_atom1912 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1912 = ((g 8) * (g 9) * (g 9)) := by
  norm_num [atom1912, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1912_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35074459173600 : Int) atom1912) := by
  rw [SparsePolynomial.eval_scale, eval_atom1912]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 8) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1913 : SparsePolynomial.Poly := [([8,9,10], 1)]
theorem eval_atom1913 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1913 = ((g 8) * (g 9) * (g 10)) := by
  norm_num [atom1913, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1913_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17799156411696 : Int) atom1913) := by
  rw [SparsePolynomial.eval_scale, eval_atom1913]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 8) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1914 : SparsePolynomial.Poly := [([8,9,14], 1)]
theorem eval_atom1914 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1914 = ((g 8) * (g 9) * (g 14)) := by
  norm_num [atom1914, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1914_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3083040576000 : Int) atom1914) := by
  rw [SparsePolynomial.eval_scale, eval_atom1914]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1915 : SparsePolynomial.Poly := [([8,9,15], 1)]
theorem eval_atom1915 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1915 = ((g 8) * (g 9) * (g 15)) := by
  norm_num [atom1915, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1915_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6166081152000 : Int) atom1915) := by
  rw [SparsePolynomial.eval_scale, eval_atom1915]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1916 : SparsePolynomial.Poly := [([8,9,16], 1)]
theorem eval_atom1916 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1916 = ((g 8) * (g 9) * (g 16)) := by
  norm_num [atom1916, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1916_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9249121728000 : Int) atom1916) := by
  rw [SparsePolynomial.eval_scale, eval_atom1916]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1917 : SparsePolynomial.Poly := [([8,9,17], 1)]
theorem eval_atom1917 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1917 = ((g 8) * (g 9) * (g 17)) := by
  norm_num [atom1917, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1917_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12332162304000 : Int) atom1917) := by
  rw [SparsePolynomial.eval_scale, eval_atom1917]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1918 : SparsePolynomial.Poly := [([8,9,19], 1)]
theorem eval_atom1918 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1918 = ((g 8) * (g 9) * (g 19)) := by
  norm_num [atom1918, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1918_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1197778982400 : Int) atom1918) := by
  rw [SparsePolynomial.eval_scale, eval_atom1918]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 9) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1919 : SparsePolynomial.Poly := [([8,9,21], 1)]
theorem eval_atom1919 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1919 = ((g 8) * (g 9) * (g 21)) := by
  norm_num [atom1919, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1919_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (45125791603200 : Int) atom1919) := by
  rw [SparsePolynomial.eval_scale, eval_atom1919]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 8) * (g 9) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1920 : SparsePolynomial.Poly := [([8,9,22], 1)]
theorem eval_atom1920 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1920 = ((g 8) * (g 9) * (g 22)) := by
  norm_num [atom1920, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1920_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (87856025241600 : Int) atom1920) := by
  rw [SparsePolynomial.eval_scale, eval_atom1920]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 8) * (g 9) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1921 : SparsePolynomial.Poly := [([8,9,23], 1)]
theorem eval_atom1921 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1921 = ((g 8) * (g 9) * (g 23)) := by
  norm_num [atom1921, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1921_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (137822544921600 : Int) atom1921) := by
  rw [SparsePolynomial.eval_scale, eval_atom1921]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 8) * (g 9) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1922 : SparsePolynomial.Poly := [([8,10,10], 1)]
theorem eval_atom1922 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1922 = ((g 8) * (g 10) * (g 10)) := by
  norm_num [atom1922, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1922_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5326574012496 : Int) atom1922) := by
  rw [SparsePolynomial.eval_scale, eval_atom1922]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 8) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1923 : SparsePolynomial.Poly := [([8,10,11], 1)]
theorem eval_atom1923 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1923 = ((g 8) * (g 10) * (g 11)) := by
  norm_num [atom1923, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1923_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2124375690096 : Int) atom1923) := by
  rw [SparsePolynomial.eval_scale, eval_atom1923]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1924 : SparsePolynomial.Poly := [([8,10,12], 1)]
theorem eval_atom1924 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1924 = ((g 8) * (g 10) * (g 12)) := by
  norm_num [atom1924, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1924_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1103782947696 : Int) atom1924) := by
  rw [SparsePolynomial.eval_scale, eval_atom1924]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 8) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1925 : SparsePolynomial.Poly := [([8,10,13], 1)]
theorem eval_atom1925 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1925 = ((g 8) * (g 10) * (g 13)) := by
  norm_num [atom1925, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1925_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6249271357296 : Int) atom1925) := by
  rw [SparsePolynomial.eval_scale, eval_atom1925]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1926 : SparsePolynomial.Poly := [([8,10,14], 1)]
theorem eval_atom1926 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1926 = ((g 8) * (g 10) * (g 14)) := by
  norm_num [atom1926, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1926_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11394759766896 : Int) atom1926) := by
  rw [SparsePolynomial.eval_scale, eval_atom1926]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1927 : SparsePolynomial.Poly := [([8,10,15], 1)]
theorem eval_atom1927 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1927 = ((g 8) * (g 10) * (g 15)) := by
  norm_num [atom1927, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1927_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16540248176496 : Int) atom1927) := by
  rw [SparsePolynomial.eval_scale, eval_atom1927]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1928 : SparsePolynomial.Poly := [([8,10,16], 1)]
theorem eval_atom1928 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1928 = ((g 8) * (g 10) * (g 16)) := by
  norm_num [atom1928, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1928_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21685736586096 : Int) atom1928) := by
  rw [SparsePolynomial.eval_scale, eval_atom1928]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1929 : SparsePolynomial.Poly := [([8,10,17], 1)]
theorem eval_atom1929 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1929 = ((g 8) * (g 10) * (g 17)) := by
  norm_num [atom1929, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1929_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26831224995696 : Int) atom1929) := by
  rw [SparsePolynomial.eval_scale, eval_atom1929]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1930 : SparsePolynomial.Poly := [([8,10,18], 1)]
theorem eval_atom1930 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1930 = ((g 8) * (g 10) * (g 18)) := by
  norm_num [atom1930, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1930_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (249966120888 : Int) atom1930) := by
  rw [SparsePolynomial.eval_scale, eval_atom1930]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1931 : SparsePolynomial.Poly := [([8,10,21], 1)]
theorem eval_atom1931 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1931 = ((g 8) * (g 10) * (g 21)) := by
  norm_num [atom1931, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1931_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (81191673285228 : Int) atom1931) := by
  rw [SparsePolynomial.eval_scale, eval_atom1931]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 8) * (g 10) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1932 : SparsePolynomial.Poly := [([8,10,22], 1)]
theorem eval_atom1932 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1932 = ((g 8) * (g 10) * (g 22)) := by
  norm_num [atom1932, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1932_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (162633312691344 : Int) atom1932) := by
  rw [SparsePolynomial.eval_scale, eval_atom1932]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 8) * (g 10) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1933 : SparsePolynomial.Poly := [([8,10,23], 1)]
theorem eval_atom1933 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1933 = ((g 8) * (g 10) * (g 23)) := by
  norm_num [atom1933, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1933_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (258589462107042 : Int) atom1933) := by
  rw [SparsePolynomial.eval_scale, eval_atom1933]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 8) * (g 10) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1934 : SparsePolynomial.Poly := [([8,11,11], 1)]
theorem eval_atom1934 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1934 = ((g 8) * (g 11) * (g 11)) := by
  norm_num [atom1934, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1934_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25565759604000 : Int) atom1934) := by
  rw [SparsePolynomial.eval_scale, eval_atom1934]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1935 : SparsePolynomial.Poly := [([8,11,12], 1)]
theorem eval_atom1935 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1935 = ((g 8) * (g 11) * (g 12)) := by
  norm_num [atom1935, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1935_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31374810482400 : Int) atom1935) := by
  rw [SparsePolynomial.eval_scale, eval_atom1935]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 8) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1936 : SparsePolynomial.Poly := [([8,11,13], 1)]
theorem eval_atom1936 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1936 = ((g 8) * (g 11) * (g 13)) := by
  norm_num [atom1936, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1936_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34479113407200 : Int) atom1936) := by
  rw [SparsePolynomial.eval_scale, eval_atom1936]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1937 : SparsePolynomial.Poly := [([8,11,14], 1)]
theorem eval_atom1937 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1937 = ((g 8) * (g 11) * (g 14)) := by
  norm_num [atom1937, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1937_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37583416332000 : Int) atom1937) := by
  rw [SparsePolynomial.eval_scale, eval_atom1937]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1938 : SparsePolynomial.Poly := [([8,11,15], 1)]
theorem eval_atom1938 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1938 = ((g 8) * (g 11) * (g 15)) := by
  norm_num [atom1938, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1938_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40687719256800 : Int) atom1938) := by
  rw [SparsePolynomial.eval_scale, eval_atom1938]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1939 : SparsePolynomial.Poly := [([8,11,16], 1)]
theorem eval_atom1939 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1939 = ((g 8) * (g 11) * (g 16)) := by
  norm_num [atom1939, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1939_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46875062757600 : Int) atom1939) := by
  rw [SparsePolynomial.eval_scale, eval_atom1939]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1940 : SparsePolynomial.Poly := [([8,11,17], 1)]
theorem eval_atom1940 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1940 = ((g 8) * (g 11) * (g 17)) := by
  norm_num [atom1940, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1940_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53062406258400 : Int) atom1940) := by
  rw [SparsePolynomial.eval_scale, eval_atom1940]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1941 : SparsePolynomial.Poly := [([8,11,18], 1)]
theorem eval_atom1941 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1941 = ((g 8) * (g 11) * (g 18)) := by
  norm_num [atom1941, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1941_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43596916084656 : Int) atom1941) := by
  rw [SparsePolynomial.eval_scale, eval_atom1941]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1942 : SparsePolynomial.Poly := [([8,11,19], 1)]
theorem eval_atom1942 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1942 = ((g 8) * (g 11) * (g 19)) := by
  norm_num [atom1942, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1942_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40466097239040 : Int) atom1942) := by
  rw [SparsePolynomial.eval_scale, eval_atom1942]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1943 : SparsePolynomial.Poly := [([8,11,20], 1)]
theorem eval_atom1943 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1943 = ((g 8) * (g 11) * (g 20)) := by
  norm_num [atom1943, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1943_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (59252072164560 : Int) atom1943) := by
  rw [SparsePolynomial.eval_scale, eval_atom1943]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1944 : SparsePolynomial.Poly := [([8,11,21], 1)]
theorem eval_atom1944 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1944 = ((g 8) * (g 11) * (g 21)) := by
  norm_num [atom1944, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1944_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (145083165594840 : Int) atom1944) := by
  rw [SparsePolynomial.eval_scale, eval_atom1944]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 8) * (g 11) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1945 : SparsePolynomial.Poly := [([8,11,22], 1)]
theorem eval_atom1945 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1945 = ((g 8) * (g 11) * (g 22)) := by
  norm_num [atom1945, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1945_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (241202304677664 : Int) atom1945) := by
  rw [SparsePolynomial.eval_scale, eval_atom1945]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 8) * (g 11) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1946 : SparsePolynomial.Poly := [([8,11,23], 1)]
theorem eval_atom1946 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1946 = ((g 8) * (g 11) * (g 23)) := by
  norm_num [atom1946, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1946_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (351539881100100 : Int) atom1946) := by
  rw [SparsePolynomial.eval_scale, eval_atom1946]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 8) * (g 11) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1947 : SparsePolynomial.Poly := [([8,12,12], 1)]
theorem eval_atom1947 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1947 = ((g 8) * (g 12) * (g 12)) := by
  norm_num [atom1947, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1947_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34577008804800 : Int) atom1947) := by
  rw [SparsePolynomial.eval_scale, eval_atom1947]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 8) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1948 : SparsePolynomial.Poly := [([8,12,13], 1)]
theorem eval_atom1948 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1948 = ((g 8) * (g 12) * (g 13)) := by
  norm_num [atom1948, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1948_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (63548730907200 : Int) atom1948) := by
  rw [SparsePolynomial.eval_scale, eval_atom1948]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1949 : SparsePolynomial.Poly := [([8,12,14], 1)]
theorem eval_atom1949 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1949 = ((g 8) * (g 12) * (g 14)) := by
  norm_num [atom1949, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1949_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (69757336756800 : Int) atom1949) := by
  rw [SparsePolynomial.eval_scale, eval_atom1949]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1950 : SparsePolynomial.Poly := [([8,12,15], 1)]
theorem eval_atom1950 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1950 = ((g 8) * (g 12) * (g 15)) := by
  norm_num [atom1950, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1950_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (75965942606400 : Int) atom1950) := by
  rw [SparsePolynomial.eval_scale, eval_atom1950]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1951 : SparsePolynomial.Poly := [([8,12,16], 1)]
theorem eval_atom1951 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1951 = ((g 8) * (g 12) * (g 16)) := by
  norm_num [atom1951, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1951_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (82174548456000 : Int) atom1951) := by
  rw [SparsePolynomial.eval_scale, eval_atom1951]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1952 : SparsePolynomial.Poly := [([8,12,17], 1)]
theorem eval_atom1952 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1952 = ((g 8) * (g 12) * (g 17)) := by
  norm_num [atom1952, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1952_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (88383154305600 : Int) atom1952) := by
  rw [SparsePolynomial.eval_scale, eval_atom1952]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1953 : SparsePolynomial.Poly := [([8,12,18], 1)]
theorem eval_atom1953 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1953 = ((g 8) * (g 12) * (g 18)) := by
  norm_num [atom1953, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1953_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (124602611211936 : Int) atom1953) := by
  rw [SparsePolynomial.eval_scale, eval_atom1953]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1954 : SparsePolynomial.Poly := [([8,12,19], 1)]
theorem eval_atom1954 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1954 = ((g 8) * (g 12) * (g 19)) := by
  norm_num [atom1954, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1954_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (106592002007040 : Int) atom1954) := by
  rw [SparsePolynomial.eval_scale, eval_atom1954]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1955 : SparsePolynomial.Poly := [([8,12,20], 1)]
theorem eval_atom1955 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1955 = ((g 8) * (g 12) * (g 20)) := by
  norm_num [atom1955, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1955_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (198627432996960 : Int) atom1955) := by
  rw [SparsePolynomial.eval_scale, eval_atom1955]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1956 : SparsePolynomial.Poly := [([8,12,21], 1)]
theorem eval_atom1956 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1956 = ((g 8) * (g 12) * (g 21)) := by
  norm_num [atom1956, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1956_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (222778113679440 : Int) atom1956) := by
  rw [SparsePolynomial.eval_scale, eval_atom1956]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 8) * (g 12) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1957 : SparsePolynomial.Poly := [([8,12,22], 1)]
theorem eval_atom1957 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1957 = ((g 8) * (g 12) * (g 22)) := by
  norm_num [atom1957, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1957_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (316603111771584 : Int) atom1957) := by
  rw [SparsePolynomial.eval_scale, eval_atom1957]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 8) * (g 12) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1958 : SparsePolynomial.Poly := [([8,12,23], 1)]
theorem eval_atom1958 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1958 = ((g 8) * (g 12) * (g 23)) := by
  norm_num [atom1958, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1958_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (419646672660600 : Int) atom1958) := by
  rw [SparsePolynomial.eval_scale, eval_atom1958]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 8) * (g 12) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1959 : SparsePolynomial.Poly := [([8,13,13], 1)]
theorem eval_atom1959 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1959 = ((g 8) * (g 13) * (g 13)) := by
  norm_num [atom1959, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1959_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (57739680028800 : Int) atom1959) := by
  rw [SparsePolynomial.eval_scale, eval_atom1959]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1960 : SparsePolynomial.Poly := [([8,13,14], 1)]
theorem eval_atom1960 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1960 = ((g 8) * (g 13) * (g 14)) := by
  norm_num [atom1960, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1960_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (108361788796800 : Int) atom1960) := by
  rw [SparsePolynomial.eval_scale, eval_atom1960]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1961 : SparsePolynomial.Poly := [([8,13,15], 1)]
theorem eval_atom1961 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1961 = ((g 8) * (g 13) * (g 15)) := by
  norm_num [atom1961, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1961_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (110488023676800 : Int) atom1961) := by
  rw [SparsePolynomial.eval_scale, eval_atom1961]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1962 : SparsePolynomial.Poly := [([8,13,16], 1)]
theorem eval_atom1962 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1962 = ((g 8) * (g 13) * (g 16)) := by
  norm_num [atom1962, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1962_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (115697299132800 : Int) atom1962) := by
  rw [SparsePolynomial.eval_scale, eval_atom1962]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1963 : SparsePolynomial.Poly := [([8,13,17], 1)]
theorem eval_atom1963 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1963 = ((g 8) * (g 13) * (g 17)) := by
  norm_num [atom1963, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1963_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (120906574588800 : Int) atom1963) := by
  rw [SparsePolynomial.eval_scale, eval_atom1963]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1964 : SparsePolynomial.Poly := [([8,13,18], 1)]
theorem eval_atom1964 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1964 = ((g 8) * (g 13) * (g 18)) := by
  norm_num [atom1964, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1964_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (152275157496000 : Int) atom1964) := by
  rw [SparsePolynomial.eval_scale, eval_atom1964]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1965 : SparsePolynomial.Poly := [([8,13,19], 1)]
theorem eval_atom1965 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1965 = ((g 8) * (g 13) * (g 19)) := by
  norm_num [atom1965, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1965_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (142638050016000 : Int) atom1965) := by
  rw [SparsePolynomial.eval_scale, eval_atom1965]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1966 : SparsePolynomial.Poly := [([8,13,20], 1)]
theorem eval_atom1966 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1966 = ((g 8) * (g 13) * (g 20)) := by
  norm_num [atom1966, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1966_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (245003491656000 : Int) atom1966) := by
  rw [SparsePolynomial.eval_scale, eval_atom1966]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1967 : SparsePolynomial.Poly := [([8,13,21], 1)]
theorem eval_atom1967 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1967 = ((g 8) * (g 13) * (g 21)) := by
  norm_num [atom1967, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1967_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (267452024162400 : Int) atom1967) := by
  rw [SparsePolynomial.eval_scale, eval_atom1967]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 8) * (g 13) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1968 : SparsePolynomial.Poly := [([8,13,22], 1)]
theorem eval_atom1968 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1968 = ((g 8) * (g 13) * (g 22)) := by
  norm_num [atom1968, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1968_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (367278829948800 : Int) atom1968) := by
  rw [SparsePolynomial.eval_scale, eval_atom1968]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 8) * (g 13) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block026 : SparsePolynomial.Poly := [([7,17,23], 690781818988800), ([7,18,18], 202067913062400), ([7,18,19], 390017626521600), ([7,18,20], 587162124595200), ([7,18,21], 591060221875200), ([7,18,22], 465720930796800), ([7,18,23], 672974601868800), ([7,19,19], 129207041187840), ([7,19,20], 426796764979200), ([7,19,21], 432844721971200), ([7,19,22], 378326949996800), ([7,19,23], 440381097072000), ([7,20,20], 309267950745600), ([7,20,21], 450681470131200), ([7,20,22], 366850113996800), ([7,20,23], 455881349347200), ([7,21,21], 89500313548800), ([7,21,22], 153592979366400), ([7,21,23], 236387787048000), ([8,8,8], 15968023948800), ([8,8,9], 30188327122800), ([8,8,10], 2502889795296), ([8,8,11], 3083040576000), ([8,9,9], 35074459173600), ([8,9,10], 17799156411696), ([8,9,14], 3083040576000), ([8,9,15], 6166081152000), ([8,9,16], 9249121728000), ([8,9,17], 12332162304000), ([8,9,19], 1197778982400), ([8,9,21], 45125791603200), ([8,9,22], 87856025241600), ([8,9,23], 137822544921600), ([8,10,10], 5326574012496), ([8,10,11], 2124375690096), ([8,10,12], 1103782947696), ([8,10,13], 6249271357296), ([8,10,14], 11394759766896), ([8,10,15], 16540248176496), ([8,10,16], 21685736586096), ([8,10,17], 26831224995696), ([8,10,18], 249966120888), ([8,10,21], 81191673285228), ([8,10,22], 162633312691344), ([8,10,23], 258589462107042), ([8,11,11], 25565759604000), ([8,11,12], 31374810482400), ([8,11,13], 34479113407200), ([8,11,14], 37583416332000), ([8,11,15], 40687719256800), ([8,11,16], 46875062757600), ([8,11,17], 53062406258400), ([8,11,18], 43596916084656), ([8,11,19], 40466097239040), ([8,11,20], 59252072164560), ([8,11,21], 145083165594840), ([8,11,22], 241202304677664), ([8,11,23], 351539881100100), ([8,12,12], 34577008804800), ([8,12,13], 63548730907200), ([8,12,14], 69757336756800), ([8,12,15], 75965942606400), ([8,12,16], 82174548456000), ([8,12,17], 88383154305600), ([8,12,18], 124602611211936), ([8,12,19], 106592002007040), ([8,12,20], 198627432996960), ([8,12,21], 222778113679440), ([8,12,22], 316603111771584), ([8,12,23], 419646672660600), ([8,13,13], 57739680028800), ([8,13,14], 108361788796800), ([8,13,15], 110488023676800), ([8,13,16], 115697299132800), ([8,13,17], 120906574588800), ([8,13,18], 152275157496000), ([8,13,19], 142638050016000), ([8,13,20], 245003491656000), ([8,13,21], 267452024162400), ([8,13,22], 367278829948800)]
theorem block026_data : block026 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (690781818988800 : Int) atom1889) (SparsePolynomial.scale (202067913062400 : Int) atom1890)) (SparsePolynomial.merge (SparsePolynomial.scale (390017626521600 : Int) atom1891) (SparsePolynomial.merge (SparsePolynomial.scale (587162124595200 : Int) atom1892) (SparsePolynomial.scale (591060221875200 : Int) atom1893)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (465720930796800 : Int) atom1894) (SparsePolynomial.scale (672974601868800 : Int) atom1895)) (SparsePolynomial.merge (SparsePolynomial.scale (129207041187840 : Int) atom1896) (SparsePolynomial.merge (SparsePolynomial.scale (426796764979200 : Int) atom1897) (SparsePolynomial.scale (432844721971200 : Int) atom1898))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (378326949996800 : Int) atom1899) (SparsePolynomial.scale (440381097072000 : Int) atom1900)) (SparsePolynomial.merge (SparsePolynomial.scale (309267950745600 : Int) atom1901) (SparsePolynomial.merge (SparsePolynomial.scale (450681470131200 : Int) atom1902) (SparsePolynomial.scale (366850113996800 : Int) atom1903)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (455881349347200 : Int) atom1904) (SparsePolynomial.scale (89500313548800 : Int) atom1905)) (SparsePolynomial.merge (SparsePolynomial.scale (153592979366400 : Int) atom1906) (SparsePolynomial.merge (SparsePolynomial.scale (236387787048000 : Int) atom1907) (SparsePolynomial.scale (15968023948800 : Int) atom1908)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (30188327122800 : Int) atom1909) (SparsePolynomial.scale (2502889795296 : Int) atom1910)) (SparsePolynomial.merge (SparsePolynomial.scale (3083040576000 : Int) atom1911) (SparsePolynomial.merge (SparsePolynomial.scale (35074459173600 : Int) atom1912) (SparsePolynomial.scale (17799156411696 : Int) atom1913)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3083040576000 : Int) atom1914) (SparsePolynomial.scale (6166081152000 : Int) atom1915)) (SparsePolynomial.merge (SparsePolynomial.scale (9249121728000 : Int) atom1916) (SparsePolynomial.merge (SparsePolynomial.scale (12332162304000 : Int) atom1917) (SparsePolynomial.scale (1197778982400 : Int) atom1918))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (45125791603200 : Int) atom1919) (SparsePolynomial.scale (87856025241600 : Int) atom1920)) (SparsePolynomial.merge (SparsePolynomial.scale (137822544921600 : Int) atom1921) (SparsePolynomial.merge (SparsePolynomial.scale (5326574012496 : Int) atom1922) (SparsePolynomial.scale (2124375690096 : Int) atom1923)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1103782947696 : Int) atom1924) (SparsePolynomial.scale (6249271357296 : Int) atom1925)) (SparsePolynomial.merge (SparsePolynomial.scale (11394759766896 : Int) atom1926) (SparsePolynomial.merge (SparsePolynomial.scale (16540248176496 : Int) atom1927) (SparsePolynomial.scale (21685736586096 : Int) atom1928))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (26831224995696 : Int) atom1929) (SparsePolynomial.scale (249966120888 : Int) atom1930)) (SparsePolynomial.merge (SparsePolynomial.scale (81191673285228 : Int) atom1931) (SparsePolynomial.merge (SparsePolynomial.scale (162633312691344 : Int) atom1932) (SparsePolynomial.scale (258589462107042 : Int) atom1933)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (25565759604000 : Int) atom1934) (SparsePolynomial.scale (31374810482400 : Int) atom1935)) (SparsePolynomial.merge (SparsePolynomial.scale (34479113407200 : Int) atom1936) (SparsePolynomial.merge (SparsePolynomial.scale (37583416332000 : Int) atom1937) (SparsePolynomial.scale (40687719256800 : Int) atom1938))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (46875062757600 : Int) atom1939) (SparsePolynomial.scale (53062406258400 : Int) atom1940)) (SparsePolynomial.merge (SparsePolynomial.scale (43596916084656 : Int) atom1941) (SparsePolynomial.merge (SparsePolynomial.scale (40466097239040 : Int) atom1942) (SparsePolynomial.scale (59252072164560 : Int) atom1943)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (145083165594840 : Int) atom1944) (SparsePolynomial.scale (241202304677664 : Int) atom1945)) (SparsePolynomial.merge (SparsePolynomial.scale (351539881100100 : Int) atom1946) (SparsePolynomial.merge (SparsePolynomial.scale (34577008804800 : Int) atom1947) (SparsePolynomial.scale (63548730907200 : Int) atom1948)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (69757336756800 : Int) atom1949) (SparsePolynomial.scale (75965942606400 : Int) atom1950)) (SparsePolynomial.merge (SparsePolynomial.scale (82174548456000 : Int) atom1951) (SparsePolynomial.merge (SparsePolynomial.scale (88383154305600 : Int) atom1952) (SparsePolynomial.scale (124602611211936 : Int) atom1953)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (106592002007040 : Int) atom1954) (SparsePolynomial.scale (198627432996960 : Int) atom1955)) (SparsePolynomial.merge (SparsePolynomial.scale (222778113679440 : Int) atom1956) (SparsePolynomial.merge (SparsePolynomial.scale (316603111771584 : Int) atom1957) (SparsePolynomial.scale (419646672660600 : Int) atom1958))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (57739680028800 : Int) atom1959) (SparsePolynomial.scale (108361788796800 : Int) atom1960)) (SparsePolynomial.merge (SparsePolynomial.scale (110488023676800 : Int) atom1961) (SparsePolynomial.merge (SparsePolynomial.scale (115697299132800 : Int) atom1962) (SparsePolynomial.scale (120906574588800 : Int) atom1963)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (152275157496000 : Int) atom1964) (SparsePolynomial.scale (142638050016000 : Int) atom1965)) (SparsePolynomial.merge (SparsePolynomial.scale (245003491656000 : Int) atom1966) (SparsePolynomial.merge (SparsePolynomial.scale (267452024162400 : Int) atom1967) (SparsePolynomial.scale (367278829948800 : Int) atom1968)))))))) := by decide +kernel
theorem block026_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block026 := by
  rw [block026_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1889_nonneg g hg hA hB) (atom1890_nonneg g hg hA hB)) (add_nonneg (atom1891_nonneg g hg hA hB) (add_nonneg (atom1892_nonneg g hg hA hB) (atom1893_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1894_nonneg g hg hA hB) (atom1895_nonneg g hg hA hB)) (add_nonneg (atom1896_nonneg g hg hA hB) (add_nonneg (atom1897_nonneg g hg hA hB) (atom1898_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1899_nonneg g hg hA hB) (atom1900_nonneg g hg hA hB)) (add_nonneg (atom1901_nonneg g hg hA hB) (add_nonneg (atom1902_nonneg g hg hA hB) (atom1903_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1904_nonneg g hg hA hB) (atom1905_nonneg g hg hA hB)) (add_nonneg (atom1906_nonneg g hg hA hB) (add_nonneg (atom1907_nonneg g hg hA hB) (atom1908_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1909_nonneg g hg hA hB) (atom1910_nonneg g hg hA hB)) (add_nonneg (atom1911_nonneg g hg hA hB) (add_nonneg (atom1912_nonneg g hg hA hB) (atom1913_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1914_nonneg g hg hA hB) (atom1915_nonneg g hg hA hB)) (add_nonneg (atom1916_nonneg g hg hA hB) (add_nonneg (atom1917_nonneg g hg hA hB) (atom1918_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1919_nonneg g hg hA hB) (atom1920_nonneg g hg hA hB)) (add_nonneg (atom1921_nonneg g hg hA hB) (add_nonneg (atom1922_nonneg g hg hA hB) (atom1923_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1924_nonneg g hg hA hB) (atom1925_nonneg g hg hA hB)) (add_nonneg (atom1926_nonneg g hg hA hB) (add_nonneg (atom1927_nonneg g hg hA hB) (atom1928_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1929_nonneg g hg hA hB) (atom1930_nonneg g hg hA hB)) (add_nonneg (atom1931_nonneg g hg hA hB) (add_nonneg (atom1932_nonneg g hg hA hB) (atom1933_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1934_nonneg g hg hA hB) (atom1935_nonneg g hg hA hB)) (add_nonneg (atom1936_nonneg g hg hA hB) (add_nonneg (atom1937_nonneg g hg hA hB) (atom1938_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1939_nonneg g hg hA hB) (atom1940_nonneg g hg hA hB)) (add_nonneg (atom1941_nonneg g hg hA hB) (add_nonneg (atom1942_nonneg g hg hA hB) (atom1943_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1944_nonneg g hg hA hB) (atom1945_nonneg g hg hA hB)) (add_nonneg (atom1946_nonneg g hg hA hB) (add_nonneg (atom1947_nonneg g hg hA hB) (atom1948_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1949_nonneg g hg hA hB) (atom1950_nonneg g hg hA hB)) (add_nonneg (atom1951_nonneg g hg hA hB) (add_nonneg (atom1952_nonneg g hg hA hB) (atom1953_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1954_nonneg g hg hA hB) (atom1955_nonneg g hg hA hB)) (add_nonneg (atom1956_nonneg g hg hA hB) (add_nonneg (atom1957_nonneg g hg hA hB) (atom1958_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1959_nonneg g hg hA hB) (atom1960_nonneg g hg hA hB)) (add_nonneg (atom1961_nonneg g hg hA hB) (add_nonneg (atom1962_nonneg g hg hA hB) (atom1963_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1964_nonneg g hg hA hB) (atom1965_nonneg g hg hA hB)) (add_nonneg (atom1966_nonneg g hg hA hB) (add_nonneg (atom1967_nonneg g hg hA hB) (atom1968_nonneg g hg hA hB))))))))

end APPT.Finite24
