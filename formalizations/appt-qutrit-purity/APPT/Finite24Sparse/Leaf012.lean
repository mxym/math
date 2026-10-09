import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom0769 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 20, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0769 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0769 = ((g 1) * (g 20) * (g 20)) := by
  norm_num [atom0769, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0769_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (279004540953600 : Int) atom0769) := by
  rw [SparsePolynomial.eval_scale, eval_atom0769]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0769Coded : CoefficientMerge.Poly := [(nat_lit 1076, Int.ofNat (nat_lit 1))]
theorem atom0769Coded_decode : atom0769 = SparsePolynomial.decodeCubic 24 atom0769Coded := by decide +kernel
theorem atom0769Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (279004540953600 : Int) atom0769Coded) := by
  have h := atom0769_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0769Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0770 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 20, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0770 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0770 = ((g 1) * (g 20) * (g 21)) := by
  norm_num [atom0770, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0770_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (444567363609600 : Int) atom0770) := by
  rw [SparsePolynomial.eval_scale, eval_atom0770]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0770Coded : CoefficientMerge.Poly := [(nat_lit 1077, Int.ofNat (nat_lit 1))]
theorem atom0770Coded_decode : atom0770 = SparsePolynomial.decodeCubic 24 atom0770Coded := by decide +kernel
theorem atom0770Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (444567363609600 : Int) atom0770Coded) := by
  have h := atom0770_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0770Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0771 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 20, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0771 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0771 = ((g 1) * (g 20) * (g 22)) := by
  norm_num [atom0771, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0771_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (345540443942400 : Int) atom0771) := by
  rw [SparsePolynomial.eval_scale, eval_atom0771]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0771Coded : CoefficientMerge.Poly := [(nat_lit 1078, Int.ofNat (nat_lit 1))]
theorem atom0771Coded_decode : atom0771 = SparsePolynomial.decodeCubic 24 atom0771Coded := by decide +kernel
theorem atom0771Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (345540443942400 : Int) atom0771Coded) := by
  have h := atom0771_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0771Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0772 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 20, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0772 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0772 = ((g 1) * (g 20) * (g 23)) := by
  norm_num [atom0772, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0772_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (358952744304000 : Int) atom0772) := by
  rw [SparsePolynomial.eval_scale, eval_atom0772]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0772Coded : CoefficientMerge.Poly := [(nat_lit 1079, Int.ofNat (nat_lit 1))]
theorem atom0772Coded_decode : atom0772 = SparsePolynomial.decodeCubic 24 atom0772Coded := by decide +kernel
theorem atom0772Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (358952744304000 : Int) atom0772Coded) := by
  have h := atom0772_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0772Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0773 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 21, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0773 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0773 = ((g 1) * (g 21) * (g 21)) := by
  norm_num [atom0773, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0773_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (158851007884800 : Int) atom0773) := by
  rw [SparsePolynomial.eval_scale, eval_atom0773]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0773Coded : CoefficientMerge.Poly := [(nat_lit 1101, Int.ofNat (nat_lit 1))]
theorem atom0773Coded_decode : atom0773 = SparsePolynomial.decodeCubic 24 atom0773Coded := by decide +kernel
theorem atom0773Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (158851007884800 : Int) atom0773Coded) := by
  have h := atom0773_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0773Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0774 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 21, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0774 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0774 = ((g 1) * (g 21) * (g 22)) := by
  norm_num [atom0774, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0774_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (218610772128000 : Int) atom0774) := by
  rw [SparsePolynomial.eval_scale, eval_atom0774]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0774Coded : CoefficientMerge.Poly := [(nat_lit 1102, Int.ofNat (nat_lit 1))]
theorem atom0774Coded_decode : atom0774 = SparsePolynomial.decodeCubic 24 atom0774Coded := by decide +kernel
theorem atom0774Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (218610772128000 : Int) atom0774Coded) := by
  have h := atom0774_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0774Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0775 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 21, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0775 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0775 = ((g 1) * (g 21) * (g 23)) := by
  norm_num [atom0775, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0775_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (225802600531200 : Int) atom0775) := by
  rw [SparsePolynomial.eval_scale, eval_atom0775]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0775Coded : CoefficientMerge.Poly := [(nat_lit 1103, Int.ofNat (nat_lit 1))]
theorem atom0775Coded_decode : atom0775 = SparsePolynomial.decodeCubic 24 atom0775Coded := by decide +kernel
theorem atom0775Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (225802600531200 : Int) atom0775Coded) := by
  have h := atom0775_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0775Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0776 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 22, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0776 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0776 = ((g 1) * (g 22) * (g 22)) := by
  norm_num [atom0776, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0776_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36833126568000 : Int) atom0776) := by
  rw [SparsePolynomial.eval_scale, eval_atom0776]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 22) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0776Coded : CoefficientMerge.Poly := [(nat_lit 1126, Int.ofNat (nat_lit 1))]
theorem atom0776Coded_decode : atom0776 = SparsePolynomial.decodeCubic 24 atom0776Coded := by decide +kernel
theorem atom0776Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (36833126568000 : Int) atom0776Coded) := by
  have h := atom0776_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0776Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0777 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 22, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0777 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0777 = ((g 1) * (g 22) * (g 23)) := by
  norm_num [atom0777, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0777_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (80799180537600 : Int) atom0777) := by
  rw [SparsePolynomial.eval_scale, eval_atom0777]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 22) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0777Coded : CoefficientMerge.Poly := [(nat_lit 1127, Int.ofNat (nat_lit 1))]
theorem atom0777Coded_decode : atom0777 = SparsePolynomial.decodeCubic 24 atom0777Coded := by decide +kernel
theorem atom0777Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (80799180537600 : Int) atom0777Coded) := by
  have h := atom0777_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0777Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0778 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 23, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0778 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0778 = ((g 1) * (g 23) * (g 23)) := by
  norm_num [atom0778, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0778_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24047716492800 : Int) atom0778) := by
  rw [SparsePolynomial.eval_scale, eval_atom0778]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 23) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0778Coded : CoefficientMerge.Poly := [(nat_lit 1151, Int.ofNat (nat_lit 1))]
theorem atom0778Coded_decode : atom0778 = SparsePolynomial.decodeCubic 24 atom0778Coded := by decide +kernel
theorem atom0778Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (24047716492800 : Int) atom0778Coded) := by
  have h := atom0778_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0778Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0779 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 2], Int.ofNat (nat_lit 1))]
theorem eval_atom0779 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0779 = ((g 2) * (g 2) * (g 2)) := by
  norm_num [atom0779, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0779_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42673534041600 : Int) atom0779) := by
  rw [SparsePolynomial.eval_scale, eval_atom0779]
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 2) * (g 2) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0779Coded : CoefficientMerge.Poly := [(nat_lit 1202, Int.ofNat (nat_lit 1))]
theorem atom0779Coded_decode : atom0779 = SparsePolynomial.decodeCubic 24 atom0779Coded := by decide +kernel
theorem atom0779Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (42673534041600 : Int) atom0779Coded) := by
  have h := atom0779_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0779Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0780 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 3], Int.ofNat (nat_lit 1))]
theorem eval_atom0780 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0780 = ((g 2) * (g 2) * (g 3)) := by
  norm_num [atom0780, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0780_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (121833258624000 : Int) atom0780) := by
  rw [SparsePolynomial.eval_scale, eval_atom0780]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 2) * (g 2) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0780Coded : CoefficientMerge.Poly := [(nat_lit 1203, Int.ofNat (nat_lit 1))]
theorem atom0780Coded_decode : atom0780 = SparsePolynomial.decodeCubic 24 atom0780Coded := by decide +kernel
theorem atom0780Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (121833258624000 : Int) atom0780Coded) := by
  have h := atom0780_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0780Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0781 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0781 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0781 = ((g 2) * (g 2) * (g 4)) := by
  norm_num [atom0781, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0781_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (115645915123200 : Int) atom0781) := by
  rw [SparsePolynomial.eval_scale, eval_atom0781]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 2) * (g 2) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0781Coded : CoefficientMerge.Poly := [(nat_lit 1204, Int.ofNat (nat_lit 1))]
theorem atom0781Coded_decode : atom0781 = SparsePolynomial.decodeCubic 24 atom0781Coded := by decide +kernel
theorem atom0781Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (115645915123200 : Int) atom0781Coded) := by
  have h := atom0781_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0781Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0782 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0782 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0782 = ((g 2) * (g 2) * (g 5)) := by
  norm_num [atom0782, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0782_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (116341465363200 : Int) atom0782) := by
  rw [SparsePolynomial.eval_scale, eval_atom0782]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 2) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0782Coded : CoefficientMerge.Poly := [(nat_lit 1205, Int.ofNat (nat_lit 1))]
theorem atom0782Coded_decode : atom0782 = SparsePolynomial.decodeCubic 24 atom0782Coded := by decide +kernel
theorem atom0782Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (116341465363200 : Int) atom0782Coded) := by
  have h := atom0782_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0782Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0783 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0783 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0783 = ((g 2) * (g 2) * (g 6)) := by
  norm_num [atom0783, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0783_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (103271228121600 : Int) atom0783) := by
  rw [SparsePolynomial.eval_scale, eval_atom0783]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 2) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0783Coded : CoefficientMerge.Poly := [(nat_lit 1206, Int.ofNat (nat_lit 1))]
theorem atom0783Coded_decode : atom0783 = SparsePolynomial.decodeCubic 24 atom0783Coded := by decide +kernel
theorem atom0783Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (103271228121600 : Int) atom0783Coded) := by
  have h := atom0783_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0783Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0784 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0784 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0784 = ((g 2) * (g 2) * (g 7)) := by
  norm_num [atom0784, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0784_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (97083884620800 : Int) atom0784) := by
  rw [SparsePolynomial.eval_scale, eval_atom0784]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 2) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0784Coded : CoefficientMerge.Poly := [(nat_lit 1207, Int.ofNat (nat_lit 1))]
theorem atom0784Coded_decode : atom0784 = SparsePolynomial.decodeCubic 24 atom0784Coded := by decide +kernel
theorem atom0784Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (97083884620800 : Int) atom0784Coded) := by
  have h := atom0784_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0784Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0785 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0785 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0785 = ((g 2) * (g 2) * (g 8)) := by
  norm_num [atom0785, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0785_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (90896541120000 : Int) atom0785) := by
  rw [SparsePolynomial.eval_scale, eval_atom0785]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 2) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0785Coded : CoefficientMerge.Poly := [(nat_lit 1208, Int.ofNat (nat_lit 1))]
theorem atom0785Coded_decode : atom0785 = SparsePolynomial.decodeCubic 24 atom0785Coded := by decide +kernel
theorem atom0785Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (90896541120000 : Int) atom0785Coded) := by
  have h := atom0785_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0785Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0786 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0786 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0786 = ((g 2) * (g 2) * (g 9)) := by
  norm_num [atom0786, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0786_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (90720978665328 : Int) atom0786) := by
  rw [SparsePolynomial.eval_scale, eval_atom0786]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 2) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0786Coded : CoefficientMerge.Poly := [(nat_lit 1209, Int.ofNat (nat_lit 1))]
theorem atom0786Coded_decode : atom0786 = SparsePolynomial.decodeCubic 24 atom0786Coded := by decide +kernel
theorem atom0786Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (90720978665328 : Int) atom0786Coded) := by
  have h := atom0786_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0786Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0787 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0787 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0787 = ((g 2) * (g 2) * (g 10)) := by
  norm_num [atom0787, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0787_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (102177132198768 : Int) atom0787) := by
  rw [SparsePolynomial.eval_scale, eval_atom0787]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 2) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0787Coded : CoefficientMerge.Poly := [(nat_lit 1210, Int.ofNat (nat_lit 1))]
theorem atom0787Coded_decode : atom0787 = SparsePolynomial.decodeCubic 24 atom0787Coded := by decide +kernel
theorem atom0787Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (102177132198768 : Int) atom0787Coded) := by
  have h := atom0787_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0787Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0788 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0788 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0788 = ((g 2) * (g 2) * (g 11)) := by
  norm_num [atom0788, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0788_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (111994858492704 : Int) atom0788) := by
  rw [SparsePolynomial.eval_scale, eval_atom0788]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 2) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0788Coded : CoefficientMerge.Poly := [(nat_lit 1211, Int.ofNat (nat_lit 1))]
theorem atom0788Coded_decode : atom0788 = SparsePolynomial.decodeCubic 24 atom0788Coded := by decide +kernel
theorem atom0788Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (111994858492704 : Int) atom0788Coded) := by
  have h := atom0788_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0788Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0789 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0789 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0789 = ((g 2) * (g 2) * (g 12)) := by
  norm_num [atom0789, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0789_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (133729497215424 : Int) atom0789) := by
  rw [SparsePolynomial.eval_scale, eval_atom0789]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 2) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0789Coded : CoefficientMerge.Poly := [(nat_lit 1212, Int.ofNat (nat_lit 1))]
theorem atom0789Coded_decode : atom0789 = SparsePolynomial.decodeCubic 24 atom0789Coded := by decide +kernel
theorem atom0789Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (133729497215424 : Int) atom0789Coded) := by
  have h := atom0789_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0789Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0790 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0790 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0790 = ((g 2) * (g 2) * (g 13)) := by
  norm_num [atom0790, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0790_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (118881023184000 : Int) atom0790) := by
  rw [SparsePolynomial.eval_scale, eval_atom0790]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 2) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0790Coded : CoefficientMerge.Poly := [(nat_lit 1213, Int.ofNat (nat_lit 1))]
theorem atom0790Coded_decode : atom0790 = SparsePolynomial.decodeCubic 24 atom0790Coded := by decide +kernel
theorem atom0790Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (118881023184000 : Int) atom0790Coded) := by
  have h := atom0790_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0790Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0791 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0791 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0791 = ((g 2) * (g 2) * (g 14)) := by
  norm_num [atom0791, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0791_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (100358286336000 : Int) atom0791) := by
  rw [SparsePolynomial.eval_scale, eval_atom0791]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 2) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0791Coded : CoefficientMerge.Poly := [(nat_lit 1214, Int.ofNat (nat_lit 1))]
theorem atom0791Coded_decode : atom0791 = SparsePolynomial.decodeCubic 24 atom0791Coded := by decide +kernel
theorem atom0791Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (100358286336000 : Int) atom0791Coded) := by
  have h := atom0791_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0791Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0792 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0792 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0792 = ((g 2) * (g 2) * (g 15)) := by
  norm_num [atom0792, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0792_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (96622556083200 : Int) atom0792) := by
  rw [SparsePolynomial.eval_scale, eval_atom0792]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 2) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0792Coded : CoefficientMerge.Poly := [(nat_lit 1215, Int.ofNat (nat_lit 1))]
theorem atom0792Coded_decode : atom0792 = SparsePolynomial.decodeCubic 24 atom0792Coded := by decide +kernel
theorem atom0792Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (96622556083200 : Int) atom0792Coded) := by
  have h := atom0792_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0792Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0793 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0793 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0793 = ((g 2) * (g 2) * (g 16)) := by
  norm_num [atom0793, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0793_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (81064315584000 : Int) atom0793) := by
  rw [SparsePolynomial.eval_scale, eval_atom0793]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 2) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0793Coded : CoefficientMerge.Poly := [(nat_lit 1216, Int.ofNat (nat_lit 1))]
theorem atom0793Coded_decode : atom0793 = SparsePolynomial.decodeCubic 24 atom0793Coded := by decide +kernel
theorem atom0793Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (81064315584000 : Int) atom0793Coded) := by
  have h := atom0793_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0793Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0794 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0794 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0794 = ((g 2) * (g 2) * (g 17)) := by
  norm_num [atom0794, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0794_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (75438813542400 : Int) atom0794) := by
  rw [SparsePolynomial.eval_scale, eval_atom0794]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 2) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0794Coded : CoefficientMerge.Poly := [(nat_lit 1217, Int.ofNat (nat_lit 1))]
theorem atom0794Coded_decode : atom0794 = SparsePolynomial.decodeCubic 24 atom0794Coded := by decide +kernel
theorem atom0794Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (75438813542400 : Int) atom0794Coded) := by
  have h := atom0794_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0794Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0795 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0795 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0795 = ((g 2) * (g 2) * (g 18)) := by
  norm_num [atom0795, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0795_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (99444005337600 : Int) atom0795) := by
  rw [SparsePolynomial.eval_scale, eval_atom0795]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 2) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0795Coded : CoefficientMerge.Poly := [(nat_lit 1218, Int.ofNat (nat_lit 1))]
theorem atom0795Coded_decode : atom0795 = SparsePolynomial.decodeCubic 24 atom0795Coded := by decide +kernel
theorem atom0795Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (99444005337600 : Int) atom0795Coded) := by
  have h := atom0795_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0795Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0796 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0796 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0796 = ((g 2) * (g 2) * (g 19)) := by
  norm_num [atom0796, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0796_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22835762611200 : Int) atom0796) := by
  rw [SparsePolynomial.eval_scale, eval_atom0796]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 2) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0796Coded : CoefficientMerge.Poly := [(nat_lit 1219, Int.ofNat (nat_lit 1))]
theorem atom0796Coded_decode : atom0796 = SparsePolynomial.decodeCubic 24 atom0796Coded := by decide +kernel
theorem atom0796Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (22835762611200 : Int) atom0796Coded) := by
  have h := atom0796_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0796Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0797 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0797 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0797 = ((g 2) * (g 2) * (g 20)) := by
  norm_num [atom0797, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0797_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (87069318336000 : Int) atom0797) := by
  rw [SparsePolynomial.eval_scale, eval_atom0797]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 2) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0797Coded : CoefficientMerge.Poly := [(nat_lit 1220, Int.ofNat (nat_lit 1))]
theorem atom0797Coded_decode : atom0797 = SparsePolynomial.decodeCubic 24 atom0797Coded := by decide +kernel
theorem atom0797Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (87069318336000 : Int) atom0797Coded) := by
  have h := atom0797_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0797Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0798 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0798 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0798 = ((g 2) * (g 2) * (g 21)) := by
  norm_num [atom0798, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0798_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10461075609600 : Int) atom0798) := by
  rw [SparsePolynomial.eval_scale, eval_atom0798]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 2) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0798Coded : CoefficientMerge.Poly := [(nat_lit 1221, Int.ofNat (nat_lit 1))]
theorem atom0798Coded_decode : atom0798 = SparsePolynomial.decodeCubic 24 atom0798Coded := by decide +kernel
theorem atom0798Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (10461075609600 : Int) atom0798Coded) := by
  have h := atom0798_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0798Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0799 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0799 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0799 = ((g 2) * (g 2) * (g 23)) := by
  norm_num [atom0799, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0799_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22272310368000 : Int) atom0799) := by
  rw [SparsePolynomial.eval_scale, eval_atom0799]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 2) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0799Coded : CoefficientMerge.Poly := [(nat_lit 1223, Int.ofNat (nat_lit 1))]
theorem atom0799Coded_decode : atom0799 = SparsePolynomial.decodeCubic 24 atom0799Coded := by decide +kernel
theorem atom0799Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (22272310368000 : Int) atom0799Coded) := by
  have h := atom0799_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0799Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0800 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 3], Int.ofNat (nat_lit 1))]
theorem eval_atom0800 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0800 = ((g 2) * (g 3) * (g 3)) := by
  norm_num [atom0800, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0800_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (106396793395200 : Int) atom0800) := by
  rw [SparsePolynomial.eval_scale, eval_atom0800]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 2) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0800Coded : CoefficientMerge.Poly := [(nat_lit 1227, Int.ofNat (nat_lit 1))]
theorem atom0800Coded_decode : atom0800 = SparsePolynomial.decodeCubic 24 atom0800Coded := by decide +kernel
theorem atom0800Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (106396793395200 : Int) atom0800Coded) := by
  have h := atom0800_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0800Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0801 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0801 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0801 = ((g 2) * (g 3) * (g 4)) := by
  norm_num [atom0801, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0801_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (203480678016000 : Int) atom0801) := by
  rw [SparsePolynomial.eval_scale, eval_atom0801]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 2) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0801Coded : CoefficientMerge.Poly := [(nat_lit 1228, Int.ofNat (nat_lit 1))]
theorem atom0801Coded_decode : atom0801 = SparsePolynomial.decodeCubic 24 atom0801Coded := by decide +kernel
theorem atom0801Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (203480678016000 : Int) atom0801Coded) := by
  have h := atom0801_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0801Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0802 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0802 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0802 = ((g 2) * (g 3) * (g 5)) := by
  norm_num [atom0802, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0802_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (207933556723200 : Int) atom0802) := by
  rw [SparsePolynomial.eval_scale, eval_atom0802]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0802Coded : CoefficientMerge.Poly := [(nat_lit 1229, Int.ofNat (nat_lit 1))]
theorem atom0802Coded_decode : atom0802 = SparsePolynomial.decodeCubic 24 atom0802Coded := by decide +kernel
theorem atom0802Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (207933556723200 : Int) atom0802Coded) := by
  have h := atom0802_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0802Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0803 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0803 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0803 = ((g 2) * (g 3) * (g 6)) := by
  norm_num [atom0803, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0803_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (184854860467200 : Int) atom0803) := by
  rw [SparsePolynomial.eval_scale, eval_atom0803]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0803Coded : CoefficientMerge.Poly := [(nat_lit 1230, Int.ofNat (nat_lit 1))]
theorem atom0803Coded_decode : atom0803 = SparsePolynomial.decodeCubic 24 atom0803Coded := by decide +kernel
theorem atom0803Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (184854860467200 : Int) atom0803Coded) := by
  have h := atom0803_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0803Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0804 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0804 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0804 = ((g 2) * (g 3) * (g 7)) := by
  norm_num [atom0804, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0804_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (175541951692800 : Int) atom0804) := by
  rw [SparsePolynomial.eval_scale, eval_atom0804]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0804Coded : CoefficientMerge.Poly := [(nat_lit 1231, Int.ofNat (nat_lit 1))]
theorem atom0804Coded_decode : atom0804 = SparsePolynomial.decodeCubic 24 atom0804Coded := by decide +kernel
theorem atom0804Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (175541951692800 : Int) atom0804Coded) := by
  have h := atom0804_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0804Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0805 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0805 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0805 = ((g 2) * (g 3) * (g 8)) := by
  norm_num [atom0805, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0805_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (166229042918400 : Int) atom0805) := by
  rw [SparsePolynomial.eval_scale, eval_atom0805]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0805Coded : CoefficientMerge.Poly := [(nat_lit 1232, Int.ofNat (nat_lit 1))]
theorem atom0805Coded_decode : atom0805 = SparsePolynomial.decodeCubic 24 atom0805Coded := by decide +kernel
theorem atom0805Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (166229042918400 : Int) atom0805Coded) := by
  have h := atom0805_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0805Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0806 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0806 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0806 = ((g 2) * (g 3) * (g 9)) := by
  norm_num [atom0806, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0806_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (168939696236256 : Int) atom0806) := by
  rw [SparsePolynomial.eval_scale, eval_atom0806]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0806Coded : CoefficientMerge.Poly := [(nat_lit 1233, Int.ofNat (nat_lit 1))]
theorem atom0806Coded_decode : atom0806 = SparsePolynomial.decodeCubic 24 atom0806Coded := by decide +kernel
theorem atom0806Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (168939696236256 : Int) atom0806Coded) := by
  have h := atom0806_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0806Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0807 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0807 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0807 = ((g 2) * (g 3) * (g 10)) := by
  norm_num [atom0807, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0807_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (194913781530336 : Int) atom0807) := by
  rw [SparsePolynomial.eval_scale, eval_atom0807]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0807Coded : CoefficientMerge.Poly := [(nat_lit 1234, Int.ofNat (nat_lit 1))]
theorem atom0807Coded_decode : atom0807 = SparsePolynomial.decodeCubic 24 atom0807Coded := by decide +kernel
theorem atom0807Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (194913781530336 : Int) atom0807Coded) := by
  have h := atom0807_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0807Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0808 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0808 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0808 = ((g 2) * (g 3) * (g 11)) := by
  norm_num [atom0808, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0808_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (217611012345408 : Int) atom0808) := by
  rw [SparsePolynomial.eval_scale, eval_atom0808]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0808Coded : CoefficientMerge.Poly := [(nat_lit 1235, Int.ofNat (nat_lit 1))]
theorem atom0808Coded_decode : atom0808 = SparsePolynomial.decodeCubic 24 atom0808Coded := by decide +kernel
theorem atom0808Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (217611012345408 : Int) atom0808Coded) := by
  have h := atom0808_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0808Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0809 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0809 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0809 = ((g 2) * (g 3) * (g 12)) := by
  norm_num [atom0809, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0809_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (264142068018048 : Int) atom0809) := by
  rw [SparsePolynomial.eval_scale, eval_atom0809]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 3) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0809Coded : CoefficientMerge.Poly := [(nat_lit 1236, Int.ofNat (nat_lit 1))]
theorem atom0809Coded_decode : atom0809 = SparsePolynomial.decodeCubic 24 atom0809Coded := by decide +kernel
theorem atom0809Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (264142068018048 : Int) atom0809Coded) := by
  have h := atom0809_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0809Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0810 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0810 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0810 = ((g 2) * (g 3) * (g 13)) := by
  norm_num [atom0810, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0810_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (237506898182400 : Int) atom0810) := by
  rw [SparsePolynomial.eval_scale, eval_atom0810]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 3) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0810Coded : CoefficientMerge.Poly := [(nat_lit 1237, Int.ofNat (nat_lit 1))]
theorem atom0810Coded_decode : atom0810 = SparsePolynomial.decodeCubic 24 atom0810Coded := by decide +kernel
theorem atom0810Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (237506898182400 : Int) atom0810Coded) := by
  have h := atom0810_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0810Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0811 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0811 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0811 = ((g 2) * (g 3) * (g 14)) := by
  norm_num [atom0811, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0811_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (203523202713600 : Int) atom0811) := by
  rw [SparsePolynomial.eval_scale, eval_atom0811]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 3) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0811Coded : CoefficientMerge.Poly := [(nat_lit 1238, Int.ofNat (nat_lit 1))]
theorem atom0811Coded_decode : atom0811 = SparsePolynomial.decodeCubic 24 atom0811Coded := by decide +kernel
theorem atom0811Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (203523202713600 : Int) atom0811Coded) := by
  have h := atom0811_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0811Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0812 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0812 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0812 = ((g 2) * (g 3) * (g 15)) := by
  norm_num [atom0812, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0812_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (199113520435200 : Int) atom0812) := by
  rw [SparsePolynomial.eval_scale, eval_atom0812]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 3) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0812Coded : CoefficientMerge.Poly := [(nat_lit 1239, Int.ofNat (nat_lit 1))]
theorem atom0812Coded_decode : atom0812 = SparsePolynomial.decodeCubic 24 atom0812Coded := by decide +kernel
theorem atom0812Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (199113520435200 : Int) atom0812Coded) := by
  have h := atom0812_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0812Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0813 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0813 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0813 = ((g 2) * (g 3) * (g 16)) := by
  norm_num [atom0813, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0813_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (171058817664000 : Int) atom0813) := by
  rw [SparsePolynomial.eval_scale, eval_atom0813]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 3) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0813Coded : CoefficientMerge.Poly := [(nat_lit 1240, Int.ofNat (nat_lit 1))]
theorem atom0813Coded_decode : atom0813 = SparsePolynomial.decodeCubic 24 atom0813Coded := by decide +kernel
theorem atom0813Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (171058817664000 : Int) atom0813Coded) := by
  have h := atom0813_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0813Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0814 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0814 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0814 = ((g 2) * (g 3) * (g 17)) := by
  norm_num [atom0814, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0814_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (162869591808000 : Int) atom0814) := by
  rw [SparsePolynomial.eval_scale, eval_atom0814]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 3) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0814Coded : CoefficientMerge.Poly := [(nat_lit 1241, Int.ofNat (nat_lit 1))]
theorem atom0814Coded_decode : atom0814 = SparsePolynomial.decodeCubic 24 atom0814Coded := by decide +kernel
theorem atom0814Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (162869591808000 : Int) atom0814Coded) := by
  have h := atom0814_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0814Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0815 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0815 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0815 = ((g 2) * (g 3) * (g 18)) := by
  norm_num [atom0815, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0815_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (213941753625600 : Int) atom0815) := by
  rw [SparsePolynomial.eval_scale, eval_atom0815]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 3) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0815Coded : CoefficientMerge.Poly := [(nat_lit 1242, Int.ofNat (nat_lit 1))]
theorem atom0815Coded_decode : atom0815 = SparsePolynomial.decodeCubic 24 atom0815Coded := by decide +kernel
theorem atom0815Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (213941753625600 : Int) atom0815Coded) := by
  have h := atom0815_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0815Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0816 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0816 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0816 = ((g 2) * (g 3) * (g 19)) := by
  norm_num [atom0816, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0816_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (91683248025600 : Int) atom0816) := by
  rw [SparsePolynomial.eval_scale, eval_atom0816]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 3) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0816Coded : CoefficientMerge.Poly := [(nat_lit 1243, Int.ofNat (nat_lit 1))]
theorem atom0816Coded_decode : atom0816 = SparsePolynomial.decodeCubic 24 atom0816Coded := by decide +kernel
theorem atom0816Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (91683248025600 : Int) atom0816Coded) := by
  have h := atom0816_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0816Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0817 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0817 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0817 = ((g 2) * (g 3) * (g 20)) := by
  norm_num [atom0817, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0817_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (195315936076800 : Int) atom0817) := by
  rw [SparsePolynomial.eval_scale, eval_atom0817]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 3) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0817Coded : CoefficientMerge.Poly := [(nat_lit 1244, Int.ofNat (nat_lit 1))]
theorem atom0817Coded_decode : atom0817 = SparsePolynomial.decodeCubic 24 atom0817Coded := by decide +kernel
theorem atom0817Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (195315936076800 : Int) atom0817Coded) := by
  have h := atom0817_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0817Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0818 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0818 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0818 = ((g 2) * (g 3) * (g 21)) := by
  norm_num [atom0818, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0818_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (85474642176000 : Int) atom0818) := by
  rw [SparsePolynomial.eval_scale, eval_atom0818]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 3) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0818Coded : CoefficientMerge.Poly := [(nat_lit 1245, Int.ofNat (nat_lit 1))]
theorem atom0818Coded_decode : atom0818 = SparsePolynomial.decodeCubic 24 atom0818Coded := by decide +kernel
theorem atom0818Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (85474642176000 : Int) atom0818Coded) := by
  have h := atom0818_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0818Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0819 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0819 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0819 = ((g 2) * (g 3) * (g 22)) := by
  norm_num [atom0819, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0819_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (78096607142400 : Int) atom0819) := by
  rw [SparsePolynomial.eval_scale, eval_atom0819]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 3) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0819Coded : CoefficientMerge.Poly := [(nat_lit 1246, Int.ofNat (nat_lit 1))]
theorem atom0819Coded_decode : atom0819 = SparsePolynomial.decodeCubic 24 atom0819Coded := by decide +kernel
theorem atom0819Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (78096607142400 : Int) atom0819Coded) := by
  have h := atom0819_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0819Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0820 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0820 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0820 = ((g 2) * (g 3) * (g 23)) := by
  norm_num [atom0820, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0820_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (103451958086400 : Int) atom0820) := by
  rw [SparsePolynomial.eval_scale, eval_atom0820]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 3) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0820Coded : CoefficientMerge.Poly := [(nat_lit 1247, Int.ofNat (nat_lit 1))]
theorem atom0820Coded_decode : atom0820 = SparsePolynomial.decodeCubic 24 atom0820Coded := by decide +kernel
theorem atom0820Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (103451958086400 : Int) atom0820Coded) := by
  have h := atom0820_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0820Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0821 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0821 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0821 = ((g 2) * (g 4) * (g 4)) := by
  norm_num [atom0821, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0821_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (105130072857600 : Int) atom0821) := by
  rw [SparsePolynomial.eval_scale, eval_atom0821]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 2) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0821Coded : CoefficientMerge.Poly := [(nat_lit 1252, Int.ofNat (nat_lit 1))]
theorem atom0821Coded_decode : atom0821 = SparsePolynomial.decodeCubic 24 atom0821Coded := by decide +kernel
theorem atom0821Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (105130072857600 : Int) atom0821Coded) := by
  have h := atom0821_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0821Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0822 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0822 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0822 = ((g 2) * (g 4) * (g 5)) := by
  norm_num [atom0822, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0822_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (191950417603296 : Int) atom0822) := by
  rw [SparsePolynomial.eval_scale, eval_atom0822]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0822Coded : CoefficientMerge.Poly := [(nat_lit 1253, Int.ofNat (nat_lit 1))]
theorem atom0822Coded_decode : atom0822 = SparsePolynomial.decodeCubic 24 atom0822Coded := by decide +kernel
theorem atom0822Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (191950417603296 : Int) atom0822Coded) := by
  have h := atom0822_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0822Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0823 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0823 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0823 = ((g 2) * (g 4) * (g 6)) := by
  norm_num [atom0823, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0823_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (163167264691200 : Int) atom0823) := by
  rw [SparsePolynomial.eval_scale, eval_atom0823]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0823Coded : CoefficientMerge.Poly := [(nat_lit 1254, Int.ofNat (nat_lit 1))]
theorem atom0823Coded_decode : atom0823 = SparsePolynomial.decodeCubic 24 atom0823Coded := by decide +kernel
theorem atom0823Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (163167264691200 : Int) atom0823Coded) := by
  have h := atom0823_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0823Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0824 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0824 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0824 = ((g 2) * (g 4) * (g 7)) := by
  norm_num [atom0824, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0824_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (156916134144000 : Int) atom0824) := by
  rw [SparsePolynomial.eval_scale, eval_atom0824]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0824Coded : CoefficientMerge.Poly := [(nat_lit 1255, Int.ofNat (nat_lit 1))]
theorem atom0824Coded_decode : atom0824 = SparsePolynomial.decodeCubic 24 atom0824Coded := by decide +kernel
theorem atom0824Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (156916134144000 : Int) atom0824Coded) := by
  have h := atom0824_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0824Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0825 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0825 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0825 = ((g 2) * (g 4) * (g 8)) := by
  norm_num [atom0825, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0825_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (150665003596800 : Int) atom0825) := by
  rw [SparsePolynomial.eval_scale, eval_atom0825]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0825Coded : CoefficientMerge.Poly := [(nat_lit 1256, Int.ofNat (nat_lit 1))]
theorem atom0825Coded_decode : atom0825 = SparsePolynomial.decodeCubic 24 atom0825Coded := by decide +kernel
theorem atom0825Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (150665003596800 : Int) atom0825Coded) := by
  have h := atom0825_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0825Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0826 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0826 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0826 = ((g 2) * (g 4) * (g 9)) := by
  norm_num [atom0826, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0826_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (156437435141856 : Int) atom0826) := by
  rw [SparsePolynomial.eval_scale, eval_atom0826]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0826Coded : CoefficientMerge.Poly := [(nat_lit 1257, Int.ofNat (nat_lit 1))]
theorem atom0826Coded_decode : atom0826 = SparsePolynomial.decodeCubic 24 atom0826Coded := by decide +kernel
theorem atom0826Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (156437435141856 : Int) atom0826Coded) := by
  have h := atom0826_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0826Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0827 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0827 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0827 = ((g 2) * (g 4) * (g 10)) := by
  norm_num [atom0827, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0827_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (185473298663136 : Int) atom0827) := by
  rw [SparsePolynomial.eval_scale, eval_atom0827]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0827Coded : CoefficientMerge.Poly := [(nat_lit 1258, Int.ofNat (nat_lit 1))]
theorem atom0827Coded_decode : atom0827 = SparsePolynomial.decodeCubic 24 atom0827Coded := by decide +kernel
theorem atom0827Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (185473298663136 : Int) atom0827Coded) := by
  have h := atom0827_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0827Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0828 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0828 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0828 = ((g 2) * (g 4) * (g 11)) := by
  norm_num [atom0828, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0828_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (211232307705408 : Int) atom0828) := by
  rw [SparsePolynomial.eval_scale, eval_atom0828]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0828Coded : CoefficientMerge.Poly := [(nat_lit 1259, Int.ofNat (nat_lit 1))]
theorem atom0828Coded_decode : atom0828 = SparsePolynomial.decodeCubic 24 atom0828Coded := by decide +kernel
theorem atom0828Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (211232307705408 : Int) atom0828Coded) := by
  have h := atom0828_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0828Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0829 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0829 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0829 = ((g 2) * (g 4) * (g 12)) := by
  norm_num [atom0829, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0829_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (260825141605248 : Int) atom0829) := by
  rw [SparsePolynomial.eval_scale, eval_atom0829]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0829Coded : CoefficientMerge.Poly := [(nat_lit 1260, Int.ofNat (nat_lit 1))]
theorem atom0829Coded_decode : atom0829 = SparsePolynomial.decodeCubic 24 atom0829Coded := by decide +kernel
theorem atom0829Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (260825141605248 : Int) atom0829Coded) := by
  have h := atom0829_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0829Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0830 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0830 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0830 = ((g 2) * (g 4) * (g 13)) := by
  norm_num [atom0830, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0830_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (237251749996800 : Int) atom0830) := by
  rw [SparsePolynomial.eval_scale, eval_atom0830]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 4) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0830Coded : CoefficientMerge.Poly := [(nat_lit 1261, Int.ofNat (nat_lit 1))]
theorem atom0830Coded_decode : atom0830 = SparsePolynomial.decodeCubic 24 atom0830Coded := by decide +kernel
theorem atom0830Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (237251749996800 : Int) atom0830Coded) := by
  have h := atom0830_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0830Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0831 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0831 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0831 = ((g 2) * (g 4) * (g 14)) := by
  norm_num [atom0831, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0831_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (206329832755200 : Int) atom0831) := by
  rw [SparsePolynomial.eval_scale, eval_atom0831]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0831Coded : CoefficientMerge.Poly := [(nat_lit 1262, Int.ofNat (nat_lit 1))]
theorem atom0831Coded_decode : atom0831 = SparsePolynomial.decodeCubic 24 atom0831Coded := by decide +kernel
theorem atom0831Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (206329832755200 : Int) atom0831Coded) := by
  have h := atom0831_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0831Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0832 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0832 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0832 = ((g 2) * (g 4) * (g 15)) := by
  norm_num [atom0832, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0832_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (204981928704000 : Int) atom0832) := by
  rw [SparsePolynomial.eval_scale, eval_atom0832]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 4) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0832Coded : CoefficientMerge.Poly := [(nat_lit 1263, Int.ofNat (nat_lit 1))]
theorem atom0832Coded_decode : atom0832 = SparsePolynomial.decodeCubic 24 atom0832Coded := by decide +kernel
theorem atom0832Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (204981928704000 : Int) atom0832Coded) := by
  have h := atom0832_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0832Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0833 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0833 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0833 = ((g 2) * (g 4) * (g 16)) := by
  norm_num [atom0833, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0833_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (179989004160000 : Int) atom0833) := by
  rw [SparsePolynomial.eval_scale, eval_atom0833]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 4) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0833Coded : CoefficientMerge.Poly := [(nat_lit 1264, Int.ofNat (nat_lit 1))]
theorem atom0833Coded_decode : atom0833 = SparsePolynomial.decodeCubic 24 atom0833Coded := by decide +kernel
theorem atom0833Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (179989004160000 : Int) atom0833Coded) := by
  have h := atom0833_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0833Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0834 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0834 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0834 = ((g 2) * (g 4) * (g 17)) := by
  norm_num [atom0834, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0834_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (179508990528000 : Int) atom0834) := by
  rw [SparsePolynomial.eval_scale, eval_atom0834]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 4) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0834Coded : CoefficientMerge.Poly := [(nat_lit 1265, Int.ofNat (nat_lit 1))]
theorem atom0834Coded_decode : atom0834 = SparsePolynomial.decodeCubic 24 atom0834Coded := by decide +kernel
theorem atom0834Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (179508990528000 : Int) atom0834Coded) := by
  have h := atom0834_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0834Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0835 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0835 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0835 = ((g 2) * (g 4) * (g 18)) := by
  norm_num [atom0835, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0835_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (228995496576000 : Int) atom0835) := by
  rw [SparsePolynomial.eval_scale, eval_atom0835]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 4) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0835Coded : CoefficientMerge.Poly := [(nat_lit 1266, Int.ofNat (nat_lit 1))]
theorem atom0835Coded_decode : atom0835 = SparsePolynomial.decodeCubic 24 atom0835Coded := by decide +kernel
theorem atom0835Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (228995496576000 : Int) atom0835Coded) := by
  have h := atom0835_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0835Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0836 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0836 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0836 = ((g 2) * (g 4) * (g 19)) := by
  norm_num [atom0836, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0836_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (143682657652800 : Int) atom0836) := by
  rw [SparsePolynomial.eval_scale, eval_atom0836]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 4) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0836Coded : CoefficientMerge.Poly := [(nat_lit 1267, Int.ofNat (nat_lit 1))]
theorem atom0836Coded_decode : atom0836 = SparsePolynomial.decodeCubic 24 atom0836Coded := by decide +kernel
theorem atom0836Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (143682657652800 : Int) atom0836Coded) := by
  have h := atom0836_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0836Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0837 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0837 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0837 = ((g 2) * (g 4) * (g 20)) := by
  norm_num [atom0837, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0837_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (217385529278400 : Int) atom0837) := by
  rw [SparsePolynomial.eval_scale, eval_atom0837]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 4) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0837Coded : CoefficientMerge.Poly := [(nat_lit 1268, Int.ofNat (nat_lit 1))]
theorem atom0837Coded_decode : atom0837 = SparsePolynomial.decodeCubic 24 atom0837Coded := by decide +kernel
theorem atom0837Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (217385529278400 : Int) atom0837Coded) := by
  have h := atom0837_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0837Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0838 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0838 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0838 = ((g 2) * (g 4) * (g 21)) := by
  norm_num [atom0838, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0838_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (154570429944000 : Int) atom0838) := by
  rw [SparsePolynomial.eval_scale, eval_atom0838]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 4) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0838Coded : CoefficientMerge.Poly := [(nat_lit 1269, Int.ofNat (nat_lit 1))]
theorem atom0838Coded_decode : atom0838 = SparsePolynomial.decodeCubic 24 atom0838Coded := by decide +kernel
theorem atom0838Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (154570429944000 : Int) atom0838Coded) := by
  have h := atom0838_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0838Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0839 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0839 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0839 = ((g 2) * (g 4) * (g 22)) := by
  norm_num [atom0839, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0839_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (157902497726400 : Int) atom0839) := by
  rw [SparsePolynomial.eval_scale, eval_atom0839]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 4) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0839Coded : CoefficientMerge.Poly := [(nat_lit 1270, Int.ofNat (nat_lit 1))]
theorem atom0839Coded_decode : atom0839 = SparsePolynomial.decodeCubic 24 atom0839Coded := by decide +kernel
theorem atom0839Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (157902497726400 : Int) atom0839Coded) := by
  have h := atom0839_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0839Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0840 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0840 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0840 = ((g 2) * (g 4) * (g 23)) := by
  norm_num [atom0840, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0840_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (193967951486400 : Int) atom0840) := by
  rw [SparsePolynomial.eval_scale, eval_atom0840]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 4) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0840Coded : CoefficientMerge.Poly := [(nat_lit 1271, Int.ofNat (nat_lit 1))]
theorem atom0840Coded_decode : atom0840 = SparsePolynomial.decodeCubic 24 atom0840Coded := by decide +kernel
theorem atom0840Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (193967951486400 : Int) atom0840Coded) := by
  have h := atom0840_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0840Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0841 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0841 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0841 = ((g 2) * (g 5) * (g 5)) := by
  norm_num [atom0841, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0841_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (121046551718400 : Int) atom0841) := by
  rw [SparsePolynomial.eval_scale, eval_atom0841]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0841Coded : CoefficientMerge.Poly := [(nat_lit 1277, Int.ofNat (nat_lit 1))]
theorem atom0841Coded_decode : atom0841 = SparsePolynomial.decodeCubic 24 atom0841Coded := by decide +kernel
theorem atom0841Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (121046551718400 : Int) atom0841Coded) := by
  have h := atom0841_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0841Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0842 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0842 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0842 = ((g 2) * (g 5) * (g 6)) := by
  norm_num [atom0842, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0842_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (207642031017696 : Int) atom0842) := by
  rw [SparsePolynomial.eval_scale, eval_atom0842]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0842Coded : CoefficientMerge.Poly := [(nat_lit 1278, Int.ofNat (nat_lit 1))]
theorem atom0842Coded_decode : atom0842 = SparsePolynomial.decodeCubic 24 atom0842Coded := by decide +kernel
theorem atom0842Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (207642031017696 : Int) atom0842Coded) := by
  have h := atom0842_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0842Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0843 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0843 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0843 = ((g 2) * (g 5) * (g 7)) := by
  norm_num [atom0843, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0843_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (182965893993696 : Int) atom0843) := by
  rw [SparsePolynomial.eval_scale, eval_atom0843]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0843Coded : CoefficientMerge.Poly := [(nat_lit 1279, Int.ofNat (nat_lit 1))]
theorem atom0843Coded_decode : atom0843 = SparsePolynomial.decodeCubic 24 atom0843Coded := by decide +kernel
theorem atom0843Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (182965893993696 : Int) atom0843Coded) := by
  have h := atom0843_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0843Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0844 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0844 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0844 = ((g 2) * (g 5) * (g 8)) := by
  norm_num [atom0844, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0844_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (182850052502304 : Int) atom0844) := by
  rw [SparsePolynomial.eval_scale, eval_atom0844]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0844Coded : CoefficientMerge.Poly := [(nat_lit 1280, Int.ofNat (nat_lit 1))]
theorem atom0844Coded_decode : atom0844 = SparsePolynomial.decodeCubic 24 atom0844Coded := by decide +kernel
theorem atom0844Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (182850052502304 : Int) atom0844Coded) := by
  have h := atom0844_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0844Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0845 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0845 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0845 = ((g 2) * (g 5) * (g 9)) := by
  norm_num [atom0845, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0845_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (188053864294032 : Int) atom0845) := by
  rw [SparsePolynomial.eval_scale, eval_atom0845]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0845Coded : CoefficientMerge.Poly := [(nat_lit 1281, Int.ofNat (nat_lit 1))]
theorem atom0845Coded_decode : atom0845 = SparsePolynomial.decodeCubic 24 atom0845Coded := by decide +kernel
theorem atom0845Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (188053864294032 : Int) atom0845Coded) := by
  have h := atom0845_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0845Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0846 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0846 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0846 = ((g 2) * (g 5) * (g 10)) := by
  norm_num [atom0846, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0846_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (199971722137968 : Int) atom0846) := by
  rw [SparsePolynomial.eval_scale, eval_atom0846]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0846Coded : CoefficientMerge.Poly := [(nat_lit 1282, Int.ofNat (nat_lit 1))]
theorem atom0846Coded_decode : atom0846 = SparsePolynomial.decodeCubic 24 atom0846Coded := by decide +kernel
theorem atom0846Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (199971722137968 : Int) atom0846Coded) := by
  have h := atom0846_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0846Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0847 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0847 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0847 = ((g 2) * (g 5) * (g 11)) := by
  norm_num [atom0847, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0847_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (218619390547008 : Int) atom0847) := by
  rw [SparsePolynomial.eval_scale, eval_atom0847]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0847Coded : CoefficientMerge.Poly := [(nat_lit 1283, Int.ofNat (nat_lit 1))]
theorem atom0847Coded_decode : atom0847 = SparsePolynomial.decodeCubic 24 atom0847Coded := by decide +kernel
theorem atom0847Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (218619390547008 : Int) atom0847Coded) := by
  have h := atom0847_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0847Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0848 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0848 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0848 = ((g 2) * (g 5) * (g 12)) := by
  norm_num [atom0848, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0848_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (271274002674048 : Int) atom0848) := by
  rw [SparsePolynomial.eval_scale, eval_atom0848]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0848Coded : CoefficientMerge.Poly := [(nat_lit 1284, Int.ofNat (nat_lit 1))]
theorem atom0848Coded_decode : atom0848 = SparsePolynomial.decodeCubic 24 atom0848Coded := by decide +kernel
theorem atom0848Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (271274002674048 : Int) atom0848Coded) := by
  have h := atom0848_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0848Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block012 : CoefficientMerge.Poly := [(nat_lit 1076, Int.ofNat (nat_lit 279004540953600)), (nat_lit 1077, Int.ofNat (nat_lit 444567363609600)), (nat_lit 1078, Int.ofNat (nat_lit 345540443942400)), (nat_lit 1079, Int.ofNat (nat_lit 358952744304000)), (nat_lit 1101, Int.ofNat (nat_lit 158851007884800)), (nat_lit 1102, Int.ofNat (nat_lit 218610772128000)), (nat_lit 1103, Int.ofNat (nat_lit 225802600531200)), (nat_lit 1126, Int.ofNat (nat_lit 36833126568000)), (nat_lit 1127, Int.ofNat (nat_lit 80799180537600)), (nat_lit 1151, Int.ofNat (nat_lit 24047716492800)), (nat_lit 1202, Int.ofNat (nat_lit 42673534041600)), (nat_lit 1203, Int.ofNat (nat_lit 121833258624000)), (nat_lit 1204, Int.ofNat (nat_lit 115645915123200)), (nat_lit 1205, Int.ofNat (nat_lit 116341465363200)), (nat_lit 1206, Int.ofNat (nat_lit 103271228121600)), (nat_lit 1207, Int.ofNat (nat_lit 97083884620800)), (nat_lit 1208, Int.ofNat (nat_lit 90896541120000)), (nat_lit 1209, Int.ofNat (nat_lit 90720978665328)), (nat_lit 1210, Int.ofNat (nat_lit 102177132198768)), (nat_lit 1211, Int.ofNat (nat_lit 111994858492704)), (nat_lit 1212, Int.ofNat (nat_lit 133729497215424)), (nat_lit 1213, Int.ofNat (nat_lit 118881023184000)), (nat_lit 1214, Int.ofNat (nat_lit 100358286336000)), (nat_lit 1215, Int.ofNat (nat_lit 96622556083200)), (nat_lit 1216, Int.ofNat (nat_lit 81064315584000)), (nat_lit 1217, Int.ofNat (nat_lit 75438813542400)), (nat_lit 1218, Int.ofNat (nat_lit 99444005337600)), (nat_lit 1219, Int.ofNat (nat_lit 22835762611200)), (nat_lit 1220, Int.ofNat (nat_lit 87069318336000)), (nat_lit 1221, Int.ofNat (nat_lit 10461075609600)), (nat_lit 1223, Int.ofNat (nat_lit 22272310368000)), (nat_lit 1227, Int.ofNat (nat_lit 106396793395200)), (nat_lit 1228, Int.ofNat (nat_lit 203480678016000)), (nat_lit 1229, Int.ofNat (nat_lit 207933556723200)), (nat_lit 1230, Int.ofNat (nat_lit 184854860467200)), (nat_lit 1231, Int.ofNat (nat_lit 175541951692800)), (nat_lit 1232, Int.ofNat (nat_lit 166229042918400)), (nat_lit 1233, Int.ofNat (nat_lit 168939696236256)), (nat_lit 1234, Int.ofNat (nat_lit 194913781530336)), (nat_lit 1235, Int.ofNat (nat_lit 217611012345408)), (nat_lit 1236, Int.ofNat (nat_lit 264142068018048)), (nat_lit 1237, Int.ofNat (nat_lit 237506898182400)), (nat_lit 1238, Int.ofNat (nat_lit 203523202713600)), (nat_lit 1239, Int.ofNat (nat_lit 199113520435200)), (nat_lit 1240, Int.ofNat (nat_lit 171058817664000)), (nat_lit 1241, Int.ofNat (nat_lit 162869591808000)), (nat_lit 1242, Int.ofNat (nat_lit 213941753625600)), (nat_lit 1243, Int.ofNat (nat_lit 91683248025600)), (nat_lit 1244, Int.ofNat (nat_lit 195315936076800)), (nat_lit 1245, Int.ofNat (nat_lit 85474642176000)), (nat_lit 1246, Int.ofNat (nat_lit 78096607142400)), (nat_lit 1247, Int.ofNat (nat_lit 103451958086400)), (nat_lit 1252, Int.ofNat (nat_lit 105130072857600)), (nat_lit 1253, Int.ofNat (nat_lit 191950417603296)), (nat_lit 1254, Int.ofNat (nat_lit 163167264691200)), (nat_lit 1255, Int.ofNat (nat_lit 156916134144000)), (nat_lit 1256, Int.ofNat (nat_lit 150665003596800)), (nat_lit 1257, Int.ofNat (nat_lit 156437435141856)), (nat_lit 1258, Int.ofNat (nat_lit 185473298663136)), (nat_lit 1259, Int.ofNat (nat_lit 211232307705408)), (nat_lit 1260, Int.ofNat (nat_lit 260825141605248)), (nat_lit 1261, Int.ofNat (nat_lit 237251749996800)), (nat_lit 1262, Int.ofNat (nat_lit 206329832755200)), (nat_lit 1263, Int.ofNat (nat_lit 204981928704000)), (nat_lit 1264, Int.ofNat (nat_lit 179989004160000)), (nat_lit 1265, Int.ofNat (nat_lit 179508990528000)), (nat_lit 1266, Int.ofNat (nat_lit 228995496576000)), (nat_lit 1267, Int.ofNat (nat_lit 143682657652800)), (nat_lit 1268, Int.ofNat (nat_lit 217385529278400)), (nat_lit 1269, Int.ofNat (nat_lit 154570429944000)), (nat_lit 1270, Int.ofNat (nat_lit 157902497726400)), (nat_lit 1271, Int.ofNat (nat_lit 193967951486400)), (nat_lit 1277, Int.ofNat (nat_lit 121046551718400)), (nat_lit 1278, Int.ofNat (nat_lit 207642031017696)), (nat_lit 1279, Int.ofNat (nat_lit 182965893993696)), (nat_lit 1280, Int.ofNat (nat_lit 182850052502304)), (nat_lit 1281, Int.ofNat (nat_lit 188053864294032)), (nat_lit 1282, Int.ofNat (nat_lit 199971722137968)), (nat_lit 1283, Int.ofNat (nat_lit 218619390547008)), (nat_lit 1284, Int.ofNat (nat_lit 271274002674048))]
theorem block012_data : block012 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (279004540953600 : Int) atom0769Coded) (CoefficientMerge.scale (444567363609600 : Int) atom0770Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (345540443942400 : Int) atom0771Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (358952744304000 : Int) atom0772Coded) (CoefficientMerge.scale (158851007884800 : Int) atom0773Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (218610772128000 : Int) atom0774Coded) (CoefficientMerge.scale (225802600531200 : Int) atom0775Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36833126568000 : Int) atom0776Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (80799180537600 : Int) atom0777Coded) (CoefficientMerge.scale (24047716492800 : Int) atom0778Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (42673534041600 : Int) atom0779Coded) (CoefficientMerge.scale (121833258624000 : Int) atom0780Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (115645915123200 : Int) atom0781Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (116341465363200 : Int) atom0782Coded) (CoefficientMerge.scale (103271228121600 : Int) atom0783Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (97083884620800 : Int) atom0784Coded) (CoefficientMerge.scale (90896541120000 : Int) atom0785Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (90720978665328 : Int) atom0786Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102177132198768 : Int) atom0787Coded) (CoefficientMerge.scale (111994858492704 : Int) atom0788Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (133729497215424 : Int) atom0789Coded) (CoefficientMerge.scale (118881023184000 : Int) atom0790Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (100358286336000 : Int) atom0791Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (96622556083200 : Int) atom0792Coded) (CoefficientMerge.scale (81064315584000 : Int) atom0793Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (75438813542400 : Int) atom0794Coded) (CoefficientMerge.scale (99444005337600 : Int) atom0795Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22835762611200 : Int) atom0796Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (87069318336000 : Int) atom0797Coded) (CoefficientMerge.scale (10461075609600 : Int) atom0798Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22272310368000 : Int) atom0799Coded) (CoefficientMerge.scale (106396793395200 : Int) atom0800Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (203480678016000 : Int) atom0801Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207933556723200 : Int) atom0802Coded) (CoefficientMerge.scale (184854860467200 : Int) atom0803Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (175541951692800 : Int) atom0804Coded) (CoefficientMerge.scale (166229042918400 : Int) atom0805Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (168939696236256 : Int) atom0806Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (194913781530336 : Int) atom0807Coded) (CoefficientMerge.scale (217611012345408 : Int) atom0808Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (264142068018048 : Int) atom0809Coded) (CoefficientMerge.scale (237506898182400 : Int) atom0810Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (203523202713600 : Int) atom0811Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (199113520435200 : Int) atom0812Coded) (CoefficientMerge.scale (171058817664000 : Int) atom0813Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (162869591808000 : Int) atom0814Coded) (CoefficientMerge.scale (213941753625600 : Int) atom0815Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (91683248025600 : Int) atom0816Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (195315936076800 : Int) atom0817Coded) (CoefficientMerge.scale (85474642176000 : Int) atom0818Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (78096607142400 : Int) atom0819Coded) (CoefficientMerge.scale (103451958086400 : Int) atom0820Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (105130072857600 : Int) atom0821Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (191950417603296 : Int) atom0822Coded) (CoefficientMerge.scale (163167264691200 : Int) atom0823Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (156916134144000 : Int) atom0824Coded) (CoefficientMerge.scale (150665003596800 : Int) atom0825Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (156437435141856 : Int) atom0826Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (185473298663136 : Int) atom0827Coded) (CoefficientMerge.scale (211232307705408 : Int) atom0828Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (260825141605248 : Int) atom0829Coded) (CoefficientMerge.scale (237251749996800 : Int) atom0830Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (206329832755200 : Int) atom0831Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (204981928704000 : Int) atom0832Coded) (CoefficientMerge.scale (179989004160000 : Int) atom0833Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (179508990528000 : Int) atom0834Coded) (CoefficientMerge.scale (228995496576000 : Int) atom0835Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (143682657652800 : Int) atom0836Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (217385529278400 : Int) atom0837Coded) (CoefficientMerge.scale (154570429944000 : Int) atom0838Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (157902497726400 : Int) atom0839Coded) (CoefficientMerge.scale (193967951486400 : Int) atom0840Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (121046551718400 : Int) atom0841Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207642031017696 : Int) atom0842Coded) (CoefficientMerge.scale (182965893993696 : Int) atom0843Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (182850052502304 : Int) atom0844Coded) (CoefficientMerge.scale (188053864294032 : Int) atom0845Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (199971722137968 : Int) atom0846Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (218619390547008 : Int) atom0847Coded) (CoefficientMerge.scale (271274002674048 : Int) atom0848Coded)))))))) := by decide +kernel
theorem block012_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block012 := by
  rw [block012_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0769Coded_nonneg g hg hA hB) (atom0770Coded_nonneg g hg hA hB)) (add_nonneg (atom0771Coded_nonneg g hg hA hB) (add_nonneg (atom0772Coded_nonneg g hg hA hB) (atom0773Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0774Coded_nonneg g hg hA hB) (atom0775Coded_nonneg g hg hA hB)) (add_nonneg (atom0776Coded_nonneg g hg hA hB) (add_nonneg (atom0777Coded_nonneg g hg hA hB) (atom0778Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0779Coded_nonneg g hg hA hB) (atom0780Coded_nonneg g hg hA hB)) (add_nonneg (atom0781Coded_nonneg g hg hA hB) (add_nonneg (atom0782Coded_nonneg g hg hA hB) (atom0783Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0784Coded_nonneg g hg hA hB) (atom0785Coded_nonneg g hg hA hB)) (add_nonneg (atom0786Coded_nonneg g hg hA hB) (add_nonneg (atom0787Coded_nonneg g hg hA hB) (atom0788Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0789Coded_nonneg g hg hA hB) (atom0790Coded_nonneg g hg hA hB)) (add_nonneg (atom0791Coded_nonneg g hg hA hB) (add_nonneg (atom0792Coded_nonneg g hg hA hB) (atom0793Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0794Coded_nonneg g hg hA hB) (atom0795Coded_nonneg g hg hA hB)) (add_nonneg (atom0796Coded_nonneg g hg hA hB) (add_nonneg (atom0797Coded_nonneg g hg hA hB) (atom0798Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0799Coded_nonneg g hg hA hB) (atom0800Coded_nonneg g hg hA hB)) (add_nonneg (atom0801Coded_nonneg g hg hA hB) (add_nonneg (atom0802Coded_nonneg g hg hA hB) (atom0803Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0804Coded_nonneg g hg hA hB) (atom0805Coded_nonneg g hg hA hB)) (add_nonneg (atom0806Coded_nonneg g hg hA hB) (add_nonneg (atom0807Coded_nonneg g hg hA hB) (atom0808Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0809Coded_nonneg g hg hA hB) (atom0810Coded_nonneg g hg hA hB)) (add_nonneg (atom0811Coded_nonneg g hg hA hB) (add_nonneg (atom0812Coded_nonneg g hg hA hB) (atom0813Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0814Coded_nonneg g hg hA hB) (atom0815Coded_nonneg g hg hA hB)) (add_nonneg (atom0816Coded_nonneg g hg hA hB) (add_nonneg (atom0817Coded_nonneg g hg hA hB) (atom0818Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0819Coded_nonneg g hg hA hB) (atom0820Coded_nonneg g hg hA hB)) (add_nonneg (atom0821Coded_nonneg g hg hA hB) (add_nonneg (atom0822Coded_nonneg g hg hA hB) (atom0823Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0824Coded_nonneg g hg hA hB) (atom0825Coded_nonneg g hg hA hB)) (add_nonneg (atom0826Coded_nonneg g hg hA hB) (add_nonneg (atom0827Coded_nonneg g hg hA hB) (atom0828Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0829Coded_nonneg g hg hA hB) (atom0830Coded_nonneg g hg hA hB)) (add_nonneg (atom0831Coded_nonneg g hg hA hB) (add_nonneg (atom0832Coded_nonneg g hg hA hB) (atom0833Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0834Coded_nonneg g hg hA hB) (atom0835Coded_nonneg g hg hA hB)) (add_nonneg (atom0836Coded_nonneg g hg hA hB) (add_nonneg (atom0837Coded_nonneg g hg hA hB) (atom0838Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0839Coded_nonneg g hg hA hB) (atom0840Coded_nonneg g hg hA hB)) (add_nonneg (atom0841Coded_nonneg g hg hA hB) (add_nonneg (atom0842Coded_nonneg g hg hA hB) (atom0843Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0844Coded_nonneg g hg hA hB) (atom0845Coded_nonneg g hg hA hB)) (add_nonneg (atom0846Coded_nonneg g hg hA hB) (add_nonneg (atom0847Coded_nonneg g hg hA hB) (atom0848Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
