import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom0529 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 2, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0529 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0529 = ((g 1) * (g 2) * (g 5)) := by
  norm_num [atom0529, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0529_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (159710549644800 : Int) atom0529) := by
  rw [SparsePolynomial.eval_scale, eval_atom0529]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 2) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0529Coded : CoefficientMerge.Poly := [(nat_lit 629, Int.ofNat (nat_lit 1))]
theorem atom0529Coded_decode : atom0529 = SparsePolynomial.decodeCubic 24 atom0529Coded := by decide +kernel
theorem atom0529Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (159710549644800 : Int) atom0529Coded) := by
  have h := atom0529_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0529Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0530 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 2, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0530 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0530 = ((g 1) * (g 2) * (g 6)) := by
  norm_num [atom0530, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0530_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (137694970828800 : Int) atom0530) := by
  rw [SparsePolynomial.eval_scale, eval_atom0530]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 2) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0530Coded : CoefficientMerge.Poly := [(nat_lit 630, Int.ofNat (nat_lit 1))]
theorem atom0530Coded_decode : atom0530 = SparsePolynomial.decodeCubic 24 atom0530Coded := by decide +kernel
theorem atom0530Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (137694970828800 : Int) atom0530Coded) := by
  have h := atom0530_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0530Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0531 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 2, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0531 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0531 = ((g 1) * (g 2) * (g 7)) := by
  norm_num [atom0531, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0531_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (129445179494400 : Int) atom0531) := by
  rw [SparsePolynomial.eval_scale, eval_atom0531]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 2) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0531Coded : CoefficientMerge.Poly := [(nat_lit 631, Int.ofNat (nat_lit 1))]
theorem atom0531Coded_decode : atom0531 = SparsePolynomial.decodeCubic 24 atom0531Coded := by decide +kernel
theorem atom0531Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (129445179494400 : Int) atom0531Coded) := by
  have h := atom0531_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0531Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0532 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 2, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0532 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0532 = ((g 1) * (g 2) * (g 8)) := by
  norm_num [atom0532, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0532_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (121195388160000 : Int) atom0532) := by
  rw [SparsePolynomial.eval_scale, eval_atom0532]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 2) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0532Coded : CoefficientMerge.Poly := [(nat_lit 632, Int.ofNat (nat_lit 1))]
theorem atom0532Coded_decode : atom0532 = SparsePolynomial.decodeCubic 24 atom0532Coded := by decide +kernel
theorem atom0532Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (121195388160000 : Int) atom0532Coded) := by
  have h := atom0532_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0532Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0533 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 2, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0533 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0533 = ((g 1) * (g 2) * (g 9)) := by
  norm_num [atom0533, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0533_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (124969158917856 : Int) atom0533) := by
  rw [SparsePolynomial.eval_scale, eval_atom0533]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 2) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0533Coded : CoefficientMerge.Poly := [(nat_lit 633, Int.ofNat (nat_lit 1))]
theorem atom0533Coded_decode : atom0533 = SparsePolynomial.decodeCubic 24 atom0533Coded := by decide +kernel
theorem atom0533Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (124969158917856 : Int) atom0533Coded) := by
  have h := atom0533_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0533Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0534 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 2, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0534 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0534 = ((g 1) * (g 2) * (g 10)) := by
  norm_num [atom0534, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0534_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (152006361651936 : Int) atom0534) := by
  rw [SparsePolynomial.eval_scale, eval_atom0534]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 2) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0534Coded : CoefficientMerge.Poly := [(nat_lit 634, Int.ofNat (nat_lit 1))]
theorem atom0534Coded_decode : atom0534 = SparsePolynomial.decodeCubic 24 atom0534Coded := by decide +kernel
theorem atom0534Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (152006361651936 : Int) atom0534Coded) := by
  have h := atom0534_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0534Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0535 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 2, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0535 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0535 = ((g 1) * (g 2) * (g 11)) := by
  norm_num [atom0535, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0535_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (175766709907008 : Int) atom0535) := by
  rw [SparsePolynomial.eval_scale, eval_atom0535]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 2) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0535Coded : CoefficientMerge.Poly := [(nat_lit 635, Int.ofNat (nat_lit 1))]
theorem atom0535Coded_decode : atom0535 = SparsePolynomial.decodeCubic 24 atom0535Coded := by decide +kernel
theorem atom0535Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (175766709907008 : Int) atom0535Coded) := by
  have h := atom0535_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0535Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0536 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 2, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0536 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0536 = ((g 1) * (g 2) * (g 12)) := by
  norm_num [atom0536, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0536_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (223360883019648 : Int) atom0536) := by
  rw [SparsePolynomial.eval_scale, eval_atom0536]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 2) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0536Coded : CoefficientMerge.Poly := [(nat_lit 636, Int.ofNat (nat_lit 1))]
theorem atom0536Coded_decode : atom0536 = SparsePolynomial.decodeCubic 24 atom0536Coded := by decide +kernel
theorem atom0536Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (223360883019648 : Int) atom0536Coded) := by
  have h := atom0536_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0536Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0537 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 2, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0537 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0537 = ((g 1) * (g 2) * (g 13)) := by
  norm_num [atom0537, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0537_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (197788830624000 : Int) atom0537) := by
  rw [SparsePolynomial.eval_scale, eval_atom0537]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 2) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0537Coded : CoefficientMerge.Poly := [(nat_lit 637, Int.ofNat (nat_lit 1))]
theorem atom0537Coded_decode : atom0537 = SparsePolynomial.decodeCubic 24 atom0537Coded := by decide +kernel
theorem atom0537Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (197788830624000 : Int) atom0537Coded) := by
  have h := atom0537_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0537Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0538 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 2, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0538 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0538 = ((g 1) * (g 2) * (g 14)) := by
  norm_num [atom0538, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0538_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (164868252595200 : Int) atom0538) := by
  rw [SparsePolynomial.eval_scale, eval_atom0538]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 2) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0538Coded : CoefficientMerge.Poly := [(nat_lit 638, Int.ofNat (nat_lit 1))]
theorem atom0538Coded_decode : atom0538 = SparsePolynomial.decodeCubic 24 atom0538Coded := by decide +kernel
theorem atom0538Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (164868252595200 : Int) atom0538Coded) := by
  have h := atom0538_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0538Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0539 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 2, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0539 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0539 = ((g 1) * (g 2) * (g 15)) := by
  norm_num [atom0539, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0539_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (161521687756800 : Int) atom0539) := by
  rw [SparsePolynomial.eval_scale, eval_atom0539]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 2) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0539Coded : CoefficientMerge.Poly := [(nat_lit 639, Int.ofNat (nat_lit 1))]
theorem atom0539Coded_decode : atom0539 = SparsePolynomial.decodeCubic 24 atom0539Coded := by decide +kernel
theorem atom0539Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (161521687756800 : Int) atom0539Coded) := by
  have h := atom0539_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0539Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0540 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 2, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0540 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0540 = ((g 1) * (g 2) * (g 16)) := by
  norm_num [atom0540, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0540_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (134530102425600 : Int) atom0540) := by
  rw [SparsePolynomial.eval_scale, eval_atom0540]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 2) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0540Coded : CoefficientMerge.Poly := [(nat_lit 640, Int.ofNat (nat_lit 1))]
theorem atom0540Coded_decode : atom0540 = SparsePolynomial.decodeCubic 24 atom0540Coded := by decide +kernel
theorem atom0540Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (134530102425600 : Int) atom0540Coded) := by
  have h := atom0540_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0540Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0541 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 2, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0541 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0541 = ((g 1) * (g 2) * (g 17)) := by
  norm_num [atom0541, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0541_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (127403994009600 : Int) atom0541) := by
  rw [SparsePolynomial.eval_scale, eval_atom0541]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 2) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0541Coded : CoefficientMerge.Poly := [(nat_lit 641, Int.ofNat (nat_lit 1))]
theorem atom0541Coded_decode : atom0541 = SparsePolynomial.decodeCubic 24 atom0541Coded := by decide +kernel
theorem atom0541Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (127403994009600 : Int) atom0541Coded) := by
  have h := atom0541_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0541Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0542 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 2, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0542 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0542 = ((g 1) * (g 2) * (g 18)) := by
  norm_num [atom0542, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0542_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (179539273267200 : Int) atom0542) := by
  rw [SparsePolynomial.eval_scale, eval_atom0542]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 2) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0542Coded : CoefficientMerge.Poly := [(nat_lit 642, Int.ofNat (nat_lit 1))]
theorem atom0542Coded_decode : atom0542 = SparsePolynomial.decodeCubic 24 atom0542Coded := by decide +kernel
theorem atom0542Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (179539273267200 : Int) atom0542Coded) := by
  have h := atom0542_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0542Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0543 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 2, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0543 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0543 = ((g 1) * (g 2) * (g 19)) := by
  norm_num [atom0543, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0543_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (97636705689600 : Int) atom0543) := by
  rw [SparsePolynomial.eval_scale, eval_atom0543]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 2) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0543Coded : CoefficientMerge.Poly := [(nat_lit 643, Int.ofNat (nat_lit 1))]
theorem atom0543Coded_decode : atom0543 = SparsePolynomial.decodeCubic 24 atom0543Coded := by decide +kernel
theorem atom0543Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (97636705689600 : Int) atom0543Coded) := by
  have h := atom0543_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0543Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0544 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 2, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0544 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0544 = ((g 1) * (g 2) * (g 20)) := by
  norm_num [atom0544, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0544_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (163039690598400 : Int) atom0544) := by
  rw [SparsePolynomial.eval_scale, eval_atom0544]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 2) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0544Coded : CoefficientMerge.Poly := [(nat_lit 644, Int.ofNat (nat_lit 1))]
theorem atom0544Coded_decode : atom0544 = SparsePolynomial.decodeCubic 24 atom0544Coded := by decide +kernel
theorem atom0544Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (163039690598400 : Int) atom0544Coded) := by
  have h := atom0544_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0544Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0545 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 2, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0545 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0545 = ((g 1) * (g 2) * (g 21)) := by
  norm_num [atom0545, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0545_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (88734868992000 : Int) atom0545) := by
  rw [SparsePolynomial.eval_scale, eval_atom0545]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 2) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0545Coded : CoefficientMerge.Poly := [(nat_lit 645, Int.ofNat (nat_lit 1))]
theorem atom0545Coded_decode : atom0545 = SparsePolynomial.decodeCubic 24 atom0545Coded := by decide +kernel
theorem atom0545Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (88734868992000 : Int) atom0545Coded) := by
  have h := atom0545_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0545Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0546 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 2, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0546 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0546 = ((g 1) * (g 2) * (g 22)) := by
  norm_num [atom0546, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0546_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (62854509849600 : Int) atom0546) := by
  rw [SparsePolynomial.eval_scale, eval_atom0546]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 2) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0546Coded : CoefficientMerge.Poly := [(nat_lit 646, Int.ofNat (nat_lit 1))]
theorem atom0546Coded_decode : atom0546 = SparsePolynomial.decodeCubic 24 atom0546Coded := by decide +kernel
theorem atom0546Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (62854509849600 : Int) atom0546Coded) := by
  have h := atom0546_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0546Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0547 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 2, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0547 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0547 = ((g 1) * (g 2) * (g 23)) := by
  norm_num [atom0547, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0547_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (56808566337600 : Int) atom0547) := by
  rw [SparsePolynomial.eval_scale, eval_atom0547]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 2) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0547Coded : CoefficientMerge.Poly := [(nat_lit 647, Int.ofNat (nat_lit 1))]
theorem atom0547Coded_decode : atom0547 = SparsePolynomial.decodeCubic 24 atom0547Coded := by decide +kernel
theorem atom0547Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (56808566337600 : Int) atom0547Coded) := by
  have h := atom0547_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0547Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0548 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 3], Int.ofNat (nat_lit 1))]
theorem eval_atom0548 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0548 = ((g 1) * (g 3) * (g 3)) := by
  norm_num [atom0548, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0548_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (70931195596800 : Int) atom0548) := by
  rw [SparsePolynomial.eval_scale, eval_atom0548]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 1) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0548Coded : CoefficientMerge.Poly := [(nat_lit 651, Int.ofNat (nat_lit 1))]
theorem atom0548Coded_decode : atom0548 = SparsePolynomial.decodeCubic 24 atom0548Coded := by decide +kernel
theorem atom0548Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (70931195596800 : Int) atom0548Coded) := by
  have h := atom0548_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0548Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0549 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0549 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0549 = ((g 1) * (g 3) * (g 4)) := by
  norm_num [atom0549, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0549_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (135653785344000 : Int) atom0549) := by
  rw [SparsePolynomial.eval_scale, eval_atom0549]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0549Coded : CoefficientMerge.Poly := [(nat_lit 652, Int.ofNat (nat_lit 1))]
theorem atom0549Coded_decode : atom0549 = SparsePolynomial.decodeCubic 24 atom0549Coded := by decide +kernel
theorem atom0549Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (135653785344000 : Int) atom0549Coded) := by
  have h := atom0549_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0549Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0550 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0550 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0550 = ((g 1) * (g 3) * (g 5)) := by
  norm_num [atom0550, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0550_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (143210966976000 : Int) atom0550) := by
  rw [SparsePolynomial.eval_scale, eval_atom0550]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0550Coded : CoefficientMerge.Poly := [(nat_lit 653, Int.ofNat (nat_lit 1))]
theorem atom0550Coded_decode : atom0550 = SparsePolynomial.decodeCubic 24 atom0550Coded := by decide +kernel
theorem atom0550Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (143210966976000 : Int) atom0550Coded) := by
  have h := atom0550_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0550Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0551 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0551 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0551 = ((g 1) * (g 3) * (g 6)) := by
  norm_num [atom0551, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0551_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (123236573644800 : Int) atom0551) := by
  rw [SparsePolynomial.eval_scale, eval_atom0551]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0551Coded : CoefficientMerge.Poly := [(nat_lit 654, Int.ofNat (nat_lit 1))]
theorem atom0551Coded_decode : atom0551 = SparsePolynomial.decodeCubic 24 atom0551Coded := by decide +kernel
theorem atom0551Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (123236573644800 : Int) atom0551Coded) := by
  have h := atom0551_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0551Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0552 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0552 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0552 = ((g 1) * (g 3) * (g 7)) := by
  norm_num [atom0552, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0552_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (117027967795200 : Int) atom0552) := by
  rw [SparsePolynomial.eval_scale, eval_atom0552]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0552Coded : CoefficientMerge.Poly := [(nat_lit 655, Int.ofNat (nat_lit 1))]
theorem atom0552Coded_decode : atom0552 = SparsePolynomial.decodeCubic 24 atom0552Coded := by decide +kernel
theorem atom0552Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (117027967795200 : Int) atom0552Coded) := by
  have h := atom0552_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0552Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0553 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0553 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0553 = ((g 1) * (g 3) * (g 8)) := by
  norm_num [atom0553, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0553_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (110819361945600 : Int) atom0553) := by
  rw [SparsePolynomial.eval_scale, eval_atom0553]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0553Coded : CoefficientMerge.Poly := [(nat_lit 656, Int.ofNat (nat_lit 1))]
theorem atom0553Coded_decode : atom0553 = SparsePolynomial.decodeCubic 24 atom0553Coded := by decide +kernel
theorem atom0553Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (110819361945600 : Int) atom0553Coded) := by
  have h := atom0553_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0553Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0554 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0554 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0554 = ((g 1) * (g 3) * (g 9)) := by
  norm_num [atom0554, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0554_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (116634318188256 : Int) atom0554) := by
  rw [SparsePolynomial.eval_scale, eval_atom0554]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0554Coded : CoefficientMerge.Poly := [(nat_lit 657, Int.ofNat (nat_lit 1))]
theorem atom0554Coded_decode : atom0554 = SparsePolynomial.decodeCubic 24 atom0554Coded := by decide +kernel
theorem atom0554Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (116634318188256 : Int) atom0554Coded) := by
  have h := atom0554_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0554Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0555 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0555 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0555 = ((g 1) * (g 3) * (g 10)) := by
  norm_num [atom0555, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0555_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (145712706407136 : Int) atom0555) := by
  rw [SparsePolynomial.eval_scale, eval_atom0555]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0555Coded : CoefficientMerge.Poly := [(nat_lit 658, Int.ofNat (nat_lit 1))]
theorem atom0555Coded_decode : atom0555 = SparsePolynomial.decodeCubic 24 atom0555Coded := by decide +kernel
theorem atom0555Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (145712706407136 : Int) atom0555Coded) := by
  have h := atom0555_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0555Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0556 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0556 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0556 = ((g 1) * (g 3) * (g 11)) := by
  norm_num [atom0556, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0556_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (171514240147008 : Int) atom0556) := by
  rw [SparsePolynomial.eval_scale, eval_atom0556]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0556Coded : CoefficientMerge.Poly := [(nat_lit 659, Int.ofNat (nat_lit 1))]
theorem atom0556Coded_decode : atom0556 = SparsePolynomial.decodeCubic 24 atom0556Coded := by decide +kernel
theorem atom0556Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (171514240147008 : Int) atom0556Coded) := by
  have h := atom0556_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0556Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0557 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0557 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0557 = ((g 1) * (g 3) * (g 12)) := by
  norm_num [atom0557, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0557_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (221149598744448 : Int) atom0557) := by
  rw [SparsePolynomial.eval_scale, eval_atom0557]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 3) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0557Coded : CoefficientMerge.Poly := [(nat_lit 660, Int.ofNat (nat_lit 1))]
theorem atom0557Coded_decode : atom0557 = SparsePolynomial.decodeCubic 24 atom0557Coded := by decide +kernel
theorem atom0557Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (221149598744448 : Int) atom0557Coded) := by
  have h := atom0557_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0557Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0558 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0558 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0558 = ((g 1) * (g 3) * (g 13)) := by
  norm_num [atom0558, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0558_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (197618731833600 : Int) atom0558) := by
  rw [SparsePolynomial.eval_scale, eval_atom0558]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 3) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0558Coded : CoefficientMerge.Poly := [(nat_lit 661, Int.ofNat (nat_lit 1))]
theorem atom0558Coded_decode : atom0558 = SparsePolynomial.decodeCubic 24 atom0558Coded := by decide +kernel
theorem atom0558Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (197618731833600 : Int) atom0558Coded) := by
  have h := atom0558_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0558Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0559 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0559 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0559 = ((g 1) * (g 3) * (g 14)) := by
  norm_num [atom0559, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0559_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (166739339289600 : Int) atom0559) := by
  rw [SparsePolynomial.eval_scale, eval_atom0559]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 3) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0559Coded : CoefficientMerge.Poly := [(nat_lit 662, Int.ofNat (nat_lit 1))]
theorem atom0559Coded_decode : atom0559 = SparsePolynomial.decodeCubic 24 atom0559Coded := by decide +kernel
theorem atom0559Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (166739339289600 : Int) atom0559Coded) := by
  have h := atom0559_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0559Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0560 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0560 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0560 = ((g 1) * (g 3) * (g 15)) := by
  norm_num [atom0560, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0560_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (165433959936000 : Int) atom0560) := by
  rw [SparsePolynomial.eval_scale, eval_atom0560]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 3) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0560Coded : CoefficientMerge.Poly := [(nat_lit 663, Int.ofNat (nat_lit 1))]
theorem atom0560Coded_decode : atom0560 = SparsePolynomial.decodeCubic 24 atom0560Coded := by decide +kernel
theorem atom0560Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (165433959936000 : Int) atom0560Coded) := by
  have h := atom0560_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0560Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0561 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0561 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0561 = ((g 1) * (g 3) * (g 16)) := by
  norm_num [atom0561, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0561_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (140483560089600 : Int) atom0561) := by
  rw [SparsePolynomial.eval_scale, eval_atom0561]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 3) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0561Coded : CoefficientMerge.Poly := [(nat_lit 664, Int.ofNat (nat_lit 1))]
theorem atom0561Coded_decode : atom0561 = SparsePolynomial.decodeCubic 24 atom0561Coded := by decide +kernel
theorem atom0561Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (140483560089600 : Int) atom0561Coded) := by
  have h := atom0561_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0561Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0562 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0562 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0562 = ((g 1) * (g 3) * (g 17)) := by
  norm_num [atom0562, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0562_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (135398637158400 : Int) atom0562) := by
  rw [SparsePolynomial.eval_scale, eval_atom0562]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 3) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0562Coded : CoefficientMerge.Poly := [(nat_lit 665, Int.ofNat (nat_lit 1))]
theorem atom0562Coded_decode : atom0562 = SparsePolynomial.decodeCubic 24 atom0562Coded := by decide +kernel
theorem atom0562Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (135398637158400 : Int) atom0562Coded) := by
  have h := atom0562_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0562Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0563 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0563 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0563 = ((g 1) * (g 3) * (g 18)) := by
  norm_num [atom0563, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0563_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (189575101900800 : Int) atom0563) := by
  rw [SparsePolynomial.eval_scale, eval_atom0563]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 3) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0563Coded : CoefficientMerge.Poly := [(nat_lit 666, Int.ofNat (nat_lit 1))]
theorem atom0563Coded_decode : atom0563 = SparsePolynomial.decodeCubic 24 atom0563Coded := by decide +kernel
theorem atom0563Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (189575101900800 : Int) atom0563Coded) := by
  have h := atom0563_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0563Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0564 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0564 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0564 = ((g 1) * (g 3) * (g 19)) := by
  norm_num [atom0564, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0564_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (123661820620800 : Int) atom0564) := by
  rw [SparsePolynomial.eval_scale, eval_atom0564]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 3) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0564Coded : CoefficientMerge.Poly := [(nat_lit 667, Int.ofNat (nat_lit 1))]
theorem atom0564Coded_decode : atom0564 = SparsePolynomial.decodeCubic 24 atom0564Coded := by decide +kernel
theorem atom0564Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (123661820620800 : Int) atom0564Coded) := by
  have h := atom0564_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0564Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0565 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0565 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0565 = ((g 1) * (g 3) * (g 20)) := by
  norm_num [atom0565, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0565_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (177157890201600 : Int) atom0565) := by
  rw [SparsePolynomial.eval_scale, eval_atom0565]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 3) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0565Coded : CoefficientMerge.Poly := [(nat_lit 668, Int.ofNat (nat_lit 1))]
theorem atom0565Coded_decode : atom0565 = SparsePolynomial.decodeCubic 24 atom0565Coded := by decide +kernel
theorem atom0565Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (177157890201600 : Int) atom0565Coded) := by
  have h := atom0565_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0565Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0566 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0566 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0566 = ((g 1) * (g 3) * (g 21)) := by
  norm_num [atom0566, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0566_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (125050960742400 : Int) atom0566) := by
  rw [SparsePolynomial.eval_scale, eval_atom0566]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 3) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0566Coded : CoefficientMerge.Poly := [(nat_lit 669, Int.ofNat (nat_lit 1))]
theorem atom0566Coded_decode : atom0566 = SparsePolynomial.decodeCubic 24 atom0566Coded := by decide +kernel
theorem atom0566Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (125050960742400 : Int) atom0566Coded) := by
  have h := atom0566_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0566Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0567 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0567 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0567 = ((g 1) * (g 3) * (g 22)) := by
  norm_num [atom0567, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0567_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (119748045043200 : Int) atom0567) := by
  rw [SparsePolynomial.eval_scale, eval_atom0567]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 3) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0567Coded : CoefficientMerge.Poly := [(nat_lit 670, Int.ofNat (nat_lit 1))]
theorem atom0567Coded_decode : atom0567 = SparsePolynomial.decodeCubic 24 atom0567Coded := by decide +kernel
theorem atom0567Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (119748045043200 : Int) atom0567Coded) := by
  have h := atom0567_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0567Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0568 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0568 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0568 = ((g 1) * (g 3) * (g 23)) := by
  norm_num [atom0568, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0568_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (85276193587200 : Int) atom0568) := by
  rw [SparsePolynomial.eval_scale, eval_atom0568]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 3) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0568Coded : CoefficientMerge.Poly := [(nat_lit 671, Int.ofNat (nat_lit 1))]
theorem atom0568Coded_decode : atom0568 = SparsePolynomial.decodeCubic 24 atom0568Coded := by decide +kernel
theorem atom0568Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (85276193587200 : Int) atom0568Coded) := by
  have h := atom0568_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0568Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0569 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0569 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0569 = ((g 1) * (g 4) * (g 4)) := by
  norm_num [atom0569, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0569_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (71527991068800 : Int) atom0569) := by
  rw [SparsePolynomial.eval_scale, eval_atom0569]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0569Coded : CoefficientMerge.Poly := [(nat_lit 676, Int.ofNat (nat_lit 1))]
theorem atom0569Coded_decode : atom0569 = SparsePolynomial.decodeCubic 24 atom0569Coded := by decide +kernel
theorem atom0569Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (71527991068800 : Int) atom0569Coded) := by
  have h := atom0569_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0569Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0570 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0570 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0570 = ((g 1) * (g 4) * (g 5)) := by
  norm_num [atom0570, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0570_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (131094501748848 : Int) atom0570) := by
  rw [SparsePolynomial.eval_scale, eval_atom0570]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0570Coded : CoefficientMerge.Poly := [(nat_lit 677, Int.ofNat (nat_lit 1))]
theorem atom0570Coded_decode : atom0570 = SparsePolynomial.decodeCubic 24 atom0570Coded := by decide +kernel
theorem atom0570Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (131094501748848 : Int) atom0570Coded) := by
  have h := atom0570_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0570Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0571 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0571 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0571 = ((g 1) * (g 4) * (g 6)) := by
  norm_num [atom0571, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0571_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (108778176460800 : Int) atom0571) := by
  rw [SparsePolynomial.eval_scale, eval_atom0571]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0571Coded : CoefficientMerge.Poly := [(nat_lit 678, Int.ofNat (nat_lit 1))]
theorem atom0571Coded_decode : atom0571 = SparsePolynomial.decodeCubic 24 atom0571Coded := by decide +kernel
theorem atom0571Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (108778176460800 : Int) atom0571Coded) := by
  have h := atom0571_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0571Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0572 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0572 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0572 = ((g 1) * (g 4) * (g 7)) := by
  norm_num [atom0572, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0572_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (104610756096000 : Int) atom0572) := by
  rw [SparsePolynomial.eval_scale, eval_atom0572]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0572Coded : CoefficientMerge.Poly := [(nat_lit 679, Int.ofNat (nat_lit 1))]
theorem atom0572Coded_decode : atom0572 = SparsePolynomial.decodeCubic 24 atom0572Coded := by decide +kernel
theorem atom0572Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (104610756096000 : Int) atom0572Coded) := by
  have h := atom0572_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0572Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0573 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0573 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0573 = ((g 1) * (g 4) * (g 8)) := by
  norm_num [atom0573, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0573_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (100443335731200 : Int) atom0573) := by
  rw [SparsePolynomial.eval_scale, eval_atom0573]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0573Coded : CoefficientMerge.Poly := [(nat_lit 680, Int.ofNat (nat_lit 1))]
theorem atom0573Coded_decode : atom0573 = SparsePolynomial.decodeCubic 24 atom0573Coded := by decide +kernel
theorem atom0573Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (100443335731200 : Int) atom0573Coded) := by
  have h := atom0573_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0573Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0574 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0574 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0574 = ((g 1) * (g 4) * (g 9)) := by
  norm_num [atom0574, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0574_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (108299477458656 : Int) atom0574) := by
  rw [SparsePolynomial.eval_scale, eval_atom0574]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0574Coded : CoefficientMerge.Poly := [(nat_lit 681, Int.ofNat (nat_lit 1))]
theorem atom0574Coded_decode : atom0574 = SparsePolynomial.decodeCubic 24 atom0574Coded := by decide +kernel
theorem atom0574Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (108299477458656 : Int) atom0574Coded) := by
  have h := atom0574_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0574Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0575 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0575 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0575 = ((g 1) * (g 4) * (g 10)) := by
  norm_num [atom0575, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0575_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (139419051162336 : Int) atom0575) := by
  rw [SparsePolynomial.eval_scale, eval_atom0575]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0575Coded : CoefficientMerge.Poly := [(nat_lit 682, Int.ofNat (nat_lit 1))]
theorem atom0575Coded_decode : atom0575 = SparsePolynomial.decodeCubic 24 atom0575Coded := by decide +kernel
theorem atom0575Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (139419051162336 : Int) atom0575Coded) := by
  have h := atom0575_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0575Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0576 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0576 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0576 = ((g 1) * (g 4) * (g 11)) := by
  norm_num [atom0576, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0576_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (167261770387008 : Int) atom0576) := by
  rw [SparsePolynomial.eval_scale, eval_atom0576]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0576Coded : CoefficientMerge.Poly := [(nat_lit 683, Int.ofNat (nat_lit 1))]
theorem atom0576Coded_decode : atom0576 = SparsePolynomial.decodeCubic 24 atom0576Coded := by decide +kernel
theorem atom0576Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (167261770387008 : Int) atom0576Coded) := by
  have h := atom0576_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0576Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0577 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0577 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0577 = ((g 1) * (g 4) * (g 12)) := by
  norm_num [atom0577, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0577_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (218938314469248 : Int) atom0577) := by
  rw [SparsePolynomial.eval_scale, eval_atom0577]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0577Coded : CoefficientMerge.Poly := [(nat_lit 684, Int.ofNat (nat_lit 1))]
theorem atom0577Coded_decode : atom0577 = SparsePolynomial.decodeCubic 24 atom0577Coded := by decide +kernel
theorem atom0577Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (218938314469248 : Int) atom0577Coded) := by
  have h := atom0577_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0577Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0578 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0578 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0578 = ((g 1) * (g 4) * (g 13)) := by
  norm_num [atom0578, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0578_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (197448633043200 : Int) atom0578) := by
  rw [SparsePolynomial.eval_scale, eval_atom0578]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 4) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0578Coded : CoefficientMerge.Poly := [(nat_lit 685, Int.ofNat (nat_lit 1))]
theorem atom0578Coded_decode : atom0578 = SparsePolynomial.decodeCubic 24 atom0578Coded := by decide +kernel
theorem atom0578Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (197448633043200 : Int) atom0578Coded) := by
  have h := atom0578_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0578Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0579 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0579 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0579 = ((g 1) * (g 4) * (g 14)) := by
  norm_num [atom0579, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0579_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (168610425984000 : Int) atom0579) := by
  rw [SparsePolynomial.eval_scale, eval_atom0579]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0579Coded : CoefficientMerge.Poly := [(nat_lit 686, Int.ofNat (nat_lit 1))]
theorem atom0579Coded_decode : atom0579 = SparsePolynomial.decodeCubic 24 atom0579Coded := by decide +kernel
theorem atom0579Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (168610425984000 : Int) atom0579Coded) := by
  have h := atom0579_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0579Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0580 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0580 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0580 = ((g 1) * (g 4) * (g 15)) := by
  norm_num [atom0580, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0580_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (169346232115200 : Int) atom0580) := by
  rw [SparsePolynomial.eval_scale, eval_atom0580]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 4) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0580Coded : CoefficientMerge.Poly := [(nat_lit 687, Int.ofNat (nat_lit 1))]
theorem atom0580Coded_decode : atom0580 = SparsePolynomial.decodeCubic 24 atom0580Coded := by decide +kernel
theorem atom0580Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (169346232115200 : Int) atom0580Coded) := by
  have h := atom0580_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0580Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0581 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0581 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0581 = ((g 1) * (g 4) * (g 16)) := by
  norm_num [atom0581, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0581_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (146437017753600 : Int) atom0581) := by
  rw [SparsePolynomial.eval_scale, eval_atom0581]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 4) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0581Coded : CoefficientMerge.Poly := [(nat_lit 688, Int.ofNat (nat_lit 1))]
theorem atom0581Coded_decode : atom0581 = SparsePolynomial.decodeCubic 24 atom0581Coded := by decide +kernel
theorem atom0581Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (146437017753600 : Int) atom0581Coded) := by
  have h := atom0581_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0581Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0582 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0582 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0582 = ((g 1) * (g 4) * (g 17)) := by
  norm_num [atom0582, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0582_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (145716997305600 : Int) atom0582) := by
  rw [SparsePolynomial.eval_scale, eval_atom0582]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 4) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0582Coded : CoefficientMerge.Poly := [(nat_lit 689, Int.ofNat (nat_lit 1))]
theorem atom0582Coded_decode : atom0582 = SparsePolynomial.decodeCubic 24 atom0582Coded := by decide +kernel
theorem atom0582Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (145716997305600 : Int) atom0582Coded) := by
  have h := atom0582_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0582Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0583 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0583 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0583 = ((g 1) * (g 4) * (g 18)) := by
  norm_num [atom0583, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0583_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (199610930534400 : Int) atom0583) := by
  rw [SparsePolynomial.eval_scale, eval_atom0583]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 4) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0583Coded : CoefficientMerge.Poly := [(nat_lit 690, Int.ofNat (nat_lit 1))]
theorem atom0583Coded_decode : atom0583 = SparsePolynomial.decodeCubic 24 atom0583Coded := by decide +kernel
theorem atom0583Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (199610930534400 : Int) atom0583Coded) := by
  have h := atom0583_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0583Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0584 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0584 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0584 = ((g 1) * (g 4) * (g 19)) := by
  norm_num [atom0584, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0584_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (152680778964000 : Int) atom0584) := by
  rw [SparsePolynomial.eval_scale, eval_atom0584]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 4) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0584Coded : CoefficientMerge.Poly := [(nat_lit 691, Int.ofNat (nat_lit 1))]
theorem atom0584Coded_decode : atom0584 = SparsePolynomial.decodeCubic 24 atom0584Coded := by decide +kernel
theorem atom0584Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (152680778964000 : Int) atom0584Coded) := by
  have h := atom0584_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0584Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0585 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0585 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0585 = ((g 1) * (g 4) * (g 20)) := by
  norm_num [atom0585, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0585_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (191722236703200 : Int) atom0585) := by
  rw [SparsePolynomial.eval_scale, eval_atom0585]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 4) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0585Coded : CoefficientMerge.Poly := [(nat_lit 692, Int.ofNat (nat_lit 1))]
theorem atom0585Coded_decode : atom0585 = SparsePolynomial.decodeCubic 24 atom0585Coded := by decide +kernel
theorem atom0585Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (191722236703200 : Int) atom0585Coded) := by
  have h := atom0585_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0585Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0586 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0586 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0586 = ((g 1) * (g 4) * (g 21)) := by
  norm_num [atom0586, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0586_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (163638700898400 : Int) atom0586) := by
  rw [SparsePolynomial.eval_scale, eval_atom0586]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 4) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0586Coded : CoefficientMerge.Poly := [(nat_lit 693, Int.ofNat (nat_lit 1))]
theorem atom0586Coded_decode : atom0586 = SparsePolynomial.decodeCubic 24 atom0586Coded := by decide +kernel
theorem atom0586Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (163638700898400 : Int) atom0586Coded) := by
  have h := atom0586_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0586Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0587 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0587 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0587 = ((g 1) * (g 4) * (g 22)) := by
  norm_num [atom0587, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0587_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (184533468789600 : Int) atom0587) := by
  rw [SparsePolynomial.eval_scale, eval_atom0587]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 4) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0587Coded : CoefficientMerge.Poly := [(nat_lit 694, Int.ofNat (nat_lit 1))]
theorem atom0587Coded_decode : atom0587 = SparsePolynomial.decodeCubic 24 atom0587Coded := by decide +kernel
theorem atom0587Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (184533468789600 : Int) atom0587Coded) := by
  have h := atom0587_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0587Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0588 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0588 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0588 = ((g 1) * (g 4) * (g 23)) := by
  norm_num [atom0588, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0588_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (135594629301600 : Int) atom0588) := by
  rw [SparsePolynomial.eval_scale, eval_atom0588]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 4) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0588Coded : CoefficientMerge.Poly := [(nat_lit 695, Int.ofNat (nat_lit 1))]
theorem atom0588Coded_decode : atom0588 = SparsePolynomial.decodeCubic 24 atom0588Coded := by decide +kernel
theorem atom0588Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (135594629301600 : Int) atom0588Coded) := by
  have h := atom0588_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0588Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0589 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0589 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0589 = ((g 1) * (g 5) * (g 5)) := by
  norm_num [atom0589, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0589_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (88198484774400 : Int) atom0589) := by
  rw [SparsePolynomial.eval_scale, eval_atom0589]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0589Coded : CoefficientMerge.Poly := [(nat_lit 701, Int.ofNat (nat_lit 1))]
theorem atom0589Coded_decode : atom0589 = SparsePolynomial.decodeCubic 24 atom0589Coded := by decide +kernel
theorem atom0589Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (88198484774400 : Int) atom0589Coded) := by
  have h := atom0589_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0589Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0590 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0590 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0590 = ((g 1) * (g 5) * (g 6)) := by
  norm_num [atom0590, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0590_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (134283854068848 : Int) atom0590) := by
  rw [SparsePolynomial.eval_scale, eval_atom0590]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0590Coded : CoefficientMerge.Poly := [(nat_lit 702, Int.ofNat (nat_lit 1))]
theorem atom0590Coded_decode : atom0590 = SparsePolynomial.decodeCubic 24 atom0590Coded := by decide +kernel
theorem atom0590Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (134283854068848 : Int) atom0590Coded) := by
  have h := atom0590_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0590Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0591 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0591 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0591 = ((g 1) * (g 5) * (g 7)) := by
  norm_num [atom0591, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0591_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (121414226836848 : Int) atom0591) := by
  rw [SparsePolynomial.eval_scale, eval_atom0591]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0591Coded : CoefficientMerge.Poly := [(nat_lit 703, Int.ofNat (nat_lit 1))]
theorem atom0591Coded_decode : atom0591 = SparsePolynomial.decodeCubic 24 atom0591Coded := by decide +kernel
theorem atom0591Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (121414226836848 : Int) atom0591Coded) := by
  have h := atom0591_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0591Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0592 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0592 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0592 = ((g 1) * (g 5) * (g 8)) := by
  norm_num [atom0592, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0592_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (120824747371152 : Int) atom0592) := by
  rw [SparsePolynomial.eval_scale, eval_atom0592]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0592Coded : CoefficientMerge.Poly := [(nat_lit 704, Int.ofNat (nat_lit 1))]
theorem atom0592Coded_decode : atom0592 = SparsePolynomial.decodeCubic 24 atom0592Coded := by decide +kernel
theorem atom0592Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (120824747371152 : Int) atom0592Coded) := by
  have h := atom0592_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0592Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0593 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0593 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0593 = ((g 1) * (g 5) * (g 9)) := by
  norm_num [atom0593, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0593_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (128906875593144 : Int) atom0593) := by
  rw [SparsePolynomial.eval_scale, eval_atom0593]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0593Coded : CoefficientMerge.Poly := [(nat_lit 705, Int.ofNat (nat_lit 1))]
theorem atom0593Coded_decode : atom0593 = SparsePolynomial.decodeCubic 24 atom0593Coded := by decide +kernel
theorem atom0593Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (128906875593144 : Int) atom0593Coded) := by
  have h := atom0593_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0593Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0594 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0594 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0594 = ((g 1) * (g 5) * (g 10)) := by
  norm_num [atom0594, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0594_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (151977742829352 : Int) atom0594) := by
  rw [SparsePolynomial.eval_scale, eval_atom0594]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0594Coded : CoefficientMerge.Poly := [(nat_lit 706, Int.ofNat (nat_lit 1))]
theorem atom0594Coded_decode : atom0594 = SparsePolynomial.decodeCubic 24 atom0594Coded := by decide +kernel
theorem atom0594Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (151977742829352 : Int) atom0594Coded) := by
  have h := atom0594_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0594Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0595 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0595 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0595 = ((g 1) * (g 5) * (g 11)) := by
  norm_num [atom0595, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0595_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (176775088108608 : Int) atom0595) := by
  rw [SparsePolynomial.eval_scale, eval_atom0595]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0595Coded : CoefficientMerge.Poly := [(nat_lit 707, Int.ofNat (nat_lit 1))]
theorem atom0595Coded_decode : atom0595 = SparsePolynomial.decodeCubic 24 atom0595Coded := by decide +kernel
theorem atom0595Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (176775088108608 : Int) atom0595Coded) := by
  have h := atom0595_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0595Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0596 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0596 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0596 = ((g 1) * (g 5) * (g 12)) := by
  norm_num [atom0596, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0596_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (230492817675648 : Int) atom0596) := by
  rw [SparsePolynomial.eval_scale, eval_atom0596]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0596Coded : CoefficientMerge.Poly := [(nat_lit 708, Int.ofNat (nat_lit 1))]
theorem atom0596Coded_decode : atom0596 = SparsePolynomial.decodeCubic 24 atom0596Coded := by decide +kernel
theorem atom0596Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (230492817675648 : Int) atom0596Coded) := by
  have h := atom0596_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0596Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0597 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0597 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0597 = ((g 1) * (g 5) * (g 13)) := by
  norm_num [atom0597, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0597_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (211044321734400 : Int) atom0597) := by
  rw [SparsePolynomial.eval_scale, eval_atom0597]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0597Coded : CoefficientMerge.Poly := [(nat_lit 709, Int.ofNat (nat_lit 1))]
theorem atom0597Coded_decode : atom0597 = SparsePolynomial.decodeCubic 24 atom0597Coded := by decide +kernel
theorem atom0597Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (211044321734400 : Int) atom0597Coded) := by
  have h := atom0597_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0597Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0598 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0598 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0598 = ((g 1) * (g 5) * (g 14)) := by
  norm_num [atom0598, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0598_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (184247300160000 : Int) atom0598) := by
  rw [SparsePolynomial.eval_scale, eval_atom0598]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0598Coded : CoefficientMerge.Poly := [(nat_lit 710, Int.ofNat (nat_lit 1))]
theorem atom0598Coded_decode : atom0598 = SparsePolynomial.decodeCubic 24 atom0598Coded := by decide +kernel
theorem atom0598Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (184247300160000 : Int) atom0598Coded) := by
  have h := atom0598_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0598Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0599 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0599 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0599 = ((g 1) * (g 5) * (g 15)) := by
  norm_num [atom0599, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0599_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (187393161312000 : Int) atom0599) := by
  rw [SparsePolynomial.eval_scale, eval_atom0599]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 5) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0599Coded : CoefficientMerge.Poly := [(nat_lit 711, Int.ofNat (nat_lit 1))]
theorem atom0599Coded_decode : atom0599 = SparsePolynomial.decodeCubic 24 atom0599Coded := by decide +kernel
theorem atom0599Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (187393161312000 : Int) atom0599Coded) := by
  have h := atom0599_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0599Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0600 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0600 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0600 = ((g 1) * (g 5) * (g 16)) := by
  norm_num [atom0600, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0600_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (172805257094400 : Int) atom0600) := by
  rw [SparsePolynomial.eval_scale, eval_atom0600]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 5) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0600Coded : CoefficientMerge.Poly := [(nat_lit 712, Int.ofNat (nat_lit 1))]
theorem atom0600Coded_decode : atom0600 = SparsePolynomial.decodeCubic 24 atom0600Coded := by decide +kernel
theorem atom0600Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (172805257094400 : Int) atom0600Coded) := by
  have h := atom0600_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0600Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0601 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0601 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0601 = ((g 1) * (g 5) * (g 17)) := by
  norm_num [atom0601, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0601_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (173116460563200 : Int) atom0601) := by
  rw [SparsePolynomial.eval_scale, eval_atom0601]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 5) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0601Coded : CoefficientMerge.Poly := [(nat_lit 713, Int.ofNat (nat_lit 1))]
theorem atom0601Coded_decode : atom0601 = SparsePolynomial.decodeCubic 24 atom0601Coded := by decide +kernel
theorem atom0601Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (173116460563200 : Int) atom0601Coded) := by
  have h := atom0601_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0601Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0602 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0602 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0602 = ((g 1) * (g 5) * (g 18)) := by
  norm_num [atom0602, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0602_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (223412546649600 : Int) atom0602) := by
  rw [SparsePolynomial.eval_scale, eval_atom0602]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 5) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0602Coded : CoefficientMerge.Poly := [(nat_lit 714, Int.ofNat (nat_lit 1))]
theorem atom0602Coded_decode : atom0602 = SparsePolynomial.decodeCubic 24 atom0602Coded := by decide +kernel
theorem atom0602Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (223412546649600 : Int) atom0602Coded) := by
  have h := atom0602_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0602Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0603 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0603 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0603 = ((g 1) * (g 5) * (g 19)) := by
  norm_num [atom0603, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0603_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (185452241990400 : Int) atom0603) := by
  rw [SparsePolynomial.eval_scale, eval_atom0603]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 5) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0603Coded : CoefficientMerge.Poly := [(nat_lit 715, Int.ofNat (nat_lit 1))]
theorem atom0603Coded_decode : atom0603 = SparsePolynomial.decodeCubic 24 atom0603Coded := by decide +kernel
theorem atom0603Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (185452241990400 : Int) atom0603Coded) := by
  have h := atom0603_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0603Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0604 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0604 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0604 = ((g 1) * (g 5) * (g 20)) := by
  norm_num [atom0604, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0604_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (227731291603200 : Int) atom0604) := by
  rw [SparsePolynomial.eval_scale, eval_atom0604]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 5) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0604Coded : CoefficientMerge.Poly := [(nat_lit 716, Int.ofNat (nat_lit 1))]
theorem atom0604Coded_decode : atom0604 = SparsePolynomial.decodeCubic 24 atom0604Coded := by decide +kernel
theorem atom0604Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (227731291603200 : Int) atom0604Coded) := by
  have h := atom0604_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0604Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0605 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0605 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0605 = ((g 1) * (g 5) * (g 21)) := by
  norm_num [atom0605, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0605_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (205091715628800 : Int) atom0605) := by
  rw [SparsePolynomial.eval_scale, eval_atom0605]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 5) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0605Coded : CoefficientMerge.Poly := [(nat_lit 717, Int.ofNat (nat_lit 1))]
theorem atom0605Coded_decode : atom0605 = SparsePolynomial.decodeCubic 24 atom0605Coded := by decide +kernel
theorem atom0605Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (205091715628800 : Int) atom0605Coded) := by
  have h := atom0605_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0605Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0606 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0606 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0606 = ((g 1) * (g 5) * (g 22)) := by
  norm_num [atom0606, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0606_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (238961209267200 : Int) atom0606) := by
  rw [SparsePolynomial.eval_scale, eval_atom0606]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 5) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0606Coded : CoefficientMerge.Poly := [(nat_lit 718, Int.ofNat (nat_lit 1))]
theorem atom0606Coded_decode : atom0606 = SparsePolynomial.decodeCubic 24 atom0606Coded := by decide +kernel
theorem atom0606Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (238961209267200 : Int) atom0606Coded) := by
  have h := atom0606_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0606Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0607 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0607 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0607 = ((g 1) * (g 5) * (g 23)) := by
  norm_num [atom0607, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0607_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (221088695990400 : Int) atom0607) := by
  rw [SparsePolynomial.eval_scale, eval_atom0607]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 5) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0607Coded : CoefficientMerge.Poly := [(nat_lit 719, Int.ofNat (nat_lit 1))]
theorem atom0607Coded_decode : atom0607 = SparsePolynomial.decodeCubic 24 atom0607Coded := by decide +kernel
theorem atom0607Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (221088695990400 : Int) atom0607Coded) := by
  have h := atom0607_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0607Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0608 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0608 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0608 = ((g 1) * (g 6) * (g 6)) := by
  norm_num [atom0608, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0608_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (89684587238400 : Int) atom0608) := by
  rw [SparsePolynomial.eval_scale, eval_atom0608]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0608Coded : CoefficientMerge.Poly := [(nat_lit 726, Int.ofNat (nat_lit 1))]
theorem atom0608Coded_decode : atom0608 = SparsePolynomial.decodeCubic 24 atom0608Coded := by decide +kernel
theorem atom0608Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (89684587238400 : Int) atom0608Coded) := by
  have h := atom0608_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0608Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block009 : CoefficientMerge.Poly := [(nat_lit 629, Int.ofNat (nat_lit 159710549644800)), (nat_lit 630, Int.ofNat (nat_lit 137694970828800)), (nat_lit 631, Int.ofNat (nat_lit 129445179494400)), (nat_lit 632, Int.ofNat (nat_lit 121195388160000)), (nat_lit 633, Int.ofNat (nat_lit 124969158917856)), (nat_lit 634, Int.ofNat (nat_lit 152006361651936)), (nat_lit 635, Int.ofNat (nat_lit 175766709907008)), (nat_lit 636, Int.ofNat (nat_lit 223360883019648)), (nat_lit 637, Int.ofNat (nat_lit 197788830624000)), (nat_lit 638, Int.ofNat (nat_lit 164868252595200)), (nat_lit 639, Int.ofNat (nat_lit 161521687756800)), (nat_lit 640, Int.ofNat (nat_lit 134530102425600)), (nat_lit 641, Int.ofNat (nat_lit 127403994009600)), (nat_lit 642, Int.ofNat (nat_lit 179539273267200)), (nat_lit 643, Int.ofNat (nat_lit 97636705689600)), (nat_lit 644, Int.ofNat (nat_lit 163039690598400)), (nat_lit 645, Int.ofNat (nat_lit 88734868992000)), (nat_lit 646, Int.ofNat (nat_lit 62854509849600)), (nat_lit 647, Int.ofNat (nat_lit 56808566337600)), (nat_lit 651, Int.ofNat (nat_lit 70931195596800)), (nat_lit 652, Int.ofNat (nat_lit 135653785344000)), (nat_lit 653, Int.ofNat (nat_lit 143210966976000)), (nat_lit 654, Int.ofNat (nat_lit 123236573644800)), (nat_lit 655, Int.ofNat (nat_lit 117027967795200)), (nat_lit 656, Int.ofNat (nat_lit 110819361945600)), (nat_lit 657, Int.ofNat (nat_lit 116634318188256)), (nat_lit 658, Int.ofNat (nat_lit 145712706407136)), (nat_lit 659, Int.ofNat (nat_lit 171514240147008)), (nat_lit 660, Int.ofNat (nat_lit 221149598744448)), (nat_lit 661, Int.ofNat (nat_lit 197618731833600)), (nat_lit 662, Int.ofNat (nat_lit 166739339289600)), (nat_lit 663, Int.ofNat (nat_lit 165433959936000)), (nat_lit 664, Int.ofNat (nat_lit 140483560089600)), (nat_lit 665, Int.ofNat (nat_lit 135398637158400)), (nat_lit 666, Int.ofNat (nat_lit 189575101900800)), (nat_lit 667, Int.ofNat (nat_lit 123661820620800)), (nat_lit 668, Int.ofNat (nat_lit 177157890201600)), (nat_lit 669, Int.ofNat (nat_lit 125050960742400)), (nat_lit 670, Int.ofNat (nat_lit 119748045043200)), (nat_lit 671, Int.ofNat (nat_lit 85276193587200)), (nat_lit 676, Int.ofNat (nat_lit 71527991068800)), (nat_lit 677, Int.ofNat (nat_lit 131094501748848)), (nat_lit 678, Int.ofNat (nat_lit 108778176460800)), (nat_lit 679, Int.ofNat (nat_lit 104610756096000)), (nat_lit 680, Int.ofNat (nat_lit 100443335731200)), (nat_lit 681, Int.ofNat (nat_lit 108299477458656)), (nat_lit 682, Int.ofNat (nat_lit 139419051162336)), (nat_lit 683, Int.ofNat (nat_lit 167261770387008)), (nat_lit 684, Int.ofNat (nat_lit 218938314469248)), (nat_lit 685, Int.ofNat (nat_lit 197448633043200)), (nat_lit 686, Int.ofNat (nat_lit 168610425984000)), (nat_lit 687, Int.ofNat (nat_lit 169346232115200)), (nat_lit 688, Int.ofNat (nat_lit 146437017753600)), (nat_lit 689, Int.ofNat (nat_lit 145716997305600)), (nat_lit 690, Int.ofNat (nat_lit 199610930534400)), (nat_lit 691, Int.ofNat (nat_lit 152680778964000)), (nat_lit 692, Int.ofNat (nat_lit 191722236703200)), (nat_lit 693, Int.ofNat (nat_lit 163638700898400)), (nat_lit 694, Int.ofNat (nat_lit 184533468789600)), (nat_lit 695, Int.ofNat (nat_lit 135594629301600)), (nat_lit 701, Int.ofNat (nat_lit 88198484774400)), (nat_lit 702, Int.ofNat (nat_lit 134283854068848)), (nat_lit 703, Int.ofNat (nat_lit 121414226836848)), (nat_lit 704, Int.ofNat (nat_lit 120824747371152)), (nat_lit 705, Int.ofNat (nat_lit 128906875593144)), (nat_lit 706, Int.ofNat (nat_lit 151977742829352)), (nat_lit 707, Int.ofNat (nat_lit 176775088108608)), (nat_lit 708, Int.ofNat (nat_lit 230492817675648)), (nat_lit 709, Int.ofNat (nat_lit 211044321734400)), (nat_lit 710, Int.ofNat (nat_lit 184247300160000)), (nat_lit 711, Int.ofNat (nat_lit 187393161312000)), (nat_lit 712, Int.ofNat (nat_lit 172805257094400)), (nat_lit 713, Int.ofNat (nat_lit 173116460563200)), (nat_lit 714, Int.ofNat (nat_lit 223412546649600)), (nat_lit 715, Int.ofNat (nat_lit 185452241990400)), (nat_lit 716, Int.ofNat (nat_lit 227731291603200)), (nat_lit 717, Int.ofNat (nat_lit 205091715628800)), (nat_lit 718, Int.ofNat (nat_lit 238961209267200)), (nat_lit 719, Int.ofNat (nat_lit 221088695990400)), (nat_lit 726, Int.ofNat (nat_lit 89684587238400))]
theorem block009_data : block009 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (159710549644800 : Int) atom0529Coded) (CoefficientMerge.scale (137694970828800 : Int) atom0530Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (129445179494400 : Int) atom0531Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (121195388160000 : Int) atom0532Coded) (CoefficientMerge.scale (124969158917856 : Int) atom0533Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (152006361651936 : Int) atom0534Coded) (CoefficientMerge.scale (175766709907008 : Int) atom0535Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (223360883019648 : Int) atom0536Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (197788830624000 : Int) atom0537Coded) (CoefficientMerge.scale (164868252595200 : Int) atom0538Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (161521687756800 : Int) atom0539Coded) (CoefficientMerge.scale (134530102425600 : Int) atom0540Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (127403994009600 : Int) atom0541Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (179539273267200 : Int) atom0542Coded) (CoefficientMerge.scale (97636705689600 : Int) atom0543Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (163039690598400 : Int) atom0544Coded) (CoefficientMerge.scale (88734868992000 : Int) atom0545Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (62854509849600 : Int) atom0546Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56808566337600 : Int) atom0547Coded) (CoefficientMerge.scale (70931195596800 : Int) atom0548Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (135653785344000 : Int) atom0549Coded) (CoefficientMerge.scale (143210966976000 : Int) atom0550Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (123236573644800 : Int) atom0551Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (117027967795200 : Int) atom0552Coded) (CoefficientMerge.scale (110819361945600 : Int) atom0553Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (116634318188256 : Int) atom0554Coded) (CoefficientMerge.scale (145712706407136 : Int) atom0555Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (171514240147008 : Int) atom0556Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (221149598744448 : Int) atom0557Coded) (CoefficientMerge.scale (197618731833600 : Int) atom0558Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (166739339289600 : Int) atom0559Coded) (CoefficientMerge.scale (165433959936000 : Int) atom0560Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140483560089600 : Int) atom0561Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (135398637158400 : Int) atom0562Coded) (CoefficientMerge.scale (189575101900800 : Int) atom0563Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (123661820620800 : Int) atom0564Coded) (CoefficientMerge.scale (177157890201600 : Int) atom0565Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (125050960742400 : Int) atom0566Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (119748045043200 : Int) atom0567Coded) (CoefficientMerge.scale (85276193587200 : Int) atom0568Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (71527991068800 : Int) atom0569Coded) (CoefficientMerge.scale (131094501748848 : Int) atom0570Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (108778176460800 : Int) atom0571Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (104610756096000 : Int) atom0572Coded) (CoefficientMerge.scale (100443335731200 : Int) atom0573Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (108299477458656 : Int) atom0574Coded) (CoefficientMerge.scale (139419051162336 : Int) atom0575Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (167261770387008 : Int) atom0576Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (218938314469248 : Int) atom0577Coded) (CoefficientMerge.scale (197448633043200 : Int) atom0578Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (168610425984000 : Int) atom0579Coded) (CoefficientMerge.scale (169346232115200 : Int) atom0580Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (146437017753600 : Int) atom0581Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (145716997305600 : Int) atom0582Coded) (CoefficientMerge.scale (199610930534400 : Int) atom0583Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (152680778964000 : Int) atom0584Coded) (CoefficientMerge.scale (191722236703200 : Int) atom0585Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (163638700898400 : Int) atom0586Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (184533468789600 : Int) atom0587Coded) (CoefficientMerge.scale (135594629301600 : Int) atom0588Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (88198484774400 : Int) atom0589Coded) (CoefficientMerge.scale (134283854068848 : Int) atom0590Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (121414226836848 : Int) atom0591Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (120824747371152 : Int) atom0592Coded) (CoefficientMerge.scale (128906875593144 : Int) atom0593Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (151977742829352 : Int) atom0594Coded) (CoefficientMerge.scale (176775088108608 : Int) atom0595Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (230492817675648 : Int) atom0596Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (211044321734400 : Int) atom0597Coded) (CoefficientMerge.scale (184247300160000 : Int) atom0598Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (187393161312000 : Int) atom0599Coded) (CoefficientMerge.scale (172805257094400 : Int) atom0600Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (173116460563200 : Int) atom0601Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (223412546649600 : Int) atom0602Coded) (CoefficientMerge.scale (185452241990400 : Int) atom0603Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (227731291603200 : Int) atom0604Coded) (CoefficientMerge.scale (205091715628800 : Int) atom0605Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (238961209267200 : Int) atom0606Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (221088695990400 : Int) atom0607Coded) (CoefficientMerge.scale (89684587238400 : Int) atom0608Coded)))))))) := by decide +kernel
theorem block009_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block009 := by
  rw [block009_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0529Coded_nonneg g hg hA hB) (atom0530Coded_nonneg g hg hA hB)) (add_nonneg (atom0531Coded_nonneg g hg hA hB) (add_nonneg (atom0532Coded_nonneg g hg hA hB) (atom0533Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0534Coded_nonneg g hg hA hB) (atom0535Coded_nonneg g hg hA hB)) (add_nonneg (atom0536Coded_nonneg g hg hA hB) (add_nonneg (atom0537Coded_nonneg g hg hA hB) (atom0538Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0539Coded_nonneg g hg hA hB) (atom0540Coded_nonneg g hg hA hB)) (add_nonneg (atom0541Coded_nonneg g hg hA hB) (add_nonneg (atom0542Coded_nonneg g hg hA hB) (atom0543Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0544Coded_nonneg g hg hA hB) (atom0545Coded_nonneg g hg hA hB)) (add_nonneg (atom0546Coded_nonneg g hg hA hB) (add_nonneg (atom0547Coded_nonneg g hg hA hB) (atom0548Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0549Coded_nonneg g hg hA hB) (atom0550Coded_nonneg g hg hA hB)) (add_nonneg (atom0551Coded_nonneg g hg hA hB) (add_nonneg (atom0552Coded_nonneg g hg hA hB) (atom0553Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0554Coded_nonneg g hg hA hB) (atom0555Coded_nonneg g hg hA hB)) (add_nonneg (atom0556Coded_nonneg g hg hA hB) (add_nonneg (atom0557Coded_nonneg g hg hA hB) (atom0558Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0559Coded_nonneg g hg hA hB) (atom0560Coded_nonneg g hg hA hB)) (add_nonneg (atom0561Coded_nonneg g hg hA hB) (add_nonneg (atom0562Coded_nonneg g hg hA hB) (atom0563Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0564Coded_nonneg g hg hA hB) (atom0565Coded_nonneg g hg hA hB)) (add_nonneg (atom0566Coded_nonneg g hg hA hB) (add_nonneg (atom0567Coded_nonneg g hg hA hB) (atom0568Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0569Coded_nonneg g hg hA hB) (atom0570Coded_nonneg g hg hA hB)) (add_nonneg (atom0571Coded_nonneg g hg hA hB) (add_nonneg (atom0572Coded_nonneg g hg hA hB) (atom0573Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0574Coded_nonneg g hg hA hB) (atom0575Coded_nonneg g hg hA hB)) (add_nonneg (atom0576Coded_nonneg g hg hA hB) (add_nonneg (atom0577Coded_nonneg g hg hA hB) (atom0578Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0579Coded_nonneg g hg hA hB) (atom0580Coded_nonneg g hg hA hB)) (add_nonneg (atom0581Coded_nonneg g hg hA hB) (add_nonneg (atom0582Coded_nonneg g hg hA hB) (atom0583Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0584Coded_nonneg g hg hA hB) (atom0585Coded_nonneg g hg hA hB)) (add_nonneg (atom0586Coded_nonneg g hg hA hB) (add_nonneg (atom0587Coded_nonneg g hg hA hB) (atom0588Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0589Coded_nonneg g hg hA hB) (atom0590Coded_nonneg g hg hA hB)) (add_nonneg (atom0591Coded_nonneg g hg hA hB) (add_nonneg (atom0592Coded_nonneg g hg hA hB) (atom0593Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0594Coded_nonneg g hg hA hB) (atom0595Coded_nonneg g hg hA hB)) (add_nonneg (atom0596Coded_nonneg g hg hA hB) (add_nonneg (atom0597Coded_nonneg g hg hA hB) (atom0598Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0599Coded_nonneg g hg hA hB) (atom0600Coded_nonneg g hg hA hB)) (add_nonneg (atom0601Coded_nonneg g hg hA hB) (add_nonneg (atom0602Coded_nonneg g hg hA hB) (atom0603Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0604Coded_nonneg g hg hA hB) (atom0605Coded_nonneg g hg hA hB)) (add_nonneg (atom0606Coded_nonneg g hg hA hB) (add_nonneg (atom0607Coded_nonneg g hg hA hB) (atom0608Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
