-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom0576 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0576 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0576 = ((g 2) * (g 2) * (g 7)) := by
  norm_num [atom0576, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0576_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13552237298304 : Int) atom0576) := by
  rw [SparsePolynomial.eval_scale, eval_atom0576]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 2) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0576Coded : CoefficientMerge.Poly := [(nat_lit 931, Int.ofNat (nat_lit 1))]
theorem atom0576Coded_decode : atom0576 = SparsePolynomial.decodeCubic 21 atom0576Coded := by decide +kernel
theorem atom0576Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13552237298304 : Int) atom0576Coded) := by
  have h := atom0576_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0576Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0577 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0577 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0577 = ((g 2) * (g 2) * (g 8)) := by
  norm_num [atom0577, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0577_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13277370355200 : Int) atom0577) := by
  rw [SparsePolynomial.eval_scale, eval_atom0577]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 2) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0577Coded : CoefficientMerge.Poly := [(nat_lit 932, Int.ofNat (nat_lit 1))]
theorem atom0577Coded_decode : atom0577 = SparsePolynomial.decodeCubic 21 atom0577Coded := by decide +kernel
theorem atom0577Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13277370355200 : Int) atom0577Coded) := by
  have h := atom0577_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0577Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0578 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0578 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0578 = ((g 2) * (g 2) * (g 9)) := by
  norm_num [atom0578, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0578_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12927508070400 : Int) atom0578) := by
  rw [SparsePolynomial.eval_scale, eval_atom0578]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 2) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0578Coded : CoefficientMerge.Poly := [(nat_lit 933, Int.ofNat (nat_lit 1))]
theorem atom0578Coded_decode : atom0578 = SparsePolynomial.decodeCubic 21 atom0578Coded := by decide +kernel
theorem atom0578Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (12927508070400 : Int) atom0578Coded) := by
  have h := atom0578_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0578Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0579 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0579 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0579 = ((g 2) * (g 2) * (g 10)) := by
  norm_num [atom0579, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0579_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12577645785600 : Int) atom0579) := by
  rw [SparsePolynomial.eval_scale, eval_atom0579]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 2) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0579Coded : CoefficientMerge.Poly := [(nat_lit 934, Int.ofNat (nat_lit 1))]
theorem atom0579Coded_decode : atom0579 = SparsePolynomial.decodeCubic 21 atom0579Coded := by decide +kernel
theorem atom0579Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (12577645785600 : Int) atom0579Coded) := by
  have h := atom0579_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0579Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0580 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0580 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0580 = ((g 2) * (g 2) * (g 11)) := by
  norm_num [atom0580, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0580_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11915859916800 : Int) atom0580) := by
  rw [SparsePolynomial.eval_scale, eval_atom0580]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 2) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0580Coded : CoefficientMerge.Poly := [(nat_lit 935, Int.ofNat (nat_lit 1))]
theorem atom0580Coded_decode : atom0580 = SparsePolynomial.decodeCubic 21 atom0580Coded := by decide +kernel
theorem atom0580Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11915859916800 : Int) atom0580Coded) := by
  have h := atom0580_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0580Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0581 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0581 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0581 = ((g 2) * (g 2) * (g 12)) := by
  norm_num [atom0581, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0581_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9204520908800 : Int) atom0581) := by
  rw [SparsePolynomial.eval_scale, eval_atom0581]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 2) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0581Coded : CoefficientMerge.Poly := [(nat_lit 936, Int.ofNat (nat_lit 1))]
theorem atom0581Coded_decode : atom0581 = SparsePolynomial.decodeCubic 21 atom0581Coded := by decide +kernel
theorem atom0581Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (9204520908800 : Int) atom0581Coded) := by
  have h := atom0581_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0581Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0582 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0582 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0582 = ((g 2) * (g 2) * (g 13)) := by
  norm_num [atom0582, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0582_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8236260748800 : Int) atom0582) := by
  rw [SparsePolynomial.eval_scale, eval_atom0582]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 2) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0582Coded : CoefficientMerge.Poly := [(nat_lit 937, Int.ofNat (nat_lit 1))]
theorem atom0582Coded_decode : atom0582 = SparsePolynomial.decodeCubic 21 atom0582Coded := by decide +kernel
theorem atom0582Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8236260748800 : Int) atom0582Coded) := by
  have h := atom0582_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0582Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0583 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0583 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0583 = ((g 2) * (g 2) * (g 14)) := by
  norm_num [atom0583, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0583_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8145412531200 : Int) atom0583) := by
  rw [SparsePolynomial.eval_scale, eval_atom0583]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 2) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0583Coded : CoefficientMerge.Poly := [(nat_lit 938, Int.ofNat (nat_lit 1))]
theorem atom0583Coded_decode : atom0583 = SparsePolynomial.decodeCubic 21 atom0583Coded := by decide +kernel
theorem atom0583Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8145412531200 : Int) atom0583Coded) := by
  have h := atom0583_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0583Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0584 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0584 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0584 = ((g 2) * (g 2) * (g 15)) := by
  norm_num [atom0584, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0584_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12461669337600 : Int) atom0584) := by
  rw [SparsePolynomial.eval_scale, eval_atom0584]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 2) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0584Coded : CoefficientMerge.Poly := [(nat_lit 939, Int.ofNat (nat_lit 1))]
theorem atom0584Coded_decode : atom0584 = SparsePolynomial.decodeCubic 21 atom0584Coded := by decide +kernel
theorem atom0584Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (12461669337600 : Int) atom0584Coded) := by
  have h := atom0584_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0584Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0585 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0585 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0585 = ((g 2) * (g 2) * (g 16)) := by
  norm_num [atom0585, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0585_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3160358208000 : Int) atom0585) := by
  rw [SparsePolynomial.eval_scale, eval_atom0585]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 2) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0585Coded : CoefficientMerge.Poly := [(nat_lit 940, Int.ofNat (nat_lit 1))]
theorem atom0585Coded_decode : atom0585 = SparsePolynomial.decodeCubic 21 atom0585Coded := by decide +kernel
theorem atom0585Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3160358208000 : Int) atom0585Coded) := by
  have h := atom0585_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0585Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0586 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0586 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0586 = ((g 2) * (g 2) * (g 17)) := by
  norm_num [atom0586, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0586_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9873255974400 : Int) atom0586) := by
  rw [SparsePolynomial.eval_scale, eval_atom0586]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 2) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0586Coded : CoefficientMerge.Poly := [(nat_lit 941, Int.ofNat (nat_lit 1))]
theorem atom0586Coded_decode : atom0586 = SparsePolynomial.decodeCubic 21 atom0586Coded := by decide +kernel
theorem atom0586Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (9873255974400 : Int) atom0586Coded) := by
  have h := atom0586_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0586Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0587 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0587 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0587 = ((g 2) * (g 2) * (g 18)) := by
  norm_num [atom0587, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0587_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1606273804800 : Int) atom0587) := by
  rw [SparsePolynomial.eval_scale, eval_atom0587]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 2) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0587Coded : CoefficientMerge.Poly := [(nat_lit 942, Int.ofNat (nat_lit 1))]
theorem atom0587Coded_decode : atom0587 = SparsePolynomial.decodeCubic 21 atom0587Coded := by decide +kernel
theorem atom0587Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1606273804800 : Int) atom0587Coded) := by
  have h := atom0587_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0587Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0588 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0588 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0588 = ((g 2) * (g 2) * (g 20)) := by
  norm_num [atom0588, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0588_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3063711168000 : Int) atom0588) := by
  rw [SparsePolynomial.eval_scale, eval_atom0588]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 2) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0588Coded : CoefficientMerge.Poly := [(nat_lit 944, Int.ofNat (nat_lit 1))]
theorem atom0588Coded_decode : atom0588 = SparsePolynomial.decodeCubic 21 atom0588Coded := by decide +kernel
theorem atom0588Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3063711168000 : Int) atom0588Coded) := by
  have h := atom0588_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0588Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0589 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 3], Int.ofNat (nat_lit 1))]
theorem eval_atom0589 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0589 = ((g 2) * (g 3) * (g 3)) := by
  norm_num [atom0589, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0589_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11203324876800 : Int) atom0589) := by
  rw [SparsePolynomial.eval_scale, eval_atom0589]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 2) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0589Coded : CoefficientMerge.Poly := [(nat_lit 948, Int.ofNat (nat_lit 1))]
theorem atom0589Coded_decode : atom0589 = SparsePolynomial.decodeCubic 21 atom0589Coded := by decide +kernel
theorem atom0589Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11203324876800 : Int) atom0589Coded) := by
  have h := atom0589_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0589Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0590 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0590 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0590 = ((g 2) * (g 3) * (g 4)) := by
  norm_num [atom0590, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0590_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21357062899200 : Int) atom0590) := by
  rw [SparsePolynomial.eval_scale, eval_atom0590]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 2) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0590Coded : CoefficientMerge.Poly := [(nat_lit 949, Int.ofNat (nat_lit 1))]
theorem atom0590Coded_decode : atom0590 = SparsePolynomial.decodeCubic 21 atom0590Coded := by decide +kernel
theorem atom0590Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21357062899200 : Int) atom0590Coded) := by
  have h := atom0590_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0590Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0591 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0591 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0591 = ((g 2) * (g 3) * (g 5)) := by
  norm_num [atom0591, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0591_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23290231970304 : Int) atom0591) := by
  rw [SparsePolynomial.eval_scale, eval_atom0591]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0591Coded : CoefficientMerge.Poly := [(nat_lit 950, Int.ofNat (nat_lit 1))]
theorem atom0591Coded_decode : atom0591 = SparsePolynomial.decodeCubic 21 atom0591Coded := by decide +kernel
theorem atom0591Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23290231970304 : Int) atom0591Coded) := by
  have h := atom0591_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0591Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0592 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0592 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0592 = ((g 2) * (g 3) * (g 6)) := by
  norm_num [atom0592, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0592_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23147295091200 : Int) atom0592) := by
  rw [SparsePolynomial.eval_scale, eval_atom0592]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0592Coded : CoefficientMerge.Poly := [(nat_lit 951, Int.ofNat (nat_lit 1))]
theorem atom0592Coded_decode : atom0592 = SparsePolynomial.decodeCubic 21 atom0592Coded := by decide +kernel
theorem atom0592Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23147295091200 : Int) atom0592Coded) := by
  have h := atom0592_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0592Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0593 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0593 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0593 = ((g 2) * (g 3) * (g 7)) := by
  norm_num [atom0593, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0593_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25005300887808 : Int) atom0593) := by
  rw [SparsePolynomial.eval_scale, eval_atom0593]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0593Coded : CoefficientMerge.Poly := [(nat_lit 952, Int.ofNat (nat_lit 1))]
theorem atom0593Coded_decode : atom0593 = SparsePolynomial.decodeCubic 21 atom0593Coded := by decide +kernel
theorem atom0593Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25005300887808 : Int) atom0593Coded) := by
  have h := atom0593_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0593Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0594 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0594 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0594 = ((g 2) * (g 3) * (g 8)) := by
  norm_num [atom0594, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0594_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24960064550400 : Int) atom0594) := by
  rw [SparsePolynomial.eval_scale, eval_atom0594]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0594Coded : CoefficientMerge.Poly := [(nat_lit 953, Int.ofNat (nat_lit 1))]
theorem atom0594Coded_decode : atom0594 = SparsePolynomial.decodeCubic 21 atom0594Coded := by decide +kernel
theorem atom0594Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24960064550400 : Int) atom0594Coded) := by
  have h := atom0594_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0594Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0595 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0595 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0595 = ((g 2) * (g 3) * (g 9)) := by
  norm_num [atom0595, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0595_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24764837529600 : Int) atom0595) := by
  rw [SparsePolynomial.eval_scale, eval_atom0595]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0595Coded : CoefficientMerge.Poly := [(nat_lit 954, Int.ofNat (nat_lit 1))]
theorem atom0595Coded_decode : atom0595 = SparsePolynomial.decodeCubic 21 atom0595Coded := by decide +kernel
theorem atom0595Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24764837529600 : Int) atom0595Coded) := by
  have h := atom0595_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0595Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0596 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0596 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0596 = ((g 2) * (g 3) * (g 10)) := by
  norm_num [atom0596, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0596_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24569610508800 : Int) atom0596) := by
  rw [SparsePolynomial.eval_scale, eval_atom0596]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0596Coded : CoefficientMerge.Poly := [(nat_lit 955, Int.ofNat (nat_lit 1))]
theorem atom0596Coded_decode : atom0596 = SparsePolynomial.decodeCubic 21 atom0596Coded := by decide +kernel
theorem atom0596Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24569610508800 : Int) atom0596Coded) := by
  have h := atom0596_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0596Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0597 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0597 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0597 = ((g 2) * (g 3) * (g 11)) := by
  norm_num [atom0597, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0597_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23750536320000 : Int) atom0597) := by
  rw [SparsePolynomial.eval_scale, eval_atom0597]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0597Coded : CoefficientMerge.Poly := [(nat_lit 956, Int.ofNat (nat_lit 1))]
theorem atom0597Coded_decode : atom0597 = SparsePolynomial.decodeCubic 21 atom0597Coded := by decide +kernel
theorem atom0597Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23750536320000 : Int) atom0597Coded) := by
  have h := atom0597_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0597Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0598 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0598 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0598 = ((g 2) * (g 3) * (g 12)) := by
  norm_num [atom0598, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0598_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18832355852800 : Int) atom0598) := by
  rw [SparsePolynomial.eval_scale, eval_atom0598]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 3) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0598Coded : CoefficientMerge.Poly := [(nat_lit 957, Int.ofNat (nat_lit 1))]
theorem atom0598Coded_decode : atom0598 = SparsePolynomial.decodeCubic 21 atom0598Coded := by decide +kernel
theorem atom0598Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18832355852800 : Int) atom0598Coded) := by
  have h := atom0598_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0598Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0599 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0599 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0599 = ((g 2) * (g 3) * (g 13)) := by
  norm_num [atom0599, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0599_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17400333081600 : Int) atom0599) := by
  rw [SparsePolynomial.eval_scale, eval_atom0599]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 3) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0599Coded : CoefficientMerge.Poly := [(nat_lit 958, Int.ofNat (nat_lit 1))]
theorem atom0599Coded_decode : atom0599 = SparsePolynomial.decodeCubic 21 atom0599Coded := by decide +kernel
theorem atom0599Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17400333081600 : Int) atom0599Coded) := by
  have h := atom0599_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0599Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0600 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0600 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0600 = ((g 2) * (g 3) * (g 14)) := by
  norm_num [atom0600, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0600_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17723134195200 : Int) atom0600) := by
  rw [SparsePolynomial.eval_scale, eval_atom0600]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 3) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0600Coded : CoefficientMerge.Poly := [(nat_lit 959, Int.ofNat (nat_lit 1))]
theorem atom0600Coded_decode : atom0600 = SparsePolynomial.decodeCubic 21 atom0600Coded := by decide +kernel
theorem atom0600Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17723134195200 : Int) atom0600Coded) := by
  have h := atom0600_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0600Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0601 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0601 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0601 = ((g 2) * (g 3) * (g 15)) := by
  norm_num [atom0601, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0601_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26860145356800 : Int) atom0601) := by
  rw [SparsePolynomial.eval_scale, eval_atom0601]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 3) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0601Coded : CoefficientMerge.Poly := [(nat_lit 960, Int.ofNat (nat_lit 1))]
theorem atom0601Coded_decode : atom0601 = SparsePolynomial.decodeCubic 21 atom0601Coded := by decide +kernel
theorem atom0601Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (26860145356800 : Int) atom0601Coded) := by
  have h := atom0601_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0601Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0602 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0602 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0602 = ((g 2) * (g 3) * (g 16)) := by
  norm_num [atom0602, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0602_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11444942476800 : Int) atom0602) := by
  rw [SparsePolynomial.eval_scale, eval_atom0602]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 3) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0602Coded : CoefficientMerge.Poly := [(nat_lit 961, Int.ofNat (nat_lit 1))]
theorem atom0602Coded_decode : atom0602 = SparsePolynomial.decodeCubic 21 atom0602Coded := by decide +kernel
theorem atom0602Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11444942476800 : Int) atom0602Coded) := by
  have h := atom0602_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0602Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0603 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0603 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0603 = ((g 2) * (g 3) * (g 17)) := by
  norm_num [atom0603, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0603_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22692313728000 : Int) atom0603) := by
  rw [SparsePolynomial.eval_scale, eval_atom0603]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 3) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0603Coded : CoefficientMerge.Poly := [(nat_lit 962, Int.ofNat (nat_lit 1))]
theorem atom0603Coded_decode : atom0603 = SparsePolynomial.decodeCubic 21 atom0603Coded := by decide +kernel
theorem atom0603Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22692313728000 : Int) atom0603Coded) := by
  have h := atom0603_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0603Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0604 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0604 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0604 = ((g 2) * (g 3) * (g 18)) := by
  norm_num [atom0604, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0604_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10745217907200 : Int) atom0604) := by
  rw [SparsePolynomial.eval_scale, eval_atom0604]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 3) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0604Coded : CoefficientMerge.Poly := [(nat_lit 963, Int.ofNat (nat_lit 1))]
theorem atom0604Coded_decode : atom0604 = SparsePolynomial.decodeCubic 21 atom0604Coded := by decide +kernel
theorem atom0604Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10745217907200 : Int) atom0604Coded) := by
  have h := atom0604_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0604Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0605 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0605 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0605 = ((g 2) * (g 3) * (g 19)) := by
  norm_num [atom0605, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0605_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9566124019200 : Int) atom0605) := by
  rw [SparsePolynomial.eval_scale, eval_atom0605]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 3) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0605Coded : CoefficientMerge.Poly := [(nat_lit 964, Int.ofNat (nat_lit 1))]
theorem atom0605Coded_decode : atom0605 = SparsePolynomial.decodeCubic 21 atom0605Coded := by decide +kernel
theorem atom0605Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (9566124019200 : Int) atom0605Coded) := by
  have h := atom0605_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0605Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0606 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0606 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0606 = ((g 2) * (g 3) * (g 20)) := by
  norm_num [atom0606, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0606_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13057015104000 : Int) atom0606) := by
  rw [SparsePolynomial.eval_scale, eval_atom0606]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 3) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0606Coded : CoefficientMerge.Poly := [(nat_lit 965, Int.ofNat (nat_lit 1))]
theorem atom0606Coded_decode : atom0606 = SparsePolynomial.decodeCubic 21 atom0606Coded := by decide +kernel
theorem atom0606Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13057015104000 : Int) atom0606Coded) := by
  have h := atom0606_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0606Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0607 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0607 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0607 = ((g 2) * (g 4) * (g 4)) := by
  norm_num [atom0607, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0607_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11020661971200 : Int) atom0607) := by
  rw [SparsePolynomial.eval_scale, eval_atom0607]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 2) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0607Coded : CoefficientMerge.Poly := [(nat_lit 970, Int.ofNat (nat_lit 1))]
theorem atom0607Coded_decode : atom0607 = SparsePolynomial.decodeCubic 21 atom0607Coded := by decide +kernel
theorem atom0607Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11020661971200 : Int) atom0607Coded) := by
  have h := atom0607_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0607Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0608 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0608 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0608 = ((g 2) * (g 4) * (g 5)) := by
  norm_num [atom0608, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0608_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20212761945600 : Int) atom0608) := by
  rw [SparsePolynomial.eval_scale, eval_atom0608]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0608Coded : CoefficientMerge.Poly := [(nat_lit 971, Int.ofNat (nat_lit 1))]
theorem atom0608Coded_decode : atom0608 = SparsePolynomial.decodeCubic 21 atom0608Coded := by decide +kernel
theorem atom0608Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20212761945600 : Int) atom0608Coded) := by
  have h := atom0608_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0608Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0609 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0609 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0609 = ((g 2) * (g 4) * (g 6)) := by
  norm_num [atom0609, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0609_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20543623833600 : Int) atom0609) := by
  rw [SparsePolynomial.eval_scale, eval_atom0609]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0609Coded : CoefficientMerge.Poly := [(nat_lit 972, Int.ofNat (nat_lit 1))]
theorem atom0609Coded_decode : atom0609 = SparsePolynomial.decodeCubic 21 atom0609Coded := by decide +kernel
theorem atom0609Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20543623833600 : Int) atom0609Coded) := by
  have h := atom0609_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0609Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0610 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0610 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0610 = ((g 2) * (g 4) * (g 7)) := by
  norm_num [atom0610, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0610_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22906127179008 : Int) atom0610) := by
  rw [SparsePolynomial.eval_scale, eval_atom0610]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0610Coded : CoefficientMerge.Poly := [(nat_lit 973, Int.ofNat (nat_lit 1))]
theorem atom0610Coded_decode : atom0610 = SparsePolynomial.decodeCubic 21 atom0610Coded := by decide +kernel
theorem atom0610Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22906127179008 : Int) atom0610Coded) := by
  have h := atom0610_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0610Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0611 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0611 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0611 = ((g 2) * (g 4) * (g 8)) := by
  norm_num [atom0611, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0611_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23365388390400 : Int) atom0611) := by
  rw [SparsePolynomial.eval_scale, eval_atom0611]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0611Coded : CoefficientMerge.Poly := [(nat_lit 974, Int.ofNat (nat_lit 1))]
theorem atom0611Coded_decode : atom0611 = SparsePolynomial.decodeCubic 21 atom0611Coded := by decide +kernel
theorem atom0611Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23365388390400 : Int) atom0611Coded) := by
  have h := atom0611_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0611Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0612 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0612 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0612 = ((g 2) * (g 4) * (g 9)) := by
  norm_num [atom0612, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0612_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23674658918400 : Int) atom0612) := by
  rw [SparsePolynomial.eval_scale, eval_atom0612]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0612Coded : CoefficientMerge.Poly := [(nat_lit 975, Int.ofNat (nat_lit 1))]
theorem atom0612Coded_decode : atom0612 = SparsePolynomial.decodeCubic 21 atom0612Coded := by decide +kernel
theorem atom0612Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23674658918400 : Int) atom0612Coded) := by
  have h := atom0612_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0612Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0613 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0613 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0613 = ((g 2) * (g 4) * (g 10)) := by
  norm_num [atom0613, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0613_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23983929446400 : Int) atom0613) := by
  rw [SparsePolynomial.eval_scale, eval_atom0613]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0613Coded : CoefficientMerge.Poly := [(nat_lit 976, Int.ofNat (nat_lit 1))]
theorem atom0613Coded_decode : atom0613 = SparsePolynomial.decodeCubic 21 atom0613Coded := by decide +kernel
theorem atom0613Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23983929446400 : Int) atom0613Coded) := by
  have h := atom0613_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0613Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0614 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0614 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0614 = ((g 2) * (g 4) * (g 11)) := by
  norm_num [atom0614, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0614_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23669352806400 : Int) atom0614) := by
  rw [SparsePolynomial.eval_scale, eval_atom0614]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0614Coded : CoefficientMerge.Poly := [(nat_lit 977, Int.ofNat (nat_lit 1))]
theorem atom0614Coded_decode : atom0614 = SparsePolynomial.decodeCubic 21 atom0614Coded := by decide +kernel
theorem atom0614Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23669352806400 : Int) atom0614Coded) := by
  have h := atom0614_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0614Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0615 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0615 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0615 = ((g 2) * (g 4) * (g 12)) := by
  norm_num [atom0615, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0615_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20066681734400 : Int) atom0615) := by
  rw [SparsePolynomial.eval_scale, eval_atom0615]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0615Coded : CoefficientMerge.Poly := [(nat_lit 978, Int.ofNat (nat_lit 1))]
theorem atom0615Coded_decode : atom0615 = SparsePolynomial.decodeCubic 21 atom0615Coded := by decide +kernel
theorem atom0615Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20066681734400 : Int) atom0615Coded) := by
  have h := atom0615_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0615Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0616 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0616 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0616 = ((g 2) * (g 4) * (g 13)) := by
  norm_num [atom0616, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0616_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19784615558400 : Int) atom0616) := by
  rw [SparsePolynomial.eval_scale, eval_atom0616]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 4) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0616Coded : CoefficientMerge.Poly := [(nat_lit 979, Int.ofNat (nat_lit 1))]
theorem atom0616Coded_decode : atom0616 = SparsePolynomial.decodeCubic 21 atom0616Coded := by decide +kernel
theorem atom0616Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19784615558400 : Int) atom0616Coded) := by
  have h := atom0616_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0616Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0617 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0617 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0617 = ((g 2) * (g 4) * (g 14)) := by
  norm_num [atom0617, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0617_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20379961324800 : Int) atom0617) := by
  rw [SparsePolynomial.eval_scale, eval_atom0617]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0617Coded : CoefficientMerge.Poly := [(nat_lit 980, Int.ofNat (nat_lit 1))]
theorem atom0617Coded_decode : atom0617 = SparsePolynomial.decodeCubic 21 atom0617Coded := by decide +kernel
theorem atom0617Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20379961324800 : Int) atom0617Coded) := by
  have h := atom0617_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0617Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0618 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0618 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0618 = ((g 2) * (g 4) * (g 15)) := by
  norm_num [atom0618, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0618_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28796952038400 : Int) atom0618) := by
  rw [SparsePolynomial.eval_scale, eval_atom0618]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 4) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0618Coded : CoefficientMerge.Poly := [(nat_lit 981, Int.ofNat (nat_lit 1))]
theorem atom0618Coded_decode : atom0618 = SparsePolynomial.decodeCubic 21 atom0618Coded := by decide +kernel
theorem atom0618Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (28796952038400 : Int) atom0618Coded) := by
  have h := atom0618_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0618Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0619 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0619 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0619 = ((g 2) * (g 4) * (g 16)) := by
  norm_num [atom0619, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0619_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17572968856800 : Int) atom0619) := by
  rw [SparsePolynomial.eval_scale, eval_atom0619]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 4) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0619Coded : CoefficientMerge.Poly := [(nat_lit 982, Int.ofNat (nat_lit 1))]
theorem atom0619Coded_decode : atom0619 = SparsePolynomial.decodeCubic 21 atom0619Coded := by decide +kernel
theorem atom0619Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17572968856800 : Int) atom0619Coded) := by
  have h := atom0619_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0619Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0620 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0620 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0620 = ((g 2) * (g 4) * (g 17)) := by
  norm_num [atom0620, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0620_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25638115507200 : Int) atom0620) := by
  rw [SparsePolynomial.eval_scale, eval_atom0620]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 4) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0620Coded : CoefficientMerge.Poly := [(nat_lit 983, Int.ofNat (nat_lit 1))]
theorem atom0620Coded_decode : atom0620 = SparsePolynomial.decodeCubic 21 atom0620Coded := by decide +kernel
theorem atom0620Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25638115507200 : Int) atom0620Coded) := by
  have h := atom0620_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0620Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0621 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0621 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0621 = ((g 2) * (g 4) * (g 18)) := by
  norm_num [atom0621, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0621_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19002620196000 : Int) atom0621) := by
  rw [SparsePolynomial.eval_scale, eval_atom0621]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 4) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0621Coded : CoefficientMerge.Poly := [(nat_lit 984, Int.ofNat (nat_lit 1))]
theorem atom0621Coded_decode : atom0621 = SparsePolynomial.decodeCubic 21 atom0621Coded := by decide +kernel
theorem atom0621Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19002620196000 : Int) atom0621Coded) := by
  have h := atom0621_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0621Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0622 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0622 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0622 = ((g 2) * (g 4) * (g 19)) := by
  norm_num [atom0622, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0622_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19156772224800 : Int) atom0622) := by
  rw [SparsePolynomial.eval_scale, eval_atom0622]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 4) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0622Coded : CoefficientMerge.Poly := [(nat_lit 985, Int.ofNat (nat_lit 1))]
theorem atom0622Coded_decode : atom0622 = SparsePolynomial.decodeCubic 21 atom0622Coded := by decide +kernel
theorem atom0622Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19156772224800 : Int) atom0622Coded) := by
  have h := atom0622_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0622Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0623 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0623 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0623 = ((g 2) * (g 4) * (g 20)) := by
  norm_num [atom0623, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0623_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23980909226400 : Int) atom0623) := by
  rw [SparsePolynomial.eval_scale, eval_atom0623]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 4) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0623Coded : CoefficientMerge.Poly := [(nat_lit 986, Int.ofNat (nat_lit 1))]
theorem atom0623Coded_decode : atom0623 = SparsePolynomial.decodeCubic 21 atom0623Coded := by decide +kernel
theorem atom0623Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23980909226400 : Int) atom0623Coded) := by
  have h := atom0623_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0623Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0624 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0624 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0624 = ((g 2) * (g 5) * (g 5)) := by
  norm_num [atom0624, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0624_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14748338304000 : Int) atom0624) := by
  rw [SparsePolynomial.eval_scale, eval_atom0624]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0624Coded : CoefficientMerge.Poly := [(nat_lit 992, Int.ofNat (nat_lit 1))]
theorem atom0624Coded_decode : atom0624 = SparsePolynomial.decodeCubic 21 atom0624Coded := by decide +kernel
theorem atom0624Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14748338304000 : Int) atom0624Coded) := by
  have h := atom0624_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0624Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0625 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0625 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0625 = ((g 2) * (g 5) * (g 6)) := by
  norm_num [atom0625, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0625_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27897168096000 : Int) atom0625) := by
  rw [SparsePolynomial.eval_scale, eval_atom0625]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0625Coded : CoefficientMerge.Poly := [(nat_lit 993, Int.ofNat (nat_lit 1))]
theorem atom0625Coded_decode : atom0625 = SparsePolynomial.decodeCubic 21 atom0625Coded := by decide +kernel
theorem atom0625Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27897168096000 : Int) atom0625Coded) := by
  have h := atom0625_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0625Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0626 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0626 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0626 = ((g 2) * (g 5) * (g 7)) := by
  norm_num [atom0626, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0626_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24726406984704 : Int) atom0626) := by
  rw [SparsePolynomial.eval_scale, eval_atom0626]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0626Coded : CoefficientMerge.Poly := [(nat_lit 994, Int.ofNat (nat_lit 1))]
theorem atom0626Coded_decode : atom0626 = SparsePolynomial.decodeCubic 21 atom0626Coded := by decide +kernel
theorem atom0626Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24726406984704 : Int) atom0626Coded) := by
  have h := atom0626_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0626Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0627 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0627 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0627 = ((g 2) * (g 5) * (g 8)) := by
  norm_num [atom0627, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0627_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24753468155904 : Int) atom0627) := by
  rw [SparsePolynomial.eval_scale, eval_atom0627]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0627Coded : CoefficientMerge.Poly := [(nat_lit 995, Int.ofNat (nat_lit 1))]
theorem atom0627Coded_decode : atom0627 = SparsePolynomial.decodeCubic 21 atom0627Coded := by decide +kernel
theorem atom0627Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24753468155904 : Int) atom0627Coded) := by
  have h := atom0627_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0627Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0628 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0628 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0628 = ((g 2) * (g 5) * (g 9)) := by
  norm_num [atom0628, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0628_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26296921384704 : Int) atom0628) := by
  rw [SparsePolynomial.eval_scale, eval_atom0628]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0628Coded : CoefficientMerge.Poly := [(nat_lit 996, Int.ofNat (nat_lit 1))]
theorem atom0628Coded_decode : atom0628 = SparsePolynomial.decodeCubic 21 atom0628Coded := by decide +kernel
theorem atom0628Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (26296921384704 : Int) atom0628Coded) := by
  have h := atom0628_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0628Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0629 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0629 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0629 = ((g 2) * (g 5) * (g 10)) := by
  norm_num [atom0629, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0629_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26381004309504 : Int) atom0629) := by
  rw [SparsePolynomial.eval_scale, eval_atom0629]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0629Coded : CoefficientMerge.Poly := [(nat_lit 997, Int.ofNat (nat_lit 1))]
theorem atom0629Coded_decode : atom0629 = SparsePolynomial.decodeCubic 21 atom0629Coded := by decide +kernel
theorem atom0629Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (26381004309504 : Int) atom0629Coded) := by
  have h := atom0629_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0629Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0630 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0630 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0630 = ((g 2) * (g 5) * (g 11)) := by
  norm_num [atom0630, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0630_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26570925218304 : Int) atom0630) := by
  rw [SparsePolynomial.eval_scale, eval_atom0630]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0630Coded : CoefficientMerge.Poly := [(nat_lit 998, Int.ofNat (nat_lit 1))]
theorem atom0630Coded_decode : atom0630 = SparsePolynomial.decodeCubic 21 atom0630Coded := by decide +kernel
theorem atom0630Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (26570925218304 : Int) atom0630Coded) := by
  have h := atom0630_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0630Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0631 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0631 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0631 = ((g 2) * (g 5) * (g 12)) := by
  norm_num [atom0631, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0631_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24050700994304 : Int) atom0631) := by
  rw [SparsePolynomial.eval_scale, eval_atom0631]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0631Coded : CoefficientMerge.Poly := [(nat_lit 999, Int.ofNat (nat_lit 1))]
theorem atom0631Coded_decode : atom0631 = SparsePolynomial.decodeCubic 21 atom0631Coded := by decide +kernel
theorem atom0631Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24050700994304 : Int) atom0631Coded) := by
  have h := atom0631_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0631Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0632 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0632 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0632 = ((g 2) * (g 5) * (g 13)) := by
  norm_num [atom0632, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0632_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23597569557504 : Int) atom0632) := by
  rw [SparsePolynomial.eval_scale, eval_atom0632]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0632Coded : CoefficientMerge.Poly := [(nat_lit 1000, Int.ofNat (nat_lit 1))]
theorem atom0632Coded_decode : atom0632 = SparsePolynomial.decodeCubic 21 atom0632Coded := by decide +kernel
theorem atom0632Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23597569557504 : Int) atom0632Coded) := by
  have h := atom0632_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0632Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0633 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0633 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0633 = ((g 2) * (g 5) * (g 14)) := by
  norm_num [atom0633, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0633_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24283763541504 : Int) atom0633) := by
  rw [SparsePolynomial.eval_scale, eval_atom0633]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0633Coded : CoefficientMerge.Poly := [(nat_lit 1001, Int.ofNat (nat_lit 1))]
theorem atom0633Coded_decode : atom0633 = SparsePolynomial.decodeCubic 21 atom0633Coded := by decide +kernel
theorem atom0633Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24283763541504 : Int) atom0633Coded) := by
  have h := atom0633_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0633Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0634 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0634 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0634 = ((g 2) * (g 5) * (g 15)) := by
  norm_num [atom0634, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0634_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33716514645504 : Int) atom0634) := by
  rw [SparsePolynomial.eval_scale, eval_atom0634]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 5) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0634Coded : CoefficientMerge.Poly := [(nat_lit 1002, Int.ofNat (nat_lit 1))]
theorem atom0634Coded_decode : atom0634 = SparsePolynomial.decodeCubic 21 atom0634Coded := by decide +kernel
theorem atom0634Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (33716514645504 : Int) atom0634Coded) := by
  have h := atom0634_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0634Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0635 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0635 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0635 = ((g 2) * (g 5) * (g 16)) := by
  norm_num [atom0635, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0635_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22622798557440 : Int) atom0635) := by
  rw [SparsePolynomial.eval_scale, eval_atom0635]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 5) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0635Coded : CoefficientMerge.Poly := [(nat_lit 1003, Int.ofNat (nat_lit 1))]
theorem atom0635Coded_decode : atom0635 = SparsePolynomial.decodeCubic 21 atom0635Coded := by decide +kernel
theorem atom0635Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22622798557440 : Int) atom0635Coded) := by
  have h := atom0635_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0635Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0636 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0636 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0636 = ((g 2) * (g 5) * (g 17)) := by
  norm_num [atom0636, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0636_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31566673211904 : Int) atom0636) := by
  rw [SparsePolynomial.eval_scale, eval_atom0636]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 5) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0636Coded : CoefficientMerge.Poly := [(nat_lit 1004, Int.ofNat (nat_lit 1))]
theorem atom0636Coded_decode : atom0636 = SparsePolynomial.decodeCubic 21 atom0636Coded := by decide +kernel
theorem atom0636Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31566673211904 : Int) atom0636Coded) := by
  have h := atom0636_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0636Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0637 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0637 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0637 = ((g 2) * (g 5) * (g 18)) := by
  norm_num [atom0637, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0637_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26162808429312 : Int) atom0637) := by
  rw [SparsePolynomial.eval_scale, eval_atom0637]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 5) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0637Coded : CoefficientMerge.Poly := [(nat_lit 1005, Int.ofNat (nat_lit 1))]
theorem atom0637Coded_decode : atom0637 = SparsePolynomial.decodeCubic 21 atom0637Coded := by decide +kernel
theorem atom0637Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (26162808429312 : Int) atom0637Coded) := by
  have h := atom0637_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0637Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0638 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0638 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0638 = ((g 2) * (g 5) * (g 19)) := by
  norm_num [atom0638, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0638_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27693583407360 : Int) atom0638) := by
  rw [SparsePolynomial.eval_scale, eval_atom0638]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 5) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0638Coded : CoefficientMerge.Poly := [(nat_lit 1006, Int.ofNat (nat_lit 1))]
theorem atom0638Coded_decode : atom0638 = SparsePolynomial.decodeCubic 21 atom0638Coded := by decide +kernel
theorem atom0638Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27693583407360 : Int) atom0638Coded) := by
  have h := atom0638_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0638Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0639 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0639 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0639 = ((g 2) * (g 5) * (g 20)) := by
  norm_num [atom0639, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0639_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33894343358208 : Int) atom0639) := by
  rw [SparsePolynomial.eval_scale, eval_atom0639]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 5) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0639Coded : CoefficientMerge.Poly := [(nat_lit 1007, Int.ofNat (nat_lit 1))]
theorem atom0639Coded_decode : atom0639 = SparsePolynomial.decodeCubic 21 atom0639Coded := by decide +kernel
theorem atom0639Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (33894343358208 : Int) atom0639Coded) := by
  have h := atom0639_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0639Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0640 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0640 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0640 = ((g 2) * (g 6) * (g 6)) := by
  norm_num [atom0640, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0640_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18705068121600 : Int) atom0640) := by
  rw [SparsePolynomial.eval_scale, eval_atom0640]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0640Coded : CoefficientMerge.Poly := [(nat_lit 1014, Int.ofNat (nat_lit 1))]
theorem atom0640Coded_decode : atom0640 = SparsePolynomial.decodeCubic 21 atom0640Coded := by decide +kernel
theorem atom0640Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18705068121600 : Int) atom0640Coded) := by
  have h := atom0640_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0640Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0641 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0641 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0641 = ((g 2) * (g 6) * (g 7)) := by
  norm_num [atom0641, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0641_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34252905717504 : Int) atom0641) := by
  rw [SparsePolynomial.eval_scale, eval_atom0641]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0641Coded : CoefficientMerge.Poly := [(nat_lit 1015, Int.ofNat (nat_lit 1))]
theorem atom0641Coded_decode : atom0641 = SparsePolynomial.decodeCubic 21 atom0641Coded := by decide +kernel
theorem atom0641Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (34252905717504 : Int) atom0641Coded) := by
  have h := atom0641_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0641Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0642 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0642 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0642 = ((g 2) * (g 6) * (g 8)) := by
  norm_num [atom0642, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0642_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30315115958400 : Int) atom0642) := by
  rw [SparsePolynomial.eval_scale, eval_atom0642]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0642Coded : CoefficientMerge.Poly := [(nat_lit 1016, Int.ofNat (nat_lit 1))]
theorem atom0642Coded_decode : atom0642 = SparsePolynomial.decodeCubic 21 atom0642Coded := by decide +kernel
theorem atom0642Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30315115958400 : Int) atom0642Coded) := by
  have h := atom0642_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0642Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0643 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0643 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0643 = ((g 2) * (g 6) * (g 9)) := by
  norm_num [atom0643, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0643_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27620120102400 : Int) atom0643) := by
  rw [SparsePolynomial.eval_scale, eval_atom0643]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0643Coded : CoefficientMerge.Poly := [(nat_lit 1017, Int.ofNat (nat_lit 1))]
theorem atom0643Coded_decode : atom0643 = SparsePolynomial.decodeCubic 21 atom0643Coded := by decide +kernel
theorem atom0643Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27620120102400 : Int) atom0643Coded) := by
  have h := atom0643_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0643Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0644 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0644 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0644 = ((g 2) * (g 6) * (g 10)) := by
  norm_num [atom0644, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0644_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27885899462400 : Int) atom0644) := by
  rw [SparsePolynomial.eval_scale, eval_atom0644]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0644Coded : CoefficientMerge.Poly := [(nat_lit 1018, Int.ofNat (nat_lit 1))]
theorem atom0644Coded_decode : atom0644 = SparsePolynomial.decodeCubic 21 atom0644Coded := by decide +kernel
theorem atom0644Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27885899462400 : Int) atom0644Coded) := by
  have h := atom0644_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0644Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0645 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0645 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0645 = ((g 2) * (g 6) * (g 11)) := by
  norm_num [atom0645, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0645_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27580741171200 : Int) atom0645) := by
  rw [SparsePolynomial.eval_scale, eval_atom0645]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0645Coded : CoefficientMerge.Poly := [(nat_lit 1019, Int.ofNat (nat_lit 1))]
theorem atom0645Coded_decode : atom0645 = SparsePolynomial.decodeCubic 21 atom0645Coded := by decide +kernel
theorem atom0645Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27580741171200 : Int) atom0645Coded) := by
  have h := atom0645_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0645Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0646 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0646 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0646 = ((g 2) * (g 6) * (g 12)) := by
  norm_num [atom0646, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0646_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25569126732800 : Int) atom0646) := by
  rw [SparsePolynomial.eval_scale, eval_atom0646]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0646Coded : CoefficientMerge.Poly := [(nat_lit 1020, Int.ofNat (nat_lit 1))]
theorem atom0646Coded_decode : atom0646 = SparsePolynomial.decodeCubic 21 atom0646Coded := by decide +kernel
theorem atom0646Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25569126732800 : Int) atom0646Coded) := by
  have h := atom0646_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0646Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0647 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0647 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0647 = ((g 2) * (g 6) * (g 13)) := by
  norm_num [atom0647, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0647_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25300591142400 : Int) atom0647) := by
  rw [SparsePolynomial.eval_scale, eval_atom0647]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0647Coded : CoefficientMerge.Poly := [(nat_lit 1021, Int.ofNat (nat_lit 1))]
theorem atom0647Coded_decode : atom0647 = SparsePolynomial.decodeCubic 21 atom0647Coded := by decide +kernel
theorem atom0647Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25300591142400 : Int) atom0647Coded) := by
  have h := atom0647_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0647Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0648 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0648 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0648 = ((g 2) * (g 6) * (g 14)) := by
  norm_num [atom0648, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0648_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25909467494400 : Int) atom0648) := by
  rw [SparsePolynomial.eval_scale, eval_atom0648]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0648Coded : CoefficientMerge.Poly := [(nat_lit 1022, Int.ofNat (nat_lit 1))]
theorem atom0648Coded_decode : atom0648 = SparsePolynomial.decodeCubic 21 atom0648Coded := by decide +kernel
theorem atom0648Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25909467494400 : Int) atom0648Coded) := by
  have h := atom0648_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0648Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0649 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0649 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0649 = ((g 2) * (g 6) * (g 15)) := by
  norm_num [atom0649, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0649_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36559971302400 : Int) atom0649) := by
  rw [SparsePolynomial.eval_scale, eval_atom0649]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0649Coded : CoefficientMerge.Poly := [(nat_lit 1023, Int.ofNat (nat_lit 1))]
theorem atom0649Coded_decode : atom0649 = SparsePolynomial.decodeCubic 21 atom0649Coded := by decide +kernel
theorem atom0649Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36559971302400 : Int) atom0649Coded) := by
  have h := atom0649_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0649Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0650 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0650 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0650 = ((g 2) * (g 6) * (g 16)) := by
  norm_num [atom0650, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0650_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25733446502400 : Int) atom0650) := by
  rw [SparsePolynomial.eval_scale, eval_atom0650]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 6) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0650Coded : CoefficientMerge.Poly := [(nat_lit 1024, Int.ofNat (nat_lit 1))]
theorem atom0650Coded_decode : atom0650 = SparsePolynomial.decodeCubic 21 atom0650Coded := by decide +kernel
theorem atom0650Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25733446502400 : Int) atom0650Coded) := by
  have h := atom0650_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0650Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0651 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0651 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0651 = ((g 2) * (g 6) * (g 17)) := by
  norm_num [atom0651, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0651_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35419124966400 : Int) atom0651) := by
  rw [SparsePolynomial.eval_scale, eval_atom0651]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0651Coded : CoefficientMerge.Poly := [(nat_lit 1025, Int.ofNat (nat_lit 1))]
theorem atom0651Coded_decode : atom0651 = SparsePolynomial.decodeCubic 21 atom0651Coded := by decide +kernel
theorem atom0651Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35419124966400 : Int) atom0651Coded) := by
  have h := atom0651_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0651Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0652 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0652 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0652 = ((g 2) * (g 6) * (g 18)) := by
  norm_num [atom0652, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0652_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32397979622400 : Int) atom0652) := by
  rw [SparsePolynomial.eval_scale, eval_atom0652]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 6) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0652Coded : CoefficientMerge.Poly := [(nat_lit 1026, Int.ofNat (nat_lit 1))]
theorem atom0652Coded_decode : atom0652 = SparsePolynomial.decodeCubic 21 atom0652Coded := by decide +kernel
theorem atom0652Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32397979622400 : Int) atom0652Coded) := by
  have h := atom0652_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0652Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0653 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0653 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0653 = ((g 2) * (g 6) * (g 19)) := by
  norm_num [atom0653, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0653_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36037542643200 : Int) atom0653) := by
  rw [SparsePolynomial.eval_scale, eval_atom0653]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 6) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0653Coded : CoefficientMerge.Poly := [(nat_lit 1027, Int.ofNat (nat_lit 1))]
theorem atom0653Coded_decode : atom0653 = SparsePolynomial.decodeCubic 21 atom0653Coded := by decide +kernel
theorem atom0653Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36037542643200 : Int) atom0653Coded) := by
  have h := atom0653_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0653Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0654 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0654 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0654 = ((g 2) * (g 6) * (g 20)) := by
  norm_num [atom0654, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0654_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44347090636800 : Int) atom0654) := by
  rw [SparsePolynomial.eval_scale, eval_atom0654]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 6) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0654Coded : CoefficientMerge.Poly := [(nat_lit 1028, Int.ofNat (nat_lit 1))]
theorem atom0654Coded_decode : atom0654 = SparsePolynomial.decodeCubic 21 atom0654Coded := by decide +kernel
theorem atom0654Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (44347090636800 : Int) atom0654Coded) := by
  have h := atom0654_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0654Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0655 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0655 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0655 = ((g 2) * (g 7) * (g 7)) := by
  norm_num [atom0655, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0655_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20414982530304 : Int) atom0655) := by
  rw [SparsePolynomial.eval_scale, eval_atom0655]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0655Coded : CoefficientMerge.Poly := [(nat_lit 1036, Int.ofNat (nat_lit 1))]
theorem atom0655Coded_decode : atom0655 = SparsePolynomial.decodeCubic 21 atom0655Coded := by decide +kernel
theorem atom0655Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20414982530304 : Int) atom0655Coded) := by
  have h := atom0655_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0655Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block009 : CoefficientMerge.Poly := [(nat_lit 931, Int.ofNat (nat_lit 13552237298304)), (nat_lit 932, Int.ofNat (nat_lit 13277370355200)), (nat_lit 933, Int.ofNat (nat_lit 12927508070400)), (nat_lit 934, Int.ofNat (nat_lit 12577645785600)), (nat_lit 935, Int.ofNat (nat_lit 11915859916800)), (nat_lit 936, Int.ofNat (nat_lit 9204520908800)), (nat_lit 937, Int.ofNat (nat_lit 8236260748800)), (nat_lit 938, Int.ofNat (nat_lit 8145412531200)), (nat_lit 939, Int.ofNat (nat_lit 12461669337600)), (nat_lit 940, Int.ofNat (nat_lit 3160358208000)), (nat_lit 941, Int.ofNat (nat_lit 9873255974400)), (nat_lit 942, Int.ofNat (nat_lit 1606273804800)), (nat_lit 944, Int.ofNat (nat_lit 3063711168000)), (nat_lit 948, Int.ofNat (nat_lit 11203324876800)), (nat_lit 949, Int.ofNat (nat_lit 21357062899200)), (nat_lit 950, Int.ofNat (nat_lit 23290231970304)), (nat_lit 951, Int.ofNat (nat_lit 23147295091200)), (nat_lit 952, Int.ofNat (nat_lit 25005300887808)), (nat_lit 953, Int.ofNat (nat_lit 24960064550400)), (nat_lit 954, Int.ofNat (nat_lit 24764837529600)), (nat_lit 955, Int.ofNat (nat_lit 24569610508800)), (nat_lit 956, Int.ofNat (nat_lit 23750536320000)), (nat_lit 957, Int.ofNat (nat_lit 18832355852800)), (nat_lit 958, Int.ofNat (nat_lit 17400333081600)), (nat_lit 959, Int.ofNat (nat_lit 17723134195200)), (nat_lit 960, Int.ofNat (nat_lit 26860145356800)), (nat_lit 961, Int.ofNat (nat_lit 11444942476800)), (nat_lit 962, Int.ofNat (nat_lit 22692313728000)), (nat_lit 963, Int.ofNat (nat_lit 10745217907200)), (nat_lit 964, Int.ofNat (nat_lit 9566124019200)), (nat_lit 965, Int.ofNat (nat_lit 13057015104000)), (nat_lit 970, Int.ofNat (nat_lit 11020661971200)), (nat_lit 971, Int.ofNat (nat_lit 20212761945600)), (nat_lit 972, Int.ofNat (nat_lit 20543623833600)), (nat_lit 973, Int.ofNat (nat_lit 22906127179008)), (nat_lit 974, Int.ofNat (nat_lit 23365388390400)), (nat_lit 975, Int.ofNat (nat_lit 23674658918400)), (nat_lit 976, Int.ofNat (nat_lit 23983929446400)), (nat_lit 977, Int.ofNat (nat_lit 23669352806400)), (nat_lit 978, Int.ofNat (nat_lit 20066681734400)), (nat_lit 979, Int.ofNat (nat_lit 19784615558400)), (nat_lit 980, Int.ofNat (nat_lit 20379961324800)), (nat_lit 981, Int.ofNat (nat_lit 28796952038400)), (nat_lit 982, Int.ofNat (nat_lit 17572968856800)), (nat_lit 983, Int.ofNat (nat_lit 25638115507200)), (nat_lit 984, Int.ofNat (nat_lit 19002620196000)), (nat_lit 985, Int.ofNat (nat_lit 19156772224800)), (nat_lit 986, Int.ofNat (nat_lit 23980909226400)), (nat_lit 992, Int.ofNat (nat_lit 14748338304000)), (nat_lit 993, Int.ofNat (nat_lit 27897168096000)), (nat_lit 994, Int.ofNat (nat_lit 24726406984704)), (nat_lit 995, Int.ofNat (nat_lit 24753468155904)), (nat_lit 996, Int.ofNat (nat_lit 26296921384704)), (nat_lit 997, Int.ofNat (nat_lit 26381004309504)), (nat_lit 998, Int.ofNat (nat_lit 26570925218304)), (nat_lit 999, Int.ofNat (nat_lit 24050700994304)), (nat_lit 1000, Int.ofNat (nat_lit 23597569557504)), (nat_lit 1001, Int.ofNat (nat_lit 24283763541504)), (nat_lit 1002, Int.ofNat (nat_lit 33716514645504)), (nat_lit 1003, Int.ofNat (nat_lit 22622798557440)), (nat_lit 1004, Int.ofNat (nat_lit 31566673211904)), (nat_lit 1005, Int.ofNat (nat_lit 26162808429312)), (nat_lit 1006, Int.ofNat (nat_lit 27693583407360)), (nat_lit 1007, Int.ofNat (nat_lit 33894343358208)), (nat_lit 1014, Int.ofNat (nat_lit 18705068121600)), (nat_lit 1015, Int.ofNat (nat_lit 34252905717504)), (nat_lit 1016, Int.ofNat (nat_lit 30315115958400)), (nat_lit 1017, Int.ofNat (nat_lit 27620120102400)), (nat_lit 1018, Int.ofNat (nat_lit 27885899462400)), (nat_lit 1019, Int.ofNat (nat_lit 27580741171200)), (nat_lit 1020, Int.ofNat (nat_lit 25569126732800)), (nat_lit 1021, Int.ofNat (nat_lit 25300591142400)), (nat_lit 1022, Int.ofNat (nat_lit 25909467494400)), (nat_lit 1023, Int.ofNat (nat_lit 36559971302400)), (nat_lit 1024, Int.ofNat (nat_lit 25733446502400)), (nat_lit 1025, Int.ofNat (nat_lit 35419124966400)), (nat_lit 1026, Int.ofNat (nat_lit 32397979622400)), (nat_lit 1027, Int.ofNat (nat_lit 36037542643200)), (nat_lit 1028, Int.ofNat (nat_lit 44347090636800)), (nat_lit 1036, Int.ofNat (nat_lit 20414982530304))]
def block009_data_flat000 : CoefficientMerge.Poly := [(nat_lit 931, Int.ofNat (nat_lit 13552237298304))]
theorem block009_data_flat000_step : block009_data_flat000 = (CoefficientMerge.scale (13552237298304 : Int) atom0576Coded) := by decide +kernel
theorem block009_data_flat000_original : block009_data_flat000 = (CoefficientMerge.scale (13552237298304 : Int) atom0576Coded) := by
  rw [block009_data_flat000_step]
def block009_data_flat001 : CoefficientMerge.Poly := [(nat_lit 932, Int.ofNat (nat_lit 13277370355200))]
theorem block009_data_flat001_step : block009_data_flat001 = (CoefficientMerge.scale (13277370355200 : Int) atom0577Coded) := by decide +kernel
theorem block009_data_flat001_original : block009_data_flat001 = (CoefficientMerge.scale (13277370355200 : Int) atom0577Coded) := by
  rw [block009_data_flat001_step]
def block009_data_flat002 : CoefficientMerge.Poly := [(nat_lit 931, Int.ofNat (nat_lit 13552237298304)), (nat_lit 932, Int.ofNat (nat_lit 13277370355200))]
theorem block009_data_flat002_step : block009_data_flat002 = (CoefficientMerge.fastMerge block009_data_flat000 block009_data_flat001) := by decide +kernel
theorem block009_data_flat002_original : block009_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (13552237298304 : Int) atom0576Coded) (CoefficientMerge.scale (13277370355200 : Int) atom0577Coded)) := by
  rw [block009_data_flat002_step, block009_data_flat000_original, block009_data_flat001_original]
def block009_data_flat003 : CoefficientMerge.Poly := [(nat_lit 933, Int.ofNat (nat_lit 12927508070400))]
theorem block009_data_flat003_step : block009_data_flat003 = (CoefficientMerge.scale (12927508070400 : Int) atom0578Coded) := by decide +kernel
theorem block009_data_flat003_original : block009_data_flat003 = (CoefficientMerge.scale (12927508070400 : Int) atom0578Coded) := by
  rw [block009_data_flat003_step]
def block009_data_flat004 : CoefficientMerge.Poly := [(nat_lit 934, Int.ofNat (nat_lit 12577645785600))]
theorem block009_data_flat004_step : block009_data_flat004 = (CoefficientMerge.scale (12577645785600 : Int) atom0579Coded) := by decide +kernel
theorem block009_data_flat004_original : block009_data_flat004 = (CoefficientMerge.scale (12577645785600 : Int) atom0579Coded) := by
  rw [block009_data_flat004_step]
def block009_data_flat005 : CoefficientMerge.Poly := [(nat_lit 935, Int.ofNat (nat_lit 11915859916800))]
theorem block009_data_flat005_step : block009_data_flat005 = (CoefficientMerge.scale (11915859916800 : Int) atom0580Coded) := by decide +kernel
theorem block009_data_flat005_original : block009_data_flat005 = (CoefficientMerge.scale (11915859916800 : Int) atom0580Coded) := by
  rw [block009_data_flat005_step]
def block009_data_flat006 : CoefficientMerge.Poly := [(nat_lit 934, Int.ofNat (nat_lit 12577645785600)), (nat_lit 935, Int.ofNat (nat_lit 11915859916800))]
theorem block009_data_flat006_step : block009_data_flat006 = (CoefficientMerge.fastMerge block009_data_flat004 block009_data_flat005) := by decide +kernel
theorem block009_data_flat006_original : block009_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (12577645785600 : Int) atom0579Coded) (CoefficientMerge.scale (11915859916800 : Int) atom0580Coded)) := by
  rw [block009_data_flat006_step, block009_data_flat004_original, block009_data_flat005_original]
def block009_data_flat007 : CoefficientMerge.Poly := [(nat_lit 933, Int.ofNat (nat_lit 12927508070400)), (nat_lit 934, Int.ofNat (nat_lit 12577645785600)), (nat_lit 935, Int.ofNat (nat_lit 11915859916800))]
theorem block009_data_flat007_step : block009_data_flat007 = (CoefficientMerge.fastMerge block009_data_flat003 block009_data_flat006) := by decide +kernel
theorem block009_data_flat007_original : block009_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (12927508070400 : Int) atom0578Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12577645785600 : Int) atom0579Coded) (CoefficientMerge.scale (11915859916800 : Int) atom0580Coded))) := by
  rw [block009_data_flat007_step, block009_data_flat003_original, block009_data_flat006_original]
def block009_data_flat008 : CoefficientMerge.Poly := [(nat_lit 931, Int.ofNat (nat_lit 13552237298304)), (nat_lit 932, Int.ofNat (nat_lit 13277370355200)), (nat_lit 933, Int.ofNat (nat_lit 12927508070400)), (nat_lit 934, Int.ofNat (nat_lit 12577645785600)), (nat_lit 935, Int.ofNat (nat_lit 11915859916800))]
theorem block009_data_flat008_step : block009_data_flat008 = (CoefficientMerge.fastMerge block009_data_flat002 block009_data_flat007) := by decide +kernel
theorem block009_data_flat008_original : block009_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13552237298304 : Int) atom0576Coded) (CoefficientMerge.scale (13277370355200 : Int) atom0577Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12927508070400 : Int) atom0578Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12577645785600 : Int) atom0579Coded) (CoefficientMerge.scale (11915859916800 : Int) atom0580Coded)))) := by
  rw [block009_data_flat008_step, block009_data_flat002_original, block009_data_flat007_original]
def block009_data_flat009 : CoefficientMerge.Poly := [(nat_lit 936, Int.ofNat (nat_lit 9204520908800))]
theorem block009_data_flat009_step : block009_data_flat009 = (CoefficientMerge.scale (9204520908800 : Int) atom0581Coded) := by decide +kernel
theorem block009_data_flat009_original : block009_data_flat009 = (CoefficientMerge.scale (9204520908800 : Int) atom0581Coded) := by
  rw [block009_data_flat009_step]
def block009_data_flat010 : CoefficientMerge.Poly := [(nat_lit 937, Int.ofNat (nat_lit 8236260748800))]
theorem block009_data_flat010_step : block009_data_flat010 = (CoefficientMerge.scale (8236260748800 : Int) atom0582Coded) := by decide +kernel
theorem block009_data_flat010_original : block009_data_flat010 = (CoefficientMerge.scale (8236260748800 : Int) atom0582Coded) := by
  rw [block009_data_flat010_step]
def block009_data_flat011 : CoefficientMerge.Poly := [(nat_lit 936, Int.ofNat (nat_lit 9204520908800)), (nat_lit 937, Int.ofNat (nat_lit 8236260748800))]
theorem block009_data_flat011_step : block009_data_flat011 = (CoefficientMerge.fastMerge block009_data_flat009 block009_data_flat010) := by decide +kernel
theorem block009_data_flat011_original : block009_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (9204520908800 : Int) atom0581Coded) (CoefficientMerge.scale (8236260748800 : Int) atom0582Coded)) := by
  rw [block009_data_flat011_step, block009_data_flat009_original, block009_data_flat010_original]
def block009_data_flat012 : CoefficientMerge.Poly := [(nat_lit 938, Int.ofNat (nat_lit 8145412531200))]
theorem block009_data_flat012_step : block009_data_flat012 = (CoefficientMerge.scale (8145412531200 : Int) atom0583Coded) := by decide +kernel
theorem block009_data_flat012_original : block009_data_flat012 = (CoefficientMerge.scale (8145412531200 : Int) atom0583Coded) := by
  rw [block009_data_flat012_step]
def block009_data_flat013 : CoefficientMerge.Poly := [(nat_lit 939, Int.ofNat (nat_lit 12461669337600))]
theorem block009_data_flat013_step : block009_data_flat013 = (CoefficientMerge.scale (12461669337600 : Int) atom0584Coded) := by decide +kernel
theorem block009_data_flat013_original : block009_data_flat013 = (CoefficientMerge.scale (12461669337600 : Int) atom0584Coded) := by
  rw [block009_data_flat013_step]
def block009_data_flat014 : CoefficientMerge.Poly := [(nat_lit 940, Int.ofNat (nat_lit 3160358208000))]
theorem block009_data_flat014_step : block009_data_flat014 = (CoefficientMerge.scale (3160358208000 : Int) atom0585Coded) := by decide +kernel
theorem block009_data_flat014_original : block009_data_flat014 = (CoefficientMerge.scale (3160358208000 : Int) atom0585Coded) := by
  rw [block009_data_flat014_step]
def block009_data_flat015 : CoefficientMerge.Poly := [(nat_lit 939, Int.ofNat (nat_lit 12461669337600)), (nat_lit 940, Int.ofNat (nat_lit 3160358208000))]
theorem block009_data_flat015_step : block009_data_flat015 = (CoefficientMerge.fastMerge block009_data_flat013 block009_data_flat014) := by decide +kernel
theorem block009_data_flat015_original : block009_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (12461669337600 : Int) atom0584Coded) (CoefficientMerge.scale (3160358208000 : Int) atom0585Coded)) := by
  rw [block009_data_flat015_step, block009_data_flat013_original, block009_data_flat014_original]
def block009_data_flat016 : CoefficientMerge.Poly := [(nat_lit 938, Int.ofNat (nat_lit 8145412531200)), (nat_lit 939, Int.ofNat (nat_lit 12461669337600)), (nat_lit 940, Int.ofNat (nat_lit 3160358208000))]
theorem block009_data_flat016_step : block009_data_flat016 = (CoefficientMerge.fastMerge block009_data_flat012 block009_data_flat015) := by decide +kernel
theorem block009_data_flat016_original : block009_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8145412531200 : Int) atom0583Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12461669337600 : Int) atom0584Coded) (CoefficientMerge.scale (3160358208000 : Int) atom0585Coded))) := by
  rw [block009_data_flat016_step, block009_data_flat012_original, block009_data_flat015_original]
def block009_data_flat017 : CoefficientMerge.Poly := [(nat_lit 936, Int.ofNat (nat_lit 9204520908800)), (nat_lit 937, Int.ofNat (nat_lit 8236260748800)), (nat_lit 938, Int.ofNat (nat_lit 8145412531200)), (nat_lit 939, Int.ofNat (nat_lit 12461669337600)), (nat_lit 940, Int.ofNat (nat_lit 3160358208000))]
theorem block009_data_flat017_step : block009_data_flat017 = (CoefficientMerge.fastMerge block009_data_flat011 block009_data_flat016) := by decide +kernel
theorem block009_data_flat017_original : block009_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9204520908800 : Int) atom0581Coded) (CoefficientMerge.scale (8236260748800 : Int) atom0582Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8145412531200 : Int) atom0583Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12461669337600 : Int) atom0584Coded) (CoefficientMerge.scale (3160358208000 : Int) atom0585Coded)))) := by
  rw [block009_data_flat017_step, block009_data_flat011_original, block009_data_flat016_original]
def block009_data_flat018 : CoefficientMerge.Poly := [(nat_lit 931, Int.ofNat (nat_lit 13552237298304)), (nat_lit 932, Int.ofNat (nat_lit 13277370355200)), (nat_lit 933, Int.ofNat (nat_lit 12927508070400)), (nat_lit 934, Int.ofNat (nat_lit 12577645785600)), (nat_lit 935, Int.ofNat (nat_lit 11915859916800)), (nat_lit 936, Int.ofNat (nat_lit 9204520908800)), (nat_lit 937, Int.ofNat (nat_lit 8236260748800)), (nat_lit 938, Int.ofNat (nat_lit 8145412531200)), (nat_lit 939, Int.ofNat (nat_lit 12461669337600)), (nat_lit 940, Int.ofNat (nat_lit 3160358208000))]
theorem block009_data_flat018_step : block009_data_flat018 = (CoefficientMerge.fastMerge block009_data_flat008 block009_data_flat017) := by decide +kernel
theorem block009_data_flat018_original : block009_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13552237298304 : Int) atom0576Coded) (CoefficientMerge.scale (13277370355200 : Int) atom0577Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12927508070400 : Int) atom0578Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12577645785600 : Int) atom0579Coded) (CoefficientMerge.scale (11915859916800 : Int) atom0580Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9204520908800 : Int) atom0581Coded) (CoefficientMerge.scale (8236260748800 : Int) atom0582Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8145412531200 : Int) atom0583Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12461669337600 : Int) atom0584Coded) (CoefficientMerge.scale (3160358208000 : Int) atom0585Coded))))) := by
  rw [block009_data_flat018_step, block009_data_flat008_original, block009_data_flat017_original]
def block009_data_flat019 : CoefficientMerge.Poly := [(nat_lit 941, Int.ofNat (nat_lit 9873255974400))]
theorem block009_data_flat019_step : block009_data_flat019 = (CoefficientMerge.scale (9873255974400 : Int) atom0586Coded) := by decide +kernel
theorem block009_data_flat019_original : block009_data_flat019 = (CoefficientMerge.scale (9873255974400 : Int) atom0586Coded) := by
  rw [block009_data_flat019_step]
def block009_data_flat020 : CoefficientMerge.Poly := [(nat_lit 942, Int.ofNat (nat_lit 1606273804800))]
theorem block009_data_flat020_step : block009_data_flat020 = (CoefficientMerge.scale (1606273804800 : Int) atom0587Coded) := by decide +kernel
theorem block009_data_flat020_original : block009_data_flat020 = (CoefficientMerge.scale (1606273804800 : Int) atom0587Coded) := by
  rw [block009_data_flat020_step]
def block009_data_flat021 : CoefficientMerge.Poly := [(nat_lit 941, Int.ofNat (nat_lit 9873255974400)), (nat_lit 942, Int.ofNat (nat_lit 1606273804800))]
theorem block009_data_flat021_step : block009_data_flat021 = (CoefficientMerge.fastMerge block009_data_flat019 block009_data_flat020) := by decide +kernel
theorem block009_data_flat021_original : block009_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (9873255974400 : Int) atom0586Coded) (CoefficientMerge.scale (1606273804800 : Int) atom0587Coded)) := by
  rw [block009_data_flat021_step, block009_data_flat019_original, block009_data_flat020_original]
def block009_data_flat022 : CoefficientMerge.Poly := [(nat_lit 944, Int.ofNat (nat_lit 3063711168000))]
theorem block009_data_flat022_step : block009_data_flat022 = (CoefficientMerge.scale (3063711168000 : Int) atom0588Coded) := by decide +kernel
theorem block009_data_flat022_original : block009_data_flat022 = (CoefficientMerge.scale (3063711168000 : Int) atom0588Coded) := by
  rw [block009_data_flat022_step]
def block009_data_flat023 : CoefficientMerge.Poly := [(nat_lit 948, Int.ofNat (nat_lit 11203324876800))]
theorem block009_data_flat023_step : block009_data_flat023 = (CoefficientMerge.scale (11203324876800 : Int) atom0589Coded) := by decide +kernel
theorem block009_data_flat023_original : block009_data_flat023 = (CoefficientMerge.scale (11203324876800 : Int) atom0589Coded) := by
  rw [block009_data_flat023_step]
def block009_data_flat024 : CoefficientMerge.Poly := [(nat_lit 949, Int.ofNat (nat_lit 21357062899200))]
theorem block009_data_flat024_step : block009_data_flat024 = (CoefficientMerge.scale (21357062899200 : Int) atom0590Coded) := by decide +kernel
theorem block009_data_flat024_original : block009_data_flat024 = (CoefficientMerge.scale (21357062899200 : Int) atom0590Coded) := by
  rw [block009_data_flat024_step]
def block009_data_flat025 : CoefficientMerge.Poly := [(nat_lit 948, Int.ofNat (nat_lit 11203324876800)), (nat_lit 949, Int.ofNat (nat_lit 21357062899200))]
theorem block009_data_flat025_step : block009_data_flat025 = (CoefficientMerge.fastMerge block009_data_flat023 block009_data_flat024) := by decide +kernel
theorem block009_data_flat025_original : block009_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11203324876800 : Int) atom0589Coded) (CoefficientMerge.scale (21357062899200 : Int) atom0590Coded)) := by
  rw [block009_data_flat025_step, block009_data_flat023_original, block009_data_flat024_original]
def block009_data_flat026 : CoefficientMerge.Poly := [(nat_lit 944, Int.ofNat (nat_lit 3063711168000)), (nat_lit 948, Int.ofNat (nat_lit 11203324876800)), (nat_lit 949, Int.ofNat (nat_lit 21357062899200))]
theorem block009_data_flat026_step : block009_data_flat026 = (CoefficientMerge.fastMerge block009_data_flat022 block009_data_flat025) := by decide +kernel
theorem block009_data_flat026_original : block009_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3063711168000 : Int) atom0588Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11203324876800 : Int) atom0589Coded) (CoefficientMerge.scale (21357062899200 : Int) atom0590Coded))) := by
  rw [block009_data_flat026_step, block009_data_flat022_original, block009_data_flat025_original]
def block009_data_flat027 : CoefficientMerge.Poly := [(nat_lit 941, Int.ofNat (nat_lit 9873255974400)), (nat_lit 942, Int.ofNat (nat_lit 1606273804800)), (nat_lit 944, Int.ofNat (nat_lit 3063711168000)), (nat_lit 948, Int.ofNat (nat_lit 11203324876800)), (nat_lit 949, Int.ofNat (nat_lit 21357062899200))]
theorem block009_data_flat027_step : block009_data_flat027 = (CoefficientMerge.fastMerge block009_data_flat021 block009_data_flat026) := by decide +kernel
theorem block009_data_flat027_original : block009_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9873255974400 : Int) atom0586Coded) (CoefficientMerge.scale (1606273804800 : Int) atom0587Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3063711168000 : Int) atom0588Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11203324876800 : Int) atom0589Coded) (CoefficientMerge.scale (21357062899200 : Int) atom0590Coded)))) := by
  rw [block009_data_flat027_step, block009_data_flat021_original, block009_data_flat026_original]
def block009_data_flat028 : CoefficientMerge.Poly := [(nat_lit 950, Int.ofNat (nat_lit 23290231970304))]
theorem block009_data_flat028_step : block009_data_flat028 = (CoefficientMerge.scale (23290231970304 : Int) atom0591Coded) := by decide +kernel
theorem block009_data_flat028_original : block009_data_flat028 = (CoefficientMerge.scale (23290231970304 : Int) atom0591Coded) := by
  rw [block009_data_flat028_step]
def block009_data_flat029 : CoefficientMerge.Poly := [(nat_lit 951, Int.ofNat (nat_lit 23147295091200))]
theorem block009_data_flat029_step : block009_data_flat029 = (CoefficientMerge.scale (23147295091200 : Int) atom0592Coded) := by decide +kernel
theorem block009_data_flat029_original : block009_data_flat029 = (CoefficientMerge.scale (23147295091200 : Int) atom0592Coded) := by
  rw [block009_data_flat029_step]
def block009_data_flat030 : CoefficientMerge.Poly := [(nat_lit 950, Int.ofNat (nat_lit 23290231970304)), (nat_lit 951, Int.ofNat (nat_lit 23147295091200))]
theorem block009_data_flat030_step : block009_data_flat030 = (CoefficientMerge.fastMerge block009_data_flat028 block009_data_flat029) := by decide +kernel
theorem block009_data_flat030_original : block009_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (23290231970304 : Int) atom0591Coded) (CoefficientMerge.scale (23147295091200 : Int) atom0592Coded)) := by
  rw [block009_data_flat030_step, block009_data_flat028_original, block009_data_flat029_original]
def block009_data_flat031 : CoefficientMerge.Poly := [(nat_lit 952, Int.ofNat (nat_lit 25005300887808))]
theorem block009_data_flat031_step : block009_data_flat031 = (CoefficientMerge.scale (25005300887808 : Int) atom0593Coded) := by decide +kernel
theorem block009_data_flat031_original : block009_data_flat031 = (CoefficientMerge.scale (25005300887808 : Int) atom0593Coded) := by
  rw [block009_data_flat031_step]
def block009_data_flat032 : CoefficientMerge.Poly := [(nat_lit 953, Int.ofNat (nat_lit 24960064550400))]
theorem block009_data_flat032_step : block009_data_flat032 = (CoefficientMerge.scale (24960064550400 : Int) atom0594Coded) := by decide +kernel
theorem block009_data_flat032_original : block009_data_flat032 = (CoefficientMerge.scale (24960064550400 : Int) atom0594Coded) := by
  rw [block009_data_flat032_step]
def block009_data_flat033 : CoefficientMerge.Poly := [(nat_lit 954, Int.ofNat (nat_lit 24764837529600))]
theorem block009_data_flat033_step : block009_data_flat033 = (CoefficientMerge.scale (24764837529600 : Int) atom0595Coded) := by decide +kernel
theorem block009_data_flat033_original : block009_data_flat033 = (CoefficientMerge.scale (24764837529600 : Int) atom0595Coded) := by
  rw [block009_data_flat033_step]
def block009_data_flat034 : CoefficientMerge.Poly := [(nat_lit 953, Int.ofNat (nat_lit 24960064550400)), (nat_lit 954, Int.ofNat (nat_lit 24764837529600))]
theorem block009_data_flat034_step : block009_data_flat034 = (CoefficientMerge.fastMerge block009_data_flat032 block009_data_flat033) := by decide +kernel
theorem block009_data_flat034_original : block009_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (24960064550400 : Int) atom0594Coded) (CoefficientMerge.scale (24764837529600 : Int) atom0595Coded)) := by
  rw [block009_data_flat034_step, block009_data_flat032_original, block009_data_flat033_original]
def block009_data_flat035 : CoefficientMerge.Poly := [(nat_lit 952, Int.ofNat (nat_lit 25005300887808)), (nat_lit 953, Int.ofNat (nat_lit 24960064550400)), (nat_lit 954, Int.ofNat (nat_lit 24764837529600))]
theorem block009_data_flat035_step : block009_data_flat035 = (CoefficientMerge.fastMerge block009_data_flat031 block009_data_flat034) := by decide +kernel
theorem block009_data_flat035_original : block009_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (25005300887808 : Int) atom0593Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24960064550400 : Int) atom0594Coded) (CoefficientMerge.scale (24764837529600 : Int) atom0595Coded))) := by
  rw [block009_data_flat035_step, block009_data_flat031_original, block009_data_flat034_original]
def block009_data_flat036 : CoefficientMerge.Poly := [(nat_lit 950, Int.ofNat (nat_lit 23290231970304)), (nat_lit 951, Int.ofNat (nat_lit 23147295091200)), (nat_lit 952, Int.ofNat (nat_lit 25005300887808)), (nat_lit 953, Int.ofNat (nat_lit 24960064550400)), (nat_lit 954, Int.ofNat (nat_lit 24764837529600))]
theorem block009_data_flat036_step : block009_data_flat036 = (CoefficientMerge.fastMerge block009_data_flat030 block009_data_flat035) := by decide +kernel
theorem block009_data_flat036_original : block009_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23290231970304 : Int) atom0591Coded) (CoefficientMerge.scale (23147295091200 : Int) atom0592Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25005300887808 : Int) atom0593Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24960064550400 : Int) atom0594Coded) (CoefficientMerge.scale (24764837529600 : Int) atom0595Coded)))) := by
  rw [block009_data_flat036_step, block009_data_flat030_original, block009_data_flat035_original]
def block009_data_flat037 : CoefficientMerge.Poly := [(nat_lit 941, Int.ofNat (nat_lit 9873255974400)), (nat_lit 942, Int.ofNat (nat_lit 1606273804800)), (nat_lit 944, Int.ofNat (nat_lit 3063711168000)), (nat_lit 948, Int.ofNat (nat_lit 11203324876800)), (nat_lit 949, Int.ofNat (nat_lit 21357062899200)), (nat_lit 950, Int.ofNat (nat_lit 23290231970304)), (nat_lit 951, Int.ofNat (nat_lit 23147295091200)), (nat_lit 952, Int.ofNat (nat_lit 25005300887808)), (nat_lit 953, Int.ofNat (nat_lit 24960064550400)), (nat_lit 954, Int.ofNat (nat_lit 24764837529600))]
theorem block009_data_flat037_step : block009_data_flat037 = (CoefficientMerge.fastMerge block009_data_flat027 block009_data_flat036) := by decide +kernel
theorem block009_data_flat037_original : block009_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9873255974400 : Int) atom0586Coded) (CoefficientMerge.scale (1606273804800 : Int) atom0587Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3063711168000 : Int) atom0588Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11203324876800 : Int) atom0589Coded) (CoefficientMerge.scale (21357062899200 : Int) atom0590Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23290231970304 : Int) atom0591Coded) (CoefficientMerge.scale (23147295091200 : Int) atom0592Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25005300887808 : Int) atom0593Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24960064550400 : Int) atom0594Coded) (CoefficientMerge.scale (24764837529600 : Int) atom0595Coded))))) := by
  rw [block009_data_flat037_step, block009_data_flat027_original, block009_data_flat036_original]
def block009_data_flat038 : CoefficientMerge.Poly := [(nat_lit 931, Int.ofNat (nat_lit 13552237298304)), (nat_lit 932, Int.ofNat (nat_lit 13277370355200)), (nat_lit 933, Int.ofNat (nat_lit 12927508070400)), (nat_lit 934, Int.ofNat (nat_lit 12577645785600)), (nat_lit 935, Int.ofNat (nat_lit 11915859916800)), (nat_lit 936, Int.ofNat (nat_lit 9204520908800)), (nat_lit 937, Int.ofNat (nat_lit 8236260748800)), (nat_lit 938, Int.ofNat (nat_lit 8145412531200)), (nat_lit 939, Int.ofNat (nat_lit 12461669337600)), (nat_lit 940, Int.ofNat (nat_lit 3160358208000)), (nat_lit 941, Int.ofNat (nat_lit 9873255974400)), (nat_lit 942, Int.ofNat (nat_lit 1606273804800)), (nat_lit 944, Int.ofNat (nat_lit 3063711168000)), (nat_lit 948, Int.ofNat (nat_lit 11203324876800)), (nat_lit 949, Int.ofNat (nat_lit 21357062899200)), (nat_lit 950, Int.ofNat (nat_lit 23290231970304)), (nat_lit 951, Int.ofNat (nat_lit 23147295091200)), (nat_lit 952, Int.ofNat (nat_lit 25005300887808)), (nat_lit 953, Int.ofNat (nat_lit 24960064550400)), (nat_lit 954, Int.ofNat (nat_lit 24764837529600))]
theorem block009_data_flat038_step : block009_data_flat038 = (CoefficientMerge.fastMerge block009_data_flat018 block009_data_flat037) := by decide +kernel
theorem block009_data_flat038_original : block009_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13552237298304 : Int) atom0576Coded) (CoefficientMerge.scale (13277370355200 : Int) atom0577Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12927508070400 : Int) atom0578Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12577645785600 : Int) atom0579Coded) (CoefficientMerge.scale (11915859916800 : Int) atom0580Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9204520908800 : Int) atom0581Coded) (CoefficientMerge.scale (8236260748800 : Int) atom0582Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8145412531200 : Int) atom0583Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12461669337600 : Int) atom0584Coded) (CoefficientMerge.scale (3160358208000 : Int) atom0585Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9873255974400 : Int) atom0586Coded) (CoefficientMerge.scale (1606273804800 : Int) atom0587Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3063711168000 : Int) atom0588Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11203324876800 : Int) atom0589Coded) (CoefficientMerge.scale (21357062899200 : Int) atom0590Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23290231970304 : Int) atom0591Coded) (CoefficientMerge.scale (23147295091200 : Int) atom0592Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25005300887808 : Int) atom0593Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24960064550400 : Int) atom0594Coded) (CoefficientMerge.scale (24764837529600 : Int) atom0595Coded)))))) := by
  rw [block009_data_flat038_step, block009_data_flat018_original, block009_data_flat037_original]
def block009_data_flat039 : CoefficientMerge.Poly := [(nat_lit 955, Int.ofNat (nat_lit 24569610508800))]
theorem block009_data_flat039_step : block009_data_flat039 = (CoefficientMerge.scale (24569610508800 : Int) atom0596Coded) := by decide +kernel
theorem block009_data_flat039_original : block009_data_flat039 = (CoefficientMerge.scale (24569610508800 : Int) atom0596Coded) := by
  rw [block009_data_flat039_step]
def block009_data_flat040 : CoefficientMerge.Poly := [(nat_lit 956, Int.ofNat (nat_lit 23750536320000))]
theorem block009_data_flat040_step : block009_data_flat040 = (CoefficientMerge.scale (23750536320000 : Int) atom0597Coded) := by decide +kernel
theorem block009_data_flat040_original : block009_data_flat040 = (CoefficientMerge.scale (23750536320000 : Int) atom0597Coded) := by
  rw [block009_data_flat040_step]
def block009_data_flat041 : CoefficientMerge.Poly := [(nat_lit 955, Int.ofNat (nat_lit 24569610508800)), (nat_lit 956, Int.ofNat (nat_lit 23750536320000))]
theorem block009_data_flat041_step : block009_data_flat041 = (CoefficientMerge.fastMerge block009_data_flat039 block009_data_flat040) := by decide +kernel
theorem block009_data_flat041_original : block009_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (24569610508800 : Int) atom0596Coded) (CoefficientMerge.scale (23750536320000 : Int) atom0597Coded)) := by
  rw [block009_data_flat041_step, block009_data_flat039_original, block009_data_flat040_original]
def block009_data_flat042 : CoefficientMerge.Poly := [(nat_lit 957, Int.ofNat (nat_lit 18832355852800))]
theorem block009_data_flat042_step : block009_data_flat042 = (CoefficientMerge.scale (18832355852800 : Int) atom0598Coded) := by decide +kernel
theorem block009_data_flat042_original : block009_data_flat042 = (CoefficientMerge.scale (18832355852800 : Int) atom0598Coded) := by
  rw [block009_data_flat042_step]
def block009_data_flat043 : CoefficientMerge.Poly := [(nat_lit 958, Int.ofNat (nat_lit 17400333081600))]
theorem block009_data_flat043_step : block009_data_flat043 = (CoefficientMerge.scale (17400333081600 : Int) atom0599Coded) := by decide +kernel
theorem block009_data_flat043_original : block009_data_flat043 = (CoefficientMerge.scale (17400333081600 : Int) atom0599Coded) := by
  rw [block009_data_flat043_step]
def block009_data_flat044 : CoefficientMerge.Poly := [(nat_lit 959, Int.ofNat (nat_lit 17723134195200))]
theorem block009_data_flat044_step : block009_data_flat044 = (CoefficientMerge.scale (17723134195200 : Int) atom0600Coded) := by decide +kernel
theorem block009_data_flat044_original : block009_data_flat044 = (CoefficientMerge.scale (17723134195200 : Int) atom0600Coded) := by
  rw [block009_data_flat044_step]
def block009_data_flat045 : CoefficientMerge.Poly := [(nat_lit 958, Int.ofNat (nat_lit 17400333081600)), (nat_lit 959, Int.ofNat (nat_lit 17723134195200))]
theorem block009_data_flat045_step : block009_data_flat045 = (CoefficientMerge.fastMerge block009_data_flat043 block009_data_flat044) := by decide +kernel
theorem block009_data_flat045_original : block009_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (17400333081600 : Int) atom0599Coded) (CoefficientMerge.scale (17723134195200 : Int) atom0600Coded)) := by
  rw [block009_data_flat045_step, block009_data_flat043_original, block009_data_flat044_original]
def block009_data_flat046 : CoefficientMerge.Poly := [(nat_lit 957, Int.ofNat (nat_lit 18832355852800)), (nat_lit 958, Int.ofNat (nat_lit 17400333081600)), (nat_lit 959, Int.ofNat (nat_lit 17723134195200))]
theorem block009_data_flat046_step : block009_data_flat046 = (CoefficientMerge.fastMerge block009_data_flat042 block009_data_flat045) := by decide +kernel
theorem block009_data_flat046_original : block009_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (18832355852800 : Int) atom0598Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17400333081600 : Int) atom0599Coded) (CoefficientMerge.scale (17723134195200 : Int) atom0600Coded))) := by
  rw [block009_data_flat046_step, block009_data_flat042_original, block009_data_flat045_original]
def block009_data_flat047 : CoefficientMerge.Poly := [(nat_lit 955, Int.ofNat (nat_lit 24569610508800)), (nat_lit 956, Int.ofNat (nat_lit 23750536320000)), (nat_lit 957, Int.ofNat (nat_lit 18832355852800)), (nat_lit 958, Int.ofNat (nat_lit 17400333081600)), (nat_lit 959, Int.ofNat (nat_lit 17723134195200))]
theorem block009_data_flat047_step : block009_data_flat047 = (CoefficientMerge.fastMerge block009_data_flat041 block009_data_flat046) := by decide +kernel
theorem block009_data_flat047_original : block009_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24569610508800 : Int) atom0596Coded) (CoefficientMerge.scale (23750536320000 : Int) atom0597Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18832355852800 : Int) atom0598Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17400333081600 : Int) atom0599Coded) (CoefficientMerge.scale (17723134195200 : Int) atom0600Coded)))) := by
  rw [block009_data_flat047_step, block009_data_flat041_original, block009_data_flat046_original]
def block009_data_flat048 : CoefficientMerge.Poly := [(nat_lit 960, Int.ofNat (nat_lit 26860145356800))]
theorem block009_data_flat048_step : block009_data_flat048 = (CoefficientMerge.scale (26860145356800 : Int) atom0601Coded) := by decide +kernel
theorem block009_data_flat048_original : block009_data_flat048 = (CoefficientMerge.scale (26860145356800 : Int) atom0601Coded) := by
  rw [block009_data_flat048_step]
def block009_data_flat049 : CoefficientMerge.Poly := [(nat_lit 961, Int.ofNat (nat_lit 11444942476800))]
theorem block009_data_flat049_step : block009_data_flat049 = (CoefficientMerge.scale (11444942476800 : Int) atom0602Coded) := by decide +kernel
theorem block009_data_flat049_original : block009_data_flat049 = (CoefficientMerge.scale (11444942476800 : Int) atom0602Coded) := by
  rw [block009_data_flat049_step]
def block009_data_flat050 : CoefficientMerge.Poly := [(nat_lit 960, Int.ofNat (nat_lit 26860145356800)), (nat_lit 961, Int.ofNat (nat_lit 11444942476800))]
theorem block009_data_flat050_step : block009_data_flat050 = (CoefficientMerge.fastMerge block009_data_flat048 block009_data_flat049) := by decide +kernel
theorem block009_data_flat050_original : block009_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (26860145356800 : Int) atom0601Coded) (CoefficientMerge.scale (11444942476800 : Int) atom0602Coded)) := by
  rw [block009_data_flat050_step, block009_data_flat048_original, block009_data_flat049_original]
def block009_data_flat051 : CoefficientMerge.Poly := [(nat_lit 962, Int.ofNat (nat_lit 22692313728000))]
theorem block009_data_flat051_step : block009_data_flat051 = (CoefficientMerge.scale (22692313728000 : Int) atom0603Coded) := by decide +kernel
theorem block009_data_flat051_original : block009_data_flat051 = (CoefficientMerge.scale (22692313728000 : Int) atom0603Coded) := by
  rw [block009_data_flat051_step]
def block009_data_flat052 : CoefficientMerge.Poly := [(nat_lit 963, Int.ofNat (nat_lit 10745217907200))]
theorem block009_data_flat052_step : block009_data_flat052 = (CoefficientMerge.scale (10745217907200 : Int) atom0604Coded) := by decide +kernel
theorem block009_data_flat052_original : block009_data_flat052 = (CoefficientMerge.scale (10745217907200 : Int) atom0604Coded) := by
  rw [block009_data_flat052_step]
def block009_data_flat053 : CoefficientMerge.Poly := [(nat_lit 964, Int.ofNat (nat_lit 9566124019200))]
theorem block009_data_flat053_step : block009_data_flat053 = (CoefficientMerge.scale (9566124019200 : Int) atom0605Coded) := by decide +kernel
theorem block009_data_flat053_original : block009_data_flat053 = (CoefficientMerge.scale (9566124019200 : Int) atom0605Coded) := by
  rw [block009_data_flat053_step]
def block009_data_flat054 : CoefficientMerge.Poly := [(nat_lit 963, Int.ofNat (nat_lit 10745217907200)), (nat_lit 964, Int.ofNat (nat_lit 9566124019200))]
theorem block009_data_flat054_step : block009_data_flat054 = (CoefficientMerge.fastMerge block009_data_flat052 block009_data_flat053) := by decide +kernel
theorem block009_data_flat054_original : block009_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (10745217907200 : Int) atom0604Coded) (CoefficientMerge.scale (9566124019200 : Int) atom0605Coded)) := by
  rw [block009_data_flat054_step, block009_data_flat052_original, block009_data_flat053_original]
def block009_data_flat055 : CoefficientMerge.Poly := [(nat_lit 962, Int.ofNat (nat_lit 22692313728000)), (nat_lit 963, Int.ofNat (nat_lit 10745217907200)), (nat_lit 964, Int.ofNat (nat_lit 9566124019200))]
theorem block009_data_flat055_step : block009_data_flat055 = (CoefficientMerge.fastMerge block009_data_flat051 block009_data_flat054) := by decide +kernel
theorem block009_data_flat055_original : block009_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (22692313728000 : Int) atom0603Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10745217907200 : Int) atom0604Coded) (CoefficientMerge.scale (9566124019200 : Int) atom0605Coded))) := by
  rw [block009_data_flat055_step, block009_data_flat051_original, block009_data_flat054_original]
def block009_data_flat056 : CoefficientMerge.Poly := [(nat_lit 960, Int.ofNat (nat_lit 26860145356800)), (nat_lit 961, Int.ofNat (nat_lit 11444942476800)), (nat_lit 962, Int.ofNat (nat_lit 22692313728000)), (nat_lit 963, Int.ofNat (nat_lit 10745217907200)), (nat_lit 964, Int.ofNat (nat_lit 9566124019200))]
theorem block009_data_flat056_step : block009_data_flat056 = (CoefficientMerge.fastMerge block009_data_flat050 block009_data_flat055) := by decide +kernel
theorem block009_data_flat056_original : block009_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26860145356800 : Int) atom0601Coded) (CoefficientMerge.scale (11444942476800 : Int) atom0602Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22692313728000 : Int) atom0603Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10745217907200 : Int) atom0604Coded) (CoefficientMerge.scale (9566124019200 : Int) atom0605Coded)))) := by
  rw [block009_data_flat056_step, block009_data_flat050_original, block009_data_flat055_original]
def block009_data_flat057 : CoefficientMerge.Poly := [(nat_lit 955, Int.ofNat (nat_lit 24569610508800)), (nat_lit 956, Int.ofNat (nat_lit 23750536320000)), (nat_lit 957, Int.ofNat (nat_lit 18832355852800)), (nat_lit 958, Int.ofNat (nat_lit 17400333081600)), (nat_lit 959, Int.ofNat (nat_lit 17723134195200)), (nat_lit 960, Int.ofNat (nat_lit 26860145356800)), (nat_lit 961, Int.ofNat (nat_lit 11444942476800)), (nat_lit 962, Int.ofNat (nat_lit 22692313728000)), (nat_lit 963, Int.ofNat (nat_lit 10745217907200)), (nat_lit 964, Int.ofNat (nat_lit 9566124019200))]
theorem block009_data_flat057_step : block009_data_flat057 = (CoefficientMerge.fastMerge block009_data_flat047 block009_data_flat056) := by decide +kernel
theorem block009_data_flat057_original : block009_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24569610508800 : Int) atom0596Coded) (CoefficientMerge.scale (23750536320000 : Int) atom0597Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18832355852800 : Int) atom0598Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17400333081600 : Int) atom0599Coded) (CoefficientMerge.scale (17723134195200 : Int) atom0600Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26860145356800 : Int) atom0601Coded) (CoefficientMerge.scale (11444942476800 : Int) atom0602Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22692313728000 : Int) atom0603Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10745217907200 : Int) atom0604Coded) (CoefficientMerge.scale (9566124019200 : Int) atom0605Coded))))) := by
  rw [block009_data_flat057_step, block009_data_flat047_original, block009_data_flat056_original]
def block009_data_flat058 : CoefficientMerge.Poly := [(nat_lit 965, Int.ofNat (nat_lit 13057015104000))]
theorem block009_data_flat058_step : block009_data_flat058 = (CoefficientMerge.scale (13057015104000 : Int) atom0606Coded) := by decide +kernel
theorem block009_data_flat058_original : block009_data_flat058 = (CoefficientMerge.scale (13057015104000 : Int) atom0606Coded) := by
  rw [block009_data_flat058_step]
def block009_data_flat059 : CoefficientMerge.Poly := [(nat_lit 970, Int.ofNat (nat_lit 11020661971200))]
theorem block009_data_flat059_step : block009_data_flat059 = (CoefficientMerge.scale (11020661971200 : Int) atom0607Coded) := by decide +kernel
theorem block009_data_flat059_original : block009_data_flat059 = (CoefficientMerge.scale (11020661971200 : Int) atom0607Coded) := by
  rw [block009_data_flat059_step]
def block009_data_flat060 : CoefficientMerge.Poly := [(nat_lit 965, Int.ofNat (nat_lit 13057015104000)), (nat_lit 970, Int.ofNat (nat_lit 11020661971200))]
theorem block009_data_flat060_step : block009_data_flat060 = (CoefficientMerge.fastMerge block009_data_flat058 block009_data_flat059) := by decide +kernel
theorem block009_data_flat060_original : block009_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (13057015104000 : Int) atom0606Coded) (CoefficientMerge.scale (11020661971200 : Int) atom0607Coded)) := by
  rw [block009_data_flat060_step, block009_data_flat058_original, block009_data_flat059_original]
def block009_data_flat061 : CoefficientMerge.Poly := [(nat_lit 971, Int.ofNat (nat_lit 20212761945600))]
theorem block009_data_flat061_step : block009_data_flat061 = (CoefficientMerge.scale (20212761945600 : Int) atom0608Coded) := by decide +kernel
theorem block009_data_flat061_original : block009_data_flat061 = (CoefficientMerge.scale (20212761945600 : Int) atom0608Coded) := by
  rw [block009_data_flat061_step]
def block009_data_flat062 : CoefficientMerge.Poly := [(nat_lit 972, Int.ofNat (nat_lit 20543623833600))]
theorem block009_data_flat062_step : block009_data_flat062 = (CoefficientMerge.scale (20543623833600 : Int) atom0609Coded) := by decide +kernel
theorem block009_data_flat062_original : block009_data_flat062 = (CoefficientMerge.scale (20543623833600 : Int) atom0609Coded) := by
  rw [block009_data_flat062_step]
def block009_data_flat063 : CoefficientMerge.Poly := [(nat_lit 973, Int.ofNat (nat_lit 22906127179008))]
theorem block009_data_flat063_step : block009_data_flat063 = (CoefficientMerge.scale (22906127179008 : Int) atom0610Coded) := by decide +kernel
theorem block009_data_flat063_original : block009_data_flat063 = (CoefficientMerge.scale (22906127179008 : Int) atom0610Coded) := by
  rw [block009_data_flat063_step]
def block009_data_flat064 : CoefficientMerge.Poly := [(nat_lit 972, Int.ofNat (nat_lit 20543623833600)), (nat_lit 973, Int.ofNat (nat_lit 22906127179008))]
theorem block009_data_flat064_step : block009_data_flat064 = (CoefficientMerge.fastMerge block009_data_flat062 block009_data_flat063) := by decide +kernel
theorem block009_data_flat064_original : block009_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (20543623833600 : Int) atom0609Coded) (CoefficientMerge.scale (22906127179008 : Int) atom0610Coded)) := by
  rw [block009_data_flat064_step, block009_data_flat062_original, block009_data_flat063_original]
def block009_data_flat065 : CoefficientMerge.Poly := [(nat_lit 971, Int.ofNat (nat_lit 20212761945600)), (nat_lit 972, Int.ofNat (nat_lit 20543623833600)), (nat_lit 973, Int.ofNat (nat_lit 22906127179008))]
theorem block009_data_flat065_step : block009_data_flat065 = (CoefficientMerge.fastMerge block009_data_flat061 block009_data_flat064) := by decide +kernel
theorem block009_data_flat065_original : block009_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (20212761945600 : Int) atom0608Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20543623833600 : Int) atom0609Coded) (CoefficientMerge.scale (22906127179008 : Int) atom0610Coded))) := by
  rw [block009_data_flat065_step, block009_data_flat061_original, block009_data_flat064_original]
def block009_data_flat066 : CoefficientMerge.Poly := [(nat_lit 965, Int.ofNat (nat_lit 13057015104000)), (nat_lit 970, Int.ofNat (nat_lit 11020661971200)), (nat_lit 971, Int.ofNat (nat_lit 20212761945600)), (nat_lit 972, Int.ofNat (nat_lit 20543623833600)), (nat_lit 973, Int.ofNat (nat_lit 22906127179008))]
theorem block009_data_flat066_step : block009_data_flat066 = (CoefficientMerge.fastMerge block009_data_flat060 block009_data_flat065) := by decide +kernel
theorem block009_data_flat066_original : block009_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13057015104000 : Int) atom0606Coded) (CoefficientMerge.scale (11020661971200 : Int) atom0607Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20212761945600 : Int) atom0608Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20543623833600 : Int) atom0609Coded) (CoefficientMerge.scale (22906127179008 : Int) atom0610Coded)))) := by
  rw [block009_data_flat066_step, block009_data_flat060_original, block009_data_flat065_original]
def block009_data_flat067 : CoefficientMerge.Poly := [(nat_lit 974, Int.ofNat (nat_lit 23365388390400))]
theorem block009_data_flat067_step : block009_data_flat067 = (CoefficientMerge.scale (23365388390400 : Int) atom0611Coded) := by decide +kernel
theorem block009_data_flat067_original : block009_data_flat067 = (CoefficientMerge.scale (23365388390400 : Int) atom0611Coded) := by
  rw [block009_data_flat067_step]
def block009_data_flat068 : CoefficientMerge.Poly := [(nat_lit 975, Int.ofNat (nat_lit 23674658918400))]
theorem block009_data_flat068_step : block009_data_flat068 = (CoefficientMerge.scale (23674658918400 : Int) atom0612Coded) := by decide +kernel
theorem block009_data_flat068_original : block009_data_flat068 = (CoefficientMerge.scale (23674658918400 : Int) atom0612Coded) := by
  rw [block009_data_flat068_step]
def block009_data_flat069 : CoefficientMerge.Poly := [(nat_lit 974, Int.ofNat (nat_lit 23365388390400)), (nat_lit 975, Int.ofNat (nat_lit 23674658918400))]
theorem block009_data_flat069_step : block009_data_flat069 = (CoefficientMerge.fastMerge block009_data_flat067 block009_data_flat068) := by decide +kernel
theorem block009_data_flat069_original : block009_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (23365388390400 : Int) atom0611Coded) (CoefficientMerge.scale (23674658918400 : Int) atom0612Coded)) := by
  rw [block009_data_flat069_step, block009_data_flat067_original, block009_data_flat068_original]
def block009_data_flat070 : CoefficientMerge.Poly := [(nat_lit 976, Int.ofNat (nat_lit 23983929446400))]
theorem block009_data_flat070_step : block009_data_flat070 = (CoefficientMerge.scale (23983929446400 : Int) atom0613Coded) := by decide +kernel
theorem block009_data_flat070_original : block009_data_flat070 = (CoefficientMerge.scale (23983929446400 : Int) atom0613Coded) := by
  rw [block009_data_flat070_step]
def block009_data_flat071 : CoefficientMerge.Poly := [(nat_lit 977, Int.ofNat (nat_lit 23669352806400))]
theorem block009_data_flat071_step : block009_data_flat071 = (CoefficientMerge.scale (23669352806400 : Int) atom0614Coded) := by decide +kernel
theorem block009_data_flat071_original : block009_data_flat071 = (CoefficientMerge.scale (23669352806400 : Int) atom0614Coded) := by
  rw [block009_data_flat071_step]
def block009_data_flat072 : CoefficientMerge.Poly := [(nat_lit 978, Int.ofNat (nat_lit 20066681734400))]
theorem block009_data_flat072_step : block009_data_flat072 = (CoefficientMerge.scale (20066681734400 : Int) atom0615Coded) := by decide +kernel
theorem block009_data_flat072_original : block009_data_flat072 = (CoefficientMerge.scale (20066681734400 : Int) atom0615Coded) := by
  rw [block009_data_flat072_step]
def block009_data_flat073 : CoefficientMerge.Poly := [(nat_lit 977, Int.ofNat (nat_lit 23669352806400)), (nat_lit 978, Int.ofNat (nat_lit 20066681734400))]
theorem block009_data_flat073_step : block009_data_flat073 = (CoefficientMerge.fastMerge block009_data_flat071 block009_data_flat072) := by decide +kernel
theorem block009_data_flat073_original : block009_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (23669352806400 : Int) atom0614Coded) (CoefficientMerge.scale (20066681734400 : Int) atom0615Coded)) := by
  rw [block009_data_flat073_step, block009_data_flat071_original, block009_data_flat072_original]
def block009_data_flat074 : CoefficientMerge.Poly := [(nat_lit 976, Int.ofNat (nat_lit 23983929446400)), (nat_lit 977, Int.ofNat (nat_lit 23669352806400)), (nat_lit 978, Int.ofNat (nat_lit 20066681734400))]
theorem block009_data_flat074_step : block009_data_flat074 = (CoefficientMerge.fastMerge block009_data_flat070 block009_data_flat073) := by decide +kernel
theorem block009_data_flat074_original : block009_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (23983929446400 : Int) atom0613Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23669352806400 : Int) atom0614Coded) (CoefficientMerge.scale (20066681734400 : Int) atom0615Coded))) := by
  rw [block009_data_flat074_step, block009_data_flat070_original, block009_data_flat073_original]
def block009_data_flat075 : CoefficientMerge.Poly := [(nat_lit 974, Int.ofNat (nat_lit 23365388390400)), (nat_lit 975, Int.ofNat (nat_lit 23674658918400)), (nat_lit 976, Int.ofNat (nat_lit 23983929446400)), (nat_lit 977, Int.ofNat (nat_lit 23669352806400)), (nat_lit 978, Int.ofNat (nat_lit 20066681734400))]
theorem block009_data_flat075_step : block009_data_flat075 = (CoefficientMerge.fastMerge block009_data_flat069 block009_data_flat074) := by decide +kernel
theorem block009_data_flat075_original : block009_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23365388390400 : Int) atom0611Coded) (CoefficientMerge.scale (23674658918400 : Int) atom0612Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23983929446400 : Int) atom0613Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23669352806400 : Int) atom0614Coded) (CoefficientMerge.scale (20066681734400 : Int) atom0615Coded)))) := by
  rw [block009_data_flat075_step, block009_data_flat069_original, block009_data_flat074_original]
def block009_data_flat076 : CoefficientMerge.Poly := [(nat_lit 965, Int.ofNat (nat_lit 13057015104000)), (nat_lit 970, Int.ofNat (nat_lit 11020661971200)), (nat_lit 971, Int.ofNat (nat_lit 20212761945600)), (nat_lit 972, Int.ofNat (nat_lit 20543623833600)), (nat_lit 973, Int.ofNat (nat_lit 22906127179008)), (nat_lit 974, Int.ofNat (nat_lit 23365388390400)), (nat_lit 975, Int.ofNat (nat_lit 23674658918400)), (nat_lit 976, Int.ofNat (nat_lit 23983929446400)), (nat_lit 977, Int.ofNat (nat_lit 23669352806400)), (nat_lit 978, Int.ofNat (nat_lit 20066681734400))]
theorem block009_data_flat076_step : block009_data_flat076 = (CoefficientMerge.fastMerge block009_data_flat066 block009_data_flat075) := by decide +kernel
theorem block009_data_flat076_original : block009_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13057015104000 : Int) atom0606Coded) (CoefficientMerge.scale (11020661971200 : Int) atom0607Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20212761945600 : Int) atom0608Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20543623833600 : Int) atom0609Coded) (CoefficientMerge.scale (22906127179008 : Int) atom0610Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23365388390400 : Int) atom0611Coded) (CoefficientMerge.scale (23674658918400 : Int) atom0612Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23983929446400 : Int) atom0613Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23669352806400 : Int) atom0614Coded) (CoefficientMerge.scale (20066681734400 : Int) atom0615Coded))))) := by
  rw [block009_data_flat076_step, block009_data_flat066_original, block009_data_flat075_original]
def block009_data_flat077 : CoefficientMerge.Poly := [(nat_lit 955, Int.ofNat (nat_lit 24569610508800)), (nat_lit 956, Int.ofNat (nat_lit 23750536320000)), (nat_lit 957, Int.ofNat (nat_lit 18832355852800)), (nat_lit 958, Int.ofNat (nat_lit 17400333081600)), (nat_lit 959, Int.ofNat (nat_lit 17723134195200)), (nat_lit 960, Int.ofNat (nat_lit 26860145356800)), (nat_lit 961, Int.ofNat (nat_lit 11444942476800)), (nat_lit 962, Int.ofNat (nat_lit 22692313728000)), (nat_lit 963, Int.ofNat (nat_lit 10745217907200)), (nat_lit 964, Int.ofNat (nat_lit 9566124019200)), (nat_lit 965, Int.ofNat (nat_lit 13057015104000)), (nat_lit 970, Int.ofNat (nat_lit 11020661971200)), (nat_lit 971, Int.ofNat (nat_lit 20212761945600)), (nat_lit 972, Int.ofNat (nat_lit 20543623833600)), (nat_lit 973, Int.ofNat (nat_lit 22906127179008)), (nat_lit 974, Int.ofNat (nat_lit 23365388390400)), (nat_lit 975, Int.ofNat (nat_lit 23674658918400)), (nat_lit 976, Int.ofNat (nat_lit 23983929446400)), (nat_lit 977, Int.ofNat (nat_lit 23669352806400)), (nat_lit 978, Int.ofNat (nat_lit 20066681734400))]
theorem block009_data_flat077_step : block009_data_flat077 = (CoefficientMerge.fastMerge block009_data_flat057 block009_data_flat076) := by decide +kernel
theorem block009_data_flat077_original : block009_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24569610508800 : Int) atom0596Coded) (CoefficientMerge.scale (23750536320000 : Int) atom0597Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18832355852800 : Int) atom0598Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17400333081600 : Int) atom0599Coded) (CoefficientMerge.scale (17723134195200 : Int) atom0600Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26860145356800 : Int) atom0601Coded) (CoefficientMerge.scale (11444942476800 : Int) atom0602Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22692313728000 : Int) atom0603Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10745217907200 : Int) atom0604Coded) (CoefficientMerge.scale (9566124019200 : Int) atom0605Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13057015104000 : Int) atom0606Coded) (CoefficientMerge.scale (11020661971200 : Int) atom0607Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20212761945600 : Int) atom0608Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20543623833600 : Int) atom0609Coded) (CoefficientMerge.scale (22906127179008 : Int) atom0610Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23365388390400 : Int) atom0611Coded) (CoefficientMerge.scale (23674658918400 : Int) atom0612Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23983929446400 : Int) atom0613Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23669352806400 : Int) atom0614Coded) (CoefficientMerge.scale (20066681734400 : Int) atom0615Coded)))))) := by
  rw [block009_data_flat077_step, block009_data_flat057_original, block009_data_flat076_original]
def block009_data_flat078 : CoefficientMerge.Poly := [(nat_lit 931, Int.ofNat (nat_lit 13552237298304)), (nat_lit 932, Int.ofNat (nat_lit 13277370355200)), (nat_lit 933, Int.ofNat (nat_lit 12927508070400)), (nat_lit 934, Int.ofNat (nat_lit 12577645785600)), (nat_lit 935, Int.ofNat (nat_lit 11915859916800)), (nat_lit 936, Int.ofNat (nat_lit 9204520908800)), (nat_lit 937, Int.ofNat (nat_lit 8236260748800)), (nat_lit 938, Int.ofNat (nat_lit 8145412531200)), (nat_lit 939, Int.ofNat (nat_lit 12461669337600)), (nat_lit 940, Int.ofNat (nat_lit 3160358208000)), (nat_lit 941, Int.ofNat (nat_lit 9873255974400)), (nat_lit 942, Int.ofNat (nat_lit 1606273804800)), (nat_lit 944, Int.ofNat (nat_lit 3063711168000)), (nat_lit 948, Int.ofNat (nat_lit 11203324876800)), (nat_lit 949, Int.ofNat (nat_lit 21357062899200)), (nat_lit 950, Int.ofNat (nat_lit 23290231970304)), (nat_lit 951, Int.ofNat (nat_lit 23147295091200)), (nat_lit 952, Int.ofNat (nat_lit 25005300887808)), (nat_lit 953, Int.ofNat (nat_lit 24960064550400)), (nat_lit 954, Int.ofNat (nat_lit 24764837529600)), (nat_lit 955, Int.ofNat (nat_lit 24569610508800)), (nat_lit 956, Int.ofNat (nat_lit 23750536320000)), (nat_lit 957, Int.ofNat (nat_lit 18832355852800)), (nat_lit 958, Int.ofNat (nat_lit 17400333081600)), (nat_lit 959, Int.ofNat (nat_lit 17723134195200)), (nat_lit 960, Int.ofNat (nat_lit 26860145356800)), (nat_lit 961, Int.ofNat (nat_lit 11444942476800)), (nat_lit 962, Int.ofNat (nat_lit 22692313728000)), (nat_lit 963, Int.ofNat (nat_lit 10745217907200)), (nat_lit 964, Int.ofNat (nat_lit 9566124019200)), (nat_lit 965, Int.ofNat (nat_lit 13057015104000)), (nat_lit 970, Int.ofNat (nat_lit 11020661971200)), (nat_lit 971, Int.ofNat (nat_lit 20212761945600)), (nat_lit 972, Int.ofNat (nat_lit 20543623833600)), (nat_lit 973, Int.ofNat (nat_lit 22906127179008)), (nat_lit 974, Int.ofNat (nat_lit 23365388390400)), (nat_lit 975, Int.ofNat (nat_lit 23674658918400)), (nat_lit 976, Int.ofNat (nat_lit 23983929446400)), (nat_lit 977, Int.ofNat (nat_lit 23669352806400)), (nat_lit 978, Int.ofNat (nat_lit 20066681734400))]
theorem block009_data_flat078_step : block009_data_flat078 = (CoefficientMerge.fastMerge block009_data_flat038 block009_data_flat077) := by decide +kernel
theorem block009_data_flat078_original : block009_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13552237298304 : Int) atom0576Coded) (CoefficientMerge.scale (13277370355200 : Int) atom0577Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12927508070400 : Int) atom0578Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12577645785600 : Int) atom0579Coded) (CoefficientMerge.scale (11915859916800 : Int) atom0580Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9204520908800 : Int) atom0581Coded) (CoefficientMerge.scale (8236260748800 : Int) atom0582Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8145412531200 : Int) atom0583Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12461669337600 : Int) atom0584Coded) (CoefficientMerge.scale (3160358208000 : Int) atom0585Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9873255974400 : Int) atom0586Coded) (CoefficientMerge.scale (1606273804800 : Int) atom0587Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3063711168000 : Int) atom0588Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11203324876800 : Int) atom0589Coded) (CoefficientMerge.scale (21357062899200 : Int) atom0590Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23290231970304 : Int) atom0591Coded) (CoefficientMerge.scale (23147295091200 : Int) atom0592Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25005300887808 : Int) atom0593Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24960064550400 : Int) atom0594Coded) (CoefficientMerge.scale (24764837529600 : Int) atom0595Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24569610508800 : Int) atom0596Coded) (CoefficientMerge.scale (23750536320000 : Int) atom0597Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18832355852800 : Int) atom0598Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17400333081600 : Int) atom0599Coded) (CoefficientMerge.scale (17723134195200 : Int) atom0600Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26860145356800 : Int) atom0601Coded) (CoefficientMerge.scale (11444942476800 : Int) atom0602Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22692313728000 : Int) atom0603Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10745217907200 : Int) atom0604Coded) (CoefficientMerge.scale (9566124019200 : Int) atom0605Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13057015104000 : Int) atom0606Coded) (CoefficientMerge.scale (11020661971200 : Int) atom0607Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20212761945600 : Int) atom0608Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20543623833600 : Int) atom0609Coded) (CoefficientMerge.scale (22906127179008 : Int) atom0610Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23365388390400 : Int) atom0611Coded) (CoefficientMerge.scale (23674658918400 : Int) atom0612Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23983929446400 : Int) atom0613Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23669352806400 : Int) atom0614Coded) (CoefficientMerge.scale (20066681734400 : Int) atom0615Coded))))))) := by
  rw [block009_data_flat078_step, block009_data_flat038_original, block009_data_flat077_original]
def block009_data_flat079 : CoefficientMerge.Poly := [(nat_lit 979, Int.ofNat (nat_lit 19784615558400))]
theorem block009_data_flat079_step : block009_data_flat079 = (CoefficientMerge.scale (19784615558400 : Int) atom0616Coded) := by decide +kernel
theorem block009_data_flat079_original : block009_data_flat079 = (CoefficientMerge.scale (19784615558400 : Int) atom0616Coded) := by
  rw [block009_data_flat079_step]
def block009_data_flat080 : CoefficientMerge.Poly := [(nat_lit 980, Int.ofNat (nat_lit 20379961324800))]
theorem block009_data_flat080_step : block009_data_flat080 = (CoefficientMerge.scale (20379961324800 : Int) atom0617Coded) := by decide +kernel
theorem block009_data_flat080_original : block009_data_flat080 = (CoefficientMerge.scale (20379961324800 : Int) atom0617Coded) := by
  rw [block009_data_flat080_step]
def block009_data_flat081 : CoefficientMerge.Poly := [(nat_lit 979, Int.ofNat (nat_lit 19784615558400)), (nat_lit 980, Int.ofNat (nat_lit 20379961324800))]
theorem block009_data_flat081_step : block009_data_flat081 = (CoefficientMerge.fastMerge block009_data_flat079 block009_data_flat080) := by decide +kernel
theorem block009_data_flat081_original : block009_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (19784615558400 : Int) atom0616Coded) (CoefficientMerge.scale (20379961324800 : Int) atom0617Coded)) := by
  rw [block009_data_flat081_step, block009_data_flat079_original, block009_data_flat080_original]
def block009_data_flat082 : CoefficientMerge.Poly := [(nat_lit 981, Int.ofNat (nat_lit 28796952038400))]
theorem block009_data_flat082_step : block009_data_flat082 = (CoefficientMerge.scale (28796952038400 : Int) atom0618Coded) := by decide +kernel
theorem block009_data_flat082_original : block009_data_flat082 = (CoefficientMerge.scale (28796952038400 : Int) atom0618Coded) := by
  rw [block009_data_flat082_step]
def block009_data_flat083 : CoefficientMerge.Poly := [(nat_lit 982, Int.ofNat (nat_lit 17572968856800))]
theorem block009_data_flat083_step : block009_data_flat083 = (CoefficientMerge.scale (17572968856800 : Int) atom0619Coded) := by decide +kernel
theorem block009_data_flat083_original : block009_data_flat083 = (CoefficientMerge.scale (17572968856800 : Int) atom0619Coded) := by
  rw [block009_data_flat083_step]
def block009_data_flat084 : CoefficientMerge.Poly := [(nat_lit 983, Int.ofNat (nat_lit 25638115507200))]
theorem block009_data_flat084_step : block009_data_flat084 = (CoefficientMerge.scale (25638115507200 : Int) atom0620Coded) := by decide +kernel
theorem block009_data_flat084_original : block009_data_flat084 = (CoefficientMerge.scale (25638115507200 : Int) atom0620Coded) := by
  rw [block009_data_flat084_step]
def block009_data_flat085 : CoefficientMerge.Poly := [(nat_lit 982, Int.ofNat (nat_lit 17572968856800)), (nat_lit 983, Int.ofNat (nat_lit 25638115507200))]
theorem block009_data_flat085_step : block009_data_flat085 = (CoefficientMerge.fastMerge block009_data_flat083 block009_data_flat084) := by decide +kernel
theorem block009_data_flat085_original : block009_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (17572968856800 : Int) atom0619Coded) (CoefficientMerge.scale (25638115507200 : Int) atom0620Coded)) := by
  rw [block009_data_flat085_step, block009_data_flat083_original, block009_data_flat084_original]
def block009_data_flat086 : CoefficientMerge.Poly := [(nat_lit 981, Int.ofNat (nat_lit 28796952038400)), (nat_lit 982, Int.ofNat (nat_lit 17572968856800)), (nat_lit 983, Int.ofNat (nat_lit 25638115507200))]
theorem block009_data_flat086_step : block009_data_flat086 = (CoefficientMerge.fastMerge block009_data_flat082 block009_data_flat085) := by decide +kernel
theorem block009_data_flat086_original : block009_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (28796952038400 : Int) atom0618Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17572968856800 : Int) atom0619Coded) (CoefficientMerge.scale (25638115507200 : Int) atom0620Coded))) := by
  rw [block009_data_flat086_step, block009_data_flat082_original, block009_data_flat085_original]
def block009_data_flat087 : CoefficientMerge.Poly := [(nat_lit 979, Int.ofNat (nat_lit 19784615558400)), (nat_lit 980, Int.ofNat (nat_lit 20379961324800)), (nat_lit 981, Int.ofNat (nat_lit 28796952038400)), (nat_lit 982, Int.ofNat (nat_lit 17572968856800)), (nat_lit 983, Int.ofNat (nat_lit 25638115507200))]
theorem block009_data_flat087_step : block009_data_flat087 = (CoefficientMerge.fastMerge block009_data_flat081 block009_data_flat086) := by decide +kernel
theorem block009_data_flat087_original : block009_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19784615558400 : Int) atom0616Coded) (CoefficientMerge.scale (20379961324800 : Int) atom0617Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28796952038400 : Int) atom0618Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17572968856800 : Int) atom0619Coded) (CoefficientMerge.scale (25638115507200 : Int) atom0620Coded)))) := by
  rw [block009_data_flat087_step, block009_data_flat081_original, block009_data_flat086_original]
def block009_data_flat088 : CoefficientMerge.Poly := [(nat_lit 984, Int.ofNat (nat_lit 19002620196000))]
theorem block009_data_flat088_step : block009_data_flat088 = (CoefficientMerge.scale (19002620196000 : Int) atom0621Coded) := by decide +kernel
theorem block009_data_flat088_original : block009_data_flat088 = (CoefficientMerge.scale (19002620196000 : Int) atom0621Coded) := by
  rw [block009_data_flat088_step]
def block009_data_flat089 : CoefficientMerge.Poly := [(nat_lit 985, Int.ofNat (nat_lit 19156772224800))]
theorem block009_data_flat089_step : block009_data_flat089 = (CoefficientMerge.scale (19156772224800 : Int) atom0622Coded) := by decide +kernel
theorem block009_data_flat089_original : block009_data_flat089 = (CoefficientMerge.scale (19156772224800 : Int) atom0622Coded) := by
  rw [block009_data_flat089_step]
def block009_data_flat090 : CoefficientMerge.Poly := [(nat_lit 984, Int.ofNat (nat_lit 19002620196000)), (nat_lit 985, Int.ofNat (nat_lit 19156772224800))]
theorem block009_data_flat090_step : block009_data_flat090 = (CoefficientMerge.fastMerge block009_data_flat088 block009_data_flat089) := by decide +kernel
theorem block009_data_flat090_original : block009_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (19002620196000 : Int) atom0621Coded) (CoefficientMerge.scale (19156772224800 : Int) atom0622Coded)) := by
  rw [block009_data_flat090_step, block009_data_flat088_original, block009_data_flat089_original]
def block009_data_flat091 : CoefficientMerge.Poly := [(nat_lit 986, Int.ofNat (nat_lit 23980909226400))]
theorem block009_data_flat091_step : block009_data_flat091 = (CoefficientMerge.scale (23980909226400 : Int) atom0623Coded) := by decide +kernel
theorem block009_data_flat091_original : block009_data_flat091 = (CoefficientMerge.scale (23980909226400 : Int) atom0623Coded) := by
  rw [block009_data_flat091_step]
def block009_data_flat092 : CoefficientMerge.Poly := [(nat_lit 992, Int.ofNat (nat_lit 14748338304000))]
theorem block009_data_flat092_step : block009_data_flat092 = (CoefficientMerge.scale (14748338304000 : Int) atom0624Coded) := by decide +kernel
theorem block009_data_flat092_original : block009_data_flat092 = (CoefficientMerge.scale (14748338304000 : Int) atom0624Coded) := by
  rw [block009_data_flat092_step]
def block009_data_flat093 : CoefficientMerge.Poly := [(nat_lit 993, Int.ofNat (nat_lit 27897168096000))]
theorem block009_data_flat093_step : block009_data_flat093 = (CoefficientMerge.scale (27897168096000 : Int) atom0625Coded) := by decide +kernel
theorem block009_data_flat093_original : block009_data_flat093 = (CoefficientMerge.scale (27897168096000 : Int) atom0625Coded) := by
  rw [block009_data_flat093_step]
def block009_data_flat094 : CoefficientMerge.Poly := [(nat_lit 992, Int.ofNat (nat_lit 14748338304000)), (nat_lit 993, Int.ofNat (nat_lit 27897168096000))]
theorem block009_data_flat094_step : block009_data_flat094 = (CoefficientMerge.fastMerge block009_data_flat092 block009_data_flat093) := by decide +kernel
theorem block009_data_flat094_original : block009_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (14748338304000 : Int) atom0624Coded) (CoefficientMerge.scale (27897168096000 : Int) atom0625Coded)) := by
  rw [block009_data_flat094_step, block009_data_flat092_original, block009_data_flat093_original]
def block009_data_flat095 : CoefficientMerge.Poly := [(nat_lit 986, Int.ofNat (nat_lit 23980909226400)), (nat_lit 992, Int.ofNat (nat_lit 14748338304000)), (nat_lit 993, Int.ofNat (nat_lit 27897168096000))]
theorem block009_data_flat095_step : block009_data_flat095 = (CoefficientMerge.fastMerge block009_data_flat091 block009_data_flat094) := by decide +kernel
theorem block009_data_flat095_original : block009_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (23980909226400 : Int) atom0623Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14748338304000 : Int) atom0624Coded) (CoefficientMerge.scale (27897168096000 : Int) atom0625Coded))) := by
  rw [block009_data_flat095_step, block009_data_flat091_original, block009_data_flat094_original]
def block009_data_flat096 : CoefficientMerge.Poly := [(nat_lit 984, Int.ofNat (nat_lit 19002620196000)), (nat_lit 985, Int.ofNat (nat_lit 19156772224800)), (nat_lit 986, Int.ofNat (nat_lit 23980909226400)), (nat_lit 992, Int.ofNat (nat_lit 14748338304000)), (nat_lit 993, Int.ofNat (nat_lit 27897168096000))]
theorem block009_data_flat096_step : block009_data_flat096 = (CoefficientMerge.fastMerge block009_data_flat090 block009_data_flat095) := by decide +kernel
theorem block009_data_flat096_original : block009_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19002620196000 : Int) atom0621Coded) (CoefficientMerge.scale (19156772224800 : Int) atom0622Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23980909226400 : Int) atom0623Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14748338304000 : Int) atom0624Coded) (CoefficientMerge.scale (27897168096000 : Int) atom0625Coded)))) := by
  rw [block009_data_flat096_step, block009_data_flat090_original, block009_data_flat095_original]
def block009_data_flat097 : CoefficientMerge.Poly := [(nat_lit 979, Int.ofNat (nat_lit 19784615558400)), (nat_lit 980, Int.ofNat (nat_lit 20379961324800)), (nat_lit 981, Int.ofNat (nat_lit 28796952038400)), (nat_lit 982, Int.ofNat (nat_lit 17572968856800)), (nat_lit 983, Int.ofNat (nat_lit 25638115507200)), (nat_lit 984, Int.ofNat (nat_lit 19002620196000)), (nat_lit 985, Int.ofNat (nat_lit 19156772224800)), (nat_lit 986, Int.ofNat (nat_lit 23980909226400)), (nat_lit 992, Int.ofNat (nat_lit 14748338304000)), (nat_lit 993, Int.ofNat (nat_lit 27897168096000))]
theorem block009_data_flat097_step : block009_data_flat097 = (CoefficientMerge.fastMerge block009_data_flat087 block009_data_flat096) := by decide +kernel
theorem block009_data_flat097_original : block009_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19784615558400 : Int) atom0616Coded) (CoefficientMerge.scale (20379961324800 : Int) atom0617Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28796952038400 : Int) atom0618Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17572968856800 : Int) atom0619Coded) (CoefficientMerge.scale (25638115507200 : Int) atom0620Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19002620196000 : Int) atom0621Coded) (CoefficientMerge.scale (19156772224800 : Int) atom0622Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23980909226400 : Int) atom0623Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14748338304000 : Int) atom0624Coded) (CoefficientMerge.scale (27897168096000 : Int) atom0625Coded))))) := by
  rw [block009_data_flat097_step, block009_data_flat087_original, block009_data_flat096_original]
def block009_data_flat098 : CoefficientMerge.Poly := [(nat_lit 994, Int.ofNat (nat_lit 24726406984704))]
theorem block009_data_flat098_step : block009_data_flat098 = (CoefficientMerge.scale (24726406984704 : Int) atom0626Coded) := by decide +kernel
theorem block009_data_flat098_original : block009_data_flat098 = (CoefficientMerge.scale (24726406984704 : Int) atom0626Coded) := by
  rw [block009_data_flat098_step]
def block009_data_flat099 : CoefficientMerge.Poly := [(nat_lit 995, Int.ofNat (nat_lit 24753468155904))]
theorem block009_data_flat099_step : block009_data_flat099 = (CoefficientMerge.scale (24753468155904 : Int) atom0627Coded) := by decide +kernel
theorem block009_data_flat099_original : block009_data_flat099 = (CoefficientMerge.scale (24753468155904 : Int) atom0627Coded) := by
  rw [block009_data_flat099_step]
def block009_data_flat100 : CoefficientMerge.Poly := [(nat_lit 994, Int.ofNat (nat_lit 24726406984704)), (nat_lit 995, Int.ofNat (nat_lit 24753468155904))]
theorem block009_data_flat100_step : block009_data_flat100 = (CoefficientMerge.fastMerge block009_data_flat098 block009_data_flat099) := by decide +kernel
theorem block009_data_flat100_original : block009_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (24726406984704 : Int) atom0626Coded) (CoefficientMerge.scale (24753468155904 : Int) atom0627Coded)) := by
  rw [block009_data_flat100_step, block009_data_flat098_original, block009_data_flat099_original]
def block009_data_flat101 : CoefficientMerge.Poly := [(nat_lit 996, Int.ofNat (nat_lit 26296921384704))]
theorem block009_data_flat101_step : block009_data_flat101 = (CoefficientMerge.scale (26296921384704 : Int) atom0628Coded) := by decide +kernel
theorem block009_data_flat101_original : block009_data_flat101 = (CoefficientMerge.scale (26296921384704 : Int) atom0628Coded) := by
  rw [block009_data_flat101_step]
def block009_data_flat102 : CoefficientMerge.Poly := [(nat_lit 997, Int.ofNat (nat_lit 26381004309504))]
theorem block009_data_flat102_step : block009_data_flat102 = (CoefficientMerge.scale (26381004309504 : Int) atom0629Coded) := by decide +kernel
theorem block009_data_flat102_original : block009_data_flat102 = (CoefficientMerge.scale (26381004309504 : Int) atom0629Coded) := by
  rw [block009_data_flat102_step]
def block009_data_flat103 : CoefficientMerge.Poly := [(nat_lit 998, Int.ofNat (nat_lit 26570925218304))]
theorem block009_data_flat103_step : block009_data_flat103 = (CoefficientMerge.scale (26570925218304 : Int) atom0630Coded) := by decide +kernel
theorem block009_data_flat103_original : block009_data_flat103 = (CoefficientMerge.scale (26570925218304 : Int) atom0630Coded) := by
  rw [block009_data_flat103_step]
def block009_data_flat104 : CoefficientMerge.Poly := [(nat_lit 997, Int.ofNat (nat_lit 26381004309504)), (nat_lit 998, Int.ofNat (nat_lit 26570925218304))]
theorem block009_data_flat104_step : block009_data_flat104 = (CoefficientMerge.fastMerge block009_data_flat102 block009_data_flat103) := by decide +kernel
theorem block009_data_flat104_original : block009_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (26381004309504 : Int) atom0629Coded) (CoefficientMerge.scale (26570925218304 : Int) atom0630Coded)) := by
  rw [block009_data_flat104_step, block009_data_flat102_original, block009_data_flat103_original]
def block009_data_flat105 : CoefficientMerge.Poly := [(nat_lit 996, Int.ofNat (nat_lit 26296921384704)), (nat_lit 997, Int.ofNat (nat_lit 26381004309504)), (nat_lit 998, Int.ofNat (nat_lit 26570925218304))]
theorem block009_data_flat105_step : block009_data_flat105 = (CoefficientMerge.fastMerge block009_data_flat101 block009_data_flat104) := by decide +kernel
theorem block009_data_flat105_original : block009_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (26296921384704 : Int) atom0628Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26381004309504 : Int) atom0629Coded) (CoefficientMerge.scale (26570925218304 : Int) atom0630Coded))) := by
  rw [block009_data_flat105_step, block009_data_flat101_original, block009_data_flat104_original]
def block009_data_flat106 : CoefficientMerge.Poly := [(nat_lit 994, Int.ofNat (nat_lit 24726406984704)), (nat_lit 995, Int.ofNat (nat_lit 24753468155904)), (nat_lit 996, Int.ofNat (nat_lit 26296921384704)), (nat_lit 997, Int.ofNat (nat_lit 26381004309504)), (nat_lit 998, Int.ofNat (nat_lit 26570925218304))]
theorem block009_data_flat106_step : block009_data_flat106 = (CoefficientMerge.fastMerge block009_data_flat100 block009_data_flat105) := by decide +kernel
theorem block009_data_flat106_original : block009_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24726406984704 : Int) atom0626Coded) (CoefficientMerge.scale (24753468155904 : Int) atom0627Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26296921384704 : Int) atom0628Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26381004309504 : Int) atom0629Coded) (CoefficientMerge.scale (26570925218304 : Int) atom0630Coded)))) := by
  rw [block009_data_flat106_step, block009_data_flat100_original, block009_data_flat105_original]
def block009_data_flat107 : CoefficientMerge.Poly := [(nat_lit 999, Int.ofNat (nat_lit 24050700994304))]
theorem block009_data_flat107_step : block009_data_flat107 = (CoefficientMerge.scale (24050700994304 : Int) atom0631Coded) := by decide +kernel
theorem block009_data_flat107_original : block009_data_flat107 = (CoefficientMerge.scale (24050700994304 : Int) atom0631Coded) := by
  rw [block009_data_flat107_step]
def block009_data_flat108 : CoefficientMerge.Poly := [(nat_lit 1000, Int.ofNat (nat_lit 23597569557504))]
theorem block009_data_flat108_step : block009_data_flat108 = (CoefficientMerge.scale (23597569557504 : Int) atom0632Coded) := by decide +kernel
theorem block009_data_flat108_original : block009_data_flat108 = (CoefficientMerge.scale (23597569557504 : Int) atom0632Coded) := by
  rw [block009_data_flat108_step]
def block009_data_flat109 : CoefficientMerge.Poly := [(nat_lit 999, Int.ofNat (nat_lit 24050700994304)), (nat_lit 1000, Int.ofNat (nat_lit 23597569557504))]
theorem block009_data_flat109_step : block009_data_flat109 = (CoefficientMerge.fastMerge block009_data_flat107 block009_data_flat108) := by decide +kernel
theorem block009_data_flat109_original : block009_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (24050700994304 : Int) atom0631Coded) (CoefficientMerge.scale (23597569557504 : Int) atom0632Coded)) := by
  rw [block009_data_flat109_step, block009_data_flat107_original, block009_data_flat108_original]
def block009_data_flat110 : CoefficientMerge.Poly := [(nat_lit 1001, Int.ofNat (nat_lit 24283763541504))]
theorem block009_data_flat110_step : block009_data_flat110 = (CoefficientMerge.scale (24283763541504 : Int) atom0633Coded) := by decide +kernel
theorem block009_data_flat110_original : block009_data_flat110 = (CoefficientMerge.scale (24283763541504 : Int) atom0633Coded) := by
  rw [block009_data_flat110_step]
def block009_data_flat111 : CoefficientMerge.Poly := [(nat_lit 1002, Int.ofNat (nat_lit 33716514645504))]
theorem block009_data_flat111_step : block009_data_flat111 = (CoefficientMerge.scale (33716514645504 : Int) atom0634Coded) := by decide +kernel
theorem block009_data_flat111_original : block009_data_flat111 = (CoefficientMerge.scale (33716514645504 : Int) atom0634Coded) := by
  rw [block009_data_flat111_step]
def block009_data_flat112 : CoefficientMerge.Poly := [(nat_lit 1003, Int.ofNat (nat_lit 22622798557440))]
theorem block009_data_flat112_step : block009_data_flat112 = (CoefficientMerge.scale (22622798557440 : Int) atom0635Coded) := by decide +kernel
theorem block009_data_flat112_original : block009_data_flat112 = (CoefficientMerge.scale (22622798557440 : Int) atom0635Coded) := by
  rw [block009_data_flat112_step]
def block009_data_flat113 : CoefficientMerge.Poly := [(nat_lit 1002, Int.ofNat (nat_lit 33716514645504)), (nat_lit 1003, Int.ofNat (nat_lit 22622798557440))]
theorem block009_data_flat113_step : block009_data_flat113 = (CoefficientMerge.fastMerge block009_data_flat111 block009_data_flat112) := by decide +kernel
theorem block009_data_flat113_original : block009_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (33716514645504 : Int) atom0634Coded) (CoefficientMerge.scale (22622798557440 : Int) atom0635Coded)) := by
  rw [block009_data_flat113_step, block009_data_flat111_original, block009_data_flat112_original]
def block009_data_flat114 : CoefficientMerge.Poly := [(nat_lit 1001, Int.ofNat (nat_lit 24283763541504)), (nat_lit 1002, Int.ofNat (nat_lit 33716514645504)), (nat_lit 1003, Int.ofNat (nat_lit 22622798557440))]
theorem block009_data_flat114_step : block009_data_flat114 = (CoefficientMerge.fastMerge block009_data_flat110 block009_data_flat113) := by decide +kernel
theorem block009_data_flat114_original : block009_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (24283763541504 : Int) atom0633Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33716514645504 : Int) atom0634Coded) (CoefficientMerge.scale (22622798557440 : Int) atom0635Coded))) := by
  rw [block009_data_flat114_step, block009_data_flat110_original, block009_data_flat113_original]
def block009_data_flat115 : CoefficientMerge.Poly := [(nat_lit 999, Int.ofNat (nat_lit 24050700994304)), (nat_lit 1000, Int.ofNat (nat_lit 23597569557504)), (nat_lit 1001, Int.ofNat (nat_lit 24283763541504)), (nat_lit 1002, Int.ofNat (nat_lit 33716514645504)), (nat_lit 1003, Int.ofNat (nat_lit 22622798557440))]
theorem block009_data_flat115_step : block009_data_flat115 = (CoefficientMerge.fastMerge block009_data_flat109 block009_data_flat114) := by decide +kernel
theorem block009_data_flat115_original : block009_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24050700994304 : Int) atom0631Coded) (CoefficientMerge.scale (23597569557504 : Int) atom0632Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24283763541504 : Int) atom0633Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33716514645504 : Int) atom0634Coded) (CoefficientMerge.scale (22622798557440 : Int) atom0635Coded)))) := by
  rw [block009_data_flat115_step, block009_data_flat109_original, block009_data_flat114_original]
def block009_data_flat116 : CoefficientMerge.Poly := [(nat_lit 994, Int.ofNat (nat_lit 24726406984704)), (nat_lit 995, Int.ofNat (nat_lit 24753468155904)), (nat_lit 996, Int.ofNat (nat_lit 26296921384704)), (nat_lit 997, Int.ofNat (nat_lit 26381004309504)), (nat_lit 998, Int.ofNat (nat_lit 26570925218304)), (nat_lit 999, Int.ofNat (nat_lit 24050700994304)), (nat_lit 1000, Int.ofNat (nat_lit 23597569557504)), (nat_lit 1001, Int.ofNat (nat_lit 24283763541504)), (nat_lit 1002, Int.ofNat (nat_lit 33716514645504)), (nat_lit 1003, Int.ofNat (nat_lit 22622798557440))]
theorem block009_data_flat116_step : block009_data_flat116 = (CoefficientMerge.fastMerge block009_data_flat106 block009_data_flat115) := by decide +kernel
theorem block009_data_flat116_original : block009_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24726406984704 : Int) atom0626Coded) (CoefficientMerge.scale (24753468155904 : Int) atom0627Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26296921384704 : Int) atom0628Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26381004309504 : Int) atom0629Coded) (CoefficientMerge.scale (26570925218304 : Int) atom0630Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24050700994304 : Int) atom0631Coded) (CoefficientMerge.scale (23597569557504 : Int) atom0632Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24283763541504 : Int) atom0633Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33716514645504 : Int) atom0634Coded) (CoefficientMerge.scale (22622798557440 : Int) atom0635Coded))))) := by
  rw [block009_data_flat116_step, block009_data_flat106_original, block009_data_flat115_original]
def block009_data_flat117 : CoefficientMerge.Poly := [(nat_lit 979, Int.ofNat (nat_lit 19784615558400)), (nat_lit 980, Int.ofNat (nat_lit 20379961324800)), (nat_lit 981, Int.ofNat (nat_lit 28796952038400)), (nat_lit 982, Int.ofNat (nat_lit 17572968856800)), (nat_lit 983, Int.ofNat (nat_lit 25638115507200)), (nat_lit 984, Int.ofNat (nat_lit 19002620196000)), (nat_lit 985, Int.ofNat (nat_lit 19156772224800)), (nat_lit 986, Int.ofNat (nat_lit 23980909226400)), (nat_lit 992, Int.ofNat (nat_lit 14748338304000)), (nat_lit 993, Int.ofNat (nat_lit 27897168096000)), (nat_lit 994, Int.ofNat (nat_lit 24726406984704)), (nat_lit 995, Int.ofNat (nat_lit 24753468155904)), (nat_lit 996, Int.ofNat (nat_lit 26296921384704)), (nat_lit 997, Int.ofNat (nat_lit 26381004309504)), (nat_lit 998, Int.ofNat (nat_lit 26570925218304)), (nat_lit 999, Int.ofNat (nat_lit 24050700994304)), (nat_lit 1000, Int.ofNat (nat_lit 23597569557504)), (nat_lit 1001, Int.ofNat (nat_lit 24283763541504)), (nat_lit 1002, Int.ofNat (nat_lit 33716514645504)), (nat_lit 1003, Int.ofNat (nat_lit 22622798557440))]
theorem block009_data_flat117_step : block009_data_flat117 = (CoefficientMerge.fastMerge block009_data_flat097 block009_data_flat116) := by decide +kernel
theorem block009_data_flat117_original : block009_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19784615558400 : Int) atom0616Coded) (CoefficientMerge.scale (20379961324800 : Int) atom0617Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28796952038400 : Int) atom0618Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17572968856800 : Int) atom0619Coded) (CoefficientMerge.scale (25638115507200 : Int) atom0620Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19002620196000 : Int) atom0621Coded) (CoefficientMerge.scale (19156772224800 : Int) atom0622Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23980909226400 : Int) atom0623Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14748338304000 : Int) atom0624Coded) (CoefficientMerge.scale (27897168096000 : Int) atom0625Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24726406984704 : Int) atom0626Coded) (CoefficientMerge.scale (24753468155904 : Int) atom0627Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26296921384704 : Int) atom0628Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26381004309504 : Int) atom0629Coded) (CoefficientMerge.scale (26570925218304 : Int) atom0630Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24050700994304 : Int) atom0631Coded) (CoefficientMerge.scale (23597569557504 : Int) atom0632Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24283763541504 : Int) atom0633Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33716514645504 : Int) atom0634Coded) (CoefficientMerge.scale (22622798557440 : Int) atom0635Coded)))))) := by
  rw [block009_data_flat117_step, block009_data_flat097_original, block009_data_flat116_original]
def block009_data_flat118 : CoefficientMerge.Poly := [(nat_lit 1004, Int.ofNat (nat_lit 31566673211904))]
theorem block009_data_flat118_step : block009_data_flat118 = (CoefficientMerge.scale (31566673211904 : Int) atom0636Coded) := by decide +kernel
theorem block009_data_flat118_original : block009_data_flat118 = (CoefficientMerge.scale (31566673211904 : Int) atom0636Coded) := by
  rw [block009_data_flat118_step]
def block009_data_flat119 : CoefficientMerge.Poly := [(nat_lit 1005, Int.ofNat (nat_lit 26162808429312))]
theorem block009_data_flat119_step : block009_data_flat119 = (CoefficientMerge.scale (26162808429312 : Int) atom0637Coded) := by decide +kernel
theorem block009_data_flat119_original : block009_data_flat119 = (CoefficientMerge.scale (26162808429312 : Int) atom0637Coded) := by
  rw [block009_data_flat119_step]
def block009_data_flat120 : CoefficientMerge.Poly := [(nat_lit 1004, Int.ofNat (nat_lit 31566673211904)), (nat_lit 1005, Int.ofNat (nat_lit 26162808429312))]
theorem block009_data_flat120_step : block009_data_flat120 = (CoefficientMerge.fastMerge block009_data_flat118 block009_data_flat119) := by decide +kernel
theorem block009_data_flat120_original : block009_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (31566673211904 : Int) atom0636Coded) (CoefficientMerge.scale (26162808429312 : Int) atom0637Coded)) := by
  rw [block009_data_flat120_step, block009_data_flat118_original, block009_data_flat119_original]
def block009_data_flat121 : CoefficientMerge.Poly := [(nat_lit 1006, Int.ofNat (nat_lit 27693583407360))]
theorem block009_data_flat121_step : block009_data_flat121 = (CoefficientMerge.scale (27693583407360 : Int) atom0638Coded) := by decide +kernel
theorem block009_data_flat121_original : block009_data_flat121 = (CoefficientMerge.scale (27693583407360 : Int) atom0638Coded) := by
  rw [block009_data_flat121_step]
def block009_data_flat122 : CoefficientMerge.Poly := [(nat_lit 1007, Int.ofNat (nat_lit 33894343358208))]
theorem block009_data_flat122_step : block009_data_flat122 = (CoefficientMerge.scale (33894343358208 : Int) atom0639Coded) := by decide +kernel
theorem block009_data_flat122_original : block009_data_flat122 = (CoefficientMerge.scale (33894343358208 : Int) atom0639Coded) := by
  rw [block009_data_flat122_step]
def block009_data_flat123 : CoefficientMerge.Poly := [(nat_lit 1014, Int.ofNat (nat_lit 18705068121600))]
theorem block009_data_flat123_step : block009_data_flat123 = (CoefficientMerge.scale (18705068121600 : Int) atom0640Coded) := by decide +kernel
theorem block009_data_flat123_original : block009_data_flat123 = (CoefficientMerge.scale (18705068121600 : Int) atom0640Coded) := by
  rw [block009_data_flat123_step]
def block009_data_flat124 : CoefficientMerge.Poly := [(nat_lit 1007, Int.ofNat (nat_lit 33894343358208)), (nat_lit 1014, Int.ofNat (nat_lit 18705068121600))]
theorem block009_data_flat124_step : block009_data_flat124 = (CoefficientMerge.fastMerge block009_data_flat122 block009_data_flat123) := by decide +kernel
theorem block009_data_flat124_original : block009_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (33894343358208 : Int) atom0639Coded) (CoefficientMerge.scale (18705068121600 : Int) atom0640Coded)) := by
  rw [block009_data_flat124_step, block009_data_flat122_original, block009_data_flat123_original]
def block009_data_flat125 : CoefficientMerge.Poly := [(nat_lit 1006, Int.ofNat (nat_lit 27693583407360)), (nat_lit 1007, Int.ofNat (nat_lit 33894343358208)), (nat_lit 1014, Int.ofNat (nat_lit 18705068121600))]
theorem block009_data_flat125_step : block009_data_flat125 = (CoefficientMerge.fastMerge block009_data_flat121 block009_data_flat124) := by decide +kernel
theorem block009_data_flat125_original : block009_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (27693583407360 : Int) atom0638Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33894343358208 : Int) atom0639Coded) (CoefficientMerge.scale (18705068121600 : Int) atom0640Coded))) := by
  rw [block009_data_flat125_step, block009_data_flat121_original, block009_data_flat124_original]
def block009_data_flat126 : CoefficientMerge.Poly := [(nat_lit 1004, Int.ofNat (nat_lit 31566673211904)), (nat_lit 1005, Int.ofNat (nat_lit 26162808429312)), (nat_lit 1006, Int.ofNat (nat_lit 27693583407360)), (nat_lit 1007, Int.ofNat (nat_lit 33894343358208)), (nat_lit 1014, Int.ofNat (nat_lit 18705068121600))]
theorem block009_data_flat126_step : block009_data_flat126 = (CoefficientMerge.fastMerge block009_data_flat120 block009_data_flat125) := by decide +kernel
theorem block009_data_flat126_original : block009_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31566673211904 : Int) atom0636Coded) (CoefficientMerge.scale (26162808429312 : Int) atom0637Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27693583407360 : Int) atom0638Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33894343358208 : Int) atom0639Coded) (CoefficientMerge.scale (18705068121600 : Int) atom0640Coded)))) := by
  rw [block009_data_flat126_step, block009_data_flat120_original, block009_data_flat125_original]
def block009_data_flat127 : CoefficientMerge.Poly := [(nat_lit 1015, Int.ofNat (nat_lit 34252905717504))]
theorem block009_data_flat127_step : block009_data_flat127 = (CoefficientMerge.scale (34252905717504 : Int) atom0641Coded) := by decide +kernel
theorem block009_data_flat127_original : block009_data_flat127 = (CoefficientMerge.scale (34252905717504 : Int) atom0641Coded) := by
  rw [block009_data_flat127_step]
def block009_data_flat128 : CoefficientMerge.Poly := [(nat_lit 1016, Int.ofNat (nat_lit 30315115958400))]
theorem block009_data_flat128_step : block009_data_flat128 = (CoefficientMerge.scale (30315115958400 : Int) atom0642Coded) := by decide +kernel
theorem block009_data_flat128_original : block009_data_flat128 = (CoefficientMerge.scale (30315115958400 : Int) atom0642Coded) := by
  rw [block009_data_flat128_step]
def block009_data_flat129 : CoefficientMerge.Poly := [(nat_lit 1015, Int.ofNat (nat_lit 34252905717504)), (nat_lit 1016, Int.ofNat (nat_lit 30315115958400))]
theorem block009_data_flat129_step : block009_data_flat129 = (CoefficientMerge.fastMerge block009_data_flat127 block009_data_flat128) := by decide +kernel
theorem block009_data_flat129_original : block009_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (34252905717504 : Int) atom0641Coded) (CoefficientMerge.scale (30315115958400 : Int) atom0642Coded)) := by
  rw [block009_data_flat129_step, block009_data_flat127_original, block009_data_flat128_original]
def block009_data_flat130 : CoefficientMerge.Poly := [(nat_lit 1017, Int.ofNat (nat_lit 27620120102400))]
theorem block009_data_flat130_step : block009_data_flat130 = (CoefficientMerge.scale (27620120102400 : Int) atom0643Coded) := by decide +kernel
theorem block009_data_flat130_original : block009_data_flat130 = (CoefficientMerge.scale (27620120102400 : Int) atom0643Coded) := by
  rw [block009_data_flat130_step]
def block009_data_flat131 : CoefficientMerge.Poly := [(nat_lit 1018, Int.ofNat (nat_lit 27885899462400))]
theorem block009_data_flat131_step : block009_data_flat131 = (CoefficientMerge.scale (27885899462400 : Int) atom0644Coded) := by decide +kernel
theorem block009_data_flat131_original : block009_data_flat131 = (CoefficientMerge.scale (27885899462400 : Int) atom0644Coded) := by
  rw [block009_data_flat131_step]
def block009_data_flat132 : CoefficientMerge.Poly := [(nat_lit 1019, Int.ofNat (nat_lit 27580741171200))]
theorem block009_data_flat132_step : block009_data_flat132 = (CoefficientMerge.scale (27580741171200 : Int) atom0645Coded) := by decide +kernel
theorem block009_data_flat132_original : block009_data_flat132 = (CoefficientMerge.scale (27580741171200 : Int) atom0645Coded) := by
  rw [block009_data_flat132_step]
def block009_data_flat133 : CoefficientMerge.Poly := [(nat_lit 1018, Int.ofNat (nat_lit 27885899462400)), (nat_lit 1019, Int.ofNat (nat_lit 27580741171200))]
theorem block009_data_flat133_step : block009_data_flat133 = (CoefficientMerge.fastMerge block009_data_flat131 block009_data_flat132) := by decide +kernel
theorem block009_data_flat133_original : block009_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (27885899462400 : Int) atom0644Coded) (CoefficientMerge.scale (27580741171200 : Int) atom0645Coded)) := by
  rw [block009_data_flat133_step, block009_data_flat131_original, block009_data_flat132_original]
def block009_data_flat134 : CoefficientMerge.Poly := [(nat_lit 1017, Int.ofNat (nat_lit 27620120102400)), (nat_lit 1018, Int.ofNat (nat_lit 27885899462400)), (nat_lit 1019, Int.ofNat (nat_lit 27580741171200))]
theorem block009_data_flat134_step : block009_data_flat134 = (CoefficientMerge.fastMerge block009_data_flat130 block009_data_flat133) := by decide +kernel
theorem block009_data_flat134_original : block009_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (27620120102400 : Int) atom0643Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27885899462400 : Int) atom0644Coded) (CoefficientMerge.scale (27580741171200 : Int) atom0645Coded))) := by
  rw [block009_data_flat134_step, block009_data_flat130_original, block009_data_flat133_original]
def block009_data_flat135 : CoefficientMerge.Poly := [(nat_lit 1015, Int.ofNat (nat_lit 34252905717504)), (nat_lit 1016, Int.ofNat (nat_lit 30315115958400)), (nat_lit 1017, Int.ofNat (nat_lit 27620120102400)), (nat_lit 1018, Int.ofNat (nat_lit 27885899462400)), (nat_lit 1019, Int.ofNat (nat_lit 27580741171200))]
theorem block009_data_flat135_step : block009_data_flat135 = (CoefficientMerge.fastMerge block009_data_flat129 block009_data_flat134) := by decide +kernel
theorem block009_data_flat135_original : block009_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34252905717504 : Int) atom0641Coded) (CoefficientMerge.scale (30315115958400 : Int) atom0642Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27620120102400 : Int) atom0643Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27885899462400 : Int) atom0644Coded) (CoefficientMerge.scale (27580741171200 : Int) atom0645Coded)))) := by
  rw [block009_data_flat135_step, block009_data_flat129_original, block009_data_flat134_original]
def block009_data_flat136 : CoefficientMerge.Poly := [(nat_lit 1004, Int.ofNat (nat_lit 31566673211904)), (nat_lit 1005, Int.ofNat (nat_lit 26162808429312)), (nat_lit 1006, Int.ofNat (nat_lit 27693583407360)), (nat_lit 1007, Int.ofNat (nat_lit 33894343358208)), (nat_lit 1014, Int.ofNat (nat_lit 18705068121600)), (nat_lit 1015, Int.ofNat (nat_lit 34252905717504)), (nat_lit 1016, Int.ofNat (nat_lit 30315115958400)), (nat_lit 1017, Int.ofNat (nat_lit 27620120102400)), (nat_lit 1018, Int.ofNat (nat_lit 27885899462400)), (nat_lit 1019, Int.ofNat (nat_lit 27580741171200))]
theorem block009_data_flat136_step : block009_data_flat136 = (CoefficientMerge.fastMerge block009_data_flat126 block009_data_flat135) := by decide +kernel
theorem block009_data_flat136_original : block009_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31566673211904 : Int) atom0636Coded) (CoefficientMerge.scale (26162808429312 : Int) atom0637Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27693583407360 : Int) atom0638Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33894343358208 : Int) atom0639Coded) (CoefficientMerge.scale (18705068121600 : Int) atom0640Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34252905717504 : Int) atom0641Coded) (CoefficientMerge.scale (30315115958400 : Int) atom0642Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27620120102400 : Int) atom0643Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27885899462400 : Int) atom0644Coded) (CoefficientMerge.scale (27580741171200 : Int) atom0645Coded))))) := by
  rw [block009_data_flat136_step, block009_data_flat126_original, block009_data_flat135_original]
def block009_data_flat137 : CoefficientMerge.Poly := [(nat_lit 1020, Int.ofNat (nat_lit 25569126732800))]
theorem block009_data_flat137_step : block009_data_flat137 = (CoefficientMerge.scale (25569126732800 : Int) atom0646Coded) := by decide +kernel
theorem block009_data_flat137_original : block009_data_flat137 = (CoefficientMerge.scale (25569126732800 : Int) atom0646Coded) := by
  rw [block009_data_flat137_step]
def block009_data_flat138 : CoefficientMerge.Poly := [(nat_lit 1021, Int.ofNat (nat_lit 25300591142400))]
theorem block009_data_flat138_step : block009_data_flat138 = (CoefficientMerge.scale (25300591142400 : Int) atom0647Coded) := by decide +kernel
theorem block009_data_flat138_original : block009_data_flat138 = (CoefficientMerge.scale (25300591142400 : Int) atom0647Coded) := by
  rw [block009_data_flat138_step]
def block009_data_flat139 : CoefficientMerge.Poly := [(nat_lit 1020, Int.ofNat (nat_lit 25569126732800)), (nat_lit 1021, Int.ofNat (nat_lit 25300591142400))]
theorem block009_data_flat139_step : block009_data_flat139 = (CoefficientMerge.fastMerge block009_data_flat137 block009_data_flat138) := by decide +kernel
theorem block009_data_flat139_original : block009_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (25569126732800 : Int) atom0646Coded) (CoefficientMerge.scale (25300591142400 : Int) atom0647Coded)) := by
  rw [block009_data_flat139_step, block009_data_flat137_original, block009_data_flat138_original]
def block009_data_flat140 : CoefficientMerge.Poly := [(nat_lit 1022, Int.ofNat (nat_lit 25909467494400))]
theorem block009_data_flat140_step : block009_data_flat140 = (CoefficientMerge.scale (25909467494400 : Int) atom0648Coded) := by decide +kernel
theorem block009_data_flat140_original : block009_data_flat140 = (CoefficientMerge.scale (25909467494400 : Int) atom0648Coded) := by
  rw [block009_data_flat140_step]
def block009_data_flat141 : CoefficientMerge.Poly := [(nat_lit 1023, Int.ofNat (nat_lit 36559971302400))]
theorem block009_data_flat141_step : block009_data_flat141 = (CoefficientMerge.scale (36559971302400 : Int) atom0649Coded) := by decide +kernel
theorem block009_data_flat141_original : block009_data_flat141 = (CoefficientMerge.scale (36559971302400 : Int) atom0649Coded) := by
  rw [block009_data_flat141_step]
def block009_data_flat142 : CoefficientMerge.Poly := [(nat_lit 1024, Int.ofNat (nat_lit 25733446502400))]
theorem block009_data_flat142_step : block009_data_flat142 = (CoefficientMerge.scale (25733446502400 : Int) atom0650Coded) := by decide +kernel
theorem block009_data_flat142_original : block009_data_flat142 = (CoefficientMerge.scale (25733446502400 : Int) atom0650Coded) := by
  rw [block009_data_flat142_step]
def block009_data_flat143 : CoefficientMerge.Poly := [(nat_lit 1023, Int.ofNat (nat_lit 36559971302400)), (nat_lit 1024, Int.ofNat (nat_lit 25733446502400))]
theorem block009_data_flat143_step : block009_data_flat143 = (CoefficientMerge.fastMerge block009_data_flat141 block009_data_flat142) := by decide +kernel
theorem block009_data_flat143_original : block009_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (36559971302400 : Int) atom0649Coded) (CoefficientMerge.scale (25733446502400 : Int) atom0650Coded)) := by
  rw [block009_data_flat143_step, block009_data_flat141_original, block009_data_flat142_original]
def block009_data_flat144 : CoefficientMerge.Poly := [(nat_lit 1022, Int.ofNat (nat_lit 25909467494400)), (nat_lit 1023, Int.ofNat (nat_lit 36559971302400)), (nat_lit 1024, Int.ofNat (nat_lit 25733446502400))]
theorem block009_data_flat144_step : block009_data_flat144 = (CoefficientMerge.fastMerge block009_data_flat140 block009_data_flat143) := by decide +kernel
theorem block009_data_flat144_original : block009_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (25909467494400 : Int) atom0648Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36559971302400 : Int) atom0649Coded) (CoefficientMerge.scale (25733446502400 : Int) atom0650Coded))) := by
  rw [block009_data_flat144_step, block009_data_flat140_original, block009_data_flat143_original]
def block009_data_flat145 : CoefficientMerge.Poly := [(nat_lit 1020, Int.ofNat (nat_lit 25569126732800)), (nat_lit 1021, Int.ofNat (nat_lit 25300591142400)), (nat_lit 1022, Int.ofNat (nat_lit 25909467494400)), (nat_lit 1023, Int.ofNat (nat_lit 36559971302400)), (nat_lit 1024, Int.ofNat (nat_lit 25733446502400))]
theorem block009_data_flat145_step : block009_data_flat145 = (CoefficientMerge.fastMerge block009_data_flat139 block009_data_flat144) := by decide +kernel
theorem block009_data_flat145_original : block009_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25569126732800 : Int) atom0646Coded) (CoefficientMerge.scale (25300591142400 : Int) atom0647Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25909467494400 : Int) atom0648Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36559971302400 : Int) atom0649Coded) (CoefficientMerge.scale (25733446502400 : Int) atom0650Coded)))) := by
  rw [block009_data_flat145_step, block009_data_flat139_original, block009_data_flat144_original]
def block009_data_flat146 : CoefficientMerge.Poly := [(nat_lit 1025, Int.ofNat (nat_lit 35419124966400))]
theorem block009_data_flat146_step : block009_data_flat146 = (CoefficientMerge.scale (35419124966400 : Int) atom0651Coded) := by decide +kernel
theorem block009_data_flat146_original : block009_data_flat146 = (CoefficientMerge.scale (35419124966400 : Int) atom0651Coded) := by
  rw [block009_data_flat146_step]
def block009_data_flat147 : CoefficientMerge.Poly := [(nat_lit 1026, Int.ofNat (nat_lit 32397979622400))]
theorem block009_data_flat147_step : block009_data_flat147 = (CoefficientMerge.scale (32397979622400 : Int) atom0652Coded) := by decide +kernel
theorem block009_data_flat147_original : block009_data_flat147 = (CoefficientMerge.scale (32397979622400 : Int) atom0652Coded) := by
  rw [block009_data_flat147_step]
def block009_data_flat148 : CoefficientMerge.Poly := [(nat_lit 1025, Int.ofNat (nat_lit 35419124966400)), (nat_lit 1026, Int.ofNat (nat_lit 32397979622400))]
theorem block009_data_flat148_step : block009_data_flat148 = (CoefficientMerge.fastMerge block009_data_flat146 block009_data_flat147) := by decide +kernel
theorem block009_data_flat148_original : block009_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (35419124966400 : Int) atom0651Coded) (CoefficientMerge.scale (32397979622400 : Int) atom0652Coded)) := by
  rw [block009_data_flat148_step, block009_data_flat146_original, block009_data_flat147_original]
def block009_data_flat149 : CoefficientMerge.Poly := [(nat_lit 1027, Int.ofNat (nat_lit 36037542643200))]
theorem block009_data_flat149_step : block009_data_flat149 = (CoefficientMerge.scale (36037542643200 : Int) atom0653Coded) := by decide +kernel
theorem block009_data_flat149_original : block009_data_flat149 = (CoefficientMerge.scale (36037542643200 : Int) atom0653Coded) := by
  rw [block009_data_flat149_step]
def block009_data_flat150 : CoefficientMerge.Poly := [(nat_lit 1028, Int.ofNat (nat_lit 44347090636800))]
theorem block009_data_flat150_step : block009_data_flat150 = (CoefficientMerge.scale (44347090636800 : Int) atom0654Coded) := by decide +kernel
theorem block009_data_flat150_original : block009_data_flat150 = (CoefficientMerge.scale (44347090636800 : Int) atom0654Coded) := by
  rw [block009_data_flat150_step]
def block009_data_flat151 : CoefficientMerge.Poly := [(nat_lit 1036, Int.ofNat (nat_lit 20414982530304))]
theorem block009_data_flat151_step : block009_data_flat151 = (CoefficientMerge.scale (20414982530304 : Int) atom0655Coded) := by decide +kernel
theorem block009_data_flat151_original : block009_data_flat151 = (CoefficientMerge.scale (20414982530304 : Int) atom0655Coded) := by
  rw [block009_data_flat151_step]
def block009_data_flat152 : CoefficientMerge.Poly := [(nat_lit 1028, Int.ofNat (nat_lit 44347090636800)), (nat_lit 1036, Int.ofNat (nat_lit 20414982530304))]
theorem block009_data_flat152_step : block009_data_flat152 = (CoefficientMerge.fastMerge block009_data_flat150 block009_data_flat151) := by decide +kernel
theorem block009_data_flat152_original : block009_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (44347090636800 : Int) atom0654Coded) (CoefficientMerge.scale (20414982530304 : Int) atom0655Coded)) := by
  rw [block009_data_flat152_step, block009_data_flat150_original, block009_data_flat151_original]
def block009_data_flat153 : CoefficientMerge.Poly := [(nat_lit 1027, Int.ofNat (nat_lit 36037542643200)), (nat_lit 1028, Int.ofNat (nat_lit 44347090636800)), (nat_lit 1036, Int.ofNat (nat_lit 20414982530304))]
theorem block009_data_flat153_step : block009_data_flat153 = (CoefficientMerge.fastMerge block009_data_flat149 block009_data_flat152) := by decide +kernel
theorem block009_data_flat153_original : block009_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (36037542643200 : Int) atom0653Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44347090636800 : Int) atom0654Coded) (CoefficientMerge.scale (20414982530304 : Int) atom0655Coded))) := by
  rw [block009_data_flat153_step, block009_data_flat149_original, block009_data_flat152_original]
def block009_data_flat154 : CoefficientMerge.Poly := [(nat_lit 1025, Int.ofNat (nat_lit 35419124966400)), (nat_lit 1026, Int.ofNat (nat_lit 32397979622400)), (nat_lit 1027, Int.ofNat (nat_lit 36037542643200)), (nat_lit 1028, Int.ofNat (nat_lit 44347090636800)), (nat_lit 1036, Int.ofNat (nat_lit 20414982530304))]
theorem block009_data_flat154_step : block009_data_flat154 = (CoefficientMerge.fastMerge block009_data_flat148 block009_data_flat153) := by decide +kernel
theorem block009_data_flat154_original : block009_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35419124966400 : Int) atom0651Coded) (CoefficientMerge.scale (32397979622400 : Int) atom0652Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36037542643200 : Int) atom0653Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44347090636800 : Int) atom0654Coded) (CoefficientMerge.scale (20414982530304 : Int) atom0655Coded)))) := by
  rw [block009_data_flat154_step, block009_data_flat148_original, block009_data_flat153_original]
def block009_data_flat155 : CoefficientMerge.Poly := [(nat_lit 1020, Int.ofNat (nat_lit 25569126732800)), (nat_lit 1021, Int.ofNat (nat_lit 25300591142400)), (nat_lit 1022, Int.ofNat (nat_lit 25909467494400)), (nat_lit 1023, Int.ofNat (nat_lit 36559971302400)), (nat_lit 1024, Int.ofNat (nat_lit 25733446502400)), (nat_lit 1025, Int.ofNat (nat_lit 35419124966400)), (nat_lit 1026, Int.ofNat (nat_lit 32397979622400)), (nat_lit 1027, Int.ofNat (nat_lit 36037542643200)), (nat_lit 1028, Int.ofNat (nat_lit 44347090636800)), (nat_lit 1036, Int.ofNat (nat_lit 20414982530304))]
theorem block009_data_flat155_step : block009_data_flat155 = (CoefficientMerge.fastMerge block009_data_flat145 block009_data_flat154) := by decide +kernel
theorem block009_data_flat155_original : block009_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25569126732800 : Int) atom0646Coded) (CoefficientMerge.scale (25300591142400 : Int) atom0647Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25909467494400 : Int) atom0648Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36559971302400 : Int) atom0649Coded) (CoefficientMerge.scale (25733446502400 : Int) atom0650Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35419124966400 : Int) atom0651Coded) (CoefficientMerge.scale (32397979622400 : Int) atom0652Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36037542643200 : Int) atom0653Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44347090636800 : Int) atom0654Coded) (CoefficientMerge.scale (20414982530304 : Int) atom0655Coded))))) := by
  rw [block009_data_flat155_step, block009_data_flat145_original, block009_data_flat154_original]
def block009_data_flat156 : CoefficientMerge.Poly := [(nat_lit 1004, Int.ofNat (nat_lit 31566673211904)), (nat_lit 1005, Int.ofNat (nat_lit 26162808429312)), (nat_lit 1006, Int.ofNat (nat_lit 27693583407360)), (nat_lit 1007, Int.ofNat (nat_lit 33894343358208)), (nat_lit 1014, Int.ofNat (nat_lit 18705068121600)), (nat_lit 1015, Int.ofNat (nat_lit 34252905717504)), (nat_lit 1016, Int.ofNat (nat_lit 30315115958400)), (nat_lit 1017, Int.ofNat (nat_lit 27620120102400)), (nat_lit 1018, Int.ofNat (nat_lit 27885899462400)), (nat_lit 1019, Int.ofNat (nat_lit 27580741171200)), (nat_lit 1020, Int.ofNat (nat_lit 25569126732800)), (nat_lit 1021, Int.ofNat (nat_lit 25300591142400)), (nat_lit 1022, Int.ofNat (nat_lit 25909467494400)), (nat_lit 1023, Int.ofNat (nat_lit 36559971302400)), (nat_lit 1024, Int.ofNat (nat_lit 25733446502400)), (nat_lit 1025, Int.ofNat (nat_lit 35419124966400)), (nat_lit 1026, Int.ofNat (nat_lit 32397979622400)), (nat_lit 1027, Int.ofNat (nat_lit 36037542643200)), (nat_lit 1028, Int.ofNat (nat_lit 44347090636800)), (nat_lit 1036, Int.ofNat (nat_lit 20414982530304))]
theorem block009_data_flat156_step : block009_data_flat156 = (CoefficientMerge.fastMerge block009_data_flat136 block009_data_flat155) := by decide +kernel
theorem block009_data_flat156_original : block009_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31566673211904 : Int) atom0636Coded) (CoefficientMerge.scale (26162808429312 : Int) atom0637Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27693583407360 : Int) atom0638Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33894343358208 : Int) atom0639Coded) (CoefficientMerge.scale (18705068121600 : Int) atom0640Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34252905717504 : Int) atom0641Coded) (CoefficientMerge.scale (30315115958400 : Int) atom0642Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27620120102400 : Int) atom0643Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27885899462400 : Int) atom0644Coded) (CoefficientMerge.scale (27580741171200 : Int) atom0645Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25569126732800 : Int) atom0646Coded) (CoefficientMerge.scale (25300591142400 : Int) atom0647Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25909467494400 : Int) atom0648Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36559971302400 : Int) atom0649Coded) (CoefficientMerge.scale (25733446502400 : Int) atom0650Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35419124966400 : Int) atom0651Coded) (CoefficientMerge.scale (32397979622400 : Int) atom0652Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36037542643200 : Int) atom0653Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44347090636800 : Int) atom0654Coded) (CoefficientMerge.scale (20414982530304 : Int) atom0655Coded)))))) := by
  rw [block009_data_flat156_step, block009_data_flat136_original, block009_data_flat155_original]
def block009_data_flat157 : CoefficientMerge.Poly := [(nat_lit 979, Int.ofNat (nat_lit 19784615558400)), (nat_lit 980, Int.ofNat (nat_lit 20379961324800)), (nat_lit 981, Int.ofNat (nat_lit 28796952038400)), (nat_lit 982, Int.ofNat (nat_lit 17572968856800)), (nat_lit 983, Int.ofNat (nat_lit 25638115507200)), (nat_lit 984, Int.ofNat (nat_lit 19002620196000)), (nat_lit 985, Int.ofNat (nat_lit 19156772224800)), (nat_lit 986, Int.ofNat (nat_lit 23980909226400)), (nat_lit 992, Int.ofNat (nat_lit 14748338304000)), (nat_lit 993, Int.ofNat (nat_lit 27897168096000)), (nat_lit 994, Int.ofNat (nat_lit 24726406984704)), (nat_lit 995, Int.ofNat (nat_lit 24753468155904)), (nat_lit 996, Int.ofNat (nat_lit 26296921384704)), (nat_lit 997, Int.ofNat (nat_lit 26381004309504)), (nat_lit 998, Int.ofNat (nat_lit 26570925218304)), (nat_lit 999, Int.ofNat (nat_lit 24050700994304)), (nat_lit 1000, Int.ofNat (nat_lit 23597569557504)), (nat_lit 1001, Int.ofNat (nat_lit 24283763541504)), (nat_lit 1002, Int.ofNat (nat_lit 33716514645504)), (nat_lit 1003, Int.ofNat (nat_lit 22622798557440)), (nat_lit 1004, Int.ofNat (nat_lit 31566673211904)), (nat_lit 1005, Int.ofNat (nat_lit 26162808429312)), (nat_lit 1006, Int.ofNat (nat_lit 27693583407360)), (nat_lit 1007, Int.ofNat (nat_lit 33894343358208)), (nat_lit 1014, Int.ofNat (nat_lit 18705068121600)), (nat_lit 1015, Int.ofNat (nat_lit 34252905717504)), (nat_lit 1016, Int.ofNat (nat_lit 30315115958400)), (nat_lit 1017, Int.ofNat (nat_lit 27620120102400)), (nat_lit 1018, Int.ofNat (nat_lit 27885899462400)), (nat_lit 1019, Int.ofNat (nat_lit 27580741171200)), (nat_lit 1020, Int.ofNat (nat_lit 25569126732800)), (nat_lit 1021, Int.ofNat (nat_lit 25300591142400)), (nat_lit 1022, Int.ofNat (nat_lit 25909467494400)), (nat_lit 1023, Int.ofNat (nat_lit 36559971302400)), (nat_lit 1024, Int.ofNat (nat_lit 25733446502400)), (nat_lit 1025, Int.ofNat (nat_lit 35419124966400)), (nat_lit 1026, Int.ofNat (nat_lit 32397979622400)), (nat_lit 1027, Int.ofNat (nat_lit 36037542643200)), (nat_lit 1028, Int.ofNat (nat_lit 44347090636800)), (nat_lit 1036, Int.ofNat (nat_lit 20414982530304))]
theorem block009_data_flat157_step : block009_data_flat157 = (CoefficientMerge.fastMerge block009_data_flat117 block009_data_flat156) := by decide +kernel
theorem block009_data_flat157_original : block009_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19784615558400 : Int) atom0616Coded) (CoefficientMerge.scale (20379961324800 : Int) atom0617Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28796952038400 : Int) atom0618Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17572968856800 : Int) atom0619Coded) (CoefficientMerge.scale (25638115507200 : Int) atom0620Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19002620196000 : Int) atom0621Coded) (CoefficientMerge.scale (19156772224800 : Int) atom0622Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23980909226400 : Int) atom0623Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14748338304000 : Int) atom0624Coded) (CoefficientMerge.scale (27897168096000 : Int) atom0625Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24726406984704 : Int) atom0626Coded) (CoefficientMerge.scale (24753468155904 : Int) atom0627Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26296921384704 : Int) atom0628Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26381004309504 : Int) atom0629Coded) (CoefficientMerge.scale (26570925218304 : Int) atom0630Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24050700994304 : Int) atom0631Coded) (CoefficientMerge.scale (23597569557504 : Int) atom0632Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24283763541504 : Int) atom0633Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33716514645504 : Int) atom0634Coded) (CoefficientMerge.scale (22622798557440 : Int) atom0635Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31566673211904 : Int) atom0636Coded) (CoefficientMerge.scale (26162808429312 : Int) atom0637Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27693583407360 : Int) atom0638Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33894343358208 : Int) atom0639Coded) (CoefficientMerge.scale (18705068121600 : Int) atom0640Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34252905717504 : Int) atom0641Coded) (CoefficientMerge.scale (30315115958400 : Int) atom0642Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27620120102400 : Int) atom0643Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27885899462400 : Int) atom0644Coded) (CoefficientMerge.scale (27580741171200 : Int) atom0645Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25569126732800 : Int) atom0646Coded) (CoefficientMerge.scale (25300591142400 : Int) atom0647Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25909467494400 : Int) atom0648Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36559971302400 : Int) atom0649Coded) (CoefficientMerge.scale (25733446502400 : Int) atom0650Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35419124966400 : Int) atom0651Coded) (CoefficientMerge.scale (32397979622400 : Int) atom0652Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36037542643200 : Int) atom0653Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44347090636800 : Int) atom0654Coded) (CoefficientMerge.scale (20414982530304 : Int) atom0655Coded))))))) := by
  rw [block009_data_flat157_step, block009_data_flat117_original, block009_data_flat156_original]
def block009_data_flat158 : CoefficientMerge.Poly := [(nat_lit 931, Int.ofNat (nat_lit 13552237298304)), (nat_lit 932, Int.ofNat (nat_lit 13277370355200)), (nat_lit 933, Int.ofNat (nat_lit 12927508070400)), (nat_lit 934, Int.ofNat (nat_lit 12577645785600)), (nat_lit 935, Int.ofNat (nat_lit 11915859916800)), (nat_lit 936, Int.ofNat (nat_lit 9204520908800)), (nat_lit 937, Int.ofNat (nat_lit 8236260748800)), (nat_lit 938, Int.ofNat (nat_lit 8145412531200)), (nat_lit 939, Int.ofNat (nat_lit 12461669337600)), (nat_lit 940, Int.ofNat (nat_lit 3160358208000)), (nat_lit 941, Int.ofNat (nat_lit 9873255974400)), (nat_lit 942, Int.ofNat (nat_lit 1606273804800)), (nat_lit 944, Int.ofNat (nat_lit 3063711168000)), (nat_lit 948, Int.ofNat (nat_lit 11203324876800)), (nat_lit 949, Int.ofNat (nat_lit 21357062899200)), (nat_lit 950, Int.ofNat (nat_lit 23290231970304)), (nat_lit 951, Int.ofNat (nat_lit 23147295091200)), (nat_lit 952, Int.ofNat (nat_lit 25005300887808)), (nat_lit 953, Int.ofNat (nat_lit 24960064550400)), (nat_lit 954, Int.ofNat (nat_lit 24764837529600)), (nat_lit 955, Int.ofNat (nat_lit 24569610508800)), (nat_lit 956, Int.ofNat (nat_lit 23750536320000)), (nat_lit 957, Int.ofNat (nat_lit 18832355852800)), (nat_lit 958, Int.ofNat (nat_lit 17400333081600)), (nat_lit 959, Int.ofNat (nat_lit 17723134195200)), (nat_lit 960, Int.ofNat (nat_lit 26860145356800)), (nat_lit 961, Int.ofNat (nat_lit 11444942476800)), (nat_lit 962, Int.ofNat (nat_lit 22692313728000)), (nat_lit 963, Int.ofNat (nat_lit 10745217907200)), (nat_lit 964, Int.ofNat (nat_lit 9566124019200)), (nat_lit 965, Int.ofNat (nat_lit 13057015104000)), (nat_lit 970, Int.ofNat (nat_lit 11020661971200)), (nat_lit 971, Int.ofNat (nat_lit 20212761945600)), (nat_lit 972, Int.ofNat (nat_lit 20543623833600)), (nat_lit 973, Int.ofNat (nat_lit 22906127179008)), (nat_lit 974, Int.ofNat (nat_lit 23365388390400)), (nat_lit 975, Int.ofNat (nat_lit 23674658918400)), (nat_lit 976, Int.ofNat (nat_lit 23983929446400)), (nat_lit 977, Int.ofNat (nat_lit 23669352806400)), (nat_lit 978, Int.ofNat (nat_lit 20066681734400)), (nat_lit 979, Int.ofNat (nat_lit 19784615558400)), (nat_lit 980, Int.ofNat (nat_lit 20379961324800)), (nat_lit 981, Int.ofNat (nat_lit 28796952038400)), (nat_lit 982, Int.ofNat (nat_lit 17572968856800)), (nat_lit 983, Int.ofNat (nat_lit 25638115507200)), (nat_lit 984, Int.ofNat (nat_lit 19002620196000)), (nat_lit 985, Int.ofNat (nat_lit 19156772224800)), (nat_lit 986, Int.ofNat (nat_lit 23980909226400)), (nat_lit 992, Int.ofNat (nat_lit 14748338304000)), (nat_lit 993, Int.ofNat (nat_lit 27897168096000)), (nat_lit 994, Int.ofNat (nat_lit 24726406984704)), (nat_lit 995, Int.ofNat (nat_lit 24753468155904)), (nat_lit 996, Int.ofNat (nat_lit 26296921384704)), (nat_lit 997, Int.ofNat (nat_lit 26381004309504)), (nat_lit 998, Int.ofNat (nat_lit 26570925218304)), (nat_lit 999, Int.ofNat (nat_lit 24050700994304)), (nat_lit 1000, Int.ofNat (nat_lit 23597569557504)), (nat_lit 1001, Int.ofNat (nat_lit 24283763541504)), (nat_lit 1002, Int.ofNat (nat_lit 33716514645504)), (nat_lit 1003, Int.ofNat (nat_lit 22622798557440)), (nat_lit 1004, Int.ofNat (nat_lit 31566673211904)), (nat_lit 1005, Int.ofNat (nat_lit 26162808429312)), (nat_lit 1006, Int.ofNat (nat_lit 27693583407360)), (nat_lit 1007, Int.ofNat (nat_lit 33894343358208)), (nat_lit 1014, Int.ofNat (nat_lit 18705068121600)), (nat_lit 1015, Int.ofNat (nat_lit 34252905717504)), (nat_lit 1016, Int.ofNat (nat_lit 30315115958400)), (nat_lit 1017, Int.ofNat (nat_lit 27620120102400)), (nat_lit 1018, Int.ofNat (nat_lit 27885899462400)), (nat_lit 1019, Int.ofNat (nat_lit 27580741171200)), (nat_lit 1020, Int.ofNat (nat_lit 25569126732800)), (nat_lit 1021, Int.ofNat (nat_lit 25300591142400)), (nat_lit 1022, Int.ofNat (nat_lit 25909467494400)), (nat_lit 1023, Int.ofNat (nat_lit 36559971302400)), (nat_lit 1024, Int.ofNat (nat_lit 25733446502400)), (nat_lit 1025, Int.ofNat (nat_lit 35419124966400)), (nat_lit 1026, Int.ofNat (nat_lit 32397979622400)), (nat_lit 1027, Int.ofNat (nat_lit 36037542643200)), (nat_lit 1028, Int.ofNat (nat_lit 44347090636800)), (nat_lit 1036, Int.ofNat (nat_lit 20414982530304))]
theorem block009_data_flat158_step : block009_data_flat158 = (CoefficientMerge.fastMerge block009_data_flat078 block009_data_flat157) := by decide +kernel
theorem block009_data_flat158_original : block009_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13552237298304 : Int) atom0576Coded) (CoefficientMerge.scale (13277370355200 : Int) atom0577Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12927508070400 : Int) atom0578Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12577645785600 : Int) atom0579Coded) (CoefficientMerge.scale (11915859916800 : Int) atom0580Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9204520908800 : Int) atom0581Coded) (CoefficientMerge.scale (8236260748800 : Int) atom0582Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8145412531200 : Int) atom0583Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12461669337600 : Int) atom0584Coded) (CoefficientMerge.scale (3160358208000 : Int) atom0585Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9873255974400 : Int) atom0586Coded) (CoefficientMerge.scale (1606273804800 : Int) atom0587Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3063711168000 : Int) atom0588Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11203324876800 : Int) atom0589Coded) (CoefficientMerge.scale (21357062899200 : Int) atom0590Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23290231970304 : Int) atom0591Coded) (CoefficientMerge.scale (23147295091200 : Int) atom0592Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25005300887808 : Int) atom0593Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24960064550400 : Int) atom0594Coded) (CoefficientMerge.scale (24764837529600 : Int) atom0595Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24569610508800 : Int) atom0596Coded) (CoefficientMerge.scale (23750536320000 : Int) atom0597Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18832355852800 : Int) atom0598Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17400333081600 : Int) atom0599Coded) (CoefficientMerge.scale (17723134195200 : Int) atom0600Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26860145356800 : Int) atom0601Coded) (CoefficientMerge.scale (11444942476800 : Int) atom0602Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22692313728000 : Int) atom0603Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10745217907200 : Int) atom0604Coded) (CoefficientMerge.scale (9566124019200 : Int) atom0605Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13057015104000 : Int) atom0606Coded) (CoefficientMerge.scale (11020661971200 : Int) atom0607Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20212761945600 : Int) atom0608Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20543623833600 : Int) atom0609Coded) (CoefficientMerge.scale (22906127179008 : Int) atom0610Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23365388390400 : Int) atom0611Coded) (CoefficientMerge.scale (23674658918400 : Int) atom0612Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23983929446400 : Int) atom0613Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23669352806400 : Int) atom0614Coded) (CoefficientMerge.scale (20066681734400 : Int) atom0615Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19784615558400 : Int) atom0616Coded) (CoefficientMerge.scale (20379961324800 : Int) atom0617Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28796952038400 : Int) atom0618Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17572968856800 : Int) atom0619Coded) (CoefficientMerge.scale (25638115507200 : Int) atom0620Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19002620196000 : Int) atom0621Coded) (CoefficientMerge.scale (19156772224800 : Int) atom0622Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23980909226400 : Int) atom0623Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14748338304000 : Int) atom0624Coded) (CoefficientMerge.scale (27897168096000 : Int) atom0625Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24726406984704 : Int) atom0626Coded) (CoefficientMerge.scale (24753468155904 : Int) atom0627Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26296921384704 : Int) atom0628Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26381004309504 : Int) atom0629Coded) (CoefficientMerge.scale (26570925218304 : Int) atom0630Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24050700994304 : Int) atom0631Coded) (CoefficientMerge.scale (23597569557504 : Int) atom0632Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24283763541504 : Int) atom0633Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33716514645504 : Int) atom0634Coded) (CoefficientMerge.scale (22622798557440 : Int) atom0635Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31566673211904 : Int) atom0636Coded) (CoefficientMerge.scale (26162808429312 : Int) atom0637Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27693583407360 : Int) atom0638Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33894343358208 : Int) atom0639Coded) (CoefficientMerge.scale (18705068121600 : Int) atom0640Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34252905717504 : Int) atom0641Coded) (CoefficientMerge.scale (30315115958400 : Int) atom0642Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27620120102400 : Int) atom0643Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27885899462400 : Int) atom0644Coded) (CoefficientMerge.scale (27580741171200 : Int) atom0645Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25569126732800 : Int) atom0646Coded) (CoefficientMerge.scale (25300591142400 : Int) atom0647Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25909467494400 : Int) atom0648Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36559971302400 : Int) atom0649Coded) (CoefficientMerge.scale (25733446502400 : Int) atom0650Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35419124966400 : Int) atom0651Coded) (CoefficientMerge.scale (32397979622400 : Int) atom0652Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36037542643200 : Int) atom0653Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44347090636800 : Int) atom0654Coded) (CoefficientMerge.scale (20414982530304 : Int) atom0655Coded)))))))) := by
  rw [block009_data_flat158_step, block009_data_flat078_original, block009_data_flat157_original]
def block009_data_flat159 : CoefficientMerge.Poly := [(nat_lit 931, Int.ofNat (nat_lit 13552237298304)), (nat_lit 932, Int.ofNat (nat_lit 13277370355200)), (nat_lit 933, Int.ofNat (nat_lit 12927508070400)), (nat_lit 934, Int.ofNat (nat_lit 12577645785600)), (nat_lit 935, Int.ofNat (nat_lit 11915859916800)), (nat_lit 936, Int.ofNat (nat_lit 9204520908800)), (nat_lit 937, Int.ofNat (nat_lit 8236260748800)), (nat_lit 938, Int.ofNat (nat_lit 8145412531200)), (nat_lit 939, Int.ofNat (nat_lit 12461669337600)), (nat_lit 940, Int.ofNat (nat_lit 3160358208000)), (nat_lit 941, Int.ofNat (nat_lit 9873255974400)), (nat_lit 942, Int.ofNat (nat_lit 1606273804800)), (nat_lit 944, Int.ofNat (nat_lit 3063711168000)), (nat_lit 948, Int.ofNat (nat_lit 11203324876800)), (nat_lit 949, Int.ofNat (nat_lit 21357062899200)), (nat_lit 950, Int.ofNat (nat_lit 23290231970304)), (nat_lit 951, Int.ofNat (nat_lit 23147295091200)), (nat_lit 952, Int.ofNat (nat_lit 25005300887808)), (nat_lit 953, Int.ofNat (nat_lit 24960064550400)), (nat_lit 954, Int.ofNat (nat_lit 24764837529600)), (nat_lit 955, Int.ofNat (nat_lit 24569610508800)), (nat_lit 956, Int.ofNat (nat_lit 23750536320000)), (nat_lit 957, Int.ofNat (nat_lit 18832355852800)), (nat_lit 958, Int.ofNat (nat_lit 17400333081600)), (nat_lit 959, Int.ofNat (nat_lit 17723134195200)), (nat_lit 960, Int.ofNat (nat_lit 26860145356800)), (nat_lit 961, Int.ofNat (nat_lit 11444942476800)), (nat_lit 962, Int.ofNat (nat_lit 22692313728000)), (nat_lit 963, Int.ofNat (nat_lit 10745217907200)), (nat_lit 964, Int.ofNat (nat_lit 9566124019200)), (nat_lit 965, Int.ofNat (nat_lit 13057015104000)), (nat_lit 970, Int.ofNat (nat_lit 11020661971200)), (nat_lit 971, Int.ofNat (nat_lit 20212761945600)), (nat_lit 972, Int.ofNat (nat_lit 20543623833600)), (nat_lit 973, Int.ofNat (nat_lit 22906127179008)), (nat_lit 974, Int.ofNat (nat_lit 23365388390400)), (nat_lit 975, Int.ofNat (nat_lit 23674658918400)), (nat_lit 976, Int.ofNat (nat_lit 23983929446400)), (nat_lit 977, Int.ofNat (nat_lit 23669352806400)), (nat_lit 978, Int.ofNat (nat_lit 20066681734400)), (nat_lit 979, Int.ofNat (nat_lit 19784615558400)), (nat_lit 980, Int.ofNat (nat_lit 20379961324800)), (nat_lit 981, Int.ofNat (nat_lit 28796952038400)), (nat_lit 982, Int.ofNat (nat_lit 17572968856800)), (nat_lit 983, Int.ofNat (nat_lit 25638115507200)), (nat_lit 984, Int.ofNat (nat_lit 19002620196000)), (nat_lit 985, Int.ofNat (nat_lit 19156772224800)), (nat_lit 986, Int.ofNat (nat_lit 23980909226400)), (nat_lit 992, Int.ofNat (nat_lit 14748338304000)), (nat_lit 993, Int.ofNat (nat_lit 27897168096000)), (nat_lit 994, Int.ofNat (nat_lit 24726406984704)), (nat_lit 995, Int.ofNat (nat_lit 24753468155904)), (nat_lit 996, Int.ofNat (nat_lit 26296921384704)), (nat_lit 997, Int.ofNat (nat_lit 26381004309504)), (nat_lit 998, Int.ofNat (nat_lit 26570925218304)), (nat_lit 999, Int.ofNat (nat_lit 24050700994304)), (nat_lit 1000, Int.ofNat (nat_lit 23597569557504)), (nat_lit 1001, Int.ofNat (nat_lit 24283763541504)), (nat_lit 1002, Int.ofNat (nat_lit 33716514645504)), (nat_lit 1003, Int.ofNat (nat_lit 22622798557440)), (nat_lit 1004, Int.ofNat (nat_lit 31566673211904)), (nat_lit 1005, Int.ofNat (nat_lit 26162808429312)), (nat_lit 1006, Int.ofNat (nat_lit 27693583407360)), (nat_lit 1007, Int.ofNat (nat_lit 33894343358208)), (nat_lit 1014, Int.ofNat (nat_lit 18705068121600)), (nat_lit 1015, Int.ofNat (nat_lit 34252905717504)), (nat_lit 1016, Int.ofNat (nat_lit 30315115958400)), (nat_lit 1017, Int.ofNat (nat_lit 27620120102400)), (nat_lit 1018, Int.ofNat (nat_lit 27885899462400)), (nat_lit 1019, Int.ofNat (nat_lit 27580741171200)), (nat_lit 1020, Int.ofNat (nat_lit 25569126732800)), (nat_lit 1021, Int.ofNat (nat_lit 25300591142400)), (nat_lit 1022, Int.ofNat (nat_lit 25909467494400)), (nat_lit 1023, Int.ofNat (nat_lit 36559971302400)), (nat_lit 1024, Int.ofNat (nat_lit 25733446502400)), (nat_lit 1025, Int.ofNat (nat_lit 35419124966400)), (nat_lit 1026, Int.ofNat (nat_lit 32397979622400)), (nat_lit 1027, Int.ofNat (nat_lit 36037542643200)), (nat_lit 1028, Int.ofNat (nat_lit 44347090636800)), (nat_lit 1036, Int.ofNat (nat_lit 20414982530304))]
theorem block009_data_flat159_step : block009_data_flat159 = (CoefficientMerge.trim block009_data_flat158) := by decide +kernel
theorem block009_data_flat159_original : block009_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13552237298304 : Int) atom0576Coded) (CoefficientMerge.scale (13277370355200 : Int) atom0577Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12927508070400 : Int) atom0578Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12577645785600 : Int) atom0579Coded) (CoefficientMerge.scale (11915859916800 : Int) atom0580Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9204520908800 : Int) atom0581Coded) (CoefficientMerge.scale (8236260748800 : Int) atom0582Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8145412531200 : Int) atom0583Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12461669337600 : Int) atom0584Coded) (CoefficientMerge.scale (3160358208000 : Int) atom0585Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9873255974400 : Int) atom0586Coded) (CoefficientMerge.scale (1606273804800 : Int) atom0587Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3063711168000 : Int) atom0588Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11203324876800 : Int) atom0589Coded) (CoefficientMerge.scale (21357062899200 : Int) atom0590Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23290231970304 : Int) atom0591Coded) (CoefficientMerge.scale (23147295091200 : Int) atom0592Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25005300887808 : Int) atom0593Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24960064550400 : Int) atom0594Coded) (CoefficientMerge.scale (24764837529600 : Int) atom0595Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24569610508800 : Int) atom0596Coded) (CoefficientMerge.scale (23750536320000 : Int) atom0597Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18832355852800 : Int) atom0598Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17400333081600 : Int) atom0599Coded) (CoefficientMerge.scale (17723134195200 : Int) atom0600Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26860145356800 : Int) atom0601Coded) (CoefficientMerge.scale (11444942476800 : Int) atom0602Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22692313728000 : Int) atom0603Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10745217907200 : Int) atom0604Coded) (CoefficientMerge.scale (9566124019200 : Int) atom0605Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13057015104000 : Int) atom0606Coded) (CoefficientMerge.scale (11020661971200 : Int) atom0607Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20212761945600 : Int) atom0608Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20543623833600 : Int) atom0609Coded) (CoefficientMerge.scale (22906127179008 : Int) atom0610Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23365388390400 : Int) atom0611Coded) (CoefficientMerge.scale (23674658918400 : Int) atom0612Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23983929446400 : Int) atom0613Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23669352806400 : Int) atom0614Coded) (CoefficientMerge.scale (20066681734400 : Int) atom0615Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19784615558400 : Int) atom0616Coded) (CoefficientMerge.scale (20379961324800 : Int) atom0617Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28796952038400 : Int) atom0618Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17572968856800 : Int) atom0619Coded) (CoefficientMerge.scale (25638115507200 : Int) atom0620Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19002620196000 : Int) atom0621Coded) (CoefficientMerge.scale (19156772224800 : Int) atom0622Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23980909226400 : Int) atom0623Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14748338304000 : Int) atom0624Coded) (CoefficientMerge.scale (27897168096000 : Int) atom0625Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24726406984704 : Int) atom0626Coded) (CoefficientMerge.scale (24753468155904 : Int) atom0627Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26296921384704 : Int) atom0628Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26381004309504 : Int) atom0629Coded) (CoefficientMerge.scale (26570925218304 : Int) atom0630Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24050700994304 : Int) atom0631Coded) (CoefficientMerge.scale (23597569557504 : Int) atom0632Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24283763541504 : Int) atom0633Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33716514645504 : Int) atom0634Coded) (CoefficientMerge.scale (22622798557440 : Int) atom0635Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31566673211904 : Int) atom0636Coded) (CoefficientMerge.scale (26162808429312 : Int) atom0637Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27693583407360 : Int) atom0638Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33894343358208 : Int) atom0639Coded) (CoefficientMerge.scale (18705068121600 : Int) atom0640Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34252905717504 : Int) atom0641Coded) (CoefficientMerge.scale (30315115958400 : Int) atom0642Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27620120102400 : Int) atom0643Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27885899462400 : Int) atom0644Coded) (CoefficientMerge.scale (27580741171200 : Int) atom0645Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25569126732800 : Int) atom0646Coded) (CoefficientMerge.scale (25300591142400 : Int) atom0647Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25909467494400 : Int) atom0648Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36559971302400 : Int) atom0649Coded) (CoefficientMerge.scale (25733446502400 : Int) atom0650Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35419124966400 : Int) atom0651Coded) (CoefficientMerge.scale (32397979622400 : Int) atom0652Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36037542643200 : Int) atom0653Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44347090636800 : Int) atom0654Coded) (CoefficientMerge.scale (20414982530304 : Int) atom0655Coded))))))))) := by
  rw [block009_data_flat159_step, block009_data_flat158_original]
theorem block009_data : block009 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13552237298304 : Int) atom0576Coded) (CoefficientMerge.scale (13277370355200 : Int) atom0577Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12927508070400 : Int) atom0578Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12577645785600 : Int) atom0579Coded) (CoefficientMerge.scale (11915859916800 : Int) atom0580Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9204520908800 : Int) atom0581Coded) (CoefficientMerge.scale (8236260748800 : Int) atom0582Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8145412531200 : Int) atom0583Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12461669337600 : Int) atom0584Coded) (CoefficientMerge.scale (3160358208000 : Int) atom0585Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9873255974400 : Int) atom0586Coded) (CoefficientMerge.scale (1606273804800 : Int) atom0587Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3063711168000 : Int) atom0588Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11203324876800 : Int) atom0589Coded) (CoefficientMerge.scale (21357062899200 : Int) atom0590Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23290231970304 : Int) atom0591Coded) (CoefficientMerge.scale (23147295091200 : Int) atom0592Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25005300887808 : Int) atom0593Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24960064550400 : Int) atom0594Coded) (CoefficientMerge.scale (24764837529600 : Int) atom0595Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24569610508800 : Int) atom0596Coded) (CoefficientMerge.scale (23750536320000 : Int) atom0597Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18832355852800 : Int) atom0598Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17400333081600 : Int) atom0599Coded) (CoefficientMerge.scale (17723134195200 : Int) atom0600Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26860145356800 : Int) atom0601Coded) (CoefficientMerge.scale (11444942476800 : Int) atom0602Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22692313728000 : Int) atom0603Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10745217907200 : Int) atom0604Coded) (CoefficientMerge.scale (9566124019200 : Int) atom0605Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13057015104000 : Int) atom0606Coded) (CoefficientMerge.scale (11020661971200 : Int) atom0607Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20212761945600 : Int) atom0608Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20543623833600 : Int) atom0609Coded) (CoefficientMerge.scale (22906127179008 : Int) atom0610Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23365388390400 : Int) atom0611Coded) (CoefficientMerge.scale (23674658918400 : Int) atom0612Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23983929446400 : Int) atom0613Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23669352806400 : Int) atom0614Coded) (CoefficientMerge.scale (20066681734400 : Int) atom0615Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19784615558400 : Int) atom0616Coded) (CoefficientMerge.scale (20379961324800 : Int) atom0617Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28796952038400 : Int) atom0618Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17572968856800 : Int) atom0619Coded) (CoefficientMerge.scale (25638115507200 : Int) atom0620Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19002620196000 : Int) atom0621Coded) (CoefficientMerge.scale (19156772224800 : Int) atom0622Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23980909226400 : Int) atom0623Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14748338304000 : Int) atom0624Coded) (CoefficientMerge.scale (27897168096000 : Int) atom0625Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24726406984704 : Int) atom0626Coded) (CoefficientMerge.scale (24753468155904 : Int) atom0627Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26296921384704 : Int) atom0628Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26381004309504 : Int) atom0629Coded) (CoefficientMerge.scale (26570925218304 : Int) atom0630Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24050700994304 : Int) atom0631Coded) (CoefficientMerge.scale (23597569557504 : Int) atom0632Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24283763541504 : Int) atom0633Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33716514645504 : Int) atom0634Coded) (CoefficientMerge.scale (22622798557440 : Int) atom0635Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31566673211904 : Int) atom0636Coded) (CoefficientMerge.scale (26162808429312 : Int) atom0637Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27693583407360 : Int) atom0638Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33894343358208 : Int) atom0639Coded) (CoefficientMerge.scale (18705068121600 : Int) atom0640Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34252905717504 : Int) atom0641Coded) (CoefficientMerge.scale (30315115958400 : Int) atom0642Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27620120102400 : Int) atom0643Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27885899462400 : Int) atom0644Coded) (CoefficientMerge.scale (27580741171200 : Int) atom0645Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25569126732800 : Int) atom0646Coded) (CoefficientMerge.scale (25300591142400 : Int) atom0647Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25909467494400 : Int) atom0648Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36559971302400 : Int) atom0649Coded) (CoefficientMerge.scale (25733446502400 : Int) atom0650Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35419124966400 : Int) atom0651Coded) (CoefficientMerge.scale (32397979622400 : Int) atom0652Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36037542643200 : Int) atom0653Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44347090636800 : Int) atom0654Coded) (CoefficientMerge.scale (20414982530304 : Int) atom0655Coded)))))))) := by
  have h : block009 = block009_data_flat159 := by decide +kernel
  exact h.trans block009_data_flat159_original
theorem block009_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) block009 := by
  rw [block009_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0576Coded_nonneg g hg hA hB) (atom0577Coded_nonneg g hg hA hB)) (add_nonneg (atom0578Coded_nonneg g hg hA hB) (add_nonneg (atom0579Coded_nonneg g hg hA hB) (atom0580Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0581Coded_nonneg g hg hA hB) (atom0582Coded_nonneg g hg hA hB)) (add_nonneg (atom0583Coded_nonneg g hg hA hB) (add_nonneg (atom0584Coded_nonneg g hg hA hB) (atom0585Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0586Coded_nonneg g hg hA hB) (atom0587Coded_nonneg g hg hA hB)) (add_nonneg (atom0588Coded_nonneg g hg hA hB) (add_nonneg (atom0589Coded_nonneg g hg hA hB) (atom0590Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0591Coded_nonneg g hg hA hB) (atom0592Coded_nonneg g hg hA hB)) (add_nonneg (atom0593Coded_nonneg g hg hA hB) (add_nonneg (atom0594Coded_nonneg g hg hA hB) (atom0595Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0596Coded_nonneg g hg hA hB) (atom0597Coded_nonneg g hg hA hB)) (add_nonneg (atom0598Coded_nonneg g hg hA hB) (add_nonneg (atom0599Coded_nonneg g hg hA hB) (atom0600Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0601Coded_nonneg g hg hA hB) (atom0602Coded_nonneg g hg hA hB)) (add_nonneg (atom0603Coded_nonneg g hg hA hB) (add_nonneg (atom0604Coded_nonneg g hg hA hB) (atom0605Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0606Coded_nonneg g hg hA hB) (atom0607Coded_nonneg g hg hA hB)) (add_nonneg (atom0608Coded_nonneg g hg hA hB) (add_nonneg (atom0609Coded_nonneg g hg hA hB) (atom0610Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0611Coded_nonneg g hg hA hB) (atom0612Coded_nonneg g hg hA hB)) (add_nonneg (atom0613Coded_nonneg g hg hA hB) (add_nonneg (atom0614Coded_nonneg g hg hA hB) (atom0615Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0616Coded_nonneg g hg hA hB) (atom0617Coded_nonneg g hg hA hB)) (add_nonneg (atom0618Coded_nonneg g hg hA hB) (add_nonneg (atom0619Coded_nonneg g hg hA hB) (atom0620Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0621Coded_nonneg g hg hA hB) (atom0622Coded_nonneg g hg hA hB)) (add_nonneg (atom0623Coded_nonneg g hg hA hB) (add_nonneg (atom0624Coded_nonneg g hg hA hB) (atom0625Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0626Coded_nonneg g hg hA hB) (atom0627Coded_nonneg g hg hA hB)) (add_nonneg (atom0628Coded_nonneg g hg hA hB) (add_nonneg (atom0629Coded_nonneg g hg hA hB) (atom0630Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0631Coded_nonneg g hg hA hB) (atom0632Coded_nonneg g hg hA hB)) (add_nonneg (atom0633Coded_nonneg g hg hA hB) (add_nonneg (atom0634Coded_nonneg g hg hA hB) (atom0635Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0636Coded_nonneg g hg hA hB) (atom0637Coded_nonneg g hg hA hB)) (add_nonneg (atom0638Coded_nonneg g hg hA hB) (add_nonneg (atom0639Coded_nonneg g hg hA hB) (atom0640Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0641Coded_nonneg g hg hA hB) (atom0642Coded_nonneg g hg hA hB)) (add_nonneg (atom0643Coded_nonneg g hg hA hB) (add_nonneg (atom0644Coded_nonneg g hg hA hB) (atom0645Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0646Coded_nonneg g hg hA hB) (atom0647Coded_nonneg g hg hA hB)) (add_nonneg (atom0648Coded_nonneg g hg hA hB) (add_nonneg (atom0649Coded_nonneg g hg hA hB) (atom0650Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0651Coded_nonneg g hg hA hB) (atom0652Coded_nonneg g hg hA hB)) (add_nonneg (atom0653Coded_nonneg g hg hA hB) (add_nonneg (atom0654Coded_nonneg g hg hA hB) (atom0655Coded_nonneg g hg hA hB))))))))

end APPT.Finite21
