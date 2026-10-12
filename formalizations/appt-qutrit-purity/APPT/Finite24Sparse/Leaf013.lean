-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom0849 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0849 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0849 = ((g 2) * (g 5) * (g 13)) := by
  norm_num [atom0849, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0849_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (250762389292800 : Int) atom0849) := by
  rw [SparsePolynomial.eval_scale, eval_atom0849]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0849Coded : CoefficientMerge.Poly := [(nat_lit 1285, Int.ofNat (nat_lit 1))]
theorem atom0849Coded_decode : atom0849 = SparsePolynomial.decodeCubic 24 atom0849Coded := by decide +kernel
theorem atom0849Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (250762389292800 : Int) atom0849Coded) := by
  have h := atom0849_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0849Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0850 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0850 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0850 = ((g 2) * (g 5) * (g 14)) := by
  norm_num [atom0850, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0850_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (222902250278400 : Int) atom0850) := by
  rw [SparsePolynomial.eval_scale, eval_atom0850]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0850Coded : CoefficientMerge.Poly := [(nat_lit 1286, Int.ofNat (nat_lit 1))]
theorem atom0850Coded_decode : atom0850 = SparsePolynomial.decodeCubic 24 atom0850Coded := by decide +kernel
theorem atom0850Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (222902250278400 : Int) atom0850Coded) := by
  have h := atom0850_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0850Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0851 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0851 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0851 = ((g 2) * (g 5) * (g 15)) := by
  norm_num [atom0851, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0851_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (225353863526400 : Int) atom0851) := by
  rw [SparsePolynomial.eval_scale, eval_atom0851]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 5) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0851Coded : CoefficientMerge.Poly := [(nat_lit 1287, Int.ofNat (nat_lit 1))]
theorem atom0851Coded_decode : atom0851 = SparsePolynomial.decodeCubic 24 atom0851Coded := by decide +kernel
theorem atom0851Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (225353863526400 : Int) atom0851Coded) := by
  have h := atom0851_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0851Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0852 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0852 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0852 = ((g 2) * (g 5) * (g 16)) := by
  norm_num [atom0852, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0852_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (215982966528000 : Int) atom0852) := by
  rw [SparsePolynomial.eval_scale, eval_atom0852]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 5) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0852Coded : CoefficientMerge.Poly := [(nat_lit 1288, Int.ofNat (nat_lit 1))]
theorem atom0852Coded_decode : atom0852 = SparsePolynomial.decodeCubic 24 atom0852Coded := by decide +kernel
theorem atom0852Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (215982966528000 : Int) atom0852Coded) := by
  have h := atom0852_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0852Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0853 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0853 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0853 = ((g 2) * (g 5) * (g 17)) := by
  norm_num [atom0853, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0853_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (216544807987200 : Int) atom0853) := by
  rw [SparsePolynomial.eval_scale, eval_atom0853]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 5) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0853Coded : CoefficientMerge.Poly := [(nat_lit 1289, Int.ofNat (nat_lit 1))]
theorem atom0853Coded_decode : atom0853 = SparsePolynomial.decodeCubic 24 atom0853Coded := by decide +kernel
theorem atom0853Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (216544807987200 : Int) atom0853Coded) := by
  have h := atom0853_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0853Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0854 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0854 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0854 = ((g 2) * (g 5) * (g 18)) := by
  norm_num [atom0854, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0854_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (257815027008000 : Int) atom0854) := by
  rw [SparsePolynomial.eval_scale, eval_atom0854]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 5) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0854Coded : CoefficientMerge.Poly := [(nat_lit 1290, Int.ofNat (nat_lit 1))]
theorem atom0854Coded_decode : atom0854 = SparsePolynomial.decodeCubic 24 atom0854Coded := by decide +kernel
theorem atom0854Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (257815027008000 : Int) atom0854Coded) := by
  have h := atom0854_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0854Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0855 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0855 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0855 = ((g 2) * (g 5) * (g 19)) := by
  norm_num [atom0855, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0855_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (189421289164800 : Int) atom0855) := by
  rw [SparsePolynomial.eval_scale, eval_atom0855]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 5) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0855Coded : CoefficientMerge.Poly := [(nat_lit 1291, Int.ofNat (nat_lit 1))]
theorem atom0855Coded_decode : atom0855 = SparsePolynomial.decodeCubic 24 atom0855Coded := by decide +kernel
theorem atom0855Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (189421289164800 : Int) atom0855Coded) := by
  have h := atom0855_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0855Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0856 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0856 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0856 = ((g 2) * (g 5) * (g 20)) := by
  norm_num [atom0856, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0856_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (268578751795200 : Int) atom0856) := by
  rw [SparsePolynomial.eval_scale, eval_atom0856]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 5) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0856Coded : CoefficientMerge.Poly := [(nat_lit 1292, Int.ofNat (nat_lit 1))]
theorem atom0856Coded_decode : atom0856 = SparsePolynomial.decodeCubic 24 atom0856Coded := by decide +kernel
theorem atom0856Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (268578751795200 : Int) atom0856Coded) := by
  have h := atom0856_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0856Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0857 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0857 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0857 = ((g 2) * (g 5) * (g 21)) := by
  norm_num [atom0857, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0857_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (215630979379200 : Int) atom0857) := by
  rw [SparsePolynomial.eval_scale, eval_atom0857]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 5) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0857Coded : CoefficientMerge.Poly := [(nat_lit 1293, Int.ofNat (nat_lit 1))]
theorem atom0857Coded_decode : atom0857 = SparsePolynomial.decodeCubic 24 atom0857Coded := by decide +kernel
theorem atom0857Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (215630979379200 : Int) atom0857Coded) := by
  have h := atom0857_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0857Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0858 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0858 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0858 = ((g 2) * (g 5) * (g 22)) := by
  norm_num [atom0858, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0858_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (228830374080000 : Int) atom0858) := by
  rw [SparsePolynomial.eval_scale, eval_atom0858]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 5) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0858Coded : CoefficientMerge.Poly := [(nat_lit 1294, Int.ofNat (nat_lit 1))]
theorem atom0858Coded_decode : atom0858 = SparsePolynomial.decodeCubic 24 atom0858Coded := by decide +kernel
theorem atom0858Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (228830374080000 : Int) atom0858Coded) := by
  have h := atom0858_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0858Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0859 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0859 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0859 = ((g 2) * (g 5) * (g 23)) := by
  norm_num [atom0859, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0859_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (274763154758400 : Int) atom0859) := by
  rw [SparsePolynomial.eval_scale, eval_atom0859]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 5) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0859Coded : CoefficientMerge.Poly := [(nat_lit 1295, Int.ofNat (nat_lit 1))]
theorem atom0859Coded_decode : atom0859 = SparsePolynomial.decodeCubic 24 atom0859Coded := by decide +kernel
theorem atom0859Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (274763154758400 : Int) atom0859Coded) := by
  have h := atom0859_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0859Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0860 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0860 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0860 = ((g 2) * (g 6) * (g 6)) := by
  norm_num [atom0860, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0860_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (126234564825600 : Int) atom0860) := by
  rw [SparsePolynomial.eval_scale, eval_atom0860]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0860Coded : CoefficientMerge.Poly := [(nat_lit 1302, Int.ofNat (nat_lit 1))]
theorem atom0860Coded_decode : atom0860 = SparsePolynomial.decodeCubic 24 atom0860Coded := by decide +kernel
theorem atom0860Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (126234564825600 : Int) atom0860Coded) := by
  have h := atom0860_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0860Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0861 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0861 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0861 = ((g 2) * (g 6) * (g 7)) := by
  norm_num [atom0861, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0861_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (224731214400000 : Int) atom0861) := by
  rw [SparsePolynomial.eval_scale, eval_atom0861]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0861Coded : CoefficientMerge.Poly := [(nat_lit 1303, Int.ofNat (nat_lit 1))]
theorem atom0861Coded_decode : atom0861 = SparsePolynomial.decodeCubic 24 atom0861Coded := by decide +kernel
theorem atom0861Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (224731214400000 : Int) atom0861Coded) := by
  have h := atom0861_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0861Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0862 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0862 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0862 = ((g 2) * (g 6) * (g 8)) := by
  norm_num [atom0862, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0862_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (202842807552000 : Int) atom0862) := by
  rw [SparsePolynomial.eval_scale, eval_atom0862]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0862Coded : CoefficientMerge.Poly := [(nat_lit 1304, Int.ofNat (nat_lit 1))]
theorem atom0862Coded_decode : atom0862 = SparsePolynomial.decodeCubic 24 atom0862Coded := by decide +kernel
theorem atom0862Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (202842807552000 : Int) atom0862Coded) := by
  have h := atom0862_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0862Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0863 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0863 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0863 = ((g 2) * (g 6) * (g 9)) := by
  norm_num [atom0863, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0863_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (206600779625328 : Int) atom0863) := by
  rw [SparsePolynomial.eval_scale, eval_atom0863]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0863Coded : CoefficientMerge.Poly := [(nat_lit 1305, Int.ofNat (nat_lit 1))]
theorem atom0863Coded_decode : atom0863 = SparsePolynomial.decodeCubic 24 atom0863Coded := by decide +kernel
theorem atom0863Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (206600779625328 : Int) atom0863Coded) := by
  have h := atom0863_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0863Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0864 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0864 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0864 = ((g 2) * (g 6) * (g 10)) := by
  norm_num [atom0864, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0864_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (226908137622672 : Int) atom0864) := by
  rw [SparsePolynomial.eval_scale, eval_atom0864]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0864Coded : CoefficientMerge.Poly := [(nat_lit 1306, Int.ofNat (nat_lit 1))]
theorem atom0864Coded_decode : atom0864 = SparsePolynomial.decodeCubic 24 atom0864Coded := by decide +kernel
theorem atom0864Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (226908137622672 : Int) atom0864Coded) := by
  have h := atom0864_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0864Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0865 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0865 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0865 = ((g 2) * (g 6) * (g 11)) := by
  norm_num [atom0865, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0865_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (237208830575904 : Int) atom0865) := by
  rw [SparsePolynomial.eval_scale, eval_atom0865]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0865Coded : CoefficientMerge.Poly := [(nat_lit 1307, Int.ofNat (nat_lit 1))]
theorem atom0865Coded_decode : atom0865 = SparsePolynomial.decodeCubic 24 atom0865Coded := by decide +kernel
theorem atom0865Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (237208830575904 : Int) atom0865Coded) := by
  have h := atom0865_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0865Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0866 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0866 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0866 = ((g 2) * (g 6) * (g 12)) := by
  norm_num [atom0866, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0866_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (263089627314624 : Int) atom0866) := by
  rw [SparsePolynomial.eval_scale, eval_atom0866]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0866Coded : CoefficientMerge.Poly := [(nat_lit 1308, Int.ofNat (nat_lit 1))]
theorem atom0866Coded_decode : atom0866 = SparsePolynomial.decodeCubic 24 atom0866Coded := by decide +kernel
theorem atom0866Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (263089627314624 : Int) atom0866Coded) := by
  have h := atom0866_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0866Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0867 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0867 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0867 = ((g 2) * (g 6) * (g 13)) := by
  norm_num [atom0867, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0867_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (254449759132800 : Int) atom0867) := by
  rw [SparsePolynomial.eval_scale, eval_atom0867]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0867Coded : CoefficientMerge.Poly := [(nat_lit 1309, Int.ofNat (nat_lit 1))]
theorem atom0867Coded_decode : atom0867 = SparsePolynomial.decodeCubic 24 atom0867Coded := by decide +kernel
theorem atom0867Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (254449759132800 : Int) atom0867Coded) := by
  have h := atom0867_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0867Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0868 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0868 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0868 = ((g 2) * (g 6) * (g 14)) := by
  norm_num [atom0868, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0868_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (242135628134400 : Int) atom0868) := by
  rw [SparsePolynomial.eval_scale, eval_atom0868]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0868Coded : CoefficientMerge.Poly := [(nat_lit 1310, Int.ofNat (nat_lit 1))]
theorem atom0868Coded_decode : atom0868 = SparsePolynomial.decodeCubic 24 atom0868Coded := by decide +kernel
theorem atom0868Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (242135628134400 : Int) atom0868Coded) := by
  have h := atom0868_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0868Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0869 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0869 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0869 = ((g 2) * (g 6) * (g 15)) := by
  norm_num [atom0869, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0869_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (244608503731200 : Int) atom0869) := by
  rw [SparsePolynomial.eval_scale, eval_atom0869]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0869Coded : CoefficientMerge.Poly := [(nat_lit 1311, Int.ofNat (nat_lit 1))]
theorem atom0869Coded_decode : atom0869 = SparsePolynomial.decodeCubic 24 atom0869Coded := by decide +kernel
theorem atom0869Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (244608503731200 : Int) atom0869Coded) := by
  have h := atom0869_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0869Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0870 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0870 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0870 = ((g 2) * (g 6) * (g 16)) := by
  norm_num [atom0870, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0870_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (235258869081600 : Int) atom0870) := by
  rw [SparsePolynomial.eval_scale, eval_atom0870]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 6) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0870Coded : CoefficientMerge.Poly := [(nat_lit 1312, Int.ofNat (nat_lit 1))]
theorem atom0870Coded_decode : atom0870 = SparsePolynomial.decodeCubic 24 atom0870Coded := by decide +kernel
theorem atom0870Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (235258869081600 : Int) atom0870Coded) := by
  have h := atom0870_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0870Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0871 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0871 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0871 = ((g 2) * (g 6) * (g 17)) := by
  norm_num [atom0871, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0871_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (235841972889600 : Int) atom0871) := by
  rw [SparsePolynomial.eval_scale, eval_atom0871]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0871Coded : CoefficientMerge.Poly := [(nat_lit 1313, Int.ofNat (nat_lit 1))]
theorem atom0871Coded_decode : atom0871 = SparsePolynomial.decodeCubic 24 atom0871Coded := by decide +kernel
theorem atom0871Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (235841972889600 : Int) atom0871Coded) := by
  have h := atom0871_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0871Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0872 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0872 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0872 = ((g 2) * (g 6) * (g 18)) := by
  norm_num [atom0872, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0872_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (274348086566400 : Int) atom0872) := by
  rw [SparsePolynomial.eval_scale, eval_atom0872]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 6) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0872Coded : CoefficientMerge.Poly := [(nat_lit 1314, Int.ofNat (nat_lit 1))]
theorem atom0872Coded_decode : atom0872 = SparsePolynomial.decodeCubic 24 atom0872Coded := by decide +kernel
theorem atom0872Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (274348086566400 : Int) atom0872Coded) := by
  have h := atom0872_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0872Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0873 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0873 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0873 = ((g 2) * (g 6) * (g 19)) := by
  norm_num [atom0873, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0873_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (220533081753600 : Int) atom0873) := by
  rw [SparsePolynomial.eval_scale, eval_atom0873]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 6) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0873Coded : CoefficientMerge.Poly := [(nat_lit 1315, Int.ofNat (nat_lit 1))]
theorem atom0873Coded_decode : atom0873 = SparsePolynomial.decodeCubic 24 atom0873Coded := by decide +kernel
theorem atom0873Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (220533081753600 : Int) atom0873Coded) := by
  have h := atom0873_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0873Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0874 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0874 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0874 = ((g 2) * (g 6) * (g 20)) := by
  norm_num [atom0874, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0874_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (307559875392000 : Int) atom0874) := by
  rw [SparsePolynomial.eval_scale, eval_atom0874]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 6) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0874Coded : CoefficientMerge.Poly := [(nat_lit 1316, Int.ofNat (nat_lit 1))]
theorem atom0874Coded_decode : atom0874 = SparsePolynomial.decodeCubic 24 atom0874Coded := by decide +kernel
theorem atom0874Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (307559875392000 : Int) atom0874Coded) := by
  have h := atom0874_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0874Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0875 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0875 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0875 = ((g 2) * (g 6) * (g 21)) := by
  norm_num [atom0875, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0875_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (270329502643200 : Int) atom0875) := by
  rw [SparsePolynomial.eval_scale, eval_atom0875]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 6) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0875Coded : CoefficientMerge.Poly := [(nat_lit 1317, Int.ofNat (nat_lit 1))]
theorem atom0875Coded_decode : atom0875 = SparsePolynomial.decodeCubic 24 atom0875Coded := by decide +kernel
theorem atom0875Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (270329502643200 : Int) atom0875Coded) := by
  have h := atom0875_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0875Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0876 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0876 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0876 = ((g 2) * (g 6) * (g 22)) := by
  norm_num [atom0876, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0876_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (299246297011200 : Int) atom0876) := by
  rw [SparsePolynomial.eval_scale, eval_atom0876]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 6) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0876Coded : CoefficientMerge.Poly := [(nat_lit 1318, Int.ofNat (nat_lit 1))]
theorem atom0876Coded_decode : atom0876 = SparsePolynomial.decodeCubic 24 atom0876Coded := by decide +kernel
theorem atom0876Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (299246297011200 : Int) atom0876Coded) := by
  have h := atom0876_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0876Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0877 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0877 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0877 = ((g 2) * (g 6) * (g 23)) := by
  norm_num [atom0877, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0877_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (360896477356800 : Int) atom0877) := by
  rw [SparsePolynomial.eval_scale, eval_atom0877]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 6) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0877Coded : CoefficientMerge.Poly := [(nat_lit 1319, Int.ofNat (nat_lit 1))]
theorem atom0877Coded_decode : atom0877 = SparsePolynomial.decodeCubic 24 atom0877Coded := by decide +kernel
theorem atom0877Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (360896477356800 : Int) atom0877Coded) := by
  have h := atom0877_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0877Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0878 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0878 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0878 = ((g 2) * (g 7) * (g 7)) := by
  norm_num [atom0878, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0878_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (135493136486400 : Int) atom0878) := by
  rw [SparsePolynomial.eval_scale, eval_atom0878]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0878Coded : CoefficientMerge.Poly := [(nat_lit 1327, Int.ofNat (nat_lit 1))]
theorem atom0878Coded_decode : atom0878 = SparsePolynomial.decodeCubic 24 atom0878Coded := by decide +kernel
theorem atom0878Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (135493136486400 : Int) atom0878Coded) := by
  have h := atom0878_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0878Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0879 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0879 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0879 = ((g 2) * (g 7) * (g 8)) := by
  norm_num [atom0879, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0879_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (254285879232000 : Int) atom0879) := by
  rw [SparsePolynomial.eval_scale, eval_atom0879]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0879Coded : CoefficientMerge.Poly := [(nat_lit 1328, Int.ofNat (nat_lit 1))]
theorem atom0879Coded_decode : atom0879 = SparsePolynomial.decodeCubic 24 atom0879Coded := by decide +kernel
theorem atom0879Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (254285879232000 : Int) atom0879Coded) := by
  have h := atom0879_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0879Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0880 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0880 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0880 = ((g 2) * (g 7) * (g 9)) := by
  norm_num [atom0880, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0880_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (240589825423728 : Int) atom0880) := by
  rw [SparsePolynomial.eval_scale, eval_atom0880]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0880Coded : CoefficientMerge.Poly := [(nat_lit 1329, Int.ofNat (nat_lit 1))]
theorem atom0880Coded_decode : atom0880 = SparsePolynomial.decodeCubic 24 atom0880Coded := by decide +kernel
theorem atom0880Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (240589825423728 : Int) atom0880Coded) := by
  have h := atom0880_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0880Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0881 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0881 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0881 = ((g 2) * (g 7) * (g 10)) := by
  norm_num [atom0881, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0881_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (257835405193872 : Int) atom0881) := by
  rw [SparsePolynomial.eval_scale, eval_atom0881]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0881Coded : CoefficientMerge.Poly := [(nat_lit 1330, Int.ofNat (nat_lit 1))]
theorem atom0881Coded_decode : atom0881 = SparsePolynomial.decodeCubic 24 atom0881Coded := by decide +kernel
theorem atom0881Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (257835405193872 : Int) atom0881Coded) := by
  have h := atom0881_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0881Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0882 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0882 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0882 = ((g 2) * (g 7) * (g 11)) := by
  norm_num [atom0882, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0882_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (269199215587104 : Int) atom0882) := by
  rw [SparsePolynomial.eval_scale, eval_atom0882]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0882Coded : CoefficientMerge.Poly := [(nat_lit 1331, Int.ofNat (nat_lit 1))]
theorem atom0882Coded_decode : atom0882 = SparsePolynomial.decodeCubic 24 atom0882Coded := by decide +kernel
theorem atom0882Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (269199215587104 : Int) atom0882Coded) := by
  have h := atom0882_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0882Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0883 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0883 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0883 = ((g 2) * (g 7) * (g 12)) := by
  norm_num [atom0883, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0883_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (296143129765824 : Int) atom0883) := by
  rw [SparsePolynomial.eval_scale, eval_atom0883]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0883Coded : CoefficientMerge.Poly := [(nat_lit 1332, Int.ofNat (nat_lit 1))]
theorem atom0883Coded_decode : atom0883 = SparsePolynomial.decodeCubic 24 atom0883Coded := by decide +kernel
theorem atom0883Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (296143129765824 : Int) atom0883Coded) := by
  have h := atom0883_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0883Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0884 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0884 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0884 = ((g 2) * (g 7) * (g 13)) := by
  norm_num [atom0884, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0884_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (286503931190400 : Int) atom0884) := by
  rw [SparsePolynomial.eval_scale, eval_atom0884]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0884Coded : CoefficientMerge.Poly := [(nat_lit 1333, Int.ofNat (nat_lit 1))]
theorem atom0884Coded_decode : atom0884 = SparsePolynomial.decodeCubic 24 atom0884Coded := by decide +kernel
theorem atom0884Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (286503931190400 : Int) atom0884Coded) := by
  have h := atom0884_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0884Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0885 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0885 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0885 = ((g 2) * (g 7) * (g 14)) := by
  norm_num [atom0885, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0885_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (273190469798400 : Int) atom0885) := by
  rw [SparsePolynomial.eval_scale, eval_atom0885]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0885Coded : CoefficientMerge.Poly := [(nat_lit 1334, Int.ofNat (nat_lit 1))]
theorem atom0885Coded_decode : atom0885 = SparsePolynomial.decodeCubic 24 atom0885Coded := by decide +kernel
theorem atom0885Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (273190469798400 : Int) atom0885Coded) := by
  have h := atom0885_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0885Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0886 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0886 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0886 = ((g 2) * (g 7) * (g 15)) := by
  norm_num [atom0886, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0886_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (274664015001600 : Int) atom0886) := by
  rw [SparsePolynomial.eval_scale, eval_atom0886]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0886Coded : CoefficientMerge.Poly := [(nat_lit 1335, Int.ofNat (nat_lit 1))]
theorem atom0886Coded_decode : atom0886 = SparsePolynomial.decodeCubic 24 atom0886Coded := by decide +kernel
theorem atom0886Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (274664015001600 : Int) atom0886Coded) := by
  have h := atom0886_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0886Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0887 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0887 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0887 = ((g 2) * (g 7) * (g 16)) := by
  norm_num [atom0887, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0887_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (264315049958400 : Int) atom0887) := by
  rw [SparsePolynomial.eval_scale, eval_atom0887]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0887Coded : CoefficientMerge.Poly := [(nat_lit 1336, Int.ofNat (nat_lit 1))]
theorem atom0887Coded_decode : atom0887 = SparsePolynomial.decodeCubic 24 atom0887Coded := by decide +kernel
theorem atom0887Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (264315049958400 : Int) atom0887Coded) := by
  have h := atom0887_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0887Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0888 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0888 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0888 = ((g 2) * (g 7) * (g 17)) := by
  norm_num [atom0888, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0888_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (263898823372800 : Int) atom0888) := by
  rw [SparsePolynomial.eval_scale, eval_atom0888]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0888Coded : CoefficientMerge.Poly := [(nat_lit 1337, Int.ofNat (nat_lit 1))]
theorem atom0888Coded_decode : atom0888 = SparsePolynomial.decodeCubic 24 atom0888Coded := by decide +kernel
theorem atom0888Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (263898823372800 : Int) atom0888Coded) := by
  have h := atom0888_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0888Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0889 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0889 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0889 = ((g 2) * (g 7) * (g 18)) := by
  norm_num [atom0889, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0889_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (303735015091200 : Int) atom0889) := by
  rw [SparsePolynomial.eval_scale, eval_atom0889]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 7) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0889Coded : CoefficientMerge.Poly := [(nat_lit 1338, Int.ofNat (nat_lit 1))]
theorem atom0889Coded_decode : atom0889 = SparsePolynomial.decodeCubic 24 atom0889Coded := by decide +kernel
theorem atom0889Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (303735015091200 : Int) atom0889Coded) := by
  have h := atom0889_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0889Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0890 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0890 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0890 = ((g 2) * (g 7) * (g 19)) := by
  norm_num [atom0890, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0890_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (253579496755200 : Int) atom0890) := by
  rw [SparsePolynomial.eval_scale, eval_atom0890]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 7) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0890Coded : CoefficientMerge.Poly := [(nat_lit 1339, Int.ofNat (nat_lit 1))]
theorem atom0890Coded_decode : atom0890 = SparsePolynomial.decodeCubic 24 atom0890Coded := by decide +kernel
theorem atom0890Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (253579496755200 : Int) atom0890Coded) := by
  have h := atom0890_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0890Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0891 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0891 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0891 = ((g 2) * (g 7) * (g 20)) := by
  norm_num [atom0891, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0891_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (344265776870400 : Int) atom0891) := by
  rw [SparsePolynomial.eval_scale, eval_atom0891]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 7) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0891Coded : CoefficientMerge.Poly := [(nat_lit 1340, Int.ofNat (nat_lit 1))]
theorem atom0891Coded_decode : atom0891 = SparsePolynomial.decodeCubic 24 atom0891Coded := by decide +kernel
theorem atom0891Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (344265776870400 : Int) atom0891Coded) := by
  have h := atom0891_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0891Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0892 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0892 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0892 = ((g 2) * (g 7) * (g 21)) := by
  norm_num [atom0892, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0892_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (315353707468800 : Int) atom0892) := by
  rw [SparsePolynomial.eval_scale, eval_atom0892]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 7) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0892Coded : CoefficientMerge.Poly := [(nat_lit 1341, Int.ofNat (nat_lit 1))]
theorem atom0892Coded_decode : atom0892 = SparsePolynomial.decodeCubic 24 atom0892Coded := by decide +kernel
theorem atom0892Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (315353707468800 : Int) atom0892Coded) := by
  have h := atom0892_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0892Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0893 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0893 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0893 = ((g 2) * (g 7) * (g 22)) := by
  norm_num [atom0893, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0893_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (352588805184000 : Int) atom0893) := by
  rw [SparsePolynomial.eval_scale, eval_atom0893]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 7) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0893Coded : CoefficientMerge.Poly := [(nat_lit 1342, Int.ofNat (nat_lit 1))]
theorem atom0893Coded_decode : atom0893 = SparsePolynomial.decodeCubic 24 atom0893Coded := by decide +kernel
theorem atom0893Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (352588805184000 : Int) atom0893Coded) := by
  have h := atom0893_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0893Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0894 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0894 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0894 = ((g 2) * (g 7) * (g 23)) := by
  norm_num [atom0894, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0894_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (422557288876800 : Int) atom0894) := by
  rw [SparsePolynomial.eval_scale, eval_atom0894]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 7) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0894Coded : CoefficientMerge.Poly := [(nat_lit 1343, Int.ofNat (nat_lit 1))]
theorem atom0894Coded_decode : atom0894 = SparsePolynomial.decodeCubic 24 atom0894Coded := by decide +kernel
theorem atom0894Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (422557288876800 : Int) atom0894Coded) := by
  have h := atom0894_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0894Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0895 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0895 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0895 = ((g 2) * (g 8) * (g 8)) := by
  norm_num [atom0895, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0895_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (156809822400000 : Int) atom0895) := by
  rw [SparsePolynomial.eval_scale, eval_atom0895]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0895Coded : CoefficientMerge.Poly := [(nat_lit 1352, Int.ofNat (nat_lit 1))]
theorem atom0895Coded_decode : atom0895 = SparsePolynomial.decodeCubic 24 atom0895Coded := by decide +kernel
theorem atom0895Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (156809822400000 : Int) atom0895Coded) := by
  have h := atom0895_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0895Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0896 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0896 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0896 = ((g 2) * (g 8) * (g 9)) := by
  norm_num [atom0896, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0896_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (298917689941728 : Int) atom0896) := by
  rw [SparsePolynomial.eval_scale, eval_atom0896]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0896Coded : CoefficientMerge.Poly := [(nat_lit 1353, Int.ofNat (nat_lit 1))]
theorem atom0896Coded_decode : atom0896 = SparsePolynomial.decodeCubic 24 atom0896Coded := by decide +kernel
theorem atom0896Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (298917689941728 : Int) atom0896Coded) := by
  have h := atom0896_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0896Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0897 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0897 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0897 = ((g 2) * (g 8) * (g 10)) := by
  norm_num [atom0897, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0897_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (285877758467664 : Int) atom0897) := by
  rw [SparsePolynomial.eval_scale, eval_atom0897]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0897Coded : CoefficientMerge.Poly := [(nat_lit 1354, Int.ofNat (nat_lit 1))]
theorem atom0897Coded_decode : atom0897 = SparsePolynomial.decodeCubic 24 atom0897Coded := by decide +kernel
theorem atom0897Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (285877758467664 : Int) atom0897Coded) := by
  have h := atom0897_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0897Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0898 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0898 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0898 = ((g 2) * (g 8) * (g 11)) := by
  norm_num [atom0898, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0898_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (299464987862304 : Int) atom0898) := by
  rw [SparsePolynomial.eval_scale, eval_atom0898]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0898Coded : CoefficientMerge.Poly := [(nat_lit 1355, Int.ofNat (nat_lit 1))]
theorem atom0898Coded_decode : atom0898 = SparsePolynomial.decodeCubic 24 atom0898Coded := by decide +kernel
theorem atom0898Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (299464987862304 : Int) atom0898Coded) := by
  have h := atom0898_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0898Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0899 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0899 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0899 = ((g 2) * (g 8) * (g 12)) := by
  norm_num [atom0899, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0899_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (321305938329024 : Int) atom0899) := by
  rw [SparsePolynomial.eval_scale, eval_atom0899]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0899Coded : CoefficientMerge.Poly := [(nat_lit 1356, Int.ofNat (nat_lit 1))]
theorem atom0899Coded_decode : atom0899 = SparsePolynomial.decodeCubic 24 atom0899Coded := by decide +kernel
theorem atom0899Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (321305938329024 : Int) atom0899Coded) := by
  have h := atom0899_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0899Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0900 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0900 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0900 = ((g 2) * (g 8) * (g 13)) := by
  norm_num [atom0900, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0900_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (309646816617600 : Int) atom0900) := by
  rw [SparsePolynomial.eval_scale, eval_atom0900]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0900Coded : CoefficientMerge.Poly := [(nat_lit 1357, Int.ofNat (nat_lit 1))]
theorem atom0900Coded_decode : atom0900 = SparsePolynomial.decodeCubic 24 atom0900Coded := by decide +kernel
theorem atom0900Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (309646816617600 : Int) atom0900Coded) := by
  have h := atom0900_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0900Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0901 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0901 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0901 = ((g 2) * (g 8) * (g 14)) := by
  norm_num [atom0901, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0901_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (294313432089600 : Int) atom0901) := by
  rw [SparsePolynomial.eval_scale, eval_atom0901]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0901Coded : CoefficientMerge.Poly := [(nat_lit 1358, Int.ofNat (nat_lit 1))]
theorem atom0901Coded_decode : atom0901 = SparsePolynomial.decodeCubic 24 atom0901Coded := by decide +kernel
theorem atom0901Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (294313432089600 : Int) atom0901Coded) := by
  have h := atom0901_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0901Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0902 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0902 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0902 = ((g 2) * (g 8) * (g 15)) := by
  norm_num [atom0902, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0902_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (293767054156800 : Int) atom0902) := by
  rw [SparsePolynomial.eval_scale, eval_atom0902]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0902Coded : CoefficientMerge.Poly := [(nat_lit 1359, Int.ofNat (nat_lit 1))]
theorem atom0902Coded_decode : atom0902 = SparsePolynomial.decodeCubic 24 atom0902Coded := by decide +kernel
theorem atom0902Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (293767054156800 : Int) atom0902Coded) := by
  have h := atom0902_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0902Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0903 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0903 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0903 = ((g 2) * (g 8) * (g 16)) := by
  norm_num [atom0903, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0903_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (281398165977600 : Int) atom0903) := by
  rw [SparsePolynomial.eval_scale, eval_atom0903]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0903Coded : CoefficientMerge.Poly := [(nat_lit 1360, Int.ofNat (nat_lit 1))]
theorem atom0903Coded_decode : atom0903 = SparsePolynomial.decodeCubic 24 atom0903Coded := by decide +kernel
theorem atom0903Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (281398165977600 : Int) atom0903Coded) := by
  have h := atom0903_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0903Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0904 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0904 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0904 = ((g 2) * (g 8) * (g 17)) := by
  norm_num [atom0904, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0904_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (278962016256000 : Int) atom0904) := by
  rw [SparsePolynomial.eval_scale, eval_atom0904]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0904Coded : CoefficientMerge.Poly := [(nat_lit 1361, Int.ofNat (nat_lit 1))]
theorem atom0904Coded_decode : atom0904 = SparsePolynomial.decodeCubic 24 atom0904Coded := by decide +kernel
theorem atom0904Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (278962016256000 : Int) atom0904Coded) := by
  have h := atom0904_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0904Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0905 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0905 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0905 = ((g 2) * (g 8) * (g 18)) := by
  norm_num [atom0905, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0905_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (320232235276800 : Int) atom0905) := by
  rw [SparsePolynomial.eval_scale, eval_atom0905]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 8) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0905Coded : CoefficientMerge.Poly := [(nat_lit 1362, Int.ofNat (nat_lit 1))]
theorem atom0905Coded_decode : atom0905 = SparsePolynomial.decodeCubic 24 atom0905Coded := by decide +kernel
theorem atom0905Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (320232235276800 : Int) atom0905Coded) := by
  have h := atom0905_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0905Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0906 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0906 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0906 = ((g 2) * (g 8) * (g 19)) := by
  norm_num [atom0906, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0906_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (274964694681600 : Int) atom0906) := by
  rw [SparsePolynomial.eval_scale, eval_atom0906]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 8) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0906Coded : CoefficientMerge.Poly := [(nat_lit 1363, Int.ofNat (nat_lit 1))]
theorem atom0906Coded_decode : atom0906 = SparsePolynomial.decodeCubic 24 atom0906Coded := by decide +kernel
theorem atom0906Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (274964694681600 : Int) atom0906Coded) := by
  have h := atom0906_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0906Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0907 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0907 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0907 = ((g 2) * (g 8) * (g 20)) := by
  norm_num [atom0907, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0907_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (370538952537600 : Int) atom0907) := by
  rw [SparsePolynomial.eval_scale, eval_atom0907]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 8) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0907Coded : CoefficientMerge.Poly := [(nat_lit 1364, Int.ofNat (nat_lit 1))]
theorem atom0907Coded_decode : atom0907 = SparsePolynomial.decodeCubic 24 atom0907Coded := by decide +kernel
theorem atom0907Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (370538952537600 : Int) atom0907Coded) := by
  have h := atom0907_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0907Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0908 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0908 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0908 = ((g 2) * (g 8) * (g 21)) := by
  norm_num [atom0908, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0908_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (353422761753600 : Int) atom0908) := by
  rw [SparsePolynomial.eval_scale, eval_atom0908]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 8) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0908Coded : CoefficientMerge.Poly := [(nat_lit 1365, Int.ofNat (nat_lit 1))]
theorem atom0908Coded_decode : atom0908 = SparsePolynomial.decodeCubic 24 atom0908Coded := by decide +kernel
theorem atom0908Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (353422761753600 : Int) atom0908Coded) := by
  have h := atom0908_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0908Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0909 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0909 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0909 = ((g 2) * (g 8) * (g 22)) := by
  norm_num [atom0909, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0909_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (402453738086400 : Int) atom0909) := by
  rw [SparsePolynomial.eval_scale, eval_atom0909]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 8) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0909Coded : CoefficientMerge.Poly := [(nat_lit 1366, Int.ofNat (nat_lit 1))]
theorem atom0909Coded_decode : atom0909 = SparsePolynomial.decodeCubic 24 atom0909Coded := by decide +kernel
theorem atom0909Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (402453738086400 : Int) atom0909Coded) := by
  have h := atom0909_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0909Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0910 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0910 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0910 = ((g 2) * (g 8) * (g 23)) := by
  norm_num [atom0910, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0910_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (484218100396800 : Int) atom0910) := by
  rw [SparsePolynomial.eval_scale, eval_atom0910]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 8) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0910Coded : CoefficientMerge.Poly := [(nat_lit 1367, Int.ofNat (nat_lit 1))]
theorem atom0910Coded_decode : atom0910 = SparsePolynomial.decodeCubic 24 atom0910Coded := by decide +kernel
theorem atom0910Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (484218100396800 : Int) atom0910Coded) := by
  have h := atom0910_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0910Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0911 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0911 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0911 = ((g 2) * (g 9) * (g 9)) := by
  norm_num [atom0911, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0911_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (183207987772128 : Int) atom0911) := by
  rw [SparsePolynomial.eval_scale, eval_atom0911]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0911Coded : CoefficientMerge.Poly := [(nat_lit 1377, Int.ofNat (nat_lit 1))]
theorem atom0911Coded_decode : atom0911 = SparsePolynomial.decodeCubic 24 atom0911Coded := by decide +kernel
theorem atom0911Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (183207987772128 : Int) atom0911Coded) := by
  have h := atom0911_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0911Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0912 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0912 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0912 = ((g 2) * (g 9) * (g 10)) := by
  norm_num [atom0912, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0912_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (350273600335296 : Int) atom0912) := by
  rw [SparsePolynomial.eval_scale, eval_atom0912]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0912Coded : CoefficientMerge.Poly := [(nat_lit 1378, Int.ofNat (nat_lit 1))]
theorem atom0912Coded_decode : atom0912 = SparsePolynomial.decodeCubic 24 atom0912Coded := by decide +kernel
theorem atom0912Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (350273600335296 : Int) atom0912Coded) := by
  have h := atom0912_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0912Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0913 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0913 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0913 = ((g 2) * (g 9) * (g 11)) := by
  norm_num [atom0913, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0913_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (338777815302432 : Int) atom0913) := by
  rw [SparsePolynomial.eval_scale, eval_atom0913]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0913Coded : CoefficientMerge.Poly := [(nat_lit 1379, Int.ofNat (nat_lit 1))]
theorem atom0913Coded_decode : atom0913 = SparsePolynomial.decodeCubic 24 atom0913Coded := by decide +kernel
theorem atom0913Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (338777815302432 : Int) atom0913Coded) := by
  have h := atom0913_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0913Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0914 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0914 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0914 = ((g 2) * (g 9) * (g 12)) := by
  norm_num [atom0914, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0914_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (360661290466752 : Int) atom0914) := by
  rw [SparsePolynomial.eval_scale, eval_atom0914]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0914Coded : CoefficientMerge.Poly := [(nat_lit 1380, Int.ofNat (nat_lit 1))]
theorem atom0914Coded_decode : atom0914 = SparsePolynomial.decodeCubic 24 atom0914Coded := by decide +kernel
theorem atom0914Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (360661290466752 : Int) atom0914Coded) := by
  have h := atom0914_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0914Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0915 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0915 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0915 = ((g 2) * (g 9) * (g 13)) := by
  norm_num [atom0915, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0915_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (342878612300928 : Int) atom0915) := by
  rw [SparsePolynomial.eval_scale, eval_atom0915]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0915Coded : CoefficientMerge.Poly := [(nat_lit 1381, Int.ofNat (nat_lit 1))]
theorem atom0915Coded_decode : atom0915 = SparsePolynomial.decodeCubic 24 atom0915Coded := by decide +kernel
theorem atom0915Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (342878612300928 : Int) atom0915Coded) := by
  have h := atom0915_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0915Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0916 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0916 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0916 = ((g 2) * (g 9) * (g 14)) := by
  norm_num [atom0916, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0916_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (324504711894528 : Int) atom0916) := by
  rw [SparsePolynomial.eval_scale, eval_atom0916]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0916Coded : CoefficientMerge.Poly := [(nat_lit 1382, Int.ofNat (nat_lit 1))]
theorem atom0916Coded_decode : atom0916 = SparsePolynomial.decodeCubic 24 atom0916Coded := by decide +kernel
theorem atom0916Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (324504711894528 : Int) atom0916Coded) := by
  have h := atom0916_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0916Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0917 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0917 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0917 = ((g 2) * (g 9) * (g 15)) := by
  norm_num [atom0917, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0917_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (320917818083328 : Int) atom0917) := by
  rw [SparsePolynomial.eval_scale, eval_atom0917]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0917Coded : CoefficientMerge.Poly := [(nat_lit 1383, Int.ofNat (nat_lit 1))]
theorem atom0917Coded_decode : atom0917 = SparsePolynomial.decodeCubic 24 atom0917Coded := by decide +kernel
theorem atom0917Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (320917818083328 : Int) atom0917Coded) := by
  have h := atom0917_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0917Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0918 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0918 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0918 = ((g 2) * (g 9) * (g 16)) := by
  norm_num [atom0918, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0918_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (305508414025728 : Int) atom0918) := by
  rw [SparsePolynomial.eval_scale, eval_atom0918]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0918Coded : CoefficientMerge.Poly := [(nat_lit 1384, Int.ofNat (nat_lit 1))]
theorem atom0918Coded_decode : atom0918 = SparsePolynomial.decodeCubic 24 atom0918Coded := by decide +kernel
theorem atom0918Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (305508414025728 : Int) atom0918Coded) := by
  have h := atom0918_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0918Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0919 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0919 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0919 = ((g 2) * (g 9) * (g 17)) := by
  norm_num [atom0919, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0919_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (300031748425728 : Int) atom0919) := by
  rw [SparsePolynomial.eval_scale, eval_atom0919]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0919Coded : CoefficientMerge.Poly := [(nat_lit 1385, Int.ofNat (nat_lit 1))]
theorem atom0919Coded_decode : atom0919 = SparsePolynomial.decodeCubic 24 atom0919Coded := by decide +kernel
theorem atom0919Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (300031748425728 : Int) atom0919Coded) := by
  have h := atom0919_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0919Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0920 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0920 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0920 = ((g 2) * (g 9) * (g 18)) := by
  norm_num [atom0920, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0920_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (340464919398912 : Int) atom0920) := by
  rw [SparsePolynomial.eval_scale, eval_atom0920]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 9) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0920Coded : CoefficientMerge.Poly := [(nat_lit 1386, Int.ofNat (nat_lit 1))]
theorem atom0920Coded_decode : atom0920 = SparsePolynomial.decodeCubic 24 atom0920Coded := by decide +kernel
theorem atom0920Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (340464919398912 : Int) atom0920Coded) := by
  have h := atom0920_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0920Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0921 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0921 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0921 = ((g 2) * (g 9) * (g 19)) := by
  norm_num [atom0921, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0921_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (296563798586880 : Int) atom0921) := by
  rw [SparsePolynomial.eval_scale, eval_atom0921]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 9) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0921Coded : CoefficientMerge.Poly := [(nat_lit 1387, Int.ofNat (nat_lit 1))]
theorem atom0921Coded_decode : atom0921 = SparsePolynomial.decodeCubic 24 atom0921Coded := by decide +kernel
theorem atom0921Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (296563798586880 : Int) atom0921Coded) := by
  have h := atom0921_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0921Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0922 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0922 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0922 = ((g 2) * (g 9) * (g 20)) := by
  norm_num [atom0922, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0922_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (393504476226048 : Int) atom0922) := by
  rw [SparsePolynomial.eval_scale, eval_atom0922]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 9) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0922Coded : CoefficientMerge.Poly := [(nat_lit 1388, Int.ofNat (nat_lit 1))]
theorem atom0922Coded_decode : atom0922 = SparsePolynomial.decodeCubic 24 atom0922Coded := by decide +kernel
theorem atom0922Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (393504476226048 : Int) atom0922Coded) := by
  have h := atom0922_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0922Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0923 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0923 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0923 = ((g 2) * (g 9) * (g 21)) := by
  norm_num [atom0923, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0923_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (382161640886784 : Int) atom0923) := by
  rw [SparsePolynomial.eval_scale, eval_atom0923]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 9) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0923Coded : CoefficientMerge.Poly := [(nat_lit 1389, Int.ofNat (nat_lit 1))]
theorem atom0923Coded_decode : atom0923 = SparsePolynomial.decodeCubic 24 atom0923Coded := by decide +kernel
theorem atom0923Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (382161640886784 : Int) atom0923Coded) := by
  have h := atom0923_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0923Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0924 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0924 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0924 = ((g 2) * (g 9) * (g 22)) := by
  norm_num [atom0924, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0924_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (436965972664320 : Int) atom0924) := by
  rw [SparsePolynomial.eval_scale, eval_atom0924]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 9) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0924Coded : CoefficientMerge.Poly := [(nat_lit 1390, Int.ofNat (nat_lit 1))]
theorem atom0924Coded_decode : atom0924 = SparsePolynomial.decodeCubic 24 atom0924Coded := by decide +kernel
theorem atom0924Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (436965972664320 : Int) atom0924Coded) := by
  have h := atom0924_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0924Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0925 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0925 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0925 = ((g 2) * (g 9) * (g 23)) := by
  norm_num [atom0925, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0925_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (524503690419456 : Int) atom0925) := by
  rw [SparsePolynomial.eval_scale, eval_atom0925]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 9) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0925Coded : CoefficientMerge.Poly := [(nat_lit 1391, Int.ofNat (nat_lit 1))]
theorem atom0925Coded_decode : atom0925 = SparsePolynomial.decodeCubic 24 atom0925Coded := by decide +kernel
theorem atom0925Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (524503690419456 : Int) atom0925Coded) := by
  have h := atom0925_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0925Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0926 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0926 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0926 = ((g 2) * (g 10) * (g 10)) := by
  norm_num [atom0926, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0926_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (208165732793568 : Int) atom0926) := by
  rw [SparsePolynomial.eval_scale, eval_atom0926]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0926Coded : CoefficientMerge.Poly := [(nat_lit 1402, Int.ofNat (nat_lit 1))]
theorem atom0926Coded_decode : atom0926 = SparsePolynomial.decodeCubic 24 atom0926Coded := by decide +kernel
theorem atom0926Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (208165732793568 : Int) atom0926Coded) := by
  have h := atom0926_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0926Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0927 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0927 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0927 = ((g 2) * (g 10) * (g 11)) := by
  norm_num [atom0927, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0927_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (407982508176672 : Int) atom0927) := by
  rw [SparsePolynomial.eval_scale, eval_atom0927]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0927Coded : CoefficientMerge.Poly := [(nat_lit 1403, Int.ofNat (nat_lit 1))]
theorem atom0927Coded_decode : atom0927 = SparsePolynomial.decodeCubic 24 atom0927Coded := by decide +kernel
theorem atom0927Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (407982508176672 : Int) atom0927Coded) := by
  have h := atom0927_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0927Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0928 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0928 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0928 = ((g 2) * (g 10) * (g 12)) := by
  norm_num [atom0928, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0928_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (422721834144192 : Int) atom0928) := by
  rw [SparsePolynomial.eval_scale, eval_atom0928]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0928Coded : CoefficientMerge.Poly := [(nat_lit 1404, Int.ofNat (nat_lit 1))]
theorem atom0928Coded_decode : atom0928 = SparsePolynomial.decodeCubic 24 atom0928Coded := by decide +kernel
theorem atom0928Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (422721834144192 : Int) atom0928Coded) := by
  have h := atom0928_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0928Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block013 : CoefficientMerge.Poly := [(nat_lit 1285, Int.ofNat (nat_lit 250762389292800)), (nat_lit 1286, Int.ofNat (nat_lit 222902250278400)), (nat_lit 1287, Int.ofNat (nat_lit 225353863526400)), (nat_lit 1288, Int.ofNat (nat_lit 215982966528000)), (nat_lit 1289, Int.ofNat (nat_lit 216544807987200)), (nat_lit 1290, Int.ofNat (nat_lit 257815027008000)), (nat_lit 1291, Int.ofNat (nat_lit 189421289164800)), (nat_lit 1292, Int.ofNat (nat_lit 268578751795200)), (nat_lit 1293, Int.ofNat (nat_lit 215630979379200)), (nat_lit 1294, Int.ofNat (nat_lit 228830374080000)), (nat_lit 1295, Int.ofNat (nat_lit 274763154758400)), (nat_lit 1302, Int.ofNat (nat_lit 126234564825600)), (nat_lit 1303, Int.ofNat (nat_lit 224731214400000)), (nat_lit 1304, Int.ofNat (nat_lit 202842807552000)), (nat_lit 1305, Int.ofNat (nat_lit 206600779625328)), (nat_lit 1306, Int.ofNat (nat_lit 226908137622672)), (nat_lit 1307, Int.ofNat (nat_lit 237208830575904)), (nat_lit 1308, Int.ofNat (nat_lit 263089627314624)), (nat_lit 1309, Int.ofNat (nat_lit 254449759132800)), (nat_lit 1310, Int.ofNat (nat_lit 242135628134400)), (nat_lit 1311, Int.ofNat (nat_lit 244608503731200)), (nat_lit 1312, Int.ofNat (nat_lit 235258869081600)), (nat_lit 1313, Int.ofNat (nat_lit 235841972889600)), (nat_lit 1314, Int.ofNat (nat_lit 274348086566400)), (nat_lit 1315, Int.ofNat (nat_lit 220533081753600)), (nat_lit 1316, Int.ofNat (nat_lit 307559875392000)), (nat_lit 1317, Int.ofNat (nat_lit 270329502643200)), (nat_lit 1318, Int.ofNat (nat_lit 299246297011200)), (nat_lit 1319, Int.ofNat (nat_lit 360896477356800)), (nat_lit 1327, Int.ofNat (nat_lit 135493136486400)), (nat_lit 1328, Int.ofNat (nat_lit 254285879232000)), (nat_lit 1329, Int.ofNat (nat_lit 240589825423728)), (nat_lit 1330, Int.ofNat (nat_lit 257835405193872)), (nat_lit 1331, Int.ofNat (nat_lit 269199215587104)), (nat_lit 1332, Int.ofNat (nat_lit 296143129765824)), (nat_lit 1333, Int.ofNat (nat_lit 286503931190400)), (nat_lit 1334, Int.ofNat (nat_lit 273190469798400)), (nat_lit 1335, Int.ofNat (nat_lit 274664015001600)), (nat_lit 1336, Int.ofNat (nat_lit 264315049958400)), (nat_lit 1337, Int.ofNat (nat_lit 263898823372800)), (nat_lit 1338, Int.ofNat (nat_lit 303735015091200)), (nat_lit 1339, Int.ofNat (nat_lit 253579496755200)), (nat_lit 1340, Int.ofNat (nat_lit 344265776870400)), (nat_lit 1341, Int.ofNat (nat_lit 315353707468800)), (nat_lit 1342, Int.ofNat (nat_lit 352588805184000)), (nat_lit 1343, Int.ofNat (nat_lit 422557288876800)), (nat_lit 1352, Int.ofNat (nat_lit 156809822400000)), (nat_lit 1353, Int.ofNat (nat_lit 298917689941728)), (nat_lit 1354, Int.ofNat (nat_lit 285877758467664)), (nat_lit 1355, Int.ofNat (nat_lit 299464987862304)), (nat_lit 1356, Int.ofNat (nat_lit 321305938329024)), (nat_lit 1357, Int.ofNat (nat_lit 309646816617600)), (nat_lit 1358, Int.ofNat (nat_lit 294313432089600)), (nat_lit 1359, Int.ofNat (nat_lit 293767054156800)), (nat_lit 1360, Int.ofNat (nat_lit 281398165977600)), (nat_lit 1361, Int.ofNat (nat_lit 278962016256000)), (nat_lit 1362, Int.ofNat (nat_lit 320232235276800)), (nat_lit 1363, Int.ofNat (nat_lit 274964694681600)), (nat_lit 1364, Int.ofNat (nat_lit 370538952537600)), (nat_lit 1365, Int.ofNat (nat_lit 353422761753600)), (nat_lit 1366, Int.ofNat (nat_lit 402453738086400)), (nat_lit 1367, Int.ofNat (nat_lit 484218100396800)), (nat_lit 1377, Int.ofNat (nat_lit 183207987772128)), (nat_lit 1378, Int.ofNat (nat_lit 350273600335296)), (nat_lit 1379, Int.ofNat (nat_lit 338777815302432)), (nat_lit 1380, Int.ofNat (nat_lit 360661290466752)), (nat_lit 1381, Int.ofNat (nat_lit 342878612300928)), (nat_lit 1382, Int.ofNat (nat_lit 324504711894528)), (nat_lit 1383, Int.ofNat (nat_lit 320917818083328)), (nat_lit 1384, Int.ofNat (nat_lit 305508414025728)), (nat_lit 1385, Int.ofNat (nat_lit 300031748425728)), (nat_lit 1386, Int.ofNat (nat_lit 340464919398912)), (nat_lit 1387, Int.ofNat (nat_lit 296563798586880)), (nat_lit 1388, Int.ofNat (nat_lit 393504476226048)), (nat_lit 1389, Int.ofNat (nat_lit 382161640886784)), (nat_lit 1390, Int.ofNat (nat_lit 436965972664320)), (nat_lit 1391, Int.ofNat (nat_lit 524503690419456)), (nat_lit 1402, Int.ofNat (nat_lit 208165732793568)), (nat_lit 1403, Int.ofNat (nat_lit 407982508176672)), (nat_lit 1404, Int.ofNat (nat_lit 422721834144192))]
def block013_data_flat000 : CoefficientMerge.Poly := [(nat_lit 1285, Int.ofNat (nat_lit 250762389292800))]
theorem block013_data_flat000_step : block013_data_flat000 = (CoefficientMerge.scale (250762389292800 : Int) atom0849Coded) := by decide +kernel
theorem block013_data_flat000_original : block013_data_flat000 = (CoefficientMerge.scale (250762389292800 : Int) atom0849Coded) := by
  rw [block013_data_flat000_step]
def block013_data_flat001 : CoefficientMerge.Poly := [(nat_lit 1286, Int.ofNat (nat_lit 222902250278400))]
theorem block013_data_flat001_step : block013_data_flat001 = (CoefficientMerge.scale (222902250278400 : Int) atom0850Coded) := by decide +kernel
theorem block013_data_flat001_original : block013_data_flat001 = (CoefficientMerge.scale (222902250278400 : Int) atom0850Coded) := by
  rw [block013_data_flat001_step]
def block013_data_flat002 : CoefficientMerge.Poly := [(nat_lit 1285, Int.ofNat (nat_lit 250762389292800)), (nat_lit 1286, Int.ofNat (nat_lit 222902250278400))]
theorem block013_data_flat002_step : block013_data_flat002 = (CoefficientMerge.fastMerge block013_data_flat000 block013_data_flat001) := by decide +kernel
theorem block013_data_flat002_original : block013_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (250762389292800 : Int) atom0849Coded) (CoefficientMerge.scale (222902250278400 : Int) atom0850Coded)) := by
  rw [block013_data_flat002_step, block013_data_flat000_original, block013_data_flat001_original]
def block013_data_flat003 : CoefficientMerge.Poly := [(nat_lit 1287, Int.ofNat (nat_lit 225353863526400))]
theorem block013_data_flat003_step : block013_data_flat003 = (CoefficientMerge.scale (225353863526400 : Int) atom0851Coded) := by decide +kernel
theorem block013_data_flat003_original : block013_data_flat003 = (CoefficientMerge.scale (225353863526400 : Int) atom0851Coded) := by
  rw [block013_data_flat003_step]
def block013_data_flat004 : CoefficientMerge.Poly := [(nat_lit 1288, Int.ofNat (nat_lit 215982966528000))]
theorem block013_data_flat004_step : block013_data_flat004 = (CoefficientMerge.scale (215982966528000 : Int) atom0852Coded) := by decide +kernel
theorem block013_data_flat004_original : block013_data_flat004 = (CoefficientMerge.scale (215982966528000 : Int) atom0852Coded) := by
  rw [block013_data_flat004_step]
def block013_data_flat005 : CoefficientMerge.Poly := [(nat_lit 1289, Int.ofNat (nat_lit 216544807987200))]
theorem block013_data_flat005_step : block013_data_flat005 = (CoefficientMerge.scale (216544807987200 : Int) atom0853Coded) := by decide +kernel
theorem block013_data_flat005_original : block013_data_flat005 = (CoefficientMerge.scale (216544807987200 : Int) atom0853Coded) := by
  rw [block013_data_flat005_step]
def block013_data_flat006 : CoefficientMerge.Poly := [(nat_lit 1288, Int.ofNat (nat_lit 215982966528000)), (nat_lit 1289, Int.ofNat (nat_lit 216544807987200))]
theorem block013_data_flat006_step : block013_data_flat006 = (CoefficientMerge.fastMerge block013_data_flat004 block013_data_flat005) := by decide +kernel
theorem block013_data_flat006_original : block013_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (215982966528000 : Int) atom0852Coded) (CoefficientMerge.scale (216544807987200 : Int) atom0853Coded)) := by
  rw [block013_data_flat006_step, block013_data_flat004_original, block013_data_flat005_original]
def block013_data_flat007 : CoefficientMerge.Poly := [(nat_lit 1287, Int.ofNat (nat_lit 225353863526400)), (nat_lit 1288, Int.ofNat (nat_lit 215982966528000)), (nat_lit 1289, Int.ofNat (nat_lit 216544807987200))]
theorem block013_data_flat007_step : block013_data_flat007 = (CoefficientMerge.fastMerge block013_data_flat003 block013_data_flat006) := by decide +kernel
theorem block013_data_flat007_original : block013_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (225353863526400 : Int) atom0851Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (215982966528000 : Int) atom0852Coded) (CoefficientMerge.scale (216544807987200 : Int) atom0853Coded))) := by
  rw [block013_data_flat007_step, block013_data_flat003_original, block013_data_flat006_original]
def block013_data_flat008 : CoefficientMerge.Poly := [(nat_lit 1285, Int.ofNat (nat_lit 250762389292800)), (nat_lit 1286, Int.ofNat (nat_lit 222902250278400)), (nat_lit 1287, Int.ofNat (nat_lit 225353863526400)), (nat_lit 1288, Int.ofNat (nat_lit 215982966528000)), (nat_lit 1289, Int.ofNat (nat_lit 216544807987200))]
theorem block013_data_flat008_step : block013_data_flat008 = (CoefficientMerge.fastMerge block013_data_flat002 block013_data_flat007) := by decide +kernel
theorem block013_data_flat008_original : block013_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (250762389292800 : Int) atom0849Coded) (CoefficientMerge.scale (222902250278400 : Int) atom0850Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (225353863526400 : Int) atom0851Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (215982966528000 : Int) atom0852Coded) (CoefficientMerge.scale (216544807987200 : Int) atom0853Coded)))) := by
  rw [block013_data_flat008_step, block013_data_flat002_original, block013_data_flat007_original]
def block013_data_flat009 : CoefficientMerge.Poly := [(nat_lit 1290, Int.ofNat (nat_lit 257815027008000))]
theorem block013_data_flat009_step : block013_data_flat009 = (CoefficientMerge.scale (257815027008000 : Int) atom0854Coded) := by decide +kernel
theorem block013_data_flat009_original : block013_data_flat009 = (CoefficientMerge.scale (257815027008000 : Int) atom0854Coded) := by
  rw [block013_data_flat009_step]
def block013_data_flat010 : CoefficientMerge.Poly := [(nat_lit 1291, Int.ofNat (nat_lit 189421289164800))]
theorem block013_data_flat010_step : block013_data_flat010 = (CoefficientMerge.scale (189421289164800 : Int) atom0855Coded) := by decide +kernel
theorem block013_data_flat010_original : block013_data_flat010 = (CoefficientMerge.scale (189421289164800 : Int) atom0855Coded) := by
  rw [block013_data_flat010_step]
def block013_data_flat011 : CoefficientMerge.Poly := [(nat_lit 1290, Int.ofNat (nat_lit 257815027008000)), (nat_lit 1291, Int.ofNat (nat_lit 189421289164800))]
theorem block013_data_flat011_step : block013_data_flat011 = (CoefficientMerge.fastMerge block013_data_flat009 block013_data_flat010) := by decide +kernel
theorem block013_data_flat011_original : block013_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (257815027008000 : Int) atom0854Coded) (CoefficientMerge.scale (189421289164800 : Int) atom0855Coded)) := by
  rw [block013_data_flat011_step, block013_data_flat009_original, block013_data_flat010_original]
def block013_data_flat012 : CoefficientMerge.Poly := [(nat_lit 1292, Int.ofNat (nat_lit 268578751795200))]
theorem block013_data_flat012_step : block013_data_flat012 = (CoefficientMerge.scale (268578751795200 : Int) atom0856Coded) := by decide +kernel
theorem block013_data_flat012_original : block013_data_flat012 = (CoefficientMerge.scale (268578751795200 : Int) atom0856Coded) := by
  rw [block013_data_flat012_step]
def block013_data_flat013 : CoefficientMerge.Poly := [(nat_lit 1293, Int.ofNat (nat_lit 215630979379200))]
theorem block013_data_flat013_step : block013_data_flat013 = (CoefficientMerge.scale (215630979379200 : Int) atom0857Coded) := by decide +kernel
theorem block013_data_flat013_original : block013_data_flat013 = (CoefficientMerge.scale (215630979379200 : Int) atom0857Coded) := by
  rw [block013_data_flat013_step]
def block013_data_flat014 : CoefficientMerge.Poly := [(nat_lit 1294, Int.ofNat (nat_lit 228830374080000))]
theorem block013_data_flat014_step : block013_data_flat014 = (CoefficientMerge.scale (228830374080000 : Int) atom0858Coded) := by decide +kernel
theorem block013_data_flat014_original : block013_data_flat014 = (CoefficientMerge.scale (228830374080000 : Int) atom0858Coded) := by
  rw [block013_data_flat014_step]
def block013_data_flat015 : CoefficientMerge.Poly := [(nat_lit 1293, Int.ofNat (nat_lit 215630979379200)), (nat_lit 1294, Int.ofNat (nat_lit 228830374080000))]
theorem block013_data_flat015_step : block013_data_flat015 = (CoefficientMerge.fastMerge block013_data_flat013 block013_data_flat014) := by decide +kernel
theorem block013_data_flat015_original : block013_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (215630979379200 : Int) atom0857Coded) (CoefficientMerge.scale (228830374080000 : Int) atom0858Coded)) := by
  rw [block013_data_flat015_step, block013_data_flat013_original, block013_data_flat014_original]
def block013_data_flat016 : CoefficientMerge.Poly := [(nat_lit 1292, Int.ofNat (nat_lit 268578751795200)), (nat_lit 1293, Int.ofNat (nat_lit 215630979379200)), (nat_lit 1294, Int.ofNat (nat_lit 228830374080000))]
theorem block013_data_flat016_step : block013_data_flat016 = (CoefficientMerge.fastMerge block013_data_flat012 block013_data_flat015) := by decide +kernel
theorem block013_data_flat016_original : block013_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (268578751795200 : Int) atom0856Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (215630979379200 : Int) atom0857Coded) (CoefficientMerge.scale (228830374080000 : Int) atom0858Coded))) := by
  rw [block013_data_flat016_step, block013_data_flat012_original, block013_data_flat015_original]
def block013_data_flat017 : CoefficientMerge.Poly := [(nat_lit 1290, Int.ofNat (nat_lit 257815027008000)), (nat_lit 1291, Int.ofNat (nat_lit 189421289164800)), (nat_lit 1292, Int.ofNat (nat_lit 268578751795200)), (nat_lit 1293, Int.ofNat (nat_lit 215630979379200)), (nat_lit 1294, Int.ofNat (nat_lit 228830374080000))]
theorem block013_data_flat017_step : block013_data_flat017 = (CoefficientMerge.fastMerge block013_data_flat011 block013_data_flat016) := by decide +kernel
theorem block013_data_flat017_original : block013_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (257815027008000 : Int) atom0854Coded) (CoefficientMerge.scale (189421289164800 : Int) atom0855Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (268578751795200 : Int) atom0856Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (215630979379200 : Int) atom0857Coded) (CoefficientMerge.scale (228830374080000 : Int) atom0858Coded)))) := by
  rw [block013_data_flat017_step, block013_data_flat011_original, block013_data_flat016_original]
def block013_data_flat018 : CoefficientMerge.Poly := [(nat_lit 1285, Int.ofNat (nat_lit 250762389292800)), (nat_lit 1286, Int.ofNat (nat_lit 222902250278400)), (nat_lit 1287, Int.ofNat (nat_lit 225353863526400)), (nat_lit 1288, Int.ofNat (nat_lit 215982966528000)), (nat_lit 1289, Int.ofNat (nat_lit 216544807987200)), (nat_lit 1290, Int.ofNat (nat_lit 257815027008000)), (nat_lit 1291, Int.ofNat (nat_lit 189421289164800)), (nat_lit 1292, Int.ofNat (nat_lit 268578751795200)), (nat_lit 1293, Int.ofNat (nat_lit 215630979379200)), (nat_lit 1294, Int.ofNat (nat_lit 228830374080000))]
theorem block013_data_flat018_step : block013_data_flat018 = (CoefficientMerge.fastMerge block013_data_flat008 block013_data_flat017) := by decide +kernel
theorem block013_data_flat018_original : block013_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (250762389292800 : Int) atom0849Coded) (CoefficientMerge.scale (222902250278400 : Int) atom0850Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (225353863526400 : Int) atom0851Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (215982966528000 : Int) atom0852Coded) (CoefficientMerge.scale (216544807987200 : Int) atom0853Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (257815027008000 : Int) atom0854Coded) (CoefficientMerge.scale (189421289164800 : Int) atom0855Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (268578751795200 : Int) atom0856Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (215630979379200 : Int) atom0857Coded) (CoefficientMerge.scale (228830374080000 : Int) atom0858Coded))))) := by
  rw [block013_data_flat018_step, block013_data_flat008_original, block013_data_flat017_original]
def block013_data_flat019 : CoefficientMerge.Poly := [(nat_lit 1295, Int.ofNat (nat_lit 274763154758400))]
theorem block013_data_flat019_step : block013_data_flat019 = (CoefficientMerge.scale (274763154758400 : Int) atom0859Coded) := by decide +kernel
theorem block013_data_flat019_original : block013_data_flat019 = (CoefficientMerge.scale (274763154758400 : Int) atom0859Coded) := by
  rw [block013_data_flat019_step]
def block013_data_flat020 : CoefficientMerge.Poly := [(nat_lit 1302, Int.ofNat (nat_lit 126234564825600))]
theorem block013_data_flat020_step : block013_data_flat020 = (CoefficientMerge.scale (126234564825600 : Int) atom0860Coded) := by decide +kernel
theorem block013_data_flat020_original : block013_data_flat020 = (CoefficientMerge.scale (126234564825600 : Int) atom0860Coded) := by
  rw [block013_data_flat020_step]
def block013_data_flat021 : CoefficientMerge.Poly := [(nat_lit 1295, Int.ofNat (nat_lit 274763154758400)), (nat_lit 1302, Int.ofNat (nat_lit 126234564825600))]
theorem block013_data_flat021_step : block013_data_flat021 = (CoefficientMerge.fastMerge block013_data_flat019 block013_data_flat020) := by decide +kernel
theorem block013_data_flat021_original : block013_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (274763154758400 : Int) atom0859Coded) (CoefficientMerge.scale (126234564825600 : Int) atom0860Coded)) := by
  rw [block013_data_flat021_step, block013_data_flat019_original, block013_data_flat020_original]
def block013_data_flat022 : CoefficientMerge.Poly := [(nat_lit 1303, Int.ofNat (nat_lit 224731214400000))]
theorem block013_data_flat022_step : block013_data_flat022 = (CoefficientMerge.scale (224731214400000 : Int) atom0861Coded) := by decide +kernel
theorem block013_data_flat022_original : block013_data_flat022 = (CoefficientMerge.scale (224731214400000 : Int) atom0861Coded) := by
  rw [block013_data_flat022_step]
def block013_data_flat023 : CoefficientMerge.Poly := [(nat_lit 1304, Int.ofNat (nat_lit 202842807552000))]
theorem block013_data_flat023_step : block013_data_flat023 = (CoefficientMerge.scale (202842807552000 : Int) atom0862Coded) := by decide +kernel
theorem block013_data_flat023_original : block013_data_flat023 = (CoefficientMerge.scale (202842807552000 : Int) atom0862Coded) := by
  rw [block013_data_flat023_step]
def block013_data_flat024 : CoefficientMerge.Poly := [(nat_lit 1305, Int.ofNat (nat_lit 206600779625328))]
theorem block013_data_flat024_step : block013_data_flat024 = (CoefficientMerge.scale (206600779625328 : Int) atom0863Coded) := by decide +kernel
theorem block013_data_flat024_original : block013_data_flat024 = (CoefficientMerge.scale (206600779625328 : Int) atom0863Coded) := by
  rw [block013_data_flat024_step]
def block013_data_flat025 : CoefficientMerge.Poly := [(nat_lit 1304, Int.ofNat (nat_lit 202842807552000)), (nat_lit 1305, Int.ofNat (nat_lit 206600779625328))]
theorem block013_data_flat025_step : block013_data_flat025 = (CoefficientMerge.fastMerge block013_data_flat023 block013_data_flat024) := by decide +kernel
theorem block013_data_flat025_original : block013_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (202842807552000 : Int) atom0862Coded) (CoefficientMerge.scale (206600779625328 : Int) atom0863Coded)) := by
  rw [block013_data_flat025_step, block013_data_flat023_original, block013_data_flat024_original]
def block013_data_flat026 : CoefficientMerge.Poly := [(nat_lit 1303, Int.ofNat (nat_lit 224731214400000)), (nat_lit 1304, Int.ofNat (nat_lit 202842807552000)), (nat_lit 1305, Int.ofNat (nat_lit 206600779625328))]
theorem block013_data_flat026_step : block013_data_flat026 = (CoefficientMerge.fastMerge block013_data_flat022 block013_data_flat025) := by decide +kernel
theorem block013_data_flat026_original : block013_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (224731214400000 : Int) atom0861Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (202842807552000 : Int) atom0862Coded) (CoefficientMerge.scale (206600779625328 : Int) atom0863Coded))) := by
  rw [block013_data_flat026_step, block013_data_flat022_original, block013_data_flat025_original]
def block013_data_flat027 : CoefficientMerge.Poly := [(nat_lit 1295, Int.ofNat (nat_lit 274763154758400)), (nat_lit 1302, Int.ofNat (nat_lit 126234564825600)), (nat_lit 1303, Int.ofNat (nat_lit 224731214400000)), (nat_lit 1304, Int.ofNat (nat_lit 202842807552000)), (nat_lit 1305, Int.ofNat (nat_lit 206600779625328))]
theorem block013_data_flat027_step : block013_data_flat027 = (CoefficientMerge.fastMerge block013_data_flat021 block013_data_flat026) := by decide +kernel
theorem block013_data_flat027_original : block013_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (274763154758400 : Int) atom0859Coded) (CoefficientMerge.scale (126234564825600 : Int) atom0860Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (224731214400000 : Int) atom0861Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (202842807552000 : Int) atom0862Coded) (CoefficientMerge.scale (206600779625328 : Int) atom0863Coded)))) := by
  rw [block013_data_flat027_step, block013_data_flat021_original, block013_data_flat026_original]
def block013_data_flat028 : CoefficientMerge.Poly := [(nat_lit 1306, Int.ofNat (nat_lit 226908137622672))]
theorem block013_data_flat028_step : block013_data_flat028 = (CoefficientMerge.scale (226908137622672 : Int) atom0864Coded) := by decide +kernel
theorem block013_data_flat028_original : block013_data_flat028 = (CoefficientMerge.scale (226908137622672 : Int) atom0864Coded) := by
  rw [block013_data_flat028_step]
def block013_data_flat029 : CoefficientMerge.Poly := [(nat_lit 1307, Int.ofNat (nat_lit 237208830575904))]
theorem block013_data_flat029_step : block013_data_flat029 = (CoefficientMerge.scale (237208830575904 : Int) atom0865Coded) := by decide +kernel
theorem block013_data_flat029_original : block013_data_flat029 = (CoefficientMerge.scale (237208830575904 : Int) atom0865Coded) := by
  rw [block013_data_flat029_step]
def block013_data_flat030 : CoefficientMerge.Poly := [(nat_lit 1306, Int.ofNat (nat_lit 226908137622672)), (nat_lit 1307, Int.ofNat (nat_lit 237208830575904))]
theorem block013_data_flat030_step : block013_data_flat030 = (CoefficientMerge.fastMerge block013_data_flat028 block013_data_flat029) := by decide +kernel
theorem block013_data_flat030_original : block013_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (226908137622672 : Int) atom0864Coded) (CoefficientMerge.scale (237208830575904 : Int) atom0865Coded)) := by
  rw [block013_data_flat030_step, block013_data_flat028_original, block013_data_flat029_original]
def block013_data_flat031 : CoefficientMerge.Poly := [(nat_lit 1308, Int.ofNat (nat_lit 263089627314624))]
theorem block013_data_flat031_step : block013_data_flat031 = (CoefficientMerge.scale (263089627314624 : Int) atom0866Coded) := by decide +kernel
theorem block013_data_flat031_original : block013_data_flat031 = (CoefficientMerge.scale (263089627314624 : Int) atom0866Coded) := by
  rw [block013_data_flat031_step]
def block013_data_flat032 : CoefficientMerge.Poly := [(nat_lit 1309, Int.ofNat (nat_lit 254449759132800))]
theorem block013_data_flat032_step : block013_data_flat032 = (CoefficientMerge.scale (254449759132800 : Int) atom0867Coded) := by decide +kernel
theorem block013_data_flat032_original : block013_data_flat032 = (CoefficientMerge.scale (254449759132800 : Int) atom0867Coded) := by
  rw [block013_data_flat032_step]
def block013_data_flat033 : CoefficientMerge.Poly := [(nat_lit 1310, Int.ofNat (nat_lit 242135628134400))]
theorem block013_data_flat033_step : block013_data_flat033 = (CoefficientMerge.scale (242135628134400 : Int) atom0868Coded) := by decide +kernel
theorem block013_data_flat033_original : block013_data_flat033 = (CoefficientMerge.scale (242135628134400 : Int) atom0868Coded) := by
  rw [block013_data_flat033_step]
def block013_data_flat034 : CoefficientMerge.Poly := [(nat_lit 1309, Int.ofNat (nat_lit 254449759132800)), (nat_lit 1310, Int.ofNat (nat_lit 242135628134400))]
theorem block013_data_flat034_step : block013_data_flat034 = (CoefficientMerge.fastMerge block013_data_flat032 block013_data_flat033) := by decide +kernel
theorem block013_data_flat034_original : block013_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (254449759132800 : Int) atom0867Coded) (CoefficientMerge.scale (242135628134400 : Int) atom0868Coded)) := by
  rw [block013_data_flat034_step, block013_data_flat032_original, block013_data_flat033_original]
def block013_data_flat035 : CoefficientMerge.Poly := [(nat_lit 1308, Int.ofNat (nat_lit 263089627314624)), (nat_lit 1309, Int.ofNat (nat_lit 254449759132800)), (nat_lit 1310, Int.ofNat (nat_lit 242135628134400))]
theorem block013_data_flat035_step : block013_data_flat035 = (CoefficientMerge.fastMerge block013_data_flat031 block013_data_flat034) := by decide +kernel
theorem block013_data_flat035_original : block013_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (263089627314624 : Int) atom0866Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (254449759132800 : Int) atom0867Coded) (CoefficientMerge.scale (242135628134400 : Int) atom0868Coded))) := by
  rw [block013_data_flat035_step, block013_data_flat031_original, block013_data_flat034_original]
def block013_data_flat036 : CoefficientMerge.Poly := [(nat_lit 1306, Int.ofNat (nat_lit 226908137622672)), (nat_lit 1307, Int.ofNat (nat_lit 237208830575904)), (nat_lit 1308, Int.ofNat (nat_lit 263089627314624)), (nat_lit 1309, Int.ofNat (nat_lit 254449759132800)), (nat_lit 1310, Int.ofNat (nat_lit 242135628134400))]
theorem block013_data_flat036_step : block013_data_flat036 = (CoefficientMerge.fastMerge block013_data_flat030 block013_data_flat035) := by decide +kernel
theorem block013_data_flat036_original : block013_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (226908137622672 : Int) atom0864Coded) (CoefficientMerge.scale (237208830575904 : Int) atom0865Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (263089627314624 : Int) atom0866Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (254449759132800 : Int) atom0867Coded) (CoefficientMerge.scale (242135628134400 : Int) atom0868Coded)))) := by
  rw [block013_data_flat036_step, block013_data_flat030_original, block013_data_flat035_original]
def block013_data_flat037 : CoefficientMerge.Poly := [(nat_lit 1295, Int.ofNat (nat_lit 274763154758400)), (nat_lit 1302, Int.ofNat (nat_lit 126234564825600)), (nat_lit 1303, Int.ofNat (nat_lit 224731214400000)), (nat_lit 1304, Int.ofNat (nat_lit 202842807552000)), (nat_lit 1305, Int.ofNat (nat_lit 206600779625328)), (nat_lit 1306, Int.ofNat (nat_lit 226908137622672)), (nat_lit 1307, Int.ofNat (nat_lit 237208830575904)), (nat_lit 1308, Int.ofNat (nat_lit 263089627314624)), (nat_lit 1309, Int.ofNat (nat_lit 254449759132800)), (nat_lit 1310, Int.ofNat (nat_lit 242135628134400))]
theorem block013_data_flat037_step : block013_data_flat037 = (CoefficientMerge.fastMerge block013_data_flat027 block013_data_flat036) := by decide +kernel
theorem block013_data_flat037_original : block013_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (274763154758400 : Int) atom0859Coded) (CoefficientMerge.scale (126234564825600 : Int) atom0860Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (224731214400000 : Int) atom0861Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (202842807552000 : Int) atom0862Coded) (CoefficientMerge.scale (206600779625328 : Int) atom0863Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (226908137622672 : Int) atom0864Coded) (CoefficientMerge.scale (237208830575904 : Int) atom0865Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (263089627314624 : Int) atom0866Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (254449759132800 : Int) atom0867Coded) (CoefficientMerge.scale (242135628134400 : Int) atom0868Coded))))) := by
  rw [block013_data_flat037_step, block013_data_flat027_original, block013_data_flat036_original]
def block013_data_flat038 : CoefficientMerge.Poly := [(nat_lit 1285, Int.ofNat (nat_lit 250762389292800)), (nat_lit 1286, Int.ofNat (nat_lit 222902250278400)), (nat_lit 1287, Int.ofNat (nat_lit 225353863526400)), (nat_lit 1288, Int.ofNat (nat_lit 215982966528000)), (nat_lit 1289, Int.ofNat (nat_lit 216544807987200)), (nat_lit 1290, Int.ofNat (nat_lit 257815027008000)), (nat_lit 1291, Int.ofNat (nat_lit 189421289164800)), (nat_lit 1292, Int.ofNat (nat_lit 268578751795200)), (nat_lit 1293, Int.ofNat (nat_lit 215630979379200)), (nat_lit 1294, Int.ofNat (nat_lit 228830374080000)), (nat_lit 1295, Int.ofNat (nat_lit 274763154758400)), (nat_lit 1302, Int.ofNat (nat_lit 126234564825600)), (nat_lit 1303, Int.ofNat (nat_lit 224731214400000)), (nat_lit 1304, Int.ofNat (nat_lit 202842807552000)), (nat_lit 1305, Int.ofNat (nat_lit 206600779625328)), (nat_lit 1306, Int.ofNat (nat_lit 226908137622672)), (nat_lit 1307, Int.ofNat (nat_lit 237208830575904)), (nat_lit 1308, Int.ofNat (nat_lit 263089627314624)), (nat_lit 1309, Int.ofNat (nat_lit 254449759132800)), (nat_lit 1310, Int.ofNat (nat_lit 242135628134400))]
theorem block013_data_flat038_step : block013_data_flat038 = (CoefficientMerge.fastMerge block013_data_flat018 block013_data_flat037) := by decide +kernel
theorem block013_data_flat038_original : block013_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (250762389292800 : Int) atom0849Coded) (CoefficientMerge.scale (222902250278400 : Int) atom0850Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (225353863526400 : Int) atom0851Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (215982966528000 : Int) atom0852Coded) (CoefficientMerge.scale (216544807987200 : Int) atom0853Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (257815027008000 : Int) atom0854Coded) (CoefficientMerge.scale (189421289164800 : Int) atom0855Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (268578751795200 : Int) atom0856Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (215630979379200 : Int) atom0857Coded) (CoefficientMerge.scale (228830374080000 : Int) atom0858Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (274763154758400 : Int) atom0859Coded) (CoefficientMerge.scale (126234564825600 : Int) atom0860Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (224731214400000 : Int) atom0861Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (202842807552000 : Int) atom0862Coded) (CoefficientMerge.scale (206600779625328 : Int) atom0863Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (226908137622672 : Int) atom0864Coded) (CoefficientMerge.scale (237208830575904 : Int) atom0865Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (263089627314624 : Int) atom0866Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (254449759132800 : Int) atom0867Coded) (CoefficientMerge.scale (242135628134400 : Int) atom0868Coded)))))) := by
  rw [block013_data_flat038_step, block013_data_flat018_original, block013_data_flat037_original]
def block013_data_flat039 : CoefficientMerge.Poly := [(nat_lit 1311, Int.ofNat (nat_lit 244608503731200))]
theorem block013_data_flat039_step : block013_data_flat039 = (CoefficientMerge.scale (244608503731200 : Int) atom0869Coded) := by decide +kernel
theorem block013_data_flat039_original : block013_data_flat039 = (CoefficientMerge.scale (244608503731200 : Int) atom0869Coded) := by
  rw [block013_data_flat039_step]
def block013_data_flat040 : CoefficientMerge.Poly := [(nat_lit 1312, Int.ofNat (nat_lit 235258869081600))]
theorem block013_data_flat040_step : block013_data_flat040 = (CoefficientMerge.scale (235258869081600 : Int) atom0870Coded) := by decide +kernel
theorem block013_data_flat040_original : block013_data_flat040 = (CoefficientMerge.scale (235258869081600 : Int) atom0870Coded) := by
  rw [block013_data_flat040_step]
def block013_data_flat041 : CoefficientMerge.Poly := [(nat_lit 1311, Int.ofNat (nat_lit 244608503731200)), (nat_lit 1312, Int.ofNat (nat_lit 235258869081600))]
theorem block013_data_flat041_step : block013_data_flat041 = (CoefficientMerge.fastMerge block013_data_flat039 block013_data_flat040) := by decide +kernel
theorem block013_data_flat041_original : block013_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (244608503731200 : Int) atom0869Coded) (CoefficientMerge.scale (235258869081600 : Int) atom0870Coded)) := by
  rw [block013_data_flat041_step, block013_data_flat039_original, block013_data_flat040_original]
def block013_data_flat042 : CoefficientMerge.Poly := [(nat_lit 1313, Int.ofNat (nat_lit 235841972889600))]
theorem block013_data_flat042_step : block013_data_flat042 = (CoefficientMerge.scale (235841972889600 : Int) atom0871Coded) := by decide +kernel
theorem block013_data_flat042_original : block013_data_flat042 = (CoefficientMerge.scale (235841972889600 : Int) atom0871Coded) := by
  rw [block013_data_flat042_step]
def block013_data_flat043 : CoefficientMerge.Poly := [(nat_lit 1314, Int.ofNat (nat_lit 274348086566400))]
theorem block013_data_flat043_step : block013_data_flat043 = (CoefficientMerge.scale (274348086566400 : Int) atom0872Coded) := by decide +kernel
theorem block013_data_flat043_original : block013_data_flat043 = (CoefficientMerge.scale (274348086566400 : Int) atom0872Coded) := by
  rw [block013_data_flat043_step]
def block013_data_flat044 : CoefficientMerge.Poly := [(nat_lit 1315, Int.ofNat (nat_lit 220533081753600))]
theorem block013_data_flat044_step : block013_data_flat044 = (CoefficientMerge.scale (220533081753600 : Int) atom0873Coded) := by decide +kernel
theorem block013_data_flat044_original : block013_data_flat044 = (CoefficientMerge.scale (220533081753600 : Int) atom0873Coded) := by
  rw [block013_data_flat044_step]
def block013_data_flat045 : CoefficientMerge.Poly := [(nat_lit 1314, Int.ofNat (nat_lit 274348086566400)), (nat_lit 1315, Int.ofNat (nat_lit 220533081753600))]
theorem block013_data_flat045_step : block013_data_flat045 = (CoefficientMerge.fastMerge block013_data_flat043 block013_data_flat044) := by decide +kernel
theorem block013_data_flat045_original : block013_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (274348086566400 : Int) atom0872Coded) (CoefficientMerge.scale (220533081753600 : Int) atom0873Coded)) := by
  rw [block013_data_flat045_step, block013_data_flat043_original, block013_data_flat044_original]
def block013_data_flat046 : CoefficientMerge.Poly := [(nat_lit 1313, Int.ofNat (nat_lit 235841972889600)), (nat_lit 1314, Int.ofNat (nat_lit 274348086566400)), (nat_lit 1315, Int.ofNat (nat_lit 220533081753600))]
theorem block013_data_flat046_step : block013_data_flat046 = (CoefficientMerge.fastMerge block013_data_flat042 block013_data_flat045) := by decide +kernel
theorem block013_data_flat046_original : block013_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (235841972889600 : Int) atom0871Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (274348086566400 : Int) atom0872Coded) (CoefficientMerge.scale (220533081753600 : Int) atom0873Coded))) := by
  rw [block013_data_flat046_step, block013_data_flat042_original, block013_data_flat045_original]
def block013_data_flat047 : CoefficientMerge.Poly := [(nat_lit 1311, Int.ofNat (nat_lit 244608503731200)), (nat_lit 1312, Int.ofNat (nat_lit 235258869081600)), (nat_lit 1313, Int.ofNat (nat_lit 235841972889600)), (nat_lit 1314, Int.ofNat (nat_lit 274348086566400)), (nat_lit 1315, Int.ofNat (nat_lit 220533081753600))]
theorem block013_data_flat047_step : block013_data_flat047 = (CoefficientMerge.fastMerge block013_data_flat041 block013_data_flat046) := by decide +kernel
theorem block013_data_flat047_original : block013_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (244608503731200 : Int) atom0869Coded) (CoefficientMerge.scale (235258869081600 : Int) atom0870Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (235841972889600 : Int) atom0871Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (274348086566400 : Int) atom0872Coded) (CoefficientMerge.scale (220533081753600 : Int) atom0873Coded)))) := by
  rw [block013_data_flat047_step, block013_data_flat041_original, block013_data_flat046_original]
def block013_data_flat048 : CoefficientMerge.Poly := [(nat_lit 1316, Int.ofNat (nat_lit 307559875392000))]
theorem block013_data_flat048_step : block013_data_flat048 = (CoefficientMerge.scale (307559875392000 : Int) atom0874Coded) := by decide +kernel
theorem block013_data_flat048_original : block013_data_flat048 = (CoefficientMerge.scale (307559875392000 : Int) atom0874Coded) := by
  rw [block013_data_flat048_step]
def block013_data_flat049 : CoefficientMerge.Poly := [(nat_lit 1317, Int.ofNat (nat_lit 270329502643200))]
theorem block013_data_flat049_step : block013_data_flat049 = (CoefficientMerge.scale (270329502643200 : Int) atom0875Coded) := by decide +kernel
theorem block013_data_flat049_original : block013_data_flat049 = (CoefficientMerge.scale (270329502643200 : Int) atom0875Coded) := by
  rw [block013_data_flat049_step]
def block013_data_flat050 : CoefficientMerge.Poly := [(nat_lit 1316, Int.ofNat (nat_lit 307559875392000)), (nat_lit 1317, Int.ofNat (nat_lit 270329502643200))]
theorem block013_data_flat050_step : block013_data_flat050 = (CoefficientMerge.fastMerge block013_data_flat048 block013_data_flat049) := by decide +kernel
theorem block013_data_flat050_original : block013_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (307559875392000 : Int) atom0874Coded) (CoefficientMerge.scale (270329502643200 : Int) atom0875Coded)) := by
  rw [block013_data_flat050_step, block013_data_flat048_original, block013_data_flat049_original]
def block013_data_flat051 : CoefficientMerge.Poly := [(nat_lit 1318, Int.ofNat (nat_lit 299246297011200))]
theorem block013_data_flat051_step : block013_data_flat051 = (CoefficientMerge.scale (299246297011200 : Int) atom0876Coded) := by decide +kernel
theorem block013_data_flat051_original : block013_data_flat051 = (CoefficientMerge.scale (299246297011200 : Int) atom0876Coded) := by
  rw [block013_data_flat051_step]
def block013_data_flat052 : CoefficientMerge.Poly := [(nat_lit 1319, Int.ofNat (nat_lit 360896477356800))]
theorem block013_data_flat052_step : block013_data_flat052 = (CoefficientMerge.scale (360896477356800 : Int) atom0877Coded) := by decide +kernel
theorem block013_data_flat052_original : block013_data_flat052 = (CoefficientMerge.scale (360896477356800 : Int) atom0877Coded) := by
  rw [block013_data_flat052_step]
def block013_data_flat053 : CoefficientMerge.Poly := [(nat_lit 1327, Int.ofNat (nat_lit 135493136486400))]
theorem block013_data_flat053_step : block013_data_flat053 = (CoefficientMerge.scale (135493136486400 : Int) atom0878Coded) := by decide +kernel
theorem block013_data_flat053_original : block013_data_flat053 = (CoefficientMerge.scale (135493136486400 : Int) atom0878Coded) := by
  rw [block013_data_flat053_step]
def block013_data_flat054 : CoefficientMerge.Poly := [(nat_lit 1319, Int.ofNat (nat_lit 360896477356800)), (nat_lit 1327, Int.ofNat (nat_lit 135493136486400))]
theorem block013_data_flat054_step : block013_data_flat054 = (CoefficientMerge.fastMerge block013_data_flat052 block013_data_flat053) := by decide +kernel
theorem block013_data_flat054_original : block013_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (360896477356800 : Int) atom0877Coded) (CoefficientMerge.scale (135493136486400 : Int) atom0878Coded)) := by
  rw [block013_data_flat054_step, block013_data_flat052_original, block013_data_flat053_original]
def block013_data_flat055 : CoefficientMerge.Poly := [(nat_lit 1318, Int.ofNat (nat_lit 299246297011200)), (nat_lit 1319, Int.ofNat (nat_lit 360896477356800)), (nat_lit 1327, Int.ofNat (nat_lit 135493136486400))]
theorem block013_data_flat055_step : block013_data_flat055 = (CoefficientMerge.fastMerge block013_data_flat051 block013_data_flat054) := by decide +kernel
theorem block013_data_flat055_original : block013_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (299246297011200 : Int) atom0876Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (360896477356800 : Int) atom0877Coded) (CoefficientMerge.scale (135493136486400 : Int) atom0878Coded))) := by
  rw [block013_data_flat055_step, block013_data_flat051_original, block013_data_flat054_original]
def block013_data_flat056 : CoefficientMerge.Poly := [(nat_lit 1316, Int.ofNat (nat_lit 307559875392000)), (nat_lit 1317, Int.ofNat (nat_lit 270329502643200)), (nat_lit 1318, Int.ofNat (nat_lit 299246297011200)), (nat_lit 1319, Int.ofNat (nat_lit 360896477356800)), (nat_lit 1327, Int.ofNat (nat_lit 135493136486400))]
theorem block013_data_flat056_step : block013_data_flat056 = (CoefficientMerge.fastMerge block013_data_flat050 block013_data_flat055) := by decide +kernel
theorem block013_data_flat056_original : block013_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (307559875392000 : Int) atom0874Coded) (CoefficientMerge.scale (270329502643200 : Int) atom0875Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (299246297011200 : Int) atom0876Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (360896477356800 : Int) atom0877Coded) (CoefficientMerge.scale (135493136486400 : Int) atom0878Coded)))) := by
  rw [block013_data_flat056_step, block013_data_flat050_original, block013_data_flat055_original]
def block013_data_flat057 : CoefficientMerge.Poly := [(nat_lit 1311, Int.ofNat (nat_lit 244608503731200)), (nat_lit 1312, Int.ofNat (nat_lit 235258869081600)), (nat_lit 1313, Int.ofNat (nat_lit 235841972889600)), (nat_lit 1314, Int.ofNat (nat_lit 274348086566400)), (nat_lit 1315, Int.ofNat (nat_lit 220533081753600)), (nat_lit 1316, Int.ofNat (nat_lit 307559875392000)), (nat_lit 1317, Int.ofNat (nat_lit 270329502643200)), (nat_lit 1318, Int.ofNat (nat_lit 299246297011200)), (nat_lit 1319, Int.ofNat (nat_lit 360896477356800)), (nat_lit 1327, Int.ofNat (nat_lit 135493136486400))]
theorem block013_data_flat057_step : block013_data_flat057 = (CoefficientMerge.fastMerge block013_data_flat047 block013_data_flat056) := by decide +kernel
theorem block013_data_flat057_original : block013_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (244608503731200 : Int) atom0869Coded) (CoefficientMerge.scale (235258869081600 : Int) atom0870Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (235841972889600 : Int) atom0871Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (274348086566400 : Int) atom0872Coded) (CoefficientMerge.scale (220533081753600 : Int) atom0873Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (307559875392000 : Int) atom0874Coded) (CoefficientMerge.scale (270329502643200 : Int) atom0875Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (299246297011200 : Int) atom0876Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (360896477356800 : Int) atom0877Coded) (CoefficientMerge.scale (135493136486400 : Int) atom0878Coded))))) := by
  rw [block013_data_flat057_step, block013_data_flat047_original, block013_data_flat056_original]
def block013_data_flat058 : CoefficientMerge.Poly := [(nat_lit 1328, Int.ofNat (nat_lit 254285879232000))]
theorem block013_data_flat058_step : block013_data_flat058 = (CoefficientMerge.scale (254285879232000 : Int) atom0879Coded) := by decide +kernel
theorem block013_data_flat058_original : block013_data_flat058 = (CoefficientMerge.scale (254285879232000 : Int) atom0879Coded) := by
  rw [block013_data_flat058_step]
def block013_data_flat059 : CoefficientMerge.Poly := [(nat_lit 1329, Int.ofNat (nat_lit 240589825423728))]
theorem block013_data_flat059_step : block013_data_flat059 = (CoefficientMerge.scale (240589825423728 : Int) atom0880Coded) := by decide +kernel
theorem block013_data_flat059_original : block013_data_flat059 = (CoefficientMerge.scale (240589825423728 : Int) atom0880Coded) := by
  rw [block013_data_flat059_step]
def block013_data_flat060 : CoefficientMerge.Poly := [(nat_lit 1328, Int.ofNat (nat_lit 254285879232000)), (nat_lit 1329, Int.ofNat (nat_lit 240589825423728))]
theorem block013_data_flat060_step : block013_data_flat060 = (CoefficientMerge.fastMerge block013_data_flat058 block013_data_flat059) := by decide +kernel
theorem block013_data_flat060_original : block013_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (254285879232000 : Int) atom0879Coded) (CoefficientMerge.scale (240589825423728 : Int) atom0880Coded)) := by
  rw [block013_data_flat060_step, block013_data_flat058_original, block013_data_flat059_original]
def block013_data_flat061 : CoefficientMerge.Poly := [(nat_lit 1330, Int.ofNat (nat_lit 257835405193872))]
theorem block013_data_flat061_step : block013_data_flat061 = (CoefficientMerge.scale (257835405193872 : Int) atom0881Coded) := by decide +kernel
theorem block013_data_flat061_original : block013_data_flat061 = (CoefficientMerge.scale (257835405193872 : Int) atom0881Coded) := by
  rw [block013_data_flat061_step]
def block013_data_flat062 : CoefficientMerge.Poly := [(nat_lit 1331, Int.ofNat (nat_lit 269199215587104))]
theorem block013_data_flat062_step : block013_data_flat062 = (CoefficientMerge.scale (269199215587104 : Int) atom0882Coded) := by decide +kernel
theorem block013_data_flat062_original : block013_data_flat062 = (CoefficientMerge.scale (269199215587104 : Int) atom0882Coded) := by
  rw [block013_data_flat062_step]
def block013_data_flat063 : CoefficientMerge.Poly := [(nat_lit 1332, Int.ofNat (nat_lit 296143129765824))]
theorem block013_data_flat063_step : block013_data_flat063 = (CoefficientMerge.scale (296143129765824 : Int) atom0883Coded) := by decide +kernel
theorem block013_data_flat063_original : block013_data_flat063 = (CoefficientMerge.scale (296143129765824 : Int) atom0883Coded) := by
  rw [block013_data_flat063_step]
def block013_data_flat064 : CoefficientMerge.Poly := [(nat_lit 1331, Int.ofNat (nat_lit 269199215587104)), (nat_lit 1332, Int.ofNat (nat_lit 296143129765824))]
theorem block013_data_flat064_step : block013_data_flat064 = (CoefficientMerge.fastMerge block013_data_flat062 block013_data_flat063) := by decide +kernel
theorem block013_data_flat064_original : block013_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (269199215587104 : Int) atom0882Coded) (CoefficientMerge.scale (296143129765824 : Int) atom0883Coded)) := by
  rw [block013_data_flat064_step, block013_data_flat062_original, block013_data_flat063_original]
def block013_data_flat065 : CoefficientMerge.Poly := [(nat_lit 1330, Int.ofNat (nat_lit 257835405193872)), (nat_lit 1331, Int.ofNat (nat_lit 269199215587104)), (nat_lit 1332, Int.ofNat (nat_lit 296143129765824))]
theorem block013_data_flat065_step : block013_data_flat065 = (CoefficientMerge.fastMerge block013_data_flat061 block013_data_flat064) := by decide +kernel
theorem block013_data_flat065_original : block013_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (257835405193872 : Int) atom0881Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (269199215587104 : Int) atom0882Coded) (CoefficientMerge.scale (296143129765824 : Int) atom0883Coded))) := by
  rw [block013_data_flat065_step, block013_data_flat061_original, block013_data_flat064_original]
def block013_data_flat066 : CoefficientMerge.Poly := [(nat_lit 1328, Int.ofNat (nat_lit 254285879232000)), (nat_lit 1329, Int.ofNat (nat_lit 240589825423728)), (nat_lit 1330, Int.ofNat (nat_lit 257835405193872)), (nat_lit 1331, Int.ofNat (nat_lit 269199215587104)), (nat_lit 1332, Int.ofNat (nat_lit 296143129765824))]
theorem block013_data_flat066_step : block013_data_flat066 = (CoefficientMerge.fastMerge block013_data_flat060 block013_data_flat065) := by decide +kernel
theorem block013_data_flat066_original : block013_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (254285879232000 : Int) atom0879Coded) (CoefficientMerge.scale (240589825423728 : Int) atom0880Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (257835405193872 : Int) atom0881Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (269199215587104 : Int) atom0882Coded) (CoefficientMerge.scale (296143129765824 : Int) atom0883Coded)))) := by
  rw [block013_data_flat066_step, block013_data_flat060_original, block013_data_flat065_original]
def block013_data_flat067 : CoefficientMerge.Poly := [(nat_lit 1333, Int.ofNat (nat_lit 286503931190400))]
theorem block013_data_flat067_step : block013_data_flat067 = (CoefficientMerge.scale (286503931190400 : Int) atom0884Coded) := by decide +kernel
theorem block013_data_flat067_original : block013_data_flat067 = (CoefficientMerge.scale (286503931190400 : Int) atom0884Coded) := by
  rw [block013_data_flat067_step]
def block013_data_flat068 : CoefficientMerge.Poly := [(nat_lit 1334, Int.ofNat (nat_lit 273190469798400))]
theorem block013_data_flat068_step : block013_data_flat068 = (CoefficientMerge.scale (273190469798400 : Int) atom0885Coded) := by decide +kernel
theorem block013_data_flat068_original : block013_data_flat068 = (CoefficientMerge.scale (273190469798400 : Int) atom0885Coded) := by
  rw [block013_data_flat068_step]
def block013_data_flat069 : CoefficientMerge.Poly := [(nat_lit 1333, Int.ofNat (nat_lit 286503931190400)), (nat_lit 1334, Int.ofNat (nat_lit 273190469798400))]
theorem block013_data_flat069_step : block013_data_flat069 = (CoefficientMerge.fastMerge block013_data_flat067 block013_data_flat068) := by decide +kernel
theorem block013_data_flat069_original : block013_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (286503931190400 : Int) atom0884Coded) (CoefficientMerge.scale (273190469798400 : Int) atom0885Coded)) := by
  rw [block013_data_flat069_step, block013_data_flat067_original, block013_data_flat068_original]
def block013_data_flat070 : CoefficientMerge.Poly := [(nat_lit 1335, Int.ofNat (nat_lit 274664015001600))]
theorem block013_data_flat070_step : block013_data_flat070 = (CoefficientMerge.scale (274664015001600 : Int) atom0886Coded) := by decide +kernel
theorem block013_data_flat070_original : block013_data_flat070 = (CoefficientMerge.scale (274664015001600 : Int) atom0886Coded) := by
  rw [block013_data_flat070_step]
def block013_data_flat071 : CoefficientMerge.Poly := [(nat_lit 1336, Int.ofNat (nat_lit 264315049958400))]
theorem block013_data_flat071_step : block013_data_flat071 = (CoefficientMerge.scale (264315049958400 : Int) atom0887Coded) := by decide +kernel
theorem block013_data_flat071_original : block013_data_flat071 = (CoefficientMerge.scale (264315049958400 : Int) atom0887Coded) := by
  rw [block013_data_flat071_step]
def block013_data_flat072 : CoefficientMerge.Poly := [(nat_lit 1337, Int.ofNat (nat_lit 263898823372800))]
theorem block013_data_flat072_step : block013_data_flat072 = (CoefficientMerge.scale (263898823372800 : Int) atom0888Coded) := by decide +kernel
theorem block013_data_flat072_original : block013_data_flat072 = (CoefficientMerge.scale (263898823372800 : Int) atom0888Coded) := by
  rw [block013_data_flat072_step]
def block013_data_flat073 : CoefficientMerge.Poly := [(nat_lit 1336, Int.ofNat (nat_lit 264315049958400)), (nat_lit 1337, Int.ofNat (nat_lit 263898823372800))]
theorem block013_data_flat073_step : block013_data_flat073 = (CoefficientMerge.fastMerge block013_data_flat071 block013_data_flat072) := by decide +kernel
theorem block013_data_flat073_original : block013_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (264315049958400 : Int) atom0887Coded) (CoefficientMerge.scale (263898823372800 : Int) atom0888Coded)) := by
  rw [block013_data_flat073_step, block013_data_flat071_original, block013_data_flat072_original]
def block013_data_flat074 : CoefficientMerge.Poly := [(nat_lit 1335, Int.ofNat (nat_lit 274664015001600)), (nat_lit 1336, Int.ofNat (nat_lit 264315049958400)), (nat_lit 1337, Int.ofNat (nat_lit 263898823372800))]
theorem block013_data_flat074_step : block013_data_flat074 = (CoefficientMerge.fastMerge block013_data_flat070 block013_data_flat073) := by decide +kernel
theorem block013_data_flat074_original : block013_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (274664015001600 : Int) atom0886Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (264315049958400 : Int) atom0887Coded) (CoefficientMerge.scale (263898823372800 : Int) atom0888Coded))) := by
  rw [block013_data_flat074_step, block013_data_flat070_original, block013_data_flat073_original]
def block013_data_flat075 : CoefficientMerge.Poly := [(nat_lit 1333, Int.ofNat (nat_lit 286503931190400)), (nat_lit 1334, Int.ofNat (nat_lit 273190469798400)), (nat_lit 1335, Int.ofNat (nat_lit 274664015001600)), (nat_lit 1336, Int.ofNat (nat_lit 264315049958400)), (nat_lit 1337, Int.ofNat (nat_lit 263898823372800))]
theorem block013_data_flat075_step : block013_data_flat075 = (CoefficientMerge.fastMerge block013_data_flat069 block013_data_flat074) := by decide +kernel
theorem block013_data_flat075_original : block013_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (286503931190400 : Int) atom0884Coded) (CoefficientMerge.scale (273190469798400 : Int) atom0885Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (274664015001600 : Int) atom0886Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (264315049958400 : Int) atom0887Coded) (CoefficientMerge.scale (263898823372800 : Int) atom0888Coded)))) := by
  rw [block013_data_flat075_step, block013_data_flat069_original, block013_data_flat074_original]
def block013_data_flat076 : CoefficientMerge.Poly := [(nat_lit 1328, Int.ofNat (nat_lit 254285879232000)), (nat_lit 1329, Int.ofNat (nat_lit 240589825423728)), (nat_lit 1330, Int.ofNat (nat_lit 257835405193872)), (nat_lit 1331, Int.ofNat (nat_lit 269199215587104)), (nat_lit 1332, Int.ofNat (nat_lit 296143129765824)), (nat_lit 1333, Int.ofNat (nat_lit 286503931190400)), (nat_lit 1334, Int.ofNat (nat_lit 273190469798400)), (nat_lit 1335, Int.ofNat (nat_lit 274664015001600)), (nat_lit 1336, Int.ofNat (nat_lit 264315049958400)), (nat_lit 1337, Int.ofNat (nat_lit 263898823372800))]
theorem block013_data_flat076_step : block013_data_flat076 = (CoefficientMerge.fastMerge block013_data_flat066 block013_data_flat075) := by decide +kernel
theorem block013_data_flat076_original : block013_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (254285879232000 : Int) atom0879Coded) (CoefficientMerge.scale (240589825423728 : Int) atom0880Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (257835405193872 : Int) atom0881Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (269199215587104 : Int) atom0882Coded) (CoefficientMerge.scale (296143129765824 : Int) atom0883Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (286503931190400 : Int) atom0884Coded) (CoefficientMerge.scale (273190469798400 : Int) atom0885Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (274664015001600 : Int) atom0886Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (264315049958400 : Int) atom0887Coded) (CoefficientMerge.scale (263898823372800 : Int) atom0888Coded))))) := by
  rw [block013_data_flat076_step, block013_data_flat066_original, block013_data_flat075_original]
def block013_data_flat077 : CoefficientMerge.Poly := [(nat_lit 1311, Int.ofNat (nat_lit 244608503731200)), (nat_lit 1312, Int.ofNat (nat_lit 235258869081600)), (nat_lit 1313, Int.ofNat (nat_lit 235841972889600)), (nat_lit 1314, Int.ofNat (nat_lit 274348086566400)), (nat_lit 1315, Int.ofNat (nat_lit 220533081753600)), (nat_lit 1316, Int.ofNat (nat_lit 307559875392000)), (nat_lit 1317, Int.ofNat (nat_lit 270329502643200)), (nat_lit 1318, Int.ofNat (nat_lit 299246297011200)), (nat_lit 1319, Int.ofNat (nat_lit 360896477356800)), (nat_lit 1327, Int.ofNat (nat_lit 135493136486400)), (nat_lit 1328, Int.ofNat (nat_lit 254285879232000)), (nat_lit 1329, Int.ofNat (nat_lit 240589825423728)), (nat_lit 1330, Int.ofNat (nat_lit 257835405193872)), (nat_lit 1331, Int.ofNat (nat_lit 269199215587104)), (nat_lit 1332, Int.ofNat (nat_lit 296143129765824)), (nat_lit 1333, Int.ofNat (nat_lit 286503931190400)), (nat_lit 1334, Int.ofNat (nat_lit 273190469798400)), (nat_lit 1335, Int.ofNat (nat_lit 274664015001600)), (nat_lit 1336, Int.ofNat (nat_lit 264315049958400)), (nat_lit 1337, Int.ofNat (nat_lit 263898823372800))]
theorem block013_data_flat077_step : block013_data_flat077 = (CoefficientMerge.fastMerge block013_data_flat057 block013_data_flat076) := by decide +kernel
theorem block013_data_flat077_original : block013_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (244608503731200 : Int) atom0869Coded) (CoefficientMerge.scale (235258869081600 : Int) atom0870Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (235841972889600 : Int) atom0871Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (274348086566400 : Int) atom0872Coded) (CoefficientMerge.scale (220533081753600 : Int) atom0873Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (307559875392000 : Int) atom0874Coded) (CoefficientMerge.scale (270329502643200 : Int) atom0875Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (299246297011200 : Int) atom0876Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (360896477356800 : Int) atom0877Coded) (CoefficientMerge.scale (135493136486400 : Int) atom0878Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (254285879232000 : Int) atom0879Coded) (CoefficientMerge.scale (240589825423728 : Int) atom0880Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (257835405193872 : Int) atom0881Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (269199215587104 : Int) atom0882Coded) (CoefficientMerge.scale (296143129765824 : Int) atom0883Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (286503931190400 : Int) atom0884Coded) (CoefficientMerge.scale (273190469798400 : Int) atom0885Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (274664015001600 : Int) atom0886Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (264315049958400 : Int) atom0887Coded) (CoefficientMerge.scale (263898823372800 : Int) atom0888Coded)))))) := by
  rw [block013_data_flat077_step, block013_data_flat057_original, block013_data_flat076_original]
def block013_data_flat078 : CoefficientMerge.Poly := [(nat_lit 1285, Int.ofNat (nat_lit 250762389292800)), (nat_lit 1286, Int.ofNat (nat_lit 222902250278400)), (nat_lit 1287, Int.ofNat (nat_lit 225353863526400)), (nat_lit 1288, Int.ofNat (nat_lit 215982966528000)), (nat_lit 1289, Int.ofNat (nat_lit 216544807987200)), (nat_lit 1290, Int.ofNat (nat_lit 257815027008000)), (nat_lit 1291, Int.ofNat (nat_lit 189421289164800)), (nat_lit 1292, Int.ofNat (nat_lit 268578751795200)), (nat_lit 1293, Int.ofNat (nat_lit 215630979379200)), (nat_lit 1294, Int.ofNat (nat_lit 228830374080000)), (nat_lit 1295, Int.ofNat (nat_lit 274763154758400)), (nat_lit 1302, Int.ofNat (nat_lit 126234564825600)), (nat_lit 1303, Int.ofNat (nat_lit 224731214400000)), (nat_lit 1304, Int.ofNat (nat_lit 202842807552000)), (nat_lit 1305, Int.ofNat (nat_lit 206600779625328)), (nat_lit 1306, Int.ofNat (nat_lit 226908137622672)), (nat_lit 1307, Int.ofNat (nat_lit 237208830575904)), (nat_lit 1308, Int.ofNat (nat_lit 263089627314624)), (nat_lit 1309, Int.ofNat (nat_lit 254449759132800)), (nat_lit 1310, Int.ofNat (nat_lit 242135628134400)), (nat_lit 1311, Int.ofNat (nat_lit 244608503731200)), (nat_lit 1312, Int.ofNat (nat_lit 235258869081600)), (nat_lit 1313, Int.ofNat (nat_lit 235841972889600)), (nat_lit 1314, Int.ofNat (nat_lit 274348086566400)), (nat_lit 1315, Int.ofNat (nat_lit 220533081753600)), (nat_lit 1316, Int.ofNat (nat_lit 307559875392000)), (nat_lit 1317, Int.ofNat (nat_lit 270329502643200)), (nat_lit 1318, Int.ofNat (nat_lit 299246297011200)), (nat_lit 1319, Int.ofNat (nat_lit 360896477356800)), (nat_lit 1327, Int.ofNat (nat_lit 135493136486400)), (nat_lit 1328, Int.ofNat (nat_lit 254285879232000)), (nat_lit 1329, Int.ofNat (nat_lit 240589825423728)), (nat_lit 1330, Int.ofNat (nat_lit 257835405193872)), (nat_lit 1331, Int.ofNat (nat_lit 269199215587104)), (nat_lit 1332, Int.ofNat (nat_lit 296143129765824)), (nat_lit 1333, Int.ofNat (nat_lit 286503931190400)), (nat_lit 1334, Int.ofNat (nat_lit 273190469798400)), (nat_lit 1335, Int.ofNat (nat_lit 274664015001600)), (nat_lit 1336, Int.ofNat (nat_lit 264315049958400)), (nat_lit 1337, Int.ofNat (nat_lit 263898823372800))]
theorem block013_data_flat078_step : block013_data_flat078 = (CoefficientMerge.fastMerge block013_data_flat038 block013_data_flat077) := by decide +kernel
theorem block013_data_flat078_original : block013_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (250762389292800 : Int) atom0849Coded) (CoefficientMerge.scale (222902250278400 : Int) atom0850Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (225353863526400 : Int) atom0851Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (215982966528000 : Int) atom0852Coded) (CoefficientMerge.scale (216544807987200 : Int) atom0853Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (257815027008000 : Int) atom0854Coded) (CoefficientMerge.scale (189421289164800 : Int) atom0855Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (268578751795200 : Int) atom0856Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (215630979379200 : Int) atom0857Coded) (CoefficientMerge.scale (228830374080000 : Int) atom0858Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (274763154758400 : Int) atom0859Coded) (CoefficientMerge.scale (126234564825600 : Int) atom0860Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (224731214400000 : Int) atom0861Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (202842807552000 : Int) atom0862Coded) (CoefficientMerge.scale (206600779625328 : Int) atom0863Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (226908137622672 : Int) atom0864Coded) (CoefficientMerge.scale (237208830575904 : Int) atom0865Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (263089627314624 : Int) atom0866Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (254449759132800 : Int) atom0867Coded) (CoefficientMerge.scale (242135628134400 : Int) atom0868Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (244608503731200 : Int) atom0869Coded) (CoefficientMerge.scale (235258869081600 : Int) atom0870Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (235841972889600 : Int) atom0871Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (274348086566400 : Int) atom0872Coded) (CoefficientMerge.scale (220533081753600 : Int) atom0873Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (307559875392000 : Int) atom0874Coded) (CoefficientMerge.scale (270329502643200 : Int) atom0875Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (299246297011200 : Int) atom0876Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (360896477356800 : Int) atom0877Coded) (CoefficientMerge.scale (135493136486400 : Int) atom0878Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (254285879232000 : Int) atom0879Coded) (CoefficientMerge.scale (240589825423728 : Int) atom0880Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (257835405193872 : Int) atom0881Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (269199215587104 : Int) atom0882Coded) (CoefficientMerge.scale (296143129765824 : Int) atom0883Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (286503931190400 : Int) atom0884Coded) (CoefficientMerge.scale (273190469798400 : Int) atom0885Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (274664015001600 : Int) atom0886Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (264315049958400 : Int) atom0887Coded) (CoefficientMerge.scale (263898823372800 : Int) atom0888Coded))))))) := by
  rw [block013_data_flat078_step, block013_data_flat038_original, block013_data_flat077_original]
def block013_data_flat079 : CoefficientMerge.Poly := [(nat_lit 1338, Int.ofNat (nat_lit 303735015091200))]
theorem block013_data_flat079_step : block013_data_flat079 = (CoefficientMerge.scale (303735015091200 : Int) atom0889Coded) := by decide +kernel
theorem block013_data_flat079_original : block013_data_flat079 = (CoefficientMerge.scale (303735015091200 : Int) atom0889Coded) := by
  rw [block013_data_flat079_step]
def block013_data_flat080 : CoefficientMerge.Poly := [(nat_lit 1339, Int.ofNat (nat_lit 253579496755200))]
theorem block013_data_flat080_step : block013_data_flat080 = (CoefficientMerge.scale (253579496755200 : Int) atom0890Coded) := by decide +kernel
theorem block013_data_flat080_original : block013_data_flat080 = (CoefficientMerge.scale (253579496755200 : Int) atom0890Coded) := by
  rw [block013_data_flat080_step]
def block013_data_flat081 : CoefficientMerge.Poly := [(nat_lit 1338, Int.ofNat (nat_lit 303735015091200)), (nat_lit 1339, Int.ofNat (nat_lit 253579496755200))]
theorem block013_data_flat081_step : block013_data_flat081 = (CoefficientMerge.fastMerge block013_data_flat079 block013_data_flat080) := by decide +kernel
theorem block013_data_flat081_original : block013_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (303735015091200 : Int) atom0889Coded) (CoefficientMerge.scale (253579496755200 : Int) atom0890Coded)) := by
  rw [block013_data_flat081_step, block013_data_flat079_original, block013_data_flat080_original]
def block013_data_flat082 : CoefficientMerge.Poly := [(nat_lit 1340, Int.ofNat (nat_lit 344265776870400))]
theorem block013_data_flat082_step : block013_data_flat082 = (CoefficientMerge.scale (344265776870400 : Int) atom0891Coded) := by decide +kernel
theorem block013_data_flat082_original : block013_data_flat082 = (CoefficientMerge.scale (344265776870400 : Int) atom0891Coded) := by
  rw [block013_data_flat082_step]
def block013_data_flat083 : CoefficientMerge.Poly := [(nat_lit 1341, Int.ofNat (nat_lit 315353707468800))]
theorem block013_data_flat083_step : block013_data_flat083 = (CoefficientMerge.scale (315353707468800 : Int) atom0892Coded) := by decide +kernel
theorem block013_data_flat083_original : block013_data_flat083 = (CoefficientMerge.scale (315353707468800 : Int) atom0892Coded) := by
  rw [block013_data_flat083_step]
def block013_data_flat084 : CoefficientMerge.Poly := [(nat_lit 1342, Int.ofNat (nat_lit 352588805184000))]
theorem block013_data_flat084_step : block013_data_flat084 = (CoefficientMerge.scale (352588805184000 : Int) atom0893Coded) := by decide +kernel
theorem block013_data_flat084_original : block013_data_flat084 = (CoefficientMerge.scale (352588805184000 : Int) atom0893Coded) := by
  rw [block013_data_flat084_step]
def block013_data_flat085 : CoefficientMerge.Poly := [(nat_lit 1341, Int.ofNat (nat_lit 315353707468800)), (nat_lit 1342, Int.ofNat (nat_lit 352588805184000))]
theorem block013_data_flat085_step : block013_data_flat085 = (CoefficientMerge.fastMerge block013_data_flat083 block013_data_flat084) := by decide +kernel
theorem block013_data_flat085_original : block013_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (315353707468800 : Int) atom0892Coded) (CoefficientMerge.scale (352588805184000 : Int) atom0893Coded)) := by
  rw [block013_data_flat085_step, block013_data_flat083_original, block013_data_flat084_original]
def block013_data_flat086 : CoefficientMerge.Poly := [(nat_lit 1340, Int.ofNat (nat_lit 344265776870400)), (nat_lit 1341, Int.ofNat (nat_lit 315353707468800)), (nat_lit 1342, Int.ofNat (nat_lit 352588805184000))]
theorem block013_data_flat086_step : block013_data_flat086 = (CoefficientMerge.fastMerge block013_data_flat082 block013_data_flat085) := by decide +kernel
theorem block013_data_flat086_original : block013_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (344265776870400 : Int) atom0891Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (315353707468800 : Int) atom0892Coded) (CoefficientMerge.scale (352588805184000 : Int) atom0893Coded))) := by
  rw [block013_data_flat086_step, block013_data_flat082_original, block013_data_flat085_original]
def block013_data_flat087 : CoefficientMerge.Poly := [(nat_lit 1338, Int.ofNat (nat_lit 303735015091200)), (nat_lit 1339, Int.ofNat (nat_lit 253579496755200)), (nat_lit 1340, Int.ofNat (nat_lit 344265776870400)), (nat_lit 1341, Int.ofNat (nat_lit 315353707468800)), (nat_lit 1342, Int.ofNat (nat_lit 352588805184000))]
theorem block013_data_flat087_step : block013_data_flat087 = (CoefficientMerge.fastMerge block013_data_flat081 block013_data_flat086) := by decide +kernel
theorem block013_data_flat087_original : block013_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (303735015091200 : Int) atom0889Coded) (CoefficientMerge.scale (253579496755200 : Int) atom0890Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (344265776870400 : Int) atom0891Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (315353707468800 : Int) atom0892Coded) (CoefficientMerge.scale (352588805184000 : Int) atom0893Coded)))) := by
  rw [block013_data_flat087_step, block013_data_flat081_original, block013_data_flat086_original]
def block013_data_flat088 : CoefficientMerge.Poly := [(nat_lit 1343, Int.ofNat (nat_lit 422557288876800))]
theorem block013_data_flat088_step : block013_data_flat088 = (CoefficientMerge.scale (422557288876800 : Int) atom0894Coded) := by decide +kernel
theorem block013_data_flat088_original : block013_data_flat088 = (CoefficientMerge.scale (422557288876800 : Int) atom0894Coded) := by
  rw [block013_data_flat088_step]
def block013_data_flat089 : CoefficientMerge.Poly := [(nat_lit 1352, Int.ofNat (nat_lit 156809822400000))]
theorem block013_data_flat089_step : block013_data_flat089 = (CoefficientMerge.scale (156809822400000 : Int) atom0895Coded) := by decide +kernel
theorem block013_data_flat089_original : block013_data_flat089 = (CoefficientMerge.scale (156809822400000 : Int) atom0895Coded) := by
  rw [block013_data_flat089_step]
def block013_data_flat090 : CoefficientMerge.Poly := [(nat_lit 1343, Int.ofNat (nat_lit 422557288876800)), (nat_lit 1352, Int.ofNat (nat_lit 156809822400000))]
theorem block013_data_flat090_step : block013_data_flat090 = (CoefficientMerge.fastMerge block013_data_flat088 block013_data_flat089) := by decide +kernel
theorem block013_data_flat090_original : block013_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (422557288876800 : Int) atom0894Coded) (CoefficientMerge.scale (156809822400000 : Int) atom0895Coded)) := by
  rw [block013_data_flat090_step, block013_data_flat088_original, block013_data_flat089_original]
def block013_data_flat091 : CoefficientMerge.Poly := [(nat_lit 1353, Int.ofNat (nat_lit 298917689941728))]
theorem block013_data_flat091_step : block013_data_flat091 = (CoefficientMerge.scale (298917689941728 : Int) atom0896Coded) := by decide +kernel
theorem block013_data_flat091_original : block013_data_flat091 = (CoefficientMerge.scale (298917689941728 : Int) atom0896Coded) := by
  rw [block013_data_flat091_step]
def block013_data_flat092 : CoefficientMerge.Poly := [(nat_lit 1354, Int.ofNat (nat_lit 285877758467664))]
theorem block013_data_flat092_step : block013_data_flat092 = (CoefficientMerge.scale (285877758467664 : Int) atom0897Coded) := by decide +kernel
theorem block013_data_flat092_original : block013_data_flat092 = (CoefficientMerge.scale (285877758467664 : Int) atom0897Coded) := by
  rw [block013_data_flat092_step]
def block013_data_flat093 : CoefficientMerge.Poly := [(nat_lit 1355, Int.ofNat (nat_lit 299464987862304))]
theorem block013_data_flat093_step : block013_data_flat093 = (CoefficientMerge.scale (299464987862304 : Int) atom0898Coded) := by decide +kernel
theorem block013_data_flat093_original : block013_data_flat093 = (CoefficientMerge.scale (299464987862304 : Int) atom0898Coded) := by
  rw [block013_data_flat093_step]
def block013_data_flat094 : CoefficientMerge.Poly := [(nat_lit 1354, Int.ofNat (nat_lit 285877758467664)), (nat_lit 1355, Int.ofNat (nat_lit 299464987862304))]
theorem block013_data_flat094_step : block013_data_flat094 = (CoefficientMerge.fastMerge block013_data_flat092 block013_data_flat093) := by decide +kernel
theorem block013_data_flat094_original : block013_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (285877758467664 : Int) atom0897Coded) (CoefficientMerge.scale (299464987862304 : Int) atom0898Coded)) := by
  rw [block013_data_flat094_step, block013_data_flat092_original, block013_data_flat093_original]
def block013_data_flat095 : CoefficientMerge.Poly := [(nat_lit 1353, Int.ofNat (nat_lit 298917689941728)), (nat_lit 1354, Int.ofNat (nat_lit 285877758467664)), (nat_lit 1355, Int.ofNat (nat_lit 299464987862304))]
theorem block013_data_flat095_step : block013_data_flat095 = (CoefficientMerge.fastMerge block013_data_flat091 block013_data_flat094) := by decide +kernel
theorem block013_data_flat095_original : block013_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (298917689941728 : Int) atom0896Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (285877758467664 : Int) atom0897Coded) (CoefficientMerge.scale (299464987862304 : Int) atom0898Coded))) := by
  rw [block013_data_flat095_step, block013_data_flat091_original, block013_data_flat094_original]
def block013_data_flat096 : CoefficientMerge.Poly := [(nat_lit 1343, Int.ofNat (nat_lit 422557288876800)), (nat_lit 1352, Int.ofNat (nat_lit 156809822400000)), (nat_lit 1353, Int.ofNat (nat_lit 298917689941728)), (nat_lit 1354, Int.ofNat (nat_lit 285877758467664)), (nat_lit 1355, Int.ofNat (nat_lit 299464987862304))]
theorem block013_data_flat096_step : block013_data_flat096 = (CoefficientMerge.fastMerge block013_data_flat090 block013_data_flat095) := by decide +kernel
theorem block013_data_flat096_original : block013_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (422557288876800 : Int) atom0894Coded) (CoefficientMerge.scale (156809822400000 : Int) atom0895Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (298917689941728 : Int) atom0896Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (285877758467664 : Int) atom0897Coded) (CoefficientMerge.scale (299464987862304 : Int) atom0898Coded)))) := by
  rw [block013_data_flat096_step, block013_data_flat090_original, block013_data_flat095_original]
def block013_data_flat097 : CoefficientMerge.Poly := [(nat_lit 1338, Int.ofNat (nat_lit 303735015091200)), (nat_lit 1339, Int.ofNat (nat_lit 253579496755200)), (nat_lit 1340, Int.ofNat (nat_lit 344265776870400)), (nat_lit 1341, Int.ofNat (nat_lit 315353707468800)), (nat_lit 1342, Int.ofNat (nat_lit 352588805184000)), (nat_lit 1343, Int.ofNat (nat_lit 422557288876800)), (nat_lit 1352, Int.ofNat (nat_lit 156809822400000)), (nat_lit 1353, Int.ofNat (nat_lit 298917689941728)), (nat_lit 1354, Int.ofNat (nat_lit 285877758467664)), (nat_lit 1355, Int.ofNat (nat_lit 299464987862304))]
theorem block013_data_flat097_step : block013_data_flat097 = (CoefficientMerge.fastMerge block013_data_flat087 block013_data_flat096) := by decide +kernel
theorem block013_data_flat097_original : block013_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (303735015091200 : Int) atom0889Coded) (CoefficientMerge.scale (253579496755200 : Int) atom0890Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (344265776870400 : Int) atom0891Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (315353707468800 : Int) atom0892Coded) (CoefficientMerge.scale (352588805184000 : Int) atom0893Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (422557288876800 : Int) atom0894Coded) (CoefficientMerge.scale (156809822400000 : Int) atom0895Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (298917689941728 : Int) atom0896Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (285877758467664 : Int) atom0897Coded) (CoefficientMerge.scale (299464987862304 : Int) atom0898Coded))))) := by
  rw [block013_data_flat097_step, block013_data_flat087_original, block013_data_flat096_original]
def block013_data_flat098 : CoefficientMerge.Poly := [(nat_lit 1356, Int.ofNat (nat_lit 321305938329024))]
theorem block013_data_flat098_step : block013_data_flat098 = (CoefficientMerge.scale (321305938329024 : Int) atom0899Coded) := by decide +kernel
theorem block013_data_flat098_original : block013_data_flat098 = (CoefficientMerge.scale (321305938329024 : Int) atom0899Coded) := by
  rw [block013_data_flat098_step]
def block013_data_flat099 : CoefficientMerge.Poly := [(nat_lit 1357, Int.ofNat (nat_lit 309646816617600))]
theorem block013_data_flat099_step : block013_data_flat099 = (CoefficientMerge.scale (309646816617600 : Int) atom0900Coded) := by decide +kernel
theorem block013_data_flat099_original : block013_data_flat099 = (CoefficientMerge.scale (309646816617600 : Int) atom0900Coded) := by
  rw [block013_data_flat099_step]
def block013_data_flat100 : CoefficientMerge.Poly := [(nat_lit 1356, Int.ofNat (nat_lit 321305938329024)), (nat_lit 1357, Int.ofNat (nat_lit 309646816617600))]
theorem block013_data_flat100_step : block013_data_flat100 = (CoefficientMerge.fastMerge block013_data_flat098 block013_data_flat099) := by decide +kernel
theorem block013_data_flat100_original : block013_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (321305938329024 : Int) atom0899Coded) (CoefficientMerge.scale (309646816617600 : Int) atom0900Coded)) := by
  rw [block013_data_flat100_step, block013_data_flat098_original, block013_data_flat099_original]
def block013_data_flat101 : CoefficientMerge.Poly := [(nat_lit 1358, Int.ofNat (nat_lit 294313432089600))]
theorem block013_data_flat101_step : block013_data_flat101 = (CoefficientMerge.scale (294313432089600 : Int) atom0901Coded) := by decide +kernel
theorem block013_data_flat101_original : block013_data_flat101 = (CoefficientMerge.scale (294313432089600 : Int) atom0901Coded) := by
  rw [block013_data_flat101_step]
def block013_data_flat102 : CoefficientMerge.Poly := [(nat_lit 1359, Int.ofNat (nat_lit 293767054156800))]
theorem block013_data_flat102_step : block013_data_flat102 = (CoefficientMerge.scale (293767054156800 : Int) atom0902Coded) := by decide +kernel
theorem block013_data_flat102_original : block013_data_flat102 = (CoefficientMerge.scale (293767054156800 : Int) atom0902Coded) := by
  rw [block013_data_flat102_step]
def block013_data_flat103 : CoefficientMerge.Poly := [(nat_lit 1360, Int.ofNat (nat_lit 281398165977600))]
theorem block013_data_flat103_step : block013_data_flat103 = (CoefficientMerge.scale (281398165977600 : Int) atom0903Coded) := by decide +kernel
theorem block013_data_flat103_original : block013_data_flat103 = (CoefficientMerge.scale (281398165977600 : Int) atom0903Coded) := by
  rw [block013_data_flat103_step]
def block013_data_flat104 : CoefficientMerge.Poly := [(nat_lit 1359, Int.ofNat (nat_lit 293767054156800)), (nat_lit 1360, Int.ofNat (nat_lit 281398165977600))]
theorem block013_data_flat104_step : block013_data_flat104 = (CoefficientMerge.fastMerge block013_data_flat102 block013_data_flat103) := by decide +kernel
theorem block013_data_flat104_original : block013_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (293767054156800 : Int) atom0902Coded) (CoefficientMerge.scale (281398165977600 : Int) atom0903Coded)) := by
  rw [block013_data_flat104_step, block013_data_flat102_original, block013_data_flat103_original]
def block013_data_flat105 : CoefficientMerge.Poly := [(nat_lit 1358, Int.ofNat (nat_lit 294313432089600)), (nat_lit 1359, Int.ofNat (nat_lit 293767054156800)), (nat_lit 1360, Int.ofNat (nat_lit 281398165977600))]
theorem block013_data_flat105_step : block013_data_flat105 = (CoefficientMerge.fastMerge block013_data_flat101 block013_data_flat104) := by decide +kernel
theorem block013_data_flat105_original : block013_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (294313432089600 : Int) atom0901Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (293767054156800 : Int) atom0902Coded) (CoefficientMerge.scale (281398165977600 : Int) atom0903Coded))) := by
  rw [block013_data_flat105_step, block013_data_flat101_original, block013_data_flat104_original]
def block013_data_flat106 : CoefficientMerge.Poly := [(nat_lit 1356, Int.ofNat (nat_lit 321305938329024)), (nat_lit 1357, Int.ofNat (nat_lit 309646816617600)), (nat_lit 1358, Int.ofNat (nat_lit 294313432089600)), (nat_lit 1359, Int.ofNat (nat_lit 293767054156800)), (nat_lit 1360, Int.ofNat (nat_lit 281398165977600))]
theorem block013_data_flat106_step : block013_data_flat106 = (CoefficientMerge.fastMerge block013_data_flat100 block013_data_flat105) := by decide +kernel
theorem block013_data_flat106_original : block013_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (321305938329024 : Int) atom0899Coded) (CoefficientMerge.scale (309646816617600 : Int) atom0900Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (294313432089600 : Int) atom0901Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (293767054156800 : Int) atom0902Coded) (CoefficientMerge.scale (281398165977600 : Int) atom0903Coded)))) := by
  rw [block013_data_flat106_step, block013_data_flat100_original, block013_data_flat105_original]
def block013_data_flat107 : CoefficientMerge.Poly := [(nat_lit 1361, Int.ofNat (nat_lit 278962016256000))]
theorem block013_data_flat107_step : block013_data_flat107 = (CoefficientMerge.scale (278962016256000 : Int) atom0904Coded) := by decide +kernel
theorem block013_data_flat107_original : block013_data_flat107 = (CoefficientMerge.scale (278962016256000 : Int) atom0904Coded) := by
  rw [block013_data_flat107_step]
def block013_data_flat108 : CoefficientMerge.Poly := [(nat_lit 1362, Int.ofNat (nat_lit 320232235276800))]
theorem block013_data_flat108_step : block013_data_flat108 = (CoefficientMerge.scale (320232235276800 : Int) atom0905Coded) := by decide +kernel
theorem block013_data_flat108_original : block013_data_flat108 = (CoefficientMerge.scale (320232235276800 : Int) atom0905Coded) := by
  rw [block013_data_flat108_step]
def block013_data_flat109 : CoefficientMerge.Poly := [(nat_lit 1361, Int.ofNat (nat_lit 278962016256000)), (nat_lit 1362, Int.ofNat (nat_lit 320232235276800))]
theorem block013_data_flat109_step : block013_data_flat109 = (CoefficientMerge.fastMerge block013_data_flat107 block013_data_flat108) := by decide +kernel
theorem block013_data_flat109_original : block013_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (278962016256000 : Int) atom0904Coded) (CoefficientMerge.scale (320232235276800 : Int) atom0905Coded)) := by
  rw [block013_data_flat109_step, block013_data_flat107_original, block013_data_flat108_original]
def block013_data_flat110 : CoefficientMerge.Poly := [(nat_lit 1363, Int.ofNat (nat_lit 274964694681600))]
theorem block013_data_flat110_step : block013_data_flat110 = (CoefficientMerge.scale (274964694681600 : Int) atom0906Coded) := by decide +kernel
theorem block013_data_flat110_original : block013_data_flat110 = (CoefficientMerge.scale (274964694681600 : Int) atom0906Coded) := by
  rw [block013_data_flat110_step]
def block013_data_flat111 : CoefficientMerge.Poly := [(nat_lit 1364, Int.ofNat (nat_lit 370538952537600))]
theorem block013_data_flat111_step : block013_data_flat111 = (CoefficientMerge.scale (370538952537600 : Int) atom0907Coded) := by decide +kernel
theorem block013_data_flat111_original : block013_data_flat111 = (CoefficientMerge.scale (370538952537600 : Int) atom0907Coded) := by
  rw [block013_data_flat111_step]
def block013_data_flat112 : CoefficientMerge.Poly := [(nat_lit 1365, Int.ofNat (nat_lit 353422761753600))]
theorem block013_data_flat112_step : block013_data_flat112 = (CoefficientMerge.scale (353422761753600 : Int) atom0908Coded) := by decide +kernel
theorem block013_data_flat112_original : block013_data_flat112 = (CoefficientMerge.scale (353422761753600 : Int) atom0908Coded) := by
  rw [block013_data_flat112_step]
def block013_data_flat113 : CoefficientMerge.Poly := [(nat_lit 1364, Int.ofNat (nat_lit 370538952537600)), (nat_lit 1365, Int.ofNat (nat_lit 353422761753600))]
theorem block013_data_flat113_step : block013_data_flat113 = (CoefficientMerge.fastMerge block013_data_flat111 block013_data_flat112) := by decide +kernel
theorem block013_data_flat113_original : block013_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (370538952537600 : Int) atom0907Coded) (CoefficientMerge.scale (353422761753600 : Int) atom0908Coded)) := by
  rw [block013_data_flat113_step, block013_data_flat111_original, block013_data_flat112_original]
def block013_data_flat114 : CoefficientMerge.Poly := [(nat_lit 1363, Int.ofNat (nat_lit 274964694681600)), (nat_lit 1364, Int.ofNat (nat_lit 370538952537600)), (nat_lit 1365, Int.ofNat (nat_lit 353422761753600))]
theorem block013_data_flat114_step : block013_data_flat114 = (CoefficientMerge.fastMerge block013_data_flat110 block013_data_flat113) := by decide +kernel
theorem block013_data_flat114_original : block013_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (274964694681600 : Int) atom0906Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (370538952537600 : Int) atom0907Coded) (CoefficientMerge.scale (353422761753600 : Int) atom0908Coded))) := by
  rw [block013_data_flat114_step, block013_data_flat110_original, block013_data_flat113_original]
def block013_data_flat115 : CoefficientMerge.Poly := [(nat_lit 1361, Int.ofNat (nat_lit 278962016256000)), (nat_lit 1362, Int.ofNat (nat_lit 320232235276800)), (nat_lit 1363, Int.ofNat (nat_lit 274964694681600)), (nat_lit 1364, Int.ofNat (nat_lit 370538952537600)), (nat_lit 1365, Int.ofNat (nat_lit 353422761753600))]
theorem block013_data_flat115_step : block013_data_flat115 = (CoefficientMerge.fastMerge block013_data_flat109 block013_data_flat114) := by decide +kernel
theorem block013_data_flat115_original : block013_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (278962016256000 : Int) atom0904Coded) (CoefficientMerge.scale (320232235276800 : Int) atom0905Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (274964694681600 : Int) atom0906Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (370538952537600 : Int) atom0907Coded) (CoefficientMerge.scale (353422761753600 : Int) atom0908Coded)))) := by
  rw [block013_data_flat115_step, block013_data_flat109_original, block013_data_flat114_original]
def block013_data_flat116 : CoefficientMerge.Poly := [(nat_lit 1356, Int.ofNat (nat_lit 321305938329024)), (nat_lit 1357, Int.ofNat (nat_lit 309646816617600)), (nat_lit 1358, Int.ofNat (nat_lit 294313432089600)), (nat_lit 1359, Int.ofNat (nat_lit 293767054156800)), (nat_lit 1360, Int.ofNat (nat_lit 281398165977600)), (nat_lit 1361, Int.ofNat (nat_lit 278962016256000)), (nat_lit 1362, Int.ofNat (nat_lit 320232235276800)), (nat_lit 1363, Int.ofNat (nat_lit 274964694681600)), (nat_lit 1364, Int.ofNat (nat_lit 370538952537600)), (nat_lit 1365, Int.ofNat (nat_lit 353422761753600))]
theorem block013_data_flat116_step : block013_data_flat116 = (CoefficientMerge.fastMerge block013_data_flat106 block013_data_flat115) := by decide +kernel
theorem block013_data_flat116_original : block013_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (321305938329024 : Int) atom0899Coded) (CoefficientMerge.scale (309646816617600 : Int) atom0900Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (294313432089600 : Int) atom0901Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (293767054156800 : Int) atom0902Coded) (CoefficientMerge.scale (281398165977600 : Int) atom0903Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (278962016256000 : Int) atom0904Coded) (CoefficientMerge.scale (320232235276800 : Int) atom0905Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (274964694681600 : Int) atom0906Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (370538952537600 : Int) atom0907Coded) (CoefficientMerge.scale (353422761753600 : Int) atom0908Coded))))) := by
  rw [block013_data_flat116_step, block013_data_flat106_original, block013_data_flat115_original]
def block013_data_flat117 : CoefficientMerge.Poly := [(nat_lit 1338, Int.ofNat (nat_lit 303735015091200)), (nat_lit 1339, Int.ofNat (nat_lit 253579496755200)), (nat_lit 1340, Int.ofNat (nat_lit 344265776870400)), (nat_lit 1341, Int.ofNat (nat_lit 315353707468800)), (nat_lit 1342, Int.ofNat (nat_lit 352588805184000)), (nat_lit 1343, Int.ofNat (nat_lit 422557288876800)), (nat_lit 1352, Int.ofNat (nat_lit 156809822400000)), (nat_lit 1353, Int.ofNat (nat_lit 298917689941728)), (nat_lit 1354, Int.ofNat (nat_lit 285877758467664)), (nat_lit 1355, Int.ofNat (nat_lit 299464987862304)), (nat_lit 1356, Int.ofNat (nat_lit 321305938329024)), (nat_lit 1357, Int.ofNat (nat_lit 309646816617600)), (nat_lit 1358, Int.ofNat (nat_lit 294313432089600)), (nat_lit 1359, Int.ofNat (nat_lit 293767054156800)), (nat_lit 1360, Int.ofNat (nat_lit 281398165977600)), (nat_lit 1361, Int.ofNat (nat_lit 278962016256000)), (nat_lit 1362, Int.ofNat (nat_lit 320232235276800)), (nat_lit 1363, Int.ofNat (nat_lit 274964694681600)), (nat_lit 1364, Int.ofNat (nat_lit 370538952537600)), (nat_lit 1365, Int.ofNat (nat_lit 353422761753600))]
theorem block013_data_flat117_step : block013_data_flat117 = (CoefficientMerge.fastMerge block013_data_flat097 block013_data_flat116) := by decide +kernel
theorem block013_data_flat117_original : block013_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (303735015091200 : Int) atom0889Coded) (CoefficientMerge.scale (253579496755200 : Int) atom0890Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (344265776870400 : Int) atom0891Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (315353707468800 : Int) atom0892Coded) (CoefficientMerge.scale (352588805184000 : Int) atom0893Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (422557288876800 : Int) atom0894Coded) (CoefficientMerge.scale (156809822400000 : Int) atom0895Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (298917689941728 : Int) atom0896Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (285877758467664 : Int) atom0897Coded) (CoefficientMerge.scale (299464987862304 : Int) atom0898Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (321305938329024 : Int) atom0899Coded) (CoefficientMerge.scale (309646816617600 : Int) atom0900Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (294313432089600 : Int) atom0901Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (293767054156800 : Int) atom0902Coded) (CoefficientMerge.scale (281398165977600 : Int) atom0903Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (278962016256000 : Int) atom0904Coded) (CoefficientMerge.scale (320232235276800 : Int) atom0905Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (274964694681600 : Int) atom0906Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (370538952537600 : Int) atom0907Coded) (CoefficientMerge.scale (353422761753600 : Int) atom0908Coded)))))) := by
  rw [block013_data_flat117_step, block013_data_flat097_original, block013_data_flat116_original]
def block013_data_flat118 : CoefficientMerge.Poly := [(nat_lit 1366, Int.ofNat (nat_lit 402453738086400))]
theorem block013_data_flat118_step : block013_data_flat118 = (CoefficientMerge.scale (402453738086400 : Int) atom0909Coded) := by decide +kernel
theorem block013_data_flat118_original : block013_data_flat118 = (CoefficientMerge.scale (402453738086400 : Int) atom0909Coded) := by
  rw [block013_data_flat118_step]
def block013_data_flat119 : CoefficientMerge.Poly := [(nat_lit 1367, Int.ofNat (nat_lit 484218100396800))]
theorem block013_data_flat119_step : block013_data_flat119 = (CoefficientMerge.scale (484218100396800 : Int) atom0910Coded) := by decide +kernel
theorem block013_data_flat119_original : block013_data_flat119 = (CoefficientMerge.scale (484218100396800 : Int) atom0910Coded) := by
  rw [block013_data_flat119_step]
def block013_data_flat120 : CoefficientMerge.Poly := [(nat_lit 1366, Int.ofNat (nat_lit 402453738086400)), (nat_lit 1367, Int.ofNat (nat_lit 484218100396800))]
theorem block013_data_flat120_step : block013_data_flat120 = (CoefficientMerge.fastMerge block013_data_flat118 block013_data_flat119) := by decide +kernel
theorem block013_data_flat120_original : block013_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (402453738086400 : Int) atom0909Coded) (CoefficientMerge.scale (484218100396800 : Int) atom0910Coded)) := by
  rw [block013_data_flat120_step, block013_data_flat118_original, block013_data_flat119_original]
def block013_data_flat121 : CoefficientMerge.Poly := [(nat_lit 1377, Int.ofNat (nat_lit 183207987772128))]
theorem block013_data_flat121_step : block013_data_flat121 = (CoefficientMerge.scale (183207987772128 : Int) atom0911Coded) := by decide +kernel
theorem block013_data_flat121_original : block013_data_flat121 = (CoefficientMerge.scale (183207987772128 : Int) atom0911Coded) := by
  rw [block013_data_flat121_step]
def block013_data_flat122 : CoefficientMerge.Poly := [(nat_lit 1378, Int.ofNat (nat_lit 350273600335296))]
theorem block013_data_flat122_step : block013_data_flat122 = (CoefficientMerge.scale (350273600335296 : Int) atom0912Coded) := by decide +kernel
theorem block013_data_flat122_original : block013_data_flat122 = (CoefficientMerge.scale (350273600335296 : Int) atom0912Coded) := by
  rw [block013_data_flat122_step]
def block013_data_flat123 : CoefficientMerge.Poly := [(nat_lit 1379, Int.ofNat (nat_lit 338777815302432))]
theorem block013_data_flat123_step : block013_data_flat123 = (CoefficientMerge.scale (338777815302432 : Int) atom0913Coded) := by decide +kernel
theorem block013_data_flat123_original : block013_data_flat123 = (CoefficientMerge.scale (338777815302432 : Int) atom0913Coded) := by
  rw [block013_data_flat123_step]
def block013_data_flat124 : CoefficientMerge.Poly := [(nat_lit 1378, Int.ofNat (nat_lit 350273600335296)), (nat_lit 1379, Int.ofNat (nat_lit 338777815302432))]
theorem block013_data_flat124_step : block013_data_flat124 = (CoefficientMerge.fastMerge block013_data_flat122 block013_data_flat123) := by decide +kernel
theorem block013_data_flat124_original : block013_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (350273600335296 : Int) atom0912Coded) (CoefficientMerge.scale (338777815302432 : Int) atom0913Coded)) := by
  rw [block013_data_flat124_step, block013_data_flat122_original, block013_data_flat123_original]
def block013_data_flat125 : CoefficientMerge.Poly := [(nat_lit 1377, Int.ofNat (nat_lit 183207987772128)), (nat_lit 1378, Int.ofNat (nat_lit 350273600335296)), (nat_lit 1379, Int.ofNat (nat_lit 338777815302432))]
theorem block013_data_flat125_step : block013_data_flat125 = (CoefficientMerge.fastMerge block013_data_flat121 block013_data_flat124) := by decide +kernel
theorem block013_data_flat125_original : block013_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (183207987772128 : Int) atom0911Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (350273600335296 : Int) atom0912Coded) (CoefficientMerge.scale (338777815302432 : Int) atom0913Coded))) := by
  rw [block013_data_flat125_step, block013_data_flat121_original, block013_data_flat124_original]
def block013_data_flat126 : CoefficientMerge.Poly := [(nat_lit 1366, Int.ofNat (nat_lit 402453738086400)), (nat_lit 1367, Int.ofNat (nat_lit 484218100396800)), (nat_lit 1377, Int.ofNat (nat_lit 183207987772128)), (nat_lit 1378, Int.ofNat (nat_lit 350273600335296)), (nat_lit 1379, Int.ofNat (nat_lit 338777815302432))]
theorem block013_data_flat126_step : block013_data_flat126 = (CoefficientMerge.fastMerge block013_data_flat120 block013_data_flat125) := by decide +kernel
theorem block013_data_flat126_original : block013_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (402453738086400 : Int) atom0909Coded) (CoefficientMerge.scale (484218100396800 : Int) atom0910Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (183207987772128 : Int) atom0911Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (350273600335296 : Int) atom0912Coded) (CoefficientMerge.scale (338777815302432 : Int) atom0913Coded)))) := by
  rw [block013_data_flat126_step, block013_data_flat120_original, block013_data_flat125_original]
def block013_data_flat127 : CoefficientMerge.Poly := [(nat_lit 1380, Int.ofNat (nat_lit 360661290466752))]
theorem block013_data_flat127_step : block013_data_flat127 = (CoefficientMerge.scale (360661290466752 : Int) atom0914Coded) := by decide +kernel
theorem block013_data_flat127_original : block013_data_flat127 = (CoefficientMerge.scale (360661290466752 : Int) atom0914Coded) := by
  rw [block013_data_flat127_step]
def block013_data_flat128 : CoefficientMerge.Poly := [(nat_lit 1381, Int.ofNat (nat_lit 342878612300928))]
theorem block013_data_flat128_step : block013_data_flat128 = (CoefficientMerge.scale (342878612300928 : Int) atom0915Coded) := by decide +kernel
theorem block013_data_flat128_original : block013_data_flat128 = (CoefficientMerge.scale (342878612300928 : Int) atom0915Coded) := by
  rw [block013_data_flat128_step]
def block013_data_flat129 : CoefficientMerge.Poly := [(nat_lit 1380, Int.ofNat (nat_lit 360661290466752)), (nat_lit 1381, Int.ofNat (nat_lit 342878612300928))]
theorem block013_data_flat129_step : block013_data_flat129 = (CoefficientMerge.fastMerge block013_data_flat127 block013_data_flat128) := by decide +kernel
theorem block013_data_flat129_original : block013_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (360661290466752 : Int) atom0914Coded) (CoefficientMerge.scale (342878612300928 : Int) atom0915Coded)) := by
  rw [block013_data_flat129_step, block013_data_flat127_original, block013_data_flat128_original]
def block013_data_flat130 : CoefficientMerge.Poly := [(nat_lit 1382, Int.ofNat (nat_lit 324504711894528))]
theorem block013_data_flat130_step : block013_data_flat130 = (CoefficientMerge.scale (324504711894528 : Int) atom0916Coded) := by decide +kernel
theorem block013_data_flat130_original : block013_data_flat130 = (CoefficientMerge.scale (324504711894528 : Int) atom0916Coded) := by
  rw [block013_data_flat130_step]
def block013_data_flat131 : CoefficientMerge.Poly := [(nat_lit 1383, Int.ofNat (nat_lit 320917818083328))]
theorem block013_data_flat131_step : block013_data_flat131 = (CoefficientMerge.scale (320917818083328 : Int) atom0917Coded) := by decide +kernel
theorem block013_data_flat131_original : block013_data_flat131 = (CoefficientMerge.scale (320917818083328 : Int) atom0917Coded) := by
  rw [block013_data_flat131_step]
def block013_data_flat132 : CoefficientMerge.Poly := [(nat_lit 1384, Int.ofNat (nat_lit 305508414025728))]
theorem block013_data_flat132_step : block013_data_flat132 = (CoefficientMerge.scale (305508414025728 : Int) atom0918Coded) := by decide +kernel
theorem block013_data_flat132_original : block013_data_flat132 = (CoefficientMerge.scale (305508414025728 : Int) atom0918Coded) := by
  rw [block013_data_flat132_step]
def block013_data_flat133 : CoefficientMerge.Poly := [(nat_lit 1383, Int.ofNat (nat_lit 320917818083328)), (nat_lit 1384, Int.ofNat (nat_lit 305508414025728))]
theorem block013_data_flat133_step : block013_data_flat133 = (CoefficientMerge.fastMerge block013_data_flat131 block013_data_flat132) := by decide +kernel
theorem block013_data_flat133_original : block013_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (320917818083328 : Int) atom0917Coded) (CoefficientMerge.scale (305508414025728 : Int) atom0918Coded)) := by
  rw [block013_data_flat133_step, block013_data_flat131_original, block013_data_flat132_original]
def block013_data_flat134 : CoefficientMerge.Poly := [(nat_lit 1382, Int.ofNat (nat_lit 324504711894528)), (nat_lit 1383, Int.ofNat (nat_lit 320917818083328)), (nat_lit 1384, Int.ofNat (nat_lit 305508414025728))]
theorem block013_data_flat134_step : block013_data_flat134 = (CoefficientMerge.fastMerge block013_data_flat130 block013_data_flat133) := by decide +kernel
theorem block013_data_flat134_original : block013_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (324504711894528 : Int) atom0916Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (320917818083328 : Int) atom0917Coded) (CoefficientMerge.scale (305508414025728 : Int) atom0918Coded))) := by
  rw [block013_data_flat134_step, block013_data_flat130_original, block013_data_flat133_original]
def block013_data_flat135 : CoefficientMerge.Poly := [(nat_lit 1380, Int.ofNat (nat_lit 360661290466752)), (nat_lit 1381, Int.ofNat (nat_lit 342878612300928)), (nat_lit 1382, Int.ofNat (nat_lit 324504711894528)), (nat_lit 1383, Int.ofNat (nat_lit 320917818083328)), (nat_lit 1384, Int.ofNat (nat_lit 305508414025728))]
theorem block013_data_flat135_step : block013_data_flat135 = (CoefficientMerge.fastMerge block013_data_flat129 block013_data_flat134) := by decide +kernel
theorem block013_data_flat135_original : block013_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (360661290466752 : Int) atom0914Coded) (CoefficientMerge.scale (342878612300928 : Int) atom0915Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (324504711894528 : Int) atom0916Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (320917818083328 : Int) atom0917Coded) (CoefficientMerge.scale (305508414025728 : Int) atom0918Coded)))) := by
  rw [block013_data_flat135_step, block013_data_flat129_original, block013_data_flat134_original]
def block013_data_flat136 : CoefficientMerge.Poly := [(nat_lit 1366, Int.ofNat (nat_lit 402453738086400)), (nat_lit 1367, Int.ofNat (nat_lit 484218100396800)), (nat_lit 1377, Int.ofNat (nat_lit 183207987772128)), (nat_lit 1378, Int.ofNat (nat_lit 350273600335296)), (nat_lit 1379, Int.ofNat (nat_lit 338777815302432)), (nat_lit 1380, Int.ofNat (nat_lit 360661290466752)), (nat_lit 1381, Int.ofNat (nat_lit 342878612300928)), (nat_lit 1382, Int.ofNat (nat_lit 324504711894528)), (nat_lit 1383, Int.ofNat (nat_lit 320917818083328)), (nat_lit 1384, Int.ofNat (nat_lit 305508414025728))]
theorem block013_data_flat136_step : block013_data_flat136 = (CoefficientMerge.fastMerge block013_data_flat126 block013_data_flat135) := by decide +kernel
theorem block013_data_flat136_original : block013_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (402453738086400 : Int) atom0909Coded) (CoefficientMerge.scale (484218100396800 : Int) atom0910Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (183207987772128 : Int) atom0911Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (350273600335296 : Int) atom0912Coded) (CoefficientMerge.scale (338777815302432 : Int) atom0913Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (360661290466752 : Int) atom0914Coded) (CoefficientMerge.scale (342878612300928 : Int) atom0915Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (324504711894528 : Int) atom0916Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (320917818083328 : Int) atom0917Coded) (CoefficientMerge.scale (305508414025728 : Int) atom0918Coded))))) := by
  rw [block013_data_flat136_step, block013_data_flat126_original, block013_data_flat135_original]
def block013_data_flat137 : CoefficientMerge.Poly := [(nat_lit 1385, Int.ofNat (nat_lit 300031748425728))]
theorem block013_data_flat137_step : block013_data_flat137 = (CoefficientMerge.scale (300031748425728 : Int) atom0919Coded) := by decide +kernel
theorem block013_data_flat137_original : block013_data_flat137 = (CoefficientMerge.scale (300031748425728 : Int) atom0919Coded) := by
  rw [block013_data_flat137_step]
def block013_data_flat138 : CoefficientMerge.Poly := [(nat_lit 1386, Int.ofNat (nat_lit 340464919398912))]
theorem block013_data_flat138_step : block013_data_flat138 = (CoefficientMerge.scale (340464919398912 : Int) atom0920Coded) := by decide +kernel
theorem block013_data_flat138_original : block013_data_flat138 = (CoefficientMerge.scale (340464919398912 : Int) atom0920Coded) := by
  rw [block013_data_flat138_step]
def block013_data_flat139 : CoefficientMerge.Poly := [(nat_lit 1385, Int.ofNat (nat_lit 300031748425728)), (nat_lit 1386, Int.ofNat (nat_lit 340464919398912))]
theorem block013_data_flat139_step : block013_data_flat139 = (CoefficientMerge.fastMerge block013_data_flat137 block013_data_flat138) := by decide +kernel
theorem block013_data_flat139_original : block013_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (300031748425728 : Int) atom0919Coded) (CoefficientMerge.scale (340464919398912 : Int) atom0920Coded)) := by
  rw [block013_data_flat139_step, block013_data_flat137_original, block013_data_flat138_original]
def block013_data_flat140 : CoefficientMerge.Poly := [(nat_lit 1387, Int.ofNat (nat_lit 296563798586880))]
theorem block013_data_flat140_step : block013_data_flat140 = (CoefficientMerge.scale (296563798586880 : Int) atom0921Coded) := by decide +kernel
theorem block013_data_flat140_original : block013_data_flat140 = (CoefficientMerge.scale (296563798586880 : Int) atom0921Coded) := by
  rw [block013_data_flat140_step]
def block013_data_flat141 : CoefficientMerge.Poly := [(nat_lit 1388, Int.ofNat (nat_lit 393504476226048))]
theorem block013_data_flat141_step : block013_data_flat141 = (CoefficientMerge.scale (393504476226048 : Int) atom0922Coded) := by decide +kernel
theorem block013_data_flat141_original : block013_data_flat141 = (CoefficientMerge.scale (393504476226048 : Int) atom0922Coded) := by
  rw [block013_data_flat141_step]
def block013_data_flat142 : CoefficientMerge.Poly := [(nat_lit 1389, Int.ofNat (nat_lit 382161640886784))]
theorem block013_data_flat142_step : block013_data_flat142 = (CoefficientMerge.scale (382161640886784 : Int) atom0923Coded) := by decide +kernel
theorem block013_data_flat142_original : block013_data_flat142 = (CoefficientMerge.scale (382161640886784 : Int) atom0923Coded) := by
  rw [block013_data_flat142_step]
def block013_data_flat143 : CoefficientMerge.Poly := [(nat_lit 1388, Int.ofNat (nat_lit 393504476226048)), (nat_lit 1389, Int.ofNat (nat_lit 382161640886784))]
theorem block013_data_flat143_step : block013_data_flat143 = (CoefficientMerge.fastMerge block013_data_flat141 block013_data_flat142) := by decide +kernel
theorem block013_data_flat143_original : block013_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (393504476226048 : Int) atom0922Coded) (CoefficientMerge.scale (382161640886784 : Int) atom0923Coded)) := by
  rw [block013_data_flat143_step, block013_data_flat141_original, block013_data_flat142_original]
def block013_data_flat144 : CoefficientMerge.Poly := [(nat_lit 1387, Int.ofNat (nat_lit 296563798586880)), (nat_lit 1388, Int.ofNat (nat_lit 393504476226048)), (nat_lit 1389, Int.ofNat (nat_lit 382161640886784))]
theorem block013_data_flat144_step : block013_data_flat144 = (CoefficientMerge.fastMerge block013_data_flat140 block013_data_flat143) := by decide +kernel
theorem block013_data_flat144_original : block013_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (296563798586880 : Int) atom0921Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (393504476226048 : Int) atom0922Coded) (CoefficientMerge.scale (382161640886784 : Int) atom0923Coded))) := by
  rw [block013_data_flat144_step, block013_data_flat140_original, block013_data_flat143_original]
def block013_data_flat145 : CoefficientMerge.Poly := [(nat_lit 1385, Int.ofNat (nat_lit 300031748425728)), (nat_lit 1386, Int.ofNat (nat_lit 340464919398912)), (nat_lit 1387, Int.ofNat (nat_lit 296563798586880)), (nat_lit 1388, Int.ofNat (nat_lit 393504476226048)), (nat_lit 1389, Int.ofNat (nat_lit 382161640886784))]
theorem block013_data_flat145_step : block013_data_flat145 = (CoefficientMerge.fastMerge block013_data_flat139 block013_data_flat144) := by decide +kernel
theorem block013_data_flat145_original : block013_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (300031748425728 : Int) atom0919Coded) (CoefficientMerge.scale (340464919398912 : Int) atom0920Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (296563798586880 : Int) atom0921Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (393504476226048 : Int) atom0922Coded) (CoefficientMerge.scale (382161640886784 : Int) atom0923Coded)))) := by
  rw [block013_data_flat145_step, block013_data_flat139_original, block013_data_flat144_original]
def block013_data_flat146 : CoefficientMerge.Poly := [(nat_lit 1390, Int.ofNat (nat_lit 436965972664320))]
theorem block013_data_flat146_step : block013_data_flat146 = (CoefficientMerge.scale (436965972664320 : Int) atom0924Coded) := by decide +kernel
theorem block013_data_flat146_original : block013_data_flat146 = (CoefficientMerge.scale (436965972664320 : Int) atom0924Coded) := by
  rw [block013_data_flat146_step]
def block013_data_flat147 : CoefficientMerge.Poly := [(nat_lit 1391, Int.ofNat (nat_lit 524503690419456))]
theorem block013_data_flat147_step : block013_data_flat147 = (CoefficientMerge.scale (524503690419456 : Int) atom0925Coded) := by decide +kernel
theorem block013_data_flat147_original : block013_data_flat147 = (CoefficientMerge.scale (524503690419456 : Int) atom0925Coded) := by
  rw [block013_data_flat147_step]
def block013_data_flat148 : CoefficientMerge.Poly := [(nat_lit 1390, Int.ofNat (nat_lit 436965972664320)), (nat_lit 1391, Int.ofNat (nat_lit 524503690419456))]
theorem block013_data_flat148_step : block013_data_flat148 = (CoefficientMerge.fastMerge block013_data_flat146 block013_data_flat147) := by decide +kernel
theorem block013_data_flat148_original : block013_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (436965972664320 : Int) atom0924Coded) (CoefficientMerge.scale (524503690419456 : Int) atom0925Coded)) := by
  rw [block013_data_flat148_step, block013_data_flat146_original, block013_data_flat147_original]
def block013_data_flat149 : CoefficientMerge.Poly := [(nat_lit 1402, Int.ofNat (nat_lit 208165732793568))]
theorem block013_data_flat149_step : block013_data_flat149 = (CoefficientMerge.scale (208165732793568 : Int) atom0926Coded) := by decide +kernel
theorem block013_data_flat149_original : block013_data_flat149 = (CoefficientMerge.scale (208165732793568 : Int) atom0926Coded) := by
  rw [block013_data_flat149_step]
def block013_data_flat150 : CoefficientMerge.Poly := [(nat_lit 1403, Int.ofNat (nat_lit 407982508176672))]
theorem block013_data_flat150_step : block013_data_flat150 = (CoefficientMerge.scale (407982508176672 : Int) atom0927Coded) := by decide +kernel
theorem block013_data_flat150_original : block013_data_flat150 = (CoefficientMerge.scale (407982508176672 : Int) atom0927Coded) := by
  rw [block013_data_flat150_step]
def block013_data_flat151 : CoefficientMerge.Poly := [(nat_lit 1404, Int.ofNat (nat_lit 422721834144192))]
theorem block013_data_flat151_step : block013_data_flat151 = (CoefficientMerge.scale (422721834144192 : Int) atom0928Coded) := by decide +kernel
theorem block013_data_flat151_original : block013_data_flat151 = (CoefficientMerge.scale (422721834144192 : Int) atom0928Coded) := by
  rw [block013_data_flat151_step]
def block013_data_flat152 : CoefficientMerge.Poly := [(nat_lit 1403, Int.ofNat (nat_lit 407982508176672)), (nat_lit 1404, Int.ofNat (nat_lit 422721834144192))]
theorem block013_data_flat152_step : block013_data_flat152 = (CoefficientMerge.fastMerge block013_data_flat150 block013_data_flat151) := by decide +kernel
theorem block013_data_flat152_original : block013_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (407982508176672 : Int) atom0927Coded) (CoefficientMerge.scale (422721834144192 : Int) atom0928Coded)) := by
  rw [block013_data_flat152_step, block013_data_flat150_original, block013_data_flat151_original]
def block013_data_flat153 : CoefficientMerge.Poly := [(nat_lit 1402, Int.ofNat (nat_lit 208165732793568)), (nat_lit 1403, Int.ofNat (nat_lit 407982508176672)), (nat_lit 1404, Int.ofNat (nat_lit 422721834144192))]
theorem block013_data_flat153_step : block013_data_flat153 = (CoefficientMerge.fastMerge block013_data_flat149 block013_data_flat152) := by decide +kernel
theorem block013_data_flat153_original : block013_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (208165732793568 : Int) atom0926Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (407982508176672 : Int) atom0927Coded) (CoefficientMerge.scale (422721834144192 : Int) atom0928Coded))) := by
  rw [block013_data_flat153_step, block013_data_flat149_original, block013_data_flat152_original]
def block013_data_flat154 : CoefficientMerge.Poly := [(nat_lit 1390, Int.ofNat (nat_lit 436965972664320)), (nat_lit 1391, Int.ofNat (nat_lit 524503690419456)), (nat_lit 1402, Int.ofNat (nat_lit 208165732793568)), (nat_lit 1403, Int.ofNat (nat_lit 407982508176672)), (nat_lit 1404, Int.ofNat (nat_lit 422721834144192))]
theorem block013_data_flat154_step : block013_data_flat154 = (CoefficientMerge.fastMerge block013_data_flat148 block013_data_flat153) := by decide +kernel
theorem block013_data_flat154_original : block013_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (436965972664320 : Int) atom0924Coded) (CoefficientMerge.scale (524503690419456 : Int) atom0925Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (208165732793568 : Int) atom0926Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (407982508176672 : Int) atom0927Coded) (CoefficientMerge.scale (422721834144192 : Int) atom0928Coded)))) := by
  rw [block013_data_flat154_step, block013_data_flat148_original, block013_data_flat153_original]
def block013_data_flat155 : CoefficientMerge.Poly := [(nat_lit 1385, Int.ofNat (nat_lit 300031748425728)), (nat_lit 1386, Int.ofNat (nat_lit 340464919398912)), (nat_lit 1387, Int.ofNat (nat_lit 296563798586880)), (nat_lit 1388, Int.ofNat (nat_lit 393504476226048)), (nat_lit 1389, Int.ofNat (nat_lit 382161640886784)), (nat_lit 1390, Int.ofNat (nat_lit 436965972664320)), (nat_lit 1391, Int.ofNat (nat_lit 524503690419456)), (nat_lit 1402, Int.ofNat (nat_lit 208165732793568)), (nat_lit 1403, Int.ofNat (nat_lit 407982508176672)), (nat_lit 1404, Int.ofNat (nat_lit 422721834144192))]
theorem block013_data_flat155_step : block013_data_flat155 = (CoefficientMerge.fastMerge block013_data_flat145 block013_data_flat154) := by decide +kernel
theorem block013_data_flat155_original : block013_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (300031748425728 : Int) atom0919Coded) (CoefficientMerge.scale (340464919398912 : Int) atom0920Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (296563798586880 : Int) atom0921Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (393504476226048 : Int) atom0922Coded) (CoefficientMerge.scale (382161640886784 : Int) atom0923Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (436965972664320 : Int) atom0924Coded) (CoefficientMerge.scale (524503690419456 : Int) atom0925Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (208165732793568 : Int) atom0926Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (407982508176672 : Int) atom0927Coded) (CoefficientMerge.scale (422721834144192 : Int) atom0928Coded))))) := by
  rw [block013_data_flat155_step, block013_data_flat145_original, block013_data_flat154_original]
def block013_data_flat156 : CoefficientMerge.Poly := [(nat_lit 1366, Int.ofNat (nat_lit 402453738086400)), (nat_lit 1367, Int.ofNat (nat_lit 484218100396800)), (nat_lit 1377, Int.ofNat (nat_lit 183207987772128)), (nat_lit 1378, Int.ofNat (nat_lit 350273600335296)), (nat_lit 1379, Int.ofNat (nat_lit 338777815302432)), (nat_lit 1380, Int.ofNat (nat_lit 360661290466752)), (nat_lit 1381, Int.ofNat (nat_lit 342878612300928)), (nat_lit 1382, Int.ofNat (nat_lit 324504711894528)), (nat_lit 1383, Int.ofNat (nat_lit 320917818083328)), (nat_lit 1384, Int.ofNat (nat_lit 305508414025728)), (nat_lit 1385, Int.ofNat (nat_lit 300031748425728)), (nat_lit 1386, Int.ofNat (nat_lit 340464919398912)), (nat_lit 1387, Int.ofNat (nat_lit 296563798586880)), (nat_lit 1388, Int.ofNat (nat_lit 393504476226048)), (nat_lit 1389, Int.ofNat (nat_lit 382161640886784)), (nat_lit 1390, Int.ofNat (nat_lit 436965972664320)), (nat_lit 1391, Int.ofNat (nat_lit 524503690419456)), (nat_lit 1402, Int.ofNat (nat_lit 208165732793568)), (nat_lit 1403, Int.ofNat (nat_lit 407982508176672)), (nat_lit 1404, Int.ofNat (nat_lit 422721834144192))]
theorem block013_data_flat156_step : block013_data_flat156 = (CoefficientMerge.fastMerge block013_data_flat136 block013_data_flat155) := by decide +kernel
theorem block013_data_flat156_original : block013_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (402453738086400 : Int) atom0909Coded) (CoefficientMerge.scale (484218100396800 : Int) atom0910Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (183207987772128 : Int) atom0911Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (350273600335296 : Int) atom0912Coded) (CoefficientMerge.scale (338777815302432 : Int) atom0913Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (360661290466752 : Int) atom0914Coded) (CoefficientMerge.scale (342878612300928 : Int) atom0915Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (324504711894528 : Int) atom0916Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (320917818083328 : Int) atom0917Coded) (CoefficientMerge.scale (305508414025728 : Int) atom0918Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (300031748425728 : Int) atom0919Coded) (CoefficientMerge.scale (340464919398912 : Int) atom0920Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (296563798586880 : Int) atom0921Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (393504476226048 : Int) atom0922Coded) (CoefficientMerge.scale (382161640886784 : Int) atom0923Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (436965972664320 : Int) atom0924Coded) (CoefficientMerge.scale (524503690419456 : Int) atom0925Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (208165732793568 : Int) atom0926Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (407982508176672 : Int) atom0927Coded) (CoefficientMerge.scale (422721834144192 : Int) atom0928Coded)))))) := by
  rw [block013_data_flat156_step, block013_data_flat136_original, block013_data_flat155_original]
def block013_data_flat157 : CoefficientMerge.Poly := [(nat_lit 1338, Int.ofNat (nat_lit 303735015091200)), (nat_lit 1339, Int.ofNat (nat_lit 253579496755200)), (nat_lit 1340, Int.ofNat (nat_lit 344265776870400)), (nat_lit 1341, Int.ofNat (nat_lit 315353707468800)), (nat_lit 1342, Int.ofNat (nat_lit 352588805184000)), (nat_lit 1343, Int.ofNat (nat_lit 422557288876800)), (nat_lit 1352, Int.ofNat (nat_lit 156809822400000)), (nat_lit 1353, Int.ofNat (nat_lit 298917689941728)), (nat_lit 1354, Int.ofNat (nat_lit 285877758467664)), (nat_lit 1355, Int.ofNat (nat_lit 299464987862304)), (nat_lit 1356, Int.ofNat (nat_lit 321305938329024)), (nat_lit 1357, Int.ofNat (nat_lit 309646816617600)), (nat_lit 1358, Int.ofNat (nat_lit 294313432089600)), (nat_lit 1359, Int.ofNat (nat_lit 293767054156800)), (nat_lit 1360, Int.ofNat (nat_lit 281398165977600)), (nat_lit 1361, Int.ofNat (nat_lit 278962016256000)), (nat_lit 1362, Int.ofNat (nat_lit 320232235276800)), (nat_lit 1363, Int.ofNat (nat_lit 274964694681600)), (nat_lit 1364, Int.ofNat (nat_lit 370538952537600)), (nat_lit 1365, Int.ofNat (nat_lit 353422761753600)), (nat_lit 1366, Int.ofNat (nat_lit 402453738086400)), (nat_lit 1367, Int.ofNat (nat_lit 484218100396800)), (nat_lit 1377, Int.ofNat (nat_lit 183207987772128)), (nat_lit 1378, Int.ofNat (nat_lit 350273600335296)), (nat_lit 1379, Int.ofNat (nat_lit 338777815302432)), (nat_lit 1380, Int.ofNat (nat_lit 360661290466752)), (nat_lit 1381, Int.ofNat (nat_lit 342878612300928)), (nat_lit 1382, Int.ofNat (nat_lit 324504711894528)), (nat_lit 1383, Int.ofNat (nat_lit 320917818083328)), (nat_lit 1384, Int.ofNat (nat_lit 305508414025728)), (nat_lit 1385, Int.ofNat (nat_lit 300031748425728)), (nat_lit 1386, Int.ofNat (nat_lit 340464919398912)), (nat_lit 1387, Int.ofNat (nat_lit 296563798586880)), (nat_lit 1388, Int.ofNat (nat_lit 393504476226048)), (nat_lit 1389, Int.ofNat (nat_lit 382161640886784)), (nat_lit 1390, Int.ofNat (nat_lit 436965972664320)), (nat_lit 1391, Int.ofNat (nat_lit 524503690419456)), (nat_lit 1402, Int.ofNat (nat_lit 208165732793568)), (nat_lit 1403, Int.ofNat (nat_lit 407982508176672)), (nat_lit 1404, Int.ofNat (nat_lit 422721834144192))]
theorem block013_data_flat157_step : block013_data_flat157 = (CoefficientMerge.fastMerge block013_data_flat117 block013_data_flat156) := by decide +kernel
theorem block013_data_flat157_original : block013_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (303735015091200 : Int) atom0889Coded) (CoefficientMerge.scale (253579496755200 : Int) atom0890Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (344265776870400 : Int) atom0891Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (315353707468800 : Int) atom0892Coded) (CoefficientMerge.scale (352588805184000 : Int) atom0893Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (422557288876800 : Int) atom0894Coded) (CoefficientMerge.scale (156809822400000 : Int) atom0895Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (298917689941728 : Int) atom0896Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (285877758467664 : Int) atom0897Coded) (CoefficientMerge.scale (299464987862304 : Int) atom0898Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (321305938329024 : Int) atom0899Coded) (CoefficientMerge.scale (309646816617600 : Int) atom0900Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (294313432089600 : Int) atom0901Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (293767054156800 : Int) atom0902Coded) (CoefficientMerge.scale (281398165977600 : Int) atom0903Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (278962016256000 : Int) atom0904Coded) (CoefficientMerge.scale (320232235276800 : Int) atom0905Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (274964694681600 : Int) atom0906Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (370538952537600 : Int) atom0907Coded) (CoefficientMerge.scale (353422761753600 : Int) atom0908Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (402453738086400 : Int) atom0909Coded) (CoefficientMerge.scale (484218100396800 : Int) atom0910Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (183207987772128 : Int) atom0911Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (350273600335296 : Int) atom0912Coded) (CoefficientMerge.scale (338777815302432 : Int) atom0913Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (360661290466752 : Int) atom0914Coded) (CoefficientMerge.scale (342878612300928 : Int) atom0915Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (324504711894528 : Int) atom0916Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (320917818083328 : Int) atom0917Coded) (CoefficientMerge.scale (305508414025728 : Int) atom0918Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (300031748425728 : Int) atom0919Coded) (CoefficientMerge.scale (340464919398912 : Int) atom0920Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (296563798586880 : Int) atom0921Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (393504476226048 : Int) atom0922Coded) (CoefficientMerge.scale (382161640886784 : Int) atom0923Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (436965972664320 : Int) atom0924Coded) (CoefficientMerge.scale (524503690419456 : Int) atom0925Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (208165732793568 : Int) atom0926Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (407982508176672 : Int) atom0927Coded) (CoefficientMerge.scale (422721834144192 : Int) atom0928Coded))))))) := by
  rw [block013_data_flat157_step, block013_data_flat117_original, block013_data_flat156_original]
def block013_data_flat158 : CoefficientMerge.Poly := [(nat_lit 1285, Int.ofNat (nat_lit 250762389292800)), (nat_lit 1286, Int.ofNat (nat_lit 222902250278400)), (nat_lit 1287, Int.ofNat (nat_lit 225353863526400)), (nat_lit 1288, Int.ofNat (nat_lit 215982966528000)), (nat_lit 1289, Int.ofNat (nat_lit 216544807987200)), (nat_lit 1290, Int.ofNat (nat_lit 257815027008000)), (nat_lit 1291, Int.ofNat (nat_lit 189421289164800)), (nat_lit 1292, Int.ofNat (nat_lit 268578751795200)), (nat_lit 1293, Int.ofNat (nat_lit 215630979379200)), (nat_lit 1294, Int.ofNat (nat_lit 228830374080000)), (nat_lit 1295, Int.ofNat (nat_lit 274763154758400)), (nat_lit 1302, Int.ofNat (nat_lit 126234564825600)), (nat_lit 1303, Int.ofNat (nat_lit 224731214400000)), (nat_lit 1304, Int.ofNat (nat_lit 202842807552000)), (nat_lit 1305, Int.ofNat (nat_lit 206600779625328)), (nat_lit 1306, Int.ofNat (nat_lit 226908137622672)), (nat_lit 1307, Int.ofNat (nat_lit 237208830575904)), (nat_lit 1308, Int.ofNat (nat_lit 263089627314624)), (nat_lit 1309, Int.ofNat (nat_lit 254449759132800)), (nat_lit 1310, Int.ofNat (nat_lit 242135628134400)), (nat_lit 1311, Int.ofNat (nat_lit 244608503731200)), (nat_lit 1312, Int.ofNat (nat_lit 235258869081600)), (nat_lit 1313, Int.ofNat (nat_lit 235841972889600)), (nat_lit 1314, Int.ofNat (nat_lit 274348086566400)), (nat_lit 1315, Int.ofNat (nat_lit 220533081753600)), (nat_lit 1316, Int.ofNat (nat_lit 307559875392000)), (nat_lit 1317, Int.ofNat (nat_lit 270329502643200)), (nat_lit 1318, Int.ofNat (nat_lit 299246297011200)), (nat_lit 1319, Int.ofNat (nat_lit 360896477356800)), (nat_lit 1327, Int.ofNat (nat_lit 135493136486400)), (nat_lit 1328, Int.ofNat (nat_lit 254285879232000)), (nat_lit 1329, Int.ofNat (nat_lit 240589825423728)), (nat_lit 1330, Int.ofNat (nat_lit 257835405193872)), (nat_lit 1331, Int.ofNat (nat_lit 269199215587104)), (nat_lit 1332, Int.ofNat (nat_lit 296143129765824)), (nat_lit 1333, Int.ofNat (nat_lit 286503931190400)), (nat_lit 1334, Int.ofNat (nat_lit 273190469798400)), (nat_lit 1335, Int.ofNat (nat_lit 274664015001600)), (nat_lit 1336, Int.ofNat (nat_lit 264315049958400)), (nat_lit 1337, Int.ofNat (nat_lit 263898823372800)), (nat_lit 1338, Int.ofNat (nat_lit 303735015091200)), (nat_lit 1339, Int.ofNat (nat_lit 253579496755200)), (nat_lit 1340, Int.ofNat (nat_lit 344265776870400)), (nat_lit 1341, Int.ofNat (nat_lit 315353707468800)), (nat_lit 1342, Int.ofNat (nat_lit 352588805184000)), (nat_lit 1343, Int.ofNat (nat_lit 422557288876800)), (nat_lit 1352, Int.ofNat (nat_lit 156809822400000)), (nat_lit 1353, Int.ofNat (nat_lit 298917689941728)), (nat_lit 1354, Int.ofNat (nat_lit 285877758467664)), (nat_lit 1355, Int.ofNat (nat_lit 299464987862304)), (nat_lit 1356, Int.ofNat (nat_lit 321305938329024)), (nat_lit 1357, Int.ofNat (nat_lit 309646816617600)), (nat_lit 1358, Int.ofNat (nat_lit 294313432089600)), (nat_lit 1359, Int.ofNat (nat_lit 293767054156800)), (nat_lit 1360, Int.ofNat (nat_lit 281398165977600)), (nat_lit 1361, Int.ofNat (nat_lit 278962016256000)), (nat_lit 1362, Int.ofNat (nat_lit 320232235276800)), (nat_lit 1363, Int.ofNat (nat_lit 274964694681600)), (nat_lit 1364, Int.ofNat (nat_lit 370538952537600)), (nat_lit 1365, Int.ofNat (nat_lit 353422761753600)), (nat_lit 1366, Int.ofNat (nat_lit 402453738086400)), (nat_lit 1367, Int.ofNat (nat_lit 484218100396800)), (nat_lit 1377, Int.ofNat (nat_lit 183207987772128)), (nat_lit 1378, Int.ofNat (nat_lit 350273600335296)), (nat_lit 1379, Int.ofNat (nat_lit 338777815302432)), (nat_lit 1380, Int.ofNat (nat_lit 360661290466752)), (nat_lit 1381, Int.ofNat (nat_lit 342878612300928)), (nat_lit 1382, Int.ofNat (nat_lit 324504711894528)), (nat_lit 1383, Int.ofNat (nat_lit 320917818083328)), (nat_lit 1384, Int.ofNat (nat_lit 305508414025728)), (nat_lit 1385, Int.ofNat (nat_lit 300031748425728)), (nat_lit 1386, Int.ofNat (nat_lit 340464919398912)), (nat_lit 1387, Int.ofNat (nat_lit 296563798586880)), (nat_lit 1388, Int.ofNat (nat_lit 393504476226048)), (nat_lit 1389, Int.ofNat (nat_lit 382161640886784)), (nat_lit 1390, Int.ofNat (nat_lit 436965972664320)), (nat_lit 1391, Int.ofNat (nat_lit 524503690419456)), (nat_lit 1402, Int.ofNat (nat_lit 208165732793568)), (nat_lit 1403, Int.ofNat (nat_lit 407982508176672)), (nat_lit 1404, Int.ofNat (nat_lit 422721834144192))]
theorem block013_data_flat158_step : block013_data_flat158 = (CoefficientMerge.fastMerge block013_data_flat078 block013_data_flat157) := by decide +kernel
theorem block013_data_flat158_original : block013_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (250762389292800 : Int) atom0849Coded) (CoefficientMerge.scale (222902250278400 : Int) atom0850Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (225353863526400 : Int) atom0851Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (215982966528000 : Int) atom0852Coded) (CoefficientMerge.scale (216544807987200 : Int) atom0853Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (257815027008000 : Int) atom0854Coded) (CoefficientMerge.scale (189421289164800 : Int) atom0855Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (268578751795200 : Int) atom0856Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (215630979379200 : Int) atom0857Coded) (CoefficientMerge.scale (228830374080000 : Int) atom0858Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (274763154758400 : Int) atom0859Coded) (CoefficientMerge.scale (126234564825600 : Int) atom0860Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (224731214400000 : Int) atom0861Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (202842807552000 : Int) atom0862Coded) (CoefficientMerge.scale (206600779625328 : Int) atom0863Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (226908137622672 : Int) atom0864Coded) (CoefficientMerge.scale (237208830575904 : Int) atom0865Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (263089627314624 : Int) atom0866Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (254449759132800 : Int) atom0867Coded) (CoefficientMerge.scale (242135628134400 : Int) atom0868Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (244608503731200 : Int) atom0869Coded) (CoefficientMerge.scale (235258869081600 : Int) atom0870Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (235841972889600 : Int) atom0871Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (274348086566400 : Int) atom0872Coded) (CoefficientMerge.scale (220533081753600 : Int) atom0873Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (307559875392000 : Int) atom0874Coded) (CoefficientMerge.scale (270329502643200 : Int) atom0875Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (299246297011200 : Int) atom0876Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (360896477356800 : Int) atom0877Coded) (CoefficientMerge.scale (135493136486400 : Int) atom0878Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (254285879232000 : Int) atom0879Coded) (CoefficientMerge.scale (240589825423728 : Int) atom0880Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (257835405193872 : Int) atom0881Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (269199215587104 : Int) atom0882Coded) (CoefficientMerge.scale (296143129765824 : Int) atom0883Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (286503931190400 : Int) atom0884Coded) (CoefficientMerge.scale (273190469798400 : Int) atom0885Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (274664015001600 : Int) atom0886Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (264315049958400 : Int) atom0887Coded) (CoefficientMerge.scale (263898823372800 : Int) atom0888Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (303735015091200 : Int) atom0889Coded) (CoefficientMerge.scale (253579496755200 : Int) atom0890Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (344265776870400 : Int) atom0891Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (315353707468800 : Int) atom0892Coded) (CoefficientMerge.scale (352588805184000 : Int) atom0893Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (422557288876800 : Int) atom0894Coded) (CoefficientMerge.scale (156809822400000 : Int) atom0895Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (298917689941728 : Int) atom0896Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (285877758467664 : Int) atom0897Coded) (CoefficientMerge.scale (299464987862304 : Int) atom0898Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (321305938329024 : Int) atom0899Coded) (CoefficientMerge.scale (309646816617600 : Int) atom0900Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (294313432089600 : Int) atom0901Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (293767054156800 : Int) atom0902Coded) (CoefficientMerge.scale (281398165977600 : Int) atom0903Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (278962016256000 : Int) atom0904Coded) (CoefficientMerge.scale (320232235276800 : Int) atom0905Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (274964694681600 : Int) atom0906Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (370538952537600 : Int) atom0907Coded) (CoefficientMerge.scale (353422761753600 : Int) atom0908Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (402453738086400 : Int) atom0909Coded) (CoefficientMerge.scale (484218100396800 : Int) atom0910Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (183207987772128 : Int) atom0911Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (350273600335296 : Int) atom0912Coded) (CoefficientMerge.scale (338777815302432 : Int) atom0913Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (360661290466752 : Int) atom0914Coded) (CoefficientMerge.scale (342878612300928 : Int) atom0915Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (324504711894528 : Int) atom0916Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (320917818083328 : Int) atom0917Coded) (CoefficientMerge.scale (305508414025728 : Int) atom0918Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (300031748425728 : Int) atom0919Coded) (CoefficientMerge.scale (340464919398912 : Int) atom0920Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (296563798586880 : Int) atom0921Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (393504476226048 : Int) atom0922Coded) (CoefficientMerge.scale (382161640886784 : Int) atom0923Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (436965972664320 : Int) atom0924Coded) (CoefficientMerge.scale (524503690419456 : Int) atom0925Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (208165732793568 : Int) atom0926Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (407982508176672 : Int) atom0927Coded) (CoefficientMerge.scale (422721834144192 : Int) atom0928Coded)))))))) := by
  rw [block013_data_flat158_step, block013_data_flat078_original, block013_data_flat157_original]
def block013_data_flat159 : CoefficientMerge.Poly := [(nat_lit 1285, Int.ofNat (nat_lit 250762389292800)), (nat_lit 1286, Int.ofNat (nat_lit 222902250278400)), (nat_lit 1287, Int.ofNat (nat_lit 225353863526400)), (nat_lit 1288, Int.ofNat (nat_lit 215982966528000)), (nat_lit 1289, Int.ofNat (nat_lit 216544807987200)), (nat_lit 1290, Int.ofNat (nat_lit 257815027008000)), (nat_lit 1291, Int.ofNat (nat_lit 189421289164800)), (nat_lit 1292, Int.ofNat (nat_lit 268578751795200)), (nat_lit 1293, Int.ofNat (nat_lit 215630979379200)), (nat_lit 1294, Int.ofNat (nat_lit 228830374080000)), (nat_lit 1295, Int.ofNat (nat_lit 274763154758400)), (nat_lit 1302, Int.ofNat (nat_lit 126234564825600)), (nat_lit 1303, Int.ofNat (nat_lit 224731214400000)), (nat_lit 1304, Int.ofNat (nat_lit 202842807552000)), (nat_lit 1305, Int.ofNat (nat_lit 206600779625328)), (nat_lit 1306, Int.ofNat (nat_lit 226908137622672)), (nat_lit 1307, Int.ofNat (nat_lit 237208830575904)), (nat_lit 1308, Int.ofNat (nat_lit 263089627314624)), (nat_lit 1309, Int.ofNat (nat_lit 254449759132800)), (nat_lit 1310, Int.ofNat (nat_lit 242135628134400)), (nat_lit 1311, Int.ofNat (nat_lit 244608503731200)), (nat_lit 1312, Int.ofNat (nat_lit 235258869081600)), (nat_lit 1313, Int.ofNat (nat_lit 235841972889600)), (nat_lit 1314, Int.ofNat (nat_lit 274348086566400)), (nat_lit 1315, Int.ofNat (nat_lit 220533081753600)), (nat_lit 1316, Int.ofNat (nat_lit 307559875392000)), (nat_lit 1317, Int.ofNat (nat_lit 270329502643200)), (nat_lit 1318, Int.ofNat (nat_lit 299246297011200)), (nat_lit 1319, Int.ofNat (nat_lit 360896477356800)), (nat_lit 1327, Int.ofNat (nat_lit 135493136486400)), (nat_lit 1328, Int.ofNat (nat_lit 254285879232000)), (nat_lit 1329, Int.ofNat (nat_lit 240589825423728)), (nat_lit 1330, Int.ofNat (nat_lit 257835405193872)), (nat_lit 1331, Int.ofNat (nat_lit 269199215587104)), (nat_lit 1332, Int.ofNat (nat_lit 296143129765824)), (nat_lit 1333, Int.ofNat (nat_lit 286503931190400)), (nat_lit 1334, Int.ofNat (nat_lit 273190469798400)), (nat_lit 1335, Int.ofNat (nat_lit 274664015001600)), (nat_lit 1336, Int.ofNat (nat_lit 264315049958400)), (nat_lit 1337, Int.ofNat (nat_lit 263898823372800)), (nat_lit 1338, Int.ofNat (nat_lit 303735015091200)), (nat_lit 1339, Int.ofNat (nat_lit 253579496755200)), (nat_lit 1340, Int.ofNat (nat_lit 344265776870400)), (nat_lit 1341, Int.ofNat (nat_lit 315353707468800)), (nat_lit 1342, Int.ofNat (nat_lit 352588805184000)), (nat_lit 1343, Int.ofNat (nat_lit 422557288876800)), (nat_lit 1352, Int.ofNat (nat_lit 156809822400000)), (nat_lit 1353, Int.ofNat (nat_lit 298917689941728)), (nat_lit 1354, Int.ofNat (nat_lit 285877758467664)), (nat_lit 1355, Int.ofNat (nat_lit 299464987862304)), (nat_lit 1356, Int.ofNat (nat_lit 321305938329024)), (nat_lit 1357, Int.ofNat (nat_lit 309646816617600)), (nat_lit 1358, Int.ofNat (nat_lit 294313432089600)), (nat_lit 1359, Int.ofNat (nat_lit 293767054156800)), (nat_lit 1360, Int.ofNat (nat_lit 281398165977600)), (nat_lit 1361, Int.ofNat (nat_lit 278962016256000)), (nat_lit 1362, Int.ofNat (nat_lit 320232235276800)), (nat_lit 1363, Int.ofNat (nat_lit 274964694681600)), (nat_lit 1364, Int.ofNat (nat_lit 370538952537600)), (nat_lit 1365, Int.ofNat (nat_lit 353422761753600)), (nat_lit 1366, Int.ofNat (nat_lit 402453738086400)), (nat_lit 1367, Int.ofNat (nat_lit 484218100396800)), (nat_lit 1377, Int.ofNat (nat_lit 183207987772128)), (nat_lit 1378, Int.ofNat (nat_lit 350273600335296)), (nat_lit 1379, Int.ofNat (nat_lit 338777815302432)), (nat_lit 1380, Int.ofNat (nat_lit 360661290466752)), (nat_lit 1381, Int.ofNat (nat_lit 342878612300928)), (nat_lit 1382, Int.ofNat (nat_lit 324504711894528)), (nat_lit 1383, Int.ofNat (nat_lit 320917818083328)), (nat_lit 1384, Int.ofNat (nat_lit 305508414025728)), (nat_lit 1385, Int.ofNat (nat_lit 300031748425728)), (nat_lit 1386, Int.ofNat (nat_lit 340464919398912)), (nat_lit 1387, Int.ofNat (nat_lit 296563798586880)), (nat_lit 1388, Int.ofNat (nat_lit 393504476226048)), (nat_lit 1389, Int.ofNat (nat_lit 382161640886784)), (nat_lit 1390, Int.ofNat (nat_lit 436965972664320)), (nat_lit 1391, Int.ofNat (nat_lit 524503690419456)), (nat_lit 1402, Int.ofNat (nat_lit 208165732793568)), (nat_lit 1403, Int.ofNat (nat_lit 407982508176672)), (nat_lit 1404, Int.ofNat (nat_lit 422721834144192))]
theorem block013_data_flat159_step : block013_data_flat159 = (CoefficientMerge.trim block013_data_flat158) := by decide +kernel
theorem block013_data_flat159_original : block013_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (250762389292800 : Int) atom0849Coded) (CoefficientMerge.scale (222902250278400 : Int) atom0850Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (225353863526400 : Int) atom0851Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (215982966528000 : Int) atom0852Coded) (CoefficientMerge.scale (216544807987200 : Int) atom0853Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (257815027008000 : Int) atom0854Coded) (CoefficientMerge.scale (189421289164800 : Int) atom0855Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (268578751795200 : Int) atom0856Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (215630979379200 : Int) atom0857Coded) (CoefficientMerge.scale (228830374080000 : Int) atom0858Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (274763154758400 : Int) atom0859Coded) (CoefficientMerge.scale (126234564825600 : Int) atom0860Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (224731214400000 : Int) atom0861Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (202842807552000 : Int) atom0862Coded) (CoefficientMerge.scale (206600779625328 : Int) atom0863Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (226908137622672 : Int) atom0864Coded) (CoefficientMerge.scale (237208830575904 : Int) atom0865Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (263089627314624 : Int) atom0866Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (254449759132800 : Int) atom0867Coded) (CoefficientMerge.scale (242135628134400 : Int) atom0868Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (244608503731200 : Int) atom0869Coded) (CoefficientMerge.scale (235258869081600 : Int) atom0870Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (235841972889600 : Int) atom0871Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (274348086566400 : Int) atom0872Coded) (CoefficientMerge.scale (220533081753600 : Int) atom0873Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (307559875392000 : Int) atom0874Coded) (CoefficientMerge.scale (270329502643200 : Int) atom0875Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (299246297011200 : Int) atom0876Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (360896477356800 : Int) atom0877Coded) (CoefficientMerge.scale (135493136486400 : Int) atom0878Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (254285879232000 : Int) atom0879Coded) (CoefficientMerge.scale (240589825423728 : Int) atom0880Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (257835405193872 : Int) atom0881Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (269199215587104 : Int) atom0882Coded) (CoefficientMerge.scale (296143129765824 : Int) atom0883Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (286503931190400 : Int) atom0884Coded) (CoefficientMerge.scale (273190469798400 : Int) atom0885Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (274664015001600 : Int) atom0886Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (264315049958400 : Int) atom0887Coded) (CoefficientMerge.scale (263898823372800 : Int) atom0888Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (303735015091200 : Int) atom0889Coded) (CoefficientMerge.scale (253579496755200 : Int) atom0890Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (344265776870400 : Int) atom0891Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (315353707468800 : Int) atom0892Coded) (CoefficientMerge.scale (352588805184000 : Int) atom0893Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (422557288876800 : Int) atom0894Coded) (CoefficientMerge.scale (156809822400000 : Int) atom0895Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (298917689941728 : Int) atom0896Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (285877758467664 : Int) atom0897Coded) (CoefficientMerge.scale (299464987862304 : Int) atom0898Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (321305938329024 : Int) atom0899Coded) (CoefficientMerge.scale (309646816617600 : Int) atom0900Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (294313432089600 : Int) atom0901Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (293767054156800 : Int) atom0902Coded) (CoefficientMerge.scale (281398165977600 : Int) atom0903Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (278962016256000 : Int) atom0904Coded) (CoefficientMerge.scale (320232235276800 : Int) atom0905Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (274964694681600 : Int) atom0906Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (370538952537600 : Int) atom0907Coded) (CoefficientMerge.scale (353422761753600 : Int) atom0908Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (402453738086400 : Int) atom0909Coded) (CoefficientMerge.scale (484218100396800 : Int) atom0910Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (183207987772128 : Int) atom0911Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (350273600335296 : Int) atom0912Coded) (CoefficientMerge.scale (338777815302432 : Int) atom0913Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (360661290466752 : Int) atom0914Coded) (CoefficientMerge.scale (342878612300928 : Int) atom0915Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (324504711894528 : Int) atom0916Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (320917818083328 : Int) atom0917Coded) (CoefficientMerge.scale (305508414025728 : Int) atom0918Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (300031748425728 : Int) atom0919Coded) (CoefficientMerge.scale (340464919398912 : Int) atom0920Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (296563798586880 : Int) atom0921Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (393504476226048 : Int) atom0922Coded) (CoefficientMerge.scale (382161640886784 : Int) atom0923Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (436965972664320 : Int) atom0924Coded) (CoefficientMerge.scale (524503690419456 : Int) atom0925Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (208165732793568 : Int) atom0926Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (407982508176672 : Int) atom0927Coded) (CoefficientMerge.scale (422721834144192 : Int) atom0928Coded))))))))) := by
  rw [block013_data_flat159_step, block013_data_flat158_original]
theorem block013_data : block013 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (250762389292800 : Int) atom0849Coded) (CoefficientMerge.scale (222902250278400 : Int) atom0850Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (225353863526400 : Int) atom0851Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (215982966528000 : Int) atom0852Coded) (CoefficientMerge.scale (216544807987200 : Int) atom0853Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (257815027008000 : Int) atom0854Coded) (CoefficientMerge.scale (189421289164800 : Int) atom0855Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (268578751795200 : Int) atom0856Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (215630979379200 : Int) atom0857Coded) (CoefficientMerge.scale (228830374080000 : Int) atom0858Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (274763154758400 : Int) atom0859Coded) (CoefficientMerge.scale (126234564825600 : Int) atom0860Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (224731214400000 : Int) atom0861Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (202842807552000 : Int) atom0862Coded) (CoefficientMerge.scale (206600779625328 : Int) atom0863Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (226908137622672 : Int) atom0864Coded) (CoefficientMerge.scale (237208830575904 : Int) atom0865Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (263089627314624 : Int) atom0866Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (254449759132800 : Int) atom0867Coded) (CoefficientMerge.scale (242135628134400 : Int) atom0868Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (244608503731200 : Int) atom0869Coded) (CoefficientMerge.scale (235258869081600 : Int) atom0870Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (235841972889600 : Int) atom0871Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (274348086566400 : Int) atom0872Coded) (CoefficientMerge.scale (220533081753600 : Int) atom0873Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (307559875392000 : Int) atom0874Coded) (CoefficientMerge.scale (270329502643200 : Int) atom0875Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (299246297011200 : Int) atom0876Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (360896477356800 : Int) atom0877Coded) (CoefficientMerge.scale (135493136486400 : Int) atom0878Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (254285879232000 : Int) atom0879Coded) (CoefficientMerge.scale (240589825423728 : Int) atom0880Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (257835405193872 : Int) atom0881Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (269199215587104 : Int) atom0882Coded) (CoefficientMerge.scale (296143129765824 : Int) atom0883Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (286503931190400 : Int) atom0884Coded) (CoefficientMerge.scale (273190469798400 : Int) atom0885Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (274664015001600 : Int) atom0886Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (264315049958400 : Int) atom0887Coded) (CoefficientMerge.scale (263898823372800 : Int) atom0888Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (303735015091200 : Int) atom0889Coded) (CoefficientMerge.scale (253579496755200 : Int) atom0890Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (344265776870400 : Int) atom0891Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (315353707468800 : Int) atom0892Coded) (CoefficientMerge.scale (352588805184000 : Int) atom0893Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (422557288876800 : Int) atom0894Coded) (CoefficientMerge.scale (156809822400000 : Int) atom0895Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (298917689941728 : Int) atom0896Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (285877758467664 : Int) atom0897Coded) (CoefficientMerge.scale (299464987862304 : Int) atom0898Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (321305938329024 : Int) atom0899Coded) (CoefficientMerge.scale (309646816617600 : Int) atom0900Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (294313432089600 : Int) atom0901Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (293767054156800 : Int) atom0902Coded) (CoefficientMerge.scale (281398165977600 : Int) atom0903Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (278962016256000 : Int) atom0904Coded) (CoefficientMerge.scale (320232235276800 : Int) atom0905Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (274964694681600 : Int) atom0906Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (370538952537600 : Int) atom0907Coded) (CoefficientMerge.scale (353422761753600 : Int) atom0908Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (402453738086400 : Int) atom0909Coded) (CoefficientMerge.scale (484218100396800 : Int) atom0910Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (183207987772128 : Int) atom0911Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (350273600335296 : Int) atom0912Coded) (CoefficientMerge.scale (338777815302432 : Int) atom0913Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (360661290466752 : Int) atom0914Coded) (CoefficientMerge.scale (342878612300928 : Int) atom0915Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (324504711894528 : Int) atom0916Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (320917818083328 : Int) atom0917Coded) (CoefficientMerge.scale (305508414025728 : Int) atom0918Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (300031748425728 : Int) atom0919Coded) (CoefficientMerge.scale (340464919398912 : Int) atom0920Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (296563798586880 : Int) atom0921Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (393504476226048 : Int) atom0922Coded) (CoefficientMerge.scale (382161640886784 : Int) atom0923Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (436965972664320 : Int) atom0924Coded) (CoefficientMerge.scale (524503690419456 : Int) atom0925Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (208165732793568 : Int) atom0926Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (407982508176672 : Int) atom0927Coded) (CoefficientMerge.scale (422721834144192 : Int) atom0928Coded)))))))) := by
  have h : block013 = block013_data_flat159 := by decide +kernel
  exact h.trans block013_data_flat159_original
theorem block013_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block013 := by
  rw [block013_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0849Coded_nonneg g hg hA hB) (atom0850Coded_nonneg g hg hA hB)) (add_nonneg (atom0851Coded_nonneg g hg hA hB) (add_nonneg (atom0852Coded_nonneg g hg hA hB) (atom0853Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0854Coded_nonneg g hg hA hB) (atom0855Coded_nonneg g hg hA hB)) (add_nonneg (atom0856Coded_nonneg g hg hA hB) (add_nonneg (atom0857Coded_nonneg g hg hA hB) (atom0858Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0859Coded_nonneg g hg hA hB) (atom0860Coded_nonneg g hg hA hB)) (add_nonneg (atom0861Coded_nonneg g hg hA hB) (add_nonneg (atom0862Coded_nonneg g hg hA hB) (atom0863Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0864Coded_nonneg g hg hA hB) (atom0865Coded_nonneg g hg hA hB)) (add_nonneg (atom0866Coded_nonneg g hg hA hB) (add_nonneg (atom0867Coded_nonneg g hg hA hB) (atom0868Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0869Coded_nonneg g hg hA hB) (atom0870Coded_nonneg g hg hA hB)) (add_nonneg (atom0871Coded_nonneg g hg hA hB) (add_nonneg (atom0872Coded_nonneg g hg hA hB) (atom0873Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0874Coded_nonneg g hg hA hB) (atom0875Coded_nonneg g hg hA hB)) (add_nonneg (atom0876Coded_nonneg g hg hA hB) (add_nonneg (atom0877Coded_nonneg g hg hA hB) (atom0878Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0879Coded_nonneg g hg hA hB) (atom0880Coded_nonneg g hg hA hB)) (add_nonneg (atom0881Coded_nonneg g hg hA hB) (add_nonneg (atom0882Coded_nonneg g hg hA hB) (atom0883Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0884Coded_nonneg g hg hA hB) (atom0885Coded_nonneg g hg hA hB)) (add_nonneg (atom0886Coded_nonneg g hg hA hB) (add_nonneg (atom0887Coded_nonneg g hg hA hB) (atom0888Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0889Coded_nonneg g hg hA hB) (atom0890Coded_nonneg g hg hA hB)) (add_nonneg (atom0891Coded_nonneg g hg hA hB) (add_nonneg (atom0892Coded_nonneg g hg hA hB) (atom0893Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0894Coded_nonneg g hg hA hB) (atom0895Coded_nonneg g hg hA hB)) (add_nonneg (atom0896Coded_nonneg g hg hA hB) (add_nonneg (atom0897Coded_nonneg g hg hA hB) (atom0898Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0899Coded_nonneg g hg hA hB) (atom0900Coded_nonneg g hg hA hB)) (add_nonneg (atom0901Coded_nonneg g hg hA hB) (add_nonneg (atom0902Coded_nonneg g hg hA hB) (atom0903Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0904Coded_nonneg g hg hA hB) (atom0905Coded_nonneg g hg hA hB)) (add_nonneg (atom0906Coded_nonneg g hg hA hB) (add_nonneg (atom0907Coded_nonneg g hg hA hB) (atom0908Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0909Coded_nonneg g hg hA hB) (atom0910Coded_nonneg g hg hA hB)) (add_nonneg (atom0911Coded_nonneg g hg hA hB) (add_nonneg (atom0912Coded_nonneg g hg hA hB) (atom0913Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0914Coded_nonneg g hg hA hB) (atom0915Coded_nonneg g hg hA hB)) (add_nonneg (atom0916Coded_nonneg g hg hA hB) (add_nonneg (atom0917Coded_nonneg g hg hA hB) (atom0918Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0919Coded_nonneg g hg hA hB) (atom0920Coded_nonneg g hg hA hB)) (add_nonneg (atom0921Coded_nonneg g hg hA hB) (add_nonneg (atom0922Coded_nonneg g hg hA hB) (atom0923Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0924Coded_nonneg g hg hA hB) (atom0925Coded_nonneg g hg hA hB)) (add_nonneg (atom0926Coded_nonneg g hg hA hB) (add_nonneg (atom0927Coded_nonneg g hg hA hB) (atom0928Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
