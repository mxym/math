import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom1569 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 13, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1569 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1569 = ((g 5) * (g 13) * (g 16)) := by
  norm_num [atom1569, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1569_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (245154757478400 : Int) atom1569) := by
  rw [SparsePolynomial.eval_scale, eval_atom1569]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1569Coded : CoefficientMerge.Poly := [(nat_lit 3208, Int.ofNat (nat_lit 1))]
theorem atom1569Coded_decode : atom1569 = SparsePolynomial.decodeCubic 24 atom1569Coded := by decide +kernel
theorem atom1569Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (245154757478400 : Int) atom1569Coded) := by
  have h := atom1569_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1569Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1570 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 13, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1570 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1570 = ((g 5) * (g 13) * (g 17)) := by
  norm_num [atom1570, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1570_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (241242485299200 : Int) atom1570) := by
  rw [SparsePolynomial.eval_scale, eval_atom1570]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1570Coded : CoefficientMerge.Poly := [(nat_lit 3209, Int.ofNat (nat_lit 1))]
theorem atom1570Coded_decode : atom1570 = SparsePolynomial.decodeCubic 24 atom1570Coded := by decide +kernel
theorem atom1570Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (241242485299200 : Int) atom1570Coded) := by
  have h := atom1570_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1570Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1571 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 13, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1571 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1571 = ((g 5) * (g 13) * (g 18)) := by
  norm_num [atom1571, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1571_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (297199359072000 : Int) atom1571) := by
  rw [SparsePolynomial.eval_scale, eval_atom1571]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1571Coded : CoefficientMerge.Poly := [(nat_lit 3210, Int.ofNat (nat_lit 1))]
theorem atom1571Coded_decode : atom1571 = SparsePolynomial.decodeCubic 24 atom1571Coded := by decide +kernel
theorem atom1571Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (297199359072000 : Int) atom1571Coded) := by
  have h := atom1571_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1571Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1572 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 13, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1572 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1572 = ((g 5) * (g 13) * (g 19)) := by
  norm_num [atom1572, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1572_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (289024345209600 : Int) atom1572) := by
  rw [SparsePolynomial.eval_scale, eval_atom1572]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1572Coded : CoefficientMerge.Poly := [(nat_lit 3211, Int.ofNat (nat_lit 1))]
theorem atom1572Coded_decode : atom1572 = SparsePolynomial.decodeCubic 24 atom1572Coded := by decide +kernel
theorem atom1572Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (289024345209600 : Int) atom1572Coded) := by
  have h := atom1572_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1572Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1573 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 13, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1573 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1573 = ((g 5) * (g 13) * (g 20)) := by
  norm_num [atom1573, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1573_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (399561282489600 : Int) atom1573) := by
  rw [SparsePolynomial.eval_scale, eval_atom1573]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1573Coded : CoefficientMerge.Poly := [(nat_lit 3212, Int.ofNat (nat_lit 1))]
theorem atom1573Coded_decode : atom1573 = SparsePolynomial.decodeCubic 24 atom1573Coded := by decide +kernel
theorem atom1573Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (399561282489600 : Int) atom1573Coded) := by
  have h := atom1573_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1573Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1574 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 13, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1574 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1574 = ((g 5) * (g 13) * (g 21)) := by
  norm_num [atom1574, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1574_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (392412609388800 : Int) atom1574) := by
  rw [SparsePolynomial.eval_scale, eval_atom1574]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 5) * (g 13) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1574Coded : CoefficientMerge.Poly := [(nat_lit 3213, Int.ofNat (nat_lit 1))]
theorem atom1574Coded_decode : atom1574 = SparsePolynomial.decodeCubic 24 atom1574Coded := by decide +kernel
theorem atom1574Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (392412609388800 : Int) atom1574Coded) := by
  have h := atom1574_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1574Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1575 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 13, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1575 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1575 = ((g 5) * (g 13) * (g 22)) := by
  norm_num [atom1575, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1575_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (462642209568000 : Int) atom1575) := by
  rw [SparsePolynomial.eval_scale, eval_atom1575]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 5) * (g 13) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1575Coded : CoefficientMerge.Poly := [(nat_lit 3214, Int.ofNat (nat_lit 1))]
theorem atom1575Coded_decode : atom1575 = SparsePolynomial.decodeCubic 24 atom1575Coded := by decide +kernel
theorem atom1575Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (462642209568000 : Int) atom1575Coded) := by
  have h := atom1575_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1575Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1576 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 13, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1576 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1576 = ((g 5) * (g 13) * (g 23)) := by
  norm_num [atom1576, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1576_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (532871809747200 : Int) atom1576) := by
  rw [SparsePolynomial.eval_scale, eval_atom1576]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 5) * (g 13) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1576Coded : CoefficientMerge.Poly := [(nat_lit 3215, Int.ofNat (nat_lit 1))]
theorem atom1576Coded_decode : atom1576 = SparsePolynomial.decodeCubic 24 atom1576Coded := by decide +kernel
theorem atom1576Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (532871809747200 : Int) atom1576Coded) := by
  have h := atom1576_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1576Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1577 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1577 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1577 = ((g 5) * (g 14) * (g 14)) := by
  norm_num [atom1577, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1577_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (150166318579200 : Int) atom1577) := by
  rw [SparsePolynomial.eval_scale, eval_atom1577]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1577Coded : CoefficientMerge.Poly := [(nat_lit 3230, Int.ofNat (nat_lit 1))]
theorem atom1577Coded_decode : atom1577 = SparsePolynomial.decodeCubic 24 atom1577Coded := by decide +kernel
theorem atom1577Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (150166318579200 : Int) atom1577Coded) := by
  have h := atom1577_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1577Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1578 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 14, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1578 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1578 = ((g 5) * (g 14) * (g 15)) := by
  norm_num [atom1578, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1578_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (283120765804800 : Int) atom1578) := by
  rw [SparsePolynomial.eval_scale, eval_atom1578]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1578Coded : CoefficientMerge.Poly := [(nat_lit 3231, Int.ofNat (nat_lit 1))]
theorem atom1578Coded_decode : atom1578 = SparsePolynomial.decodeCubic 24 atom1578Coded := by decide +kernel
theorem atom1578Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (283120765804800 : Int) atom1578Coded) := by
  have h := atom1578_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1578Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1579 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 14, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1579 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1579 = ((g 5) * (g 14) * (g 16)) := by
  norm_num [atom1579, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1579_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (274126792262400 : Int) atom1579) := by
  rw [SparsePolynomial.eval_scale, eval_atom1579]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1579Coded : CoefficientMerge.Poly := [(nat_lit 3232, Int.ofNat (nat_lit 1))]
theorem atom1579Coded_decode : atom1579 = SparsePolynomial.decodeCubic 24 atom1579Coded := by decide +kernel
theorem atom1579Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (274126792262400 : Int) atom1579Coded) := by
  have h := atom1579_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1579Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1580 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 14, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1580 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1580 = ((g 5) * (g 14) * (g 17)) := by
  norm_num [atom1580, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1580_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (265132818720000 : Int) atom1580) := by
  rw [SparsePolynomial.eval_scale, eval_atom1580]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1580Coded : CoefficientMerge.Poly := [(nat_lit 3233, Int.ofNat (nat_lit 1))]
theorem atom1580Coded_decode : atom1580 = SparsePolynomial.decodeCubic 24 atom1580Coded := by decide +kernel
theorem atom1580Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (265132818720000 : Int) atom1580Coded) := by
  have h := atom1580_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1580Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1581 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 14, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1581 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1581 = ((g 5) * (g 14) * (g 18)) := by
  norm_num [atom1581, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1581_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (302636058278400 : Int) atom1581) := by
  rw [SparsePolynomial.eval_scale, eval_atom1581]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1581Coded : CoefficientMerge.Poly := [(nat_lit 3234, Int.ofNat (nat_lit 1))]
theorem atom1581Coded_decode : atom1581 = SparsePolynomial.decodeCubic 24 atom1581Coded := by decide +kernel
theorem atom1581Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (302636058278400 : Int) atom1581Coded) := by
  have h := atom1581_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1581Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1582 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 14, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1582 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1582 = ((g 5) * (g 14) * (g 19)) := by
  norm_num [atom1582, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1582_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (305305962746400 : Int) atom1582) := by
  rw [SparsePolynomial.eval_scale, eval_atom1582]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1582Coded : CoefficientMerge.Poly := [(nat_lit 3235, Int.ofNat (nat_lit 1))]
theorem atom1582Coded_decode : atom1582 = SparsePolynomial.decodeCubic 24 atom1582Coded := by decide +kernel
theorem atom1582Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (305305962746400 : Int) atom1582Coded) := by
  have h := atom1582_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1582Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1583 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 14, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1583 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1583 = ((g 5) * (g 14) * (g 20)) := by
  norm_num [atom1583, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1583_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (417245094604800 : Int) atom1583) := by
  rw [SparsePolynomial.eval_scale, eval_atom1583]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1583Coded : CoefficientMerge.Poly := [(nat_lit 3236, Int.ofNat (nat_lit 1))]
theorem atom1583Coded_decode : atom1583 = SparsePolynomial.decodeCubic 24 atom1583Coded := by decide +kernel
theorem atom1583Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (417245094604800 : Int) atom1583Coded) := by
  have h := atom1583_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1583Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1584 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 14, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1584 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1584 = ((g 5) * (g 14) * (g 21)) := by
  norm_num [atom1584, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1584_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (416219977958400 : Int) atom1584) := by
  rw [SparsePolynomial.eval_scale, eval_atom1584]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 5) * (g 14) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1584Coded : CoefficientMerge.Poly := [(nat_lit 3237, Int.ofNat (nat_lit 1))]
theorem atom1584Coded_decode : atom1584 = SparsePolynomial.decodeCubic 24 atom1584Coded := by decide +kernel
theorem atom1584Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (416219977958400 : Int) atom1584Coded) := by
  have h := atom1584_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1584Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1585 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 14, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1585 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1585 = ((g 5) * (g 14) * (g 22)) := by
  norm_num [atom1585, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1585_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (472194345823200 : Int) atom1585) := by
  rw [SparsePolynomial.eval_scale, eval_atom1585]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 5) * (g 14) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1585Coded : CoefficientMerge.Poly := [(nat_lit 3238, Int.ofNat (nat_lit 1))]
theorem atom1585Coded_decode : atom1585 = SparsePolynomial.decodeCubic 24 atom1585Coded := by decide +kernel
theorem atom1585Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (472194345823200 : Int) atom1585Coded) := by
  have h := atom1585_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1585Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1586 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 14, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1586 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1586 = ((g 5) * (g 14) * (g 23)) := by
  norm_num [atom1586, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1586_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (540748493762400 : Int) atom1586) := by
  rw [SparsePolynomial.eval_scale, eval_atom1586]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 5) * (g 14) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1586Coded : CoefficientMerge.Poly := [(nat_lit 3239, Int.ofNat (nat_lit 1))]
theorem atom1586Coded_decode : atom1586 = SparsePolynomial.decodeCubic 24 atom1586Coded := by decide +kernel
theorem atom1586Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (540748493762400 : Int) atom1586Coded) := by
  have h := atom1586_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1586Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1587 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1587 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1587 = ((g 5) * (g 15) * (g 15)) := by
  norm_num [atom1587, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1587_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (174054567456000 : Int) atom1587) := by
  rw [SparsePolynomial.eval_scale, eval_atom1587]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1587Coded : CoefficientMerge.Poly := [(nat_lit 3255, Int.ofNat (nat_lit 1))]
theorem atom1587Coded_decode : atom1587 = SparsePolynomial.decodeCubic 24 atom1587Coded := by decide +kernel
theorem atom1587Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (174054567456000 : Int) atom1587Coded) := by
  have h := atom1587_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1587Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1588 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 15, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1588 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1588 = ((g 5) * (g 15) * (g 16)) := by
  norm_num [atom1588, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1588_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (319660112217600 : Int) atom1588) := by
  rw [SparsePolynomial.eval_scale, eval_atom1588]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1588Coded : CoefficientMerge.Poly := [(nat_lit 3256, Int.ofNat (nat_lit 1))]
theorem atom1588Coded_decode : atom1588 = SparsePolynomial.decodeCubic 24 atom1588Coded := by decide +kernel
theorem atom1588Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (319660112217600 : Int) atom1588Coded) := by
  have h := atom1588_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1588Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1589 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 15, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1589 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1589 = ((g 5) * (g 15) * (g 17)) := by
  norm_num [atom1589, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1589_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (304563844569600 : Int) atom1589) := by
  rw [SparsePolynomial.eval_scale, eval_atom1589]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1589Coded : CoefficientMerge.Poly := [(nat_lit 3257, Int.ofNat (nat_lit 1))]
theorem atom1589Coded_decode : atom1589 = SparsePolynomial.decodeCubic 24 atom1589Coded := by decide +kernel
theorem atom1589Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (304563844569600 : Int) atom1589Coded) := by
  have h := atom1589_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1589Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1590 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 15, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1590 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1590 = ((g 5) * (g 15) * (g 18)) := by
  norm_num [atom1590, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1590_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (338015640211200 : Int) atom1590) := by
  rw [SparsePolynomial.eval_scale, eval_atom1590]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1590Coded : CoefficientMerge.Poly := [(nat_lit 3258, Int.ofNat (nat_lit 1))]
theorem atom1590Coded_decode : atom1590 = SparsePolynomial.decodeCubic 24 atom1590Coded := by decide +kernel
theorem atom1590Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (338015640211200 : Int) atom1590Coded) := by
  have h := atom1590_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1590Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1591 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 15, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1591 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1591 = ((g 5) * (g 15) * (g 19)) := by
  norm_num [atom1591, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1591_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (327299245056000 : Int) atom1591) := by
  rw [SparsePolynomial.eval_scale, eval_atom1591]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1591Coded : CoefficientMerge.Poly := [(nat_lit 3259, Int.ofNat (nat_lit 1))]
theorem atom1591Coded_decode : atom1591 = SparsePolynomial.decodeCubic 24 atom1591Coded := by decide +kernel
theorem atom1591Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (327299245056000 : Int) atom1591Coded) := by
  have h := atom1591_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1591Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1592 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 15, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1592 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1592 = ((g 5) * (g 15) * (g 20)) := by
  norm_num [atom1592, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1592_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (464134050374400 : Int) atom1592) := by
  rw [SparsePolynomial.eval_scale, eval_atom1592]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1592Coded : CoefficientMerge.Poly := [(nat_lit 3260, Int.ofNat (nat_lit 1))]
theorem atom1592Coded_decode : atom1592 = SparsePolynomial.decodeCubic 24 atom1592Coded := by decide +kernel
theorem atom1592Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (464134050374400 : Int) atom1592Coded) := by
  have h := atom1592_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1592Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1593 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 15, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1593 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1593 = ((g 5) * (g 15) * (g 21)) := by
  norm_num [atom1593, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1593_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (469048055414400 : Int) atom1593) := by
  rw [SparsePolynomial.eval_scale, eval_atom1593]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 5) * (g 15) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1593Coded : CoefficientMerge.Poly := [(nat_lit 3261, Int.ofNat (nat_lit 1))]
theorem atom1593Coded_decode : atom1593 = SparsePolynomial.decodeCubic 24 atom1593Coded := by decide +kernel
theorem atom1593Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (469048055414400 : Int) atom1593Coded) := by
  have h := atom1593_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1593Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1594 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 15, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1594 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1594 = ((g 5) * (g 15) * (g 22)) := by
  norm_num [atom1594, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1594_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (460158285888000 : Int) atom1594) := by
  rw [SparsePolynomial.eval_scale, eval_atom1594]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 5) * (g 15) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1594Coded : CoefficientMerge.Poly := [(nat_lit 3262, Int.ofNat (nat_lit 1))]
theorem atom1594Coded_decode : atom1594 = SparsePolynomial.decodeCubic 24 atom1594Coded := by decide +kernel
theorem atom1594Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (460158285888000 : Int) atom1594Coded) := by
  have h := atom1594_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1594Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1595 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 15, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1595 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1595 = ((g 5) * (g 15) * (g 23)) := by
  norm_num [atom1595, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1595_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (521735242392000 : Int) atom1595) := by
  rw [SparsePolynomial.eval_scale, eval_atom1595]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 5) * (g 15) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1595Coded : CoefficientMerge.Poly := [(nat_lit 3263, Int.ofNat (nat_lit 1))]
theorem atom1595Coded_decode : atom1595 = SparsePolynomial.decodeCubic 24 atom1595Coded := by decide +kernel
theorem atom1595Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (521735242392000 : Int) atom1595Coded) := by
  have h := atom1595_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1595Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1596 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 16, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1596 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1596 = ((g 5) * (g 16) * (g 16)) := by
  norm_num [atom1596, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1596_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (189788705568000 : Int) atom1596) := by
  rw [SparsePolynomial.eval_scale, eval_atom1596]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1596Coded : CoefficientMerge.Poly := [(nat_lit 3280, Int.ofNat (nat_lit 1))]
theorem atom1596Coded_decode : atom1596 = SparsePolynomial.decodeCubic 24 atom1596Coded := by decide +kernel
theorem atom1596Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (189788705568000 : Int) atom1596Coded) := by
  have h := atom1596_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1596Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1597 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1597 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1597 = ((g 5) * (g 16) * (g 17)) := by
  norm_num [atom1597, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1597_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (354275216064000 : Int) atom1597) := by
  rw [SparsePolynomial.eval_scale, eval_atom1597]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1597Coded : CoefficientMerge.Poly := [(nat_lit 3281, Int.ofNat (nat_lit 1))]
theorem atom1597Coded_decode : atom1597 = SparsePolynomial.decodeCubic 24 atom1597Coded := by decide +kernel
theorem atom1597Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (354275216064000 : Int) atom1597Coded) := by
  have h := atom1597_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1597Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1598 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 16, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1598 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1598 = ((g 5) * (g 16) * (g 18)) := by
  norm_num [atom1598, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1598_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (355661456774400 : Int) atom1598) := by
  rw [SparsePolynomial.eval_scale, eval_atom1598]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1598Coded : CoefficientMerge.Poly := [(nat_lit 3282, Int.ofNat (nat_lit 1))]
theorem atom1598Coded_decode : atom1598 = SparsePolynomial.decodeCubic 24 atom1598Coded := by decide +kernel
theorem atom1598Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (355661456774400 : Int) atom1598Coded) := by
  have h := atom1598_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1598Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1599 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 16, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1599 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1599 = ((g 5) * (g 16) * (g 19)) := by
  norm_num [atom1599, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1599_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (344788493414400 : Int) atom1599) := by
  rw [SparsePolynomial.eval_scale, eval_atom1599]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1599Coded : CoefficientMerge.Poly := [(nat_lit 3283, Int.ofNat (nat_lit 1))]
theorem atom1599Coded_decode : atom1599 = SparsePolynomial.decodeCubic 24 atom1599Coded := by decide +kernel
theorem atom1599Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (344788493414400 : Int) atom1599Coded) := by
  have h := atom1599_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1599Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1600 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 16, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1600 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1600 = ((g 5) * (g 16) * (g 20)) := by
  norm_num [atom1600, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1600_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (481466730528000 : Int) atom1600) := by
  rw [SparsePolynomial.eval_scale, eval_atom1600]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1600Coded : CoefficientMerge.Poly := [(nat_lit 3284, Int.ofNat (nat_lit 1))]
theorem atom1600Coded_decode : atom1600 = SparsePolynomial.decodeCubic 24 atom1600Coded := by decide +kernel
theorem atom1600Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (481466730528000 : Int) atom1600Coded) := by
  have h := atom1600_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1600Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1601 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 16, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1601 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1601 = ((g 5) * (g 16) * (g 21)) := by
  norm_num [atom1601, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1601_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (489364229692800 : Int) atom1601) := by
  rw [SparsePolynomial.eval_scale, eval_atom1601]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 5) * (g 16) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1601Coded : CoefficientMerge.Poly := [(nat_lit 3285, Int.ofNat (nat_lit 1))]
theorem atom1601Coded_decode : atom1601 = SparsePolynomial.decodeCubic 24 atom1601Coded := by decide +kernel
theorem atom1601Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (489364229692800 : Int) atom1601Coded) := by
  have h := atom1601_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1601Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1602 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 16, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1602 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1602 = ((g 5) * (g 16) * (g 22)) := by
  norm_num [atom1602, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1602_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (425664957312000 : Int) atom1602) := by
  rw [SparsePolynomial.eval_scale, eval_atom1602]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 5) * (g 16) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1602Coded : CoefficientMerge.Poly := [(nat_lit 3286, Int.ofNat (nat_lit 1))]
theorem atom1602Coded_decode : atom1602 = SparsePolynomial.decodeCubic 24 atom1602Coded := by decide +kernel
theorem atom1602Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (425664957312000 : Int) atom1602Coded) := by
  have h := atom1602_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1602Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1603 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 16, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1603 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1603 = ((g 5) * (g 16) * (g 23)) := by
  norm_num [atom1603, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1603_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (568330230081600 : Int) atom1603) := by
  rw [SparsePolynomial.eval_scale, eval_atom1603]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 5) * (g 16) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1603Coded : CoefficientMerge.Poly := [(nat_lit 3287, Int.ofNat (nat_lit 1))]
theorem atom1603Coded_decode : atom1603 = SparsePolynomial.decodeCubic 24 atom1603Coded := by decide +kernel
theorem atom1603Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (568330230081600 : Int) atom1603Coded) := by
  have h := atom1603_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1603Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1604 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1604 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1604 = ((g 5) * (g 17) * (g 17)) := by
  norm_num [atom1604, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1604_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (203878555372800 : Int) atom1604) := by
  rw [SparsePolynomial.eval_scale, eval_atom1604]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1604Coded : CoefficientMerge.Poly := [(nat_lit 3305, Int.ofNat (nat_lit 1))]
theorem atom1604Coded_decode : atom1604 = SparsePolynomial.decodeCubic 24 atom1604Coded := by decide +kernel
theorem atom1604Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (203878555372800 : Int) atom1604Coded) := by
  have h := atom1604_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1604Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1605 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 17, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1605 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1605 = ((g 5) * (g 17) * (g 18)) := by
  norm_num [atom1605, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1605_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (388206381024000 : Int) atom1605) := by
  rw [SparsePolynomial.eval_scale, eval_atom1605]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1605Coded : CoefficientMerge.Poly := [(nat_lit 3306, Int.ofNat (nat_lit 1))]
theorem atom1605Coded_decode : atom1605 = SparsePolynomial.decodeCubic 24 atom1605Coded := by decide +kernel
theorem atom1605Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (388206381024000 : Int) atom1605Coded) := by
  have h := atom1605_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1605Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1606 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 17, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1606 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1606 = ((g 5) * (g 17) * (g 19)) := by
  norm_num [atom1606, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1606_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (382143218688000 : Int) atom1606) := by
  rw [SparsePolynomial.eval_scale, eval_atom1606]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1606Coded : CoefficientMerge.Poly := [(nat_lit 3307, Int.ofNat (nat_lit 1))]
theorem atom1606Coded_decode : atom1606 = SparsePolynomial.decodeCubic 24 atom1606Coded := by decide +kernel
theorem atom1606Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (382143218688000 : Int) atom1606Coded) := by
  have h := atom1606_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1606Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1607 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 17, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1607 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1607 = ((g 5) * (g 17) * (g 20)) := by
  norm_num [atom1607, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1607_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (523631256825600 : Int) atom1607) := by
  rw [SparsePolynomial.eval_scale, eval_atom1607]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1607Coded : CoefficientMerge.Poly := [(nat_lit 3308, Int.ofNat (nat_lit 1))]
theorem atom1607Coded_decode : atom1607 = SparsePolynomial.decodeCubic 24 atom1607Coded := by decide +kernel
theorem atom1607Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (523631256825600 : Int) atom1607Coded) := by
  have h := atom1607_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1607Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1608 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 17, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1608 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1608 = ((g 5) * (g 17) * (g 21)) := by
  norm_num [atom1608, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1608_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (536995434729600 : Int) atom1608) := by
  rw [SparsePolynomial.eval_scale, eval_atom1608]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 5) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1608Coded : CoefficientMerge.Poly := [(nat_lit 3309, Int.ofNat (nat_lit 1))]
theorem atom1608Coded_decode : atom1608 = SparsePolynomial.decodeCubic 24 atom1608Coded := by decide +kernel
theorem atom1608Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (536995434729600 : Int) atom1608Coded) := by
  have h := atom1608_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1608Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1609 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 17, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1609 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1609 = ((g 5) * (g 17) * (g 22)) := by
  norm_num [atom1609, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1609_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (477639158169600 : Int) atom1609) := by
  rw [SparsePolynomial.eval_scale, eval_atom1609]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 5) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1609Coded : CoefficientMerge.Poly := [(nat_lit 3310, Int.ofNat (nat_lit 1))]
theorem atom1609Coded_decode : atom1609 = SparsePolynomial.decodeCubic 24 atom1609Coded := by decide +kernel
theorem atom1609Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (477639158169600 : Int) atom1609Coded) := by
  have h := atom1609_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1609Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1610 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 17, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1610 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1610 = ((g 5) * (g 17) * (g 23)) := by
  norm_num [atom1610, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1610_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (626099548536000 : Int) atom1610) := by
  rw [SparsePolynomial.eval_scale, eval_atom1610]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 5) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1610Coded : CoefficientMerge.Poly := [(nat_lit 3311, Int.ofNat (nat_lit 1))]
theorem atom1610Coded_decode : atom1610 = SparsePolynomial.decodeCubic 24 atom1610Coded := by decide +kernel
theorem atom1610Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (626099548536000 : Int) atom1610Coded) := by
  have h := atom1610_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1610Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1611 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 18, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1611 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1611 = ((g 5) * (g 18) * (g 18)) := by
  norm_num [atom1611, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1611_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (235368093945600 : Int) atom1611) := by
  rw [SparsePolynomial.eval_scale, eval_atom1611]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1611Coded : CoefficientMerge.Poly := [(nat_lit 3330, Int.ofNat (nat_lit 1))]
theorem atom1611Coded_decode : atom1611 = SparsePolynomial.decodeCubic 24 atom1611Coded := by decide +kernel
theorem atom1611Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (235368093945600 : Int) atom1611Coded) := by
  have h := atom1611_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1611Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1612 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 18, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1612 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1612 = ((g 5) * (g 18) * (g 19)) := by
  norm_num [atom1612, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1612_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (440940625171200 : Int) atom1612) := by
  rw [SparsePolynomial.eval_scale, eval_atom1612]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1612Coded : CoefficientMerge.Poly := [(nat_lit 3331, Int.ofNat (nat_lit 1))]
theorem atom1612Coded_decode : atom1612 = SparsePolynomial.decodeCubic 24 atom1612Coded := by decide +kernel
theorem atom1612Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (440940625171200 : Int) atom1612Coded) := by
  have h := atom1612_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1612Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1613 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 18, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1613 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1613 = ((g 5) * (g 18) * (g 20)) := by
  norm_num [atom1613, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1613_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (625762461139200 : Int) atom1613) := by
  rw [SparsePolynomial.eval_scale, eval_atom1613]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1613Coded : CoefficientMerge.Poly := [(nat_lit 3332, Int.ofNat (nat_lit 1))]
theorem atom1613Coded_decode : atom1613 = SparsePolynomial.decodeCubic 24 atom1613Coded := by decide +kernel
theorem atom1613Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (625762461139200 : Int) atom1613Coded) := by
  have h := atom1613_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1613Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1614 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 18, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1614 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1614 = ((g 5) * (g 18) * (g 21)) := by
  norm_num [atom1614, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1614_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (603689881132800 : Int) atom1614) := by
  rw [SparsePolynomial.eval_scale, eval_atom1614]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 5) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1614Coded : CoefficientMerge.Poly := [(nat_lit 3333, Int.ofNat (nat_lit 1))]
theorem atom1614Coded_decode : atom1614 = SparsePolynomial.decodeCubic 24 atom1614Coded := by decide +kernel
theorem atom1614Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (603689881132800 : Int) atom1614Coded) := by
  have h := atom1614_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1614Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1615 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 18, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1615 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1615 = ((g 5) * (g 18) * (g 22)) := by
  norm_num [atom1615, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1615_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (445497019027200 : Int) atom1615) := by
  rw [SparsePolynomial.eval_scale, eval_atom1615]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 5) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1615Coded : CoefficientMerge.Poly := [(nat_lit 3334, Int.ofNat (nat_lit 1))]
theorem atom1615Coded_decode : atom1615 = SparsePolynomial.decodeCubic 24 atom1615Coded := by decide +kernel
theorem atom1615Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (445497019027200 : Int) atom1615Coded) := by
  have h := atom1615_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1615Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1616 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 18, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1616 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1616 = ((g 5) * (g 18) * (g 23)) := by
  norm_num [atom1616, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1616_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (623082726604800 : Int) atom1616) := by
  rw [SparsePolynomial.eval_scale, eval_atom1616]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 5) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1616Coded : CoefficientMerge.Poly := [(nat_lit 3335, Int.ofNat (nat_lit 1))]
theorem atom1616Coded_decode : atom1616 = SparsePolynomial.decodeCubic 24 atom1616Coded := by decide +kernel
theorem atom1616Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (623082726604800 : Int) atom1616Coded) := by
  have h := atom1616_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1616Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1617 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 19, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1617 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1617 = ((g 5) * (g 19) * (g 19)) := by
  norm_num [atom1617, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1617_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (159053271632640 : Int) atom1617) := by
  rw [SparsePolynomial.eval_scale, eval_atom1617]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1617Coded : CoefficientMerge.Poly := [(nat_lit 3355, Int.ofNat (nat_lit 1))]
theorem atom1617Coded_decode : atom1617 = SparsePolynomial.decodeCubic 24 atom1617Coded := by decide +kernel
theorem atom1617Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (159053271632640 : Int) atom1617Coded) := by
  have h := atom1617_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1617Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1618 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 19, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1618 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1618 = ((g 5) * (g 19) * (g 20)) := by
  norm_num [atom1618, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1618_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (480885340320000 : Int) atom1618) := by
  rw [SparsePolynomial.eval_scale, eval_atom1618]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1618Coded : CoefficientMerge.Poly := [(nat_lit 3356, Int.ofNat (nat_lit 1))]
theorem atom1618Coded_decode : atom1618 = SparsePolynomial.decodeCubic 24 atom1618Coded := by decide +kernel
theorem atom1618Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (480885340320000 : Int) atom1618Coded) := by
  have h := atom1618_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1618Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1619 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 19, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1619 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1619 = ((g 5) * (g 19) * (g 21)) := by
  norm_num [atom1619, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1619_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (470906173584000 : Int) atom1619) := by
  rw [SparsePolynomial.eval_scale, eval_atom1619]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 5) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1619Coded : CoefficientMerge.Poly := [(nat_lit 3357, Int.ofNat (nat_lit 1))]
theorem atom1619Coded_decode : atom1619 = SparsePolynomial.decodeCubic 24 atom1619Coded := by decide +kernel
theorem atom1619Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (470906173584000 : Int) atom1619Coded) := by
  have h := atom1619_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1619Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1620 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 19, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1620 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1620 = ((g 5) * (g 19) * (g 22)) := by
  norm_num [atom1620, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1620_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (369833052153600 : Int) atom1620) := by
  rw [SparsePolynomial.eval_scale, eval_atom1620]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 5) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1620Coded : CoefficientMerge.Poly := [(nat_lit 3358, Int.ofNat (nat_lit 1))]
theorem atom1620Coded_decode : atom1620 = SparsePolynomial.decodeCubic 24 atom1620Coded := by decide +kernel
theorem atom1620Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (369833052153600 : Int) atom1620Coded) := by
  have h := atom1620_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1620Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1621 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 19, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1621 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1621 = ((g 5) * (g 19) * (g 23)) := by
  norm_num [atom1621, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1621_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (416251856059200 : Int) atom1621) := by
  rw [SparsePolynomial.eval_scale, eval_atom1621]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 5) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1621Coded : CoefficientMerge.Poly := [(nat_lit 3359, Int.ofNat (nat_lit 1))]
theorem atom1621Coded_decode : atom1621 = SparsePolynomial.decodeCubic 24 atom1621Coded := by decide +kernel
theorem atom1621Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (416251856059200 : Int) atom1621Coded) := by
  have h := atom1621_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1621Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1622 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 20, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1622 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1622 = ((g 5) * (g 20) * (g 20)) := by
  norm_num [atom1622, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1622_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (342379007308800 : Int) atom1622) := by
  rw [SparsePolynomial.eval_scale, eval_atom1622]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1622Coded : CoefficientMerge.Poly := [(nat_lit 3380, Int.ofNat (nat_lit 1))]
theorem atom1622Coded_decode : atom1622 = SparsePolynomial.decodeCubic 24 atom1622Coded := by decide +kernel
theorem atom1622Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (342379007308800 : Int) atom1622Coded) := by
  have h := atom1622_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1622Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1623 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 20, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1623 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1623 = ((g 5) * (g 20) * (g 21)) := by
  norm_num [atom1623, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1623_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (509142662582400 : Int) atom1623) := by
  rw [SparsePolynomial.eval_scale, eval_atom1623]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 5) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1623Coded : CoefficientMerge.Poly := [(nat_lit 3381, Int.ofNat (nat_lit 1))]
theorem atom1623Coded_decode : atom1623 = SparsePolynomial.decodeCubic 24 atom1623Coded := by decide +kernel
theorem atom1623Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (509142662582400 : Int) atom1623Coded) := by
  have h := atom1623_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1623Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1624 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 20, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1624 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1624 = ((g 5) * (g 20) * (g 22)) := by
  norm_num [atom1624, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1624_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (380139266304000 : Int) atom1624) := by
  rw [SparsePolynomial.eval_scale, eval_atom1624]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 5) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1624Coded : CoefficientMerge.Poly := [(nat_lit 3382, Int.ofNat (nat_lit 1))]
theorem atom1624Coded_decode : atom1624 = SparsePolynomial.decodeCubic 24 atom1624Coded := by decide +kernel
theorem atom1624Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (380139266304000 : Int) atom1624Coded) := by
  have h := atom1624_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1624Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1625 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 20, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1625 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1625 = ((g 5) * (g 20) * (g 23)) := by
  norm_num [atom1625, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1625_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (433594128945600 : Int) atom1625) := by
  rw [SparsePolynomial.eval_scale, eval_atom1625]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 5) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1625Coded : CoefficientMerge.Poly := [(nat_lit 3383, Int.ofNat (nat_lit 1))]
theorem atom1625Coded_decode : atom1625 = SparsePolynomial.decodeCubic 24 atom1625Coded := by decide +kernel
theorem atom1625Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (433594128945600 : Int) atom1625Coded) := by
  have h := atom1625_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1625Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1626 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 21, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1626 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1626 = ((g 5) * (g 21) * (g 21)) := by
  norm_num [atom1626, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1626_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (125494567228800 : Int) atom1626) := by
  rw [SparsePolynomial.eval_scale, eval_atom1626]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 5) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1626Coded : CoefficientMerge.Poly := [(nat_lit 3405, Int.ofNat (nat_lit 1))]
theorem atom1626Coded_decode : atom1626 = SparsePolynomial.decodeCubic 24 atom1626Coded := by decide +kernel
theorem atom1626Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (125494567228800 : Int) atom1626Coded) := by
  have h := atom1626_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1626Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1627 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 21, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1627 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1627 = ((g 5) * (g 21) * (g 22)) := by
  norm_num [atom1627, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1627_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (175501668384000 : Int) atom1627) := by
  rw [SparsePolynomial.eval_scale, eval_atom1627]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 5) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1627Coded : CoefficientMerge.Poly := [(nat_lit 3406, Int.ofNat (nat_lit 1))]
theorem atom1627Coded_decode : atom1627 = SparsePolynomial.decodeCubic 24 atom1627Coded := by decide +kernel
theorem atom1627Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (175501668384000 : Int) atom1627Coded) := by
  have h := atom1627_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1627Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1628 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 21, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1628 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1628 = ((g 5) * (g 21) * (g 23)) := by
  norm_num [atom1628, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1628_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (230197672656000 : Int) atom1628) := by
  rw [SparsePolynomial.eval_scale, eval_atom1628]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 5) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1628Coded : CoefficientMerge.Poly := [(nat_lit 3407, Int.ofNat (nat_lit 1))]
theorem atom1628Coded_decode : atom1628 = SparsePolynomial.decodeCubic 24 atom1628Coded := by decide +kernel
theorem atom1628Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (230197672656000 : Int) atom1628Coded) := by
  have h := atom1628_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1628Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1629 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 6, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom1629 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1629 = ((g 6) * (g 6) * (g 6)) := by
  norm_num [atom1629, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1629_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19029802176000 : Int) atom1629) := by
  rw [SparsePolynomial.eval_scale, eval_atom1629]
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 6) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1629Coded : CoefficientMerge.Poly := [(nat_lit 3606, Int.ofNat (nat_lit 1))]
theorem atom1629Coded_decode : atom1629 = SparsePolynomial.decodeCubic 24 atom1629Coded := by decide +kernel
theorem atom1629Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (19029802176000 : Int) atom1629Coded) := by
  have h := atom1629_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1629Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1630 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 6, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom1630 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1630 = ((g 6) * (g 6) * (g 7)) := by
  norm_num [atom1630, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1630_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29330228928000 : Int) atom1630) := by
  rw [SparsePolynomial.eval_scale, eval_atom1630]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 6) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1630Coded : CoefficientMerge.Poly := [(nat_lit 3607, Int.ofNat (nat_lit 1))]
theorem atom1630Coded_decode : atom1630 = SparsePolynomial.decodeCubic 24 atom1630Coded := by decide +kernel
theorem atom1630Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (29330228928000 : Int) atom1630Coded) := by
  have h := atom1630_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1630Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1631 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 6, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom1631 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1631 = ((g 6) * (g 6) * (g 8)) := by
  norm_num [atom1631, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1631_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7420559731200 : Int) atom1631) := by
  rw [SparsePolynomial.eval_scale, eval_atom1631]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 6) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1631Coded : CoefficientMerge.Poly := [(nat_lit 3608, Int.ofNat (nat_lit 1))]
theorem atom1631Coded_decode : atom1631 = SparsePolynomial.decodeCubic 24 atom1631Coded := by decide +kernel
theorem atom1631Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (7420559731200 : Int) atom1631Coded) := by
  have h := atom1631_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1631Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1632 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 6, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom1632 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1632 = ((g 6) * (g 6) * (g 9)) := by
  norm_num [atom1632, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1632_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5145488409600 : Int) atom1632) := by
  rw [SparsePolynomial.eval_scale, eval_atom1632]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 6) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1632Coded : CoefficientMerge.Poly := [(nat_lit 3609, Int.ofNat (nat_lit 1))]
theorem atom1632Coded_decode : atom1632 = SparsePolynomial.decodeCubic 24 atom1632Coded := by decide +kernel
theorem atom1632Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (5145488409600 : Int) atom1632Coded) := by
  have h := atom1632_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1632Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1633 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 6, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1633 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1633 = ((g 6) * (g 6) * (g 10)) := by
  norm_num [atom1633, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1633_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7788087023904 : Int) atom1633) := by
  rw [SparsePolynomial.eval_scale, eval_atom1633]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1633Coded : CoefficientMerge.Poly := [(nat_lit 3610, Int.ofNat (nat_lit 1))]
theorem atom1633Coded_decode : atom1633 = SparsePolynomial.decodeCubic 24 atom1633Coded := by decide +kernel
theorem atom1633Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (7788087023904 : Int) atom1633Coded) := by
  have h := atom1633_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1633Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1634 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 6, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1634 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1634 = ((g 6) * (g 6) * (g 11)) := by
  norm_num [atom1634, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1634_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2062447833600 : Int) atom1634) := by
  rw [SparsePolynomial.eval_scale, eval_atom1634]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1634Coded : CoefficientMerge.Poly := [(nat_lit 3611, Int.ofNat (nat_lit 1))]
theorem atom1634Coded_decode : atom1634 = SparsePolynomial.decodeCubic 24 atom1634Coded := by decide +kernel
theorem atom1634Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (2062447833600 : Int) atom1634Coded) := by
  have h := atom1634_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1634Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1635 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom1635 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1635 = ((g 6) * (g 7) * (g 7)) := by
  norm_num [atom1635, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1635_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26235375936000 : Int) atom1635) := by
  rw [SparsePolynomial.eval_scale, eval_atom1635]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 6) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1635Coded : CoefficientMerge.Poly := [(nat_lit 3631, Int.ofNat (nat_lit 1))]
theorem atom1635Coded_decode : atom1635 = SparsePolynomial.decodeCubic 24 atom1635Coded := by decide +kernel
theorem atom1635Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (26235375936000 : Int) atom1635Coded) := by
  have h := atom1635_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1635Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1636 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom1636 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1636 = ((g 6) * (g 7) * (g 8)) := by
  norm_num [atom1636, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1636_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17921797555200 : Int) atom1636) := by
  rw [SparsePolynomial.eval_scale, eval_atom1636]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 6) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1636Coded : CoefficientMerge.Poly := [(nat_lit 3632, Int.ofNat (nat_lit 1))]
theorem atom1636Coded_decode : atom1636 = SparsePolynomial.decodeCubic 24 atom1636Coded := by decide +kernel
theorem atom1636Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (17921797555200 : Int) atom1636Coded) := by
  have h := atom1636_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1636Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1637 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1637 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1637 = ((g 6) * (g 7) * (g 10)) := by
  norm_num [atom1637, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1637_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6305789971008 : Int) atom1637) := by
  rw [SparsePolynomial.eval_scale, eval_atom1637]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1637Coded : CoefficientMerge.Poly := [(nat_lit 3634, Int.ofNat (nat_lit 1))]
theorem atom1637Coded_decode : atom1637 = SparsePolynomial.decodeCubic 24 atom1637Coded := by decide +kernel
theorem atom1637Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (6305789971008 : Int) atom1637Coded) := by
  have h := atom1637_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1637Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1638 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1638 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1638 = ((g 6) * (g 7) * (g 12)) := by
  norm_num [atom1638, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1638_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1020592742400 : Int) atom1638) := by
  rw [SparsePolynomial.eval_scale, eval_atom1638]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1638Coded : CoefficientMerge.Poly := [(nat_lit 3636, Int.ofNat (nat_lit 1))]
theorem atom1638Coded_decode : atom1638 = SparsePolynomial.decodeCubic 24 atom1638Coded := by decide +kernel
theorem atom1638Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (1020592742400 : Int) atom1638Coded) := by
  have h := atom1638_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1638Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1639 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1639 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1639 = ((g 6) * (g 7) * (g 13)) := by
  norm_num [atom1639, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1639_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4103633318400 : Int) atom1639) := by
  rw [SparsePolynomial.eval_scale, eval_atom1639]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1639Coded : CoefficientMerge.Poly := [(nat_lit 3637, Int.ofNat (nat_lit 1))]
theorem atom1639Coded_decode : atom1639 = SparsePolynomial.decodeCubic 24 atom1639Coded := by decide +kernel
theorem atom1639Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (4103633318400 : Int) atom1639Coded) := by
  have h := atom1639_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1639Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1640 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1640 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1640 = ((g 6) * (g 7) * (g 14)) := by
  norm_num [atom1640, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1640_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7186673894400 : Int) atom1640) := by
  rw [SparsePolynomial.eval_scale, eval_atom1640]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1640Coded : CoefficientMerge.Poly := [(nat_lit 3638, Int.ofNat (nat_lit 1))]
theorem atom1640Coded_decode : atom1640 = SparsePolynomial.decodeCubic 24 atom1640Coded := by decide +kernel
theorem atom1640Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (7186673894400 : Int) atom1640Coded) := by
  have h := atom1640_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1640Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1641 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1641 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1641 = ((g 6) * (g 7) * (g 15)) := by
  norm_num [atom1641, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1641_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10269714470400 : Int) atom1641) := by
  rw [SparsePolynomial.eval_scale, eval_atom1641]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1641Coded : CoefficientMerge.Poly := [(nat_lit 3639, Int.ofNat (nat_lit 1))]
theorem atom1641Coded_decode : atom1641 = SparsePolynomial.decodeCubic 24 atom1641Coded := by decide +kernel
theorem atom1641Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (10269714470400 : Int) atom1641Coded) := by
  have h := atom1641_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1641Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1642 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1642 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1642 = ((g 6) * (g 7) * (g 16)) := by
  norm_num [atom1642, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1642_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13352755046400 : Int) atom1642) := by
  rw [SparsePolynomial.eval_scale, eval_atom1642]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1642Coded : CoefficientMerge.Poly := [(nat_lit 3640, Int.ofNat (nat_lit 1))]
theorem atom1642Coded_decode : atom1642 = SparsePolynomial.decodeCubic 24 atom1642Coded := by decide +kernel
theorem atom1642Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (13352755046400 : Int) atom1642Coded) := by
  have h := atom1642_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1642Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1643 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1643 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1643 = ((g 6) * (g 7) * (g 17)) := by
  norm_num [atom1643, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1643_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16435795622400 : Int) atom1643) := by
  rw [SparsePolynomial.eval_scale, eval_atom1643]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1643Coded : CoefficientMerge.Poly := [(nat_lit 3641, Int.ofNat (nat_lit 1))]
theorem atom1643Coded_decode : atom1643 = SparsePolynomial.decodeCubic 24 atom1643Coded := by decide +kernel
theorem atom1643Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (16435795622400 : Int) atom1643Coded) := by
  have h := atom1643_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1643Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1644 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1644 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1644 = ((g 6) * (g 7) * (g 18)) := by
  norm_num [atom1644, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1644_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1333149269760 : Int) atom1644) := by
  rw [SparsePolynomial.eval_scale, eval_atom1644]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 7) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1644Coded : CoefficientMerge.Poly := [(nat_lit 3642, Int.ofNat (nat_lit 1))]
theorem atom1644Coded_decode : atom1644 = SparsePolynomial.decodeCubic 24 atom1644Coded := by decide +kernel
theorem atom1644Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (1333149269760 : Int) atom1644Coded) := by
  have h := atom1644_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1644Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1645 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1645 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1645 = ((g 6) * (g 7) * (g 21)) := by
  norm_num [atom1645, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1645_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40850287632000 : Int) atom1645) := by
  rw [SparsePolynomial.eval_scale, eval_atom1645]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 6) * (g 7) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1645Coded : CoefficientMerge.Poly := [(nat_lit 3645, Int.ofNat (nat_lit 1))]
theorem atom1645Coded_decode : atom1645 = SparsePolynomial.decodeCubic 24 atom1645Coded := by decide +kernel
theorem atom1645Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (40850287632000 : Int) atom1645Coded) := by
  have h := atom1645_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1645Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1646 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1646 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1646 = ((g 6) * (g 7) * (g 22)) := by
  norm_num [atom1646, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1646_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (83033724533760 : Int) atom1646) := by
  rw [SparsePolynomial.eval_scale, eval_atom1646]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 6) * (g 7) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1646Coded : CoefficientMerge.Poly := [(nat_lit 3646, Int.ofNat (nat_lit 1))]
theorem atom1646Coded_decode : atom1646 = SparsePolynomial.decodeCubic 24 atom1646Coded := by decide +kernel
theorem atom1646Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (83033724533760 : Int) atom1646Coded) := by
  have h := atom1646_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1646Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1647 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1647 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1647 = ((g 6) * (g 7) * (g 23)) := by
  norm_num [atom1647, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1647_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (133205957438400 : Int) atom1647) := by
  rw [SparsePolynomial.eval_scale, eval_atom1647]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 6) * (g 7) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1647Coded : CoefficientMerge.Poly := [(nat_lit 3647, Int.ofNat (nat_lit 1))]
theorem atom1647Coded_decode : atom1647 = SparsePolynomial.decodeCubic 24 atom1647Coded := by decide +kernel
theorem atom1647Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (133205957438400 : Int) atom1647Coded) := by
  have h := atom1647_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1647Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1648 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom1648 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1648 = ((g 6) * (g 8) * (g 8)) := by
  norm_num [atom1648, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1648_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17371338969600 : Int) atom1648) := by
  rw [SparsePolynomial.eval_scale, eval_atom1648]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 6) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1648Coded : CoefficientMerge.Poly := [(nat_lit 3656, Int.ofNat (nat_lit 1))]
theorem atom1648Coded_decode : atom1648 = SparsePolynomial.decodeCubic 24 atom1648Coded := by decide +kernel
theorem atom1648Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (17371338969600 : Int) atom1648Coded) := by
  have h := atom1648_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1648Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block022 : CoefficientMerge.Poly := [(nat_lit 3208, Int.ofNat (nat_lit 245154757478400)), (nat_lit 3209, Int.ofNat (nat_lit 241242485299200)), (nat_lit 3210, Int.ofNat (nat_lit 297199359072000)), (nat_lit 3211, Int.ofNat (nat_lit 289024345209600)), (nat_lit 3212, Int.ofNat (nat_lit 399561282489600)), (nat_lit 3213, Int.ofNat (nat_lit 392412609388800)), (nat_lit 3214, Int.ofNat (nat_lit 462642209568000)), (nat_lit 3215, Int.ofNat (nat_lit 532871809747200)), (nat_lit 3230, Int.ofNat (nat_lit 150166318579200)), (nat_lit 3231, Int.ofNat (nat_lit 283120765804800)), (nat_lit 3232, Int.ofNat (nat_lit 274126792262400)), (nat_lit 3233, Int.ofNat (nat_lit 265132818720000)), (nat_lit 3234, Int.ofNat (nat_lit 302636058278400)), (nat_lit 3235, Int.ofNat (nat_lit 305305962746400)), (nat_lit 3236, Int.ofNat (nat_lit 417245094604800)), (nat_lit 3237, Int.ofNat (nat_lit 416219977958400)), (nat_lit 3238, Int.ofNat (nat_lit 472194345823200)), (nat_lit 3239, Int.ofNat (nat_lit 540748493762400)), (nat_lit 3255, Int.ofNat (nat_lit 174054567456000)), (nat_lit 3256, Int.ofNat (nat_lit 319660112217600)), (nat_lit 3257, Int.ofNat (nat_lit 304563844569600)), (nat_lit 3258, Int.ofNat (nat_lit 338015640211200)), (nat_lit 3259, Int.ofNat (nat_lit 327299245056000)), (nat_lit 3260, Int.ofNat (nat_lit 464134050374400)), (nat_lit 3261, Int.ofNat (nat_lit 469048055414400)), (nat_lit 3262, Int.ofNat (nat_lit 460158285888000)), (nat_lit 3263, Int.ofNat (nat_lit 521735242392000)), (nat_lit 3280, Int.ofNat (nat_lit 189788705568000)), (nat_lit 3281, Int.ofNat (nat_lit 354275216064000)), (nat_lit 3282, Int.ofNat (nat_lit 355661456774400)), (nat_lit 3283, Int.ofNat (nat_lit 344788493414400)), (nat_lit 3284, Int.ofNat (nat_lit 481466730528000)), (nat_lit 3285, Int.ofNat (nat_lit 489364229692800)), (nat_lit 3286, Int.ofNat (nat_lit 425664957312000)), (nat_lit 3287, Int.ofNat (nat_lit 568330230081600)), (nat_lit 3305, Int.ofNat (nat_lit 203878555372800)), (nat_lit 3306, Int.ofNat (nat_lit 388206381024000)), (nat_lit 3307, Int.ofNat (nat_lit 382143218688000)), (nat_lit 3308, Int.ofNat (nat_lit 523631256825600)), (nat_lit 3309, Int.ofNat (nat_lit 536995434729600)), (nat_lit 3310, Int.ofNat (nat_lit 477639158169600)), (nat_lit 3311, Int.ofNat (nat_lit 626099548536000)), (nat_lit 3330, Int.ofNat (nat_lit 235368093945600)), (nat_lit 3331, Int.ofNat (nat_lit 440940625171200)), (nat_lit 3332, Int.ofNat (nat_lit 625762461139200)), (nat_lit 3333, Int.ofNat (nat_lit 603689881132800)), (nat_lit 3334, Int.ofNat (nat_lit 445497019027200)), (nat_lit 3335, Int.ofNat (nat_lit 623082726604800)), (nat_lit 3355, Int.ofNat (nat_lit 159053271632640)), (nat_lit 3356, Int.ofNat (nat_lit 480885340320000)), (nat_lit 3357, Int.ofNat (nat_lit 470906173584000)), (nat_lit 3358, Int.ofNat (nat_lit 369833052153600)), (nat_lit 3359, Int.ofNat (nat_lit 416251856059200)), (nat_lit 3380, Int.ofNat (nat_lit 342379007308800)), (nat_lit 3381, Int.ofNat (nat_lit 509142662582400)), (nat_lit 3382, Int.ofNat (nat_lit 380139266304000)), (nat_lit 3383, Int.ofNat (nat_lit 433594128945600)), (nat_lit 3405, Int.ofNat (nat_lit 125494567228800)), (nat_lit 3406, Int.ofNat (nat_lit 175501668384000)), (nat_lit 3407, Int.ofNat (nat_lit 230197672656000)), (nat_lit 3606, Int.ofNat (nat_lit 19029802176000)), (nat_lit 3607, Int.ofNat (nat_lit 29330228928000)), (nat_lit 3608, Int.ofNat (nat_lit 7420559731200)), (nat_lit 3609, Int.ofNat (nat_lit 5145488409600)), (nat_lit 3610, Int.ofNat (nat_lit 7788087023904)), (nat_lit 3611, Int.ofNat (nat_lit 2062447833600)), (nat_lit 3631, Int.ofNat (nat_lit 26235375936000)), (nat_lit 3632, Int.ofNat (nat_lit 17921797555200)), (nat_lit 3634, Int.ofNat (nat_lit 6305789971008)), (nat_lit 3636, Int.ofNat (nat_lit 1020592742400)), (nat_lit 3637, Int.ofNat (nat_lit 4103633318400)), (nat_lit 3638, Int.ofNat (nat_lit 7186673894400)), (nat_lit 3639, Int.ofNat (nat_lit 10269714470400)), (nat_lit 3640, Int.ofNat (nat_lit 13352755046400)), (nat_lit 3641, Int.ofNat (nat_lit 16435795622400)), (nat_lit 3642, Int.ofNat (nat_lit 1333149269760)), (nat_lit 3645, Int.ofNat (nat_lit 40850287632000)), (nat_lit 3646, Int.ofNat (nat_lit 83033724533760)), (nat_lit 3647, Int.ofNat (nat_lit 133205957438400)), (nat_lit 3656, Int.ofNat (nat_lit 17371338969600))]
theorem block022_data : block022 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (245154757478400 : Int) atom1569Coded) (CoefficientMerge.scale (241242485299200 : Int) atom1570Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (297199359072000 : Int) atom1571Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (289024345209600 : Int) atom1572Coded) (CoefficientMerge.scale (399561282489600 : Int) atom1573Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (392412609388800 : Int) atom1574Coded) (CoefficientMerge.scale (462642209568000 : Int) atom1575Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (532871809747200 : Int) atom1576Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (150166318579200 : Int) atom1577Coded) (CoefficientMerge.scale (283120765804800 : Int) atom1578Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (274126792262400 : Int) atom1579Coded) (CoefficientMerge.scale (265132818720000 : Int) atom1580Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (302636058278400 : Int) atom1581Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (305305962746400 : Int) atom1582Coded) (CoefficientMerge.scale (417245094604800 : Int) atom1583Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (416219977958400 : Int) atom1584Coded) (CoefficientMerge.scale (472194345823200 : Int) atom1585Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (540748493762400 : Int) atom1586Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (174054567456000 : Int) atom1587Coded) (CoefficientMerge.scale (319660112217600 : Int) atom1588Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (304563844569600 : Int) atom1589Coded) (CoefficientMerge.scale (338015640211200 : Int) atom1590Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (327299245056000 : Int) atom1591Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (464134050374400 : Int) atom1592Coded) (CoefficientMerge.scale (469048055414400 : Int) atom1593Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (460158285888000 : Int) atom1594Coded) (CoefficientMerge.scale (521735242392000 : Int) atom1595Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (189788705568000 : Int) atom1596Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (354275216064000 : Int) atom1597Coded) (CoefficientMerge.scale (355661456774400 : Int) atom1598Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (344788493414400 : Int) atom1599Coded) (CoefficientMerge.scale (481466730528000 : Int) atom1600Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (489364229692800 : Int) atom1601Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (425664957312000 : Int) atom1602Coded) (CoefficientMerge.scale (568330230081600 : Int) atom1603Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (203878555372800 : Int) atom1604Coded) (CoefficientMerge.scale (388206381024000 : Int) atom1605Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (382143218688000 : Int) atom1606Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (523631256825600 : Int) atom1607Coded) (CoefficientMerge.scale (536995434729600 : Int) atom1608Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (477639158169600 : Int) atom1609Coded) (CoefficientMerge.scale (626099548536000 : Int) atom1610Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (235368093945600 : Int) atom1611Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (440940625171200 : Int) atom1612Coded) (CoefficientMerge.scale (625762461139200 : Int) atom1613Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (603689881132800 : Int) atom1614Coded) (CoefficientMerge.scale (445497019027200 : Int) atom1615Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (623082726604800 : Int) atom1616Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (159053271632640 : Int) atom1617Coded) (CoefficientMerge.scale (480885340320000 : Int) atom1618Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (470906173584000 : Int) atom1619Coded) (CoefficientMerge.scale (369833052153600 : Int) atom1620Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (416251856059200 : Int) atom1621Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (342379007308800 : Int) atom1622Coded) (CoefficientMerge.scale (509142662582400 : Int) atom1623Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (380139266304000 : Int) atom1624Coded) (CoefficientMerge.scale (433594128945600 : Int) atom1625Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (125494567228800 : Int) atom1626Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (175501668384000 : Int) atom1627Coded) (CoefficientMerge.scale (230197672656000 : Int) atom1628Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19029802176000 : Int) atom1629Coded) (CoefficientMerge.scale (29330228928000 : Int) atom1630Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7420559731200 : Int) atom1631Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5145488409600 : Int) atom1632Coded) (CoefficientMerge.scale (7788087023904 : Int) atom1633Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2062447833600 : Int) atom1634Coded) (CoefficientMerge.scale (26235375936000 : Int) atom1635Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17921797555200 : Int) atom1636Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6305789971008 : Int) atom1637Coded) (CoefficientMerge.scale (1020592742400 : Int) atom1638Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4103633318400 : Int) atom1639Coded) (CoefficientMerge.scale (7186673894400 : Int) atom1640Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10269714470400 : Int) atom1641Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13352755046400 : Int) atom1642Coded) (CoefficientMerge.scale (16435795622400 : Int) atom1643Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1333149269760 : Int) atom1644Coded) (CoefficientMerge.scale (40850287632000 : Int) atom1645Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83033724533760 : Int) atom1646Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (133205957438400 : Int) atom1647Coded) (CoefficientMerge.scale (17371338969600 : Int) atom1648Coded)))))))) := by decide +kernel
theorem block022_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block022 := by
  rw [block022_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1569Coded_nonneg g hg hA hB) (atom1570Coded_nonneg g hg hA hB)) (add_nonneg (atom1571Coded_nonneg g hg hA hB) (add_nonneg (atom1572Coded_nonneg g hg hA hB) (atom1573Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1574Coded_nonneg g hg hA hB) (atom1575Coded_nonneg g hg hA hB)) (add_nonneg (atom1576Coded_nonneg g hg hA hB) (add_nonneg (atom1577Coded_nonneg g hg hA hB) (atom1578Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1579Coded_nonneg g hg hA hB) (atom1580Coded_nonneg g hg hA hB)) (add_nonneg (atom1581Coded_nonneg g hg hA hB) (add_nonneg (atom1582Coded_nonneg g hg hA hB) (atom1583Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1584Coded_nonneg g hg hA hB) (atom1585Coded_nonneg g hg hA hB)) (add_nonneg (atom1586Coded_nonneg g hg hA hB) (add_nonneg (atom1587Coded_nonneg g hg hA hB) (atom1588Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1589Coded_nonneg g hg hA hB) (atom1590Coded_nonneg g hg hA hB)) (add_nonneg (atom1591Coded_nonneg g hg hA hB) (add_nonneg (atom1592Coded_nonneg g hg hA hB) (atom1593Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1594Coded_nonneg g hg hA hB) (atom1595Coded_nonneg g hg hA hB)) (add_nonneg (atom1596Coded_nonneg g hg hA hB) (add_nonneg (atom1597Coded_nonneg g hg hA hB) (atom1598Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1599Coded_nonneg g hg hA hB) (atom1600Coded_nonneg g hg hA hB)) (add_nonneg (atom1601Coded_nonneg g hg hA hB) (add_nonneg (atom1602Coded_nonneg g hg hA hB) (atom1603Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1604Coded_nonneg g hg hA hB) (atom1605Coded_nonneg g hg hA hB)) (add_nonneg (atom1606Coded_nonneg g hg hA hB) (add_nonneg (atom1607Coded_nonneg g hg hA hB) (atom1608Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1609Coded_nonneg g hg hA hB) (atom1610Coded_nonneg g hg hA hB)) (add_nonneg (atom1611Coded_nonneg g hg hA hB) (add_nonneg (atom1612Coded_nonneg g hg hA hB) (atom1613Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1614Coded_nonneg g hg hA hB) (atom1615Coded_nonneg g hg hA hB)) (add_nonneg (atom1616Coded_nonneg g hg hA hB) (add_nonneg (atom1617Coded_nonneg g hg hA hB) (atom1618Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1619Coded_nonneg g hg hA hB) (atom1620Coded_nonneg g hg hA hB)) (add_nonneg (atom1621Coded_nonneg g hg hA hB) (add_nonneg (atom1622Coded_nonneg g hg hA hB) (atom1623Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1624Coded_nonneg g hg hA hB) (atom1625Coded_nonneg g hg hA hB)) (add_nonneg (atom1626Coded_nonneg g hg hA hB) (add_nonneg (atom1627Coded_nonneg g hg hA hB) (atom1628Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1629Coded_nonneg g hg hA hB) (atom1630Coded_nonneg g hg hA hB)) (add_nonneg (atom1631Coded_nonneg g hg hA hB) (add_nonneg (atom1632Coded_nonneg g hg hA hB) (atom1633Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1634Coded_nonneg g hg hA hB) (atom1635Coded_nonneg g hg hA hB)) (add_nonneg (atom1636Coded_nonneg g hg hA hB) (add_nonneg (atom1637Coded_nonneg g hg hA hB) (atom1638Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1639Coded_nonneg g hg hA hB) (atom1640Coded_nonneg g hg hA hB)) (add_nonneg (atom1641Coded_nonneg g hg hA hB) (add_nonneg (atom1642Coded_nonneg g hg hA hB) (atom1643Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1644Coded_nonneg g hg hA hB) (atom1645Coded_nonneg g hg hA hB)) (add_nonneg (atom1646Coded_nonneg g hg hA hB) (add_nonneg (atom1647Coded_nonneg g hg hA hB) (atom1648Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
