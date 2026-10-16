import Extraction.BellCoherent

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace Extraction

variable {d : Type*} [Fintype d] [DecidableEq d]

def swapMatrix : Matrix (d × d) (d × d) ℂ :=
  fun p q => if p.swap = q then 1 else 0

@[simp] theorem swapMatrix_mul (X : Matrix (d × d) (d × d) ℂ) :
    swapMatrix * X = X.submatrix Prod.swap id := by
  ext p q
  simp [Matrix.mul_apply, swapMatrix, ite_mul, eq_comm]

theorem swapMatrix_hermitian : (swapMatrix (d := d)).IsHermitian := by
  ext ⟨x,y⟩ ⟨z,t⟩
  by_cases hx : x = t <;> by_cases hy : y = z <;>
    simp_all [swapMatrix, Matrix.conjTranspose_apply, eq_comm]

@[simp] theorem swapMatrix_square : (swapMatrix (d := d)) * swapMatrix = 1 := by
  rw [swapMatrix_mul]
  ext p q
  simp [swapMatrix, Matrix.one_apply]

/-- The swap bounds are proved by actual positive squares. -/
theorem one_add_swapMatrix_posSemidef :
    (1 + swapMatrix (d := d)).PosSemidef := by
  have hh : (1 + swapMatrix (d := d)).IsHermitian := by
    change (1 + swapMatrix (d := d))ᴴ = 1 + swapMatrix
    simp [swapMatrix_hermitian.eq]
  have he : (1 + swapMatrix (d := d)) * (1 + swapMatrix)ᴴ =
      (2 : ℝ) • (1 + swapMatrix) := by
    rw [hh.eq]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      swapMatrix_square]
    module
  have hs := (Matrix.posSemidef_self_mul_conjTranspose (1 + swapMatrix (d := d))).smul
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  rw [he] at hs
  simpa only [smul_smul, one_div, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0),
    one_smul] using hs

theorem one_sub_swapMatrix_posSemidef :
    (1 - swapMatrix (d := d)).PosSemidef := by
  have hh : (1 - swapMatrix (d := d)).IsHermitian := by
    change (1 - swapMatrix (d := d))ᴴ = 1 - swapMatrix
    simp [swapMatrix_hermitian.eq]
  have he : (1 - swapMatrix (d := d)) * (1 - swapMatrix)ᴴ =
      (2 : ℝ) • (1 - swapMatrix) := by
    rw [hh.eq]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      swapMatrix_square]
    module
  have hs := (Matrix.posSemidef_self_mul_conjTranspose (1 - swapMatrix (d := d))).smul
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  rw [he] at hs
  simpa only [smul_smul, one_div, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0),
    one_smul] using hs

noncomputable def bellProjector : Matrix (d × d) (d × d) ℂ :=
  Matrix.vecMulVec (bellVector (bellCoeff d)) (star (bellVector (bellCoeff d)))

theorem bellProjector_idempotent [Nonempty d] :
    bellProjector (d := d) * bellProjector = bellProjector := by
  have hn : star (bellVector (d := d) (bellCoeff d)) ⬝ᵥ
      bellVector (d := d) (bellCoeff d) = 1 := by
    simpa [Matrix.trace_vecMulVec, dotProduct_comm] using
      (bellProjector_density (d := d)).2
  simp [bellProjector, Matrix.vecMulVec_mul_vecMulVec, hn]

theorem one_sub_bellProjector_posSemidef [Nonempty d] :
    (1 - bellProjector (d := d)).PosSemidef := by
  have hh : (1 - bellProjector (d := d)).IsHermitian := by
    change (1 - bellProjector (d := d))ᴴ = 1 - bellProjector
    simp [bellProjector, Matrix.conjTranspose_vecMulVec]
  have he : (1 - bellProjector (d := d)) * (1 - bellProjector)ᴴ =
      1 - bellProjector := by
    rw [hh.eq]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      bellProjector_idempotent]
    abel
  rw [← he]
  exact Matrix.posSemidef_self_mul_conjTranspose _

theorem bellCoeff_mul_star [Nonempty d] :
    bellCoeff d * star (bellCoeff d) = ((1 / (Fintype.card d : ℝ) : ℝ) : ℂ) := by
  have hc : (Fintype.card d : ℂ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card d ≠ 0)
  have h := bellCoeff_normalized (d := d)
  have hr : bellCoeff d * star (bellCoeff d) = 1 / (Fintype.card d : ℂ) := by
    apply (eq_div_iff hc).mpr
    convert h using 1 <;> ring
  simpa using hr

/-- The maximally entangled projector's physical partial transpose is swap/K. -/
theorem partialTranspose_bellProjector [Nonempty d] :
    APPT.Quantum.partialTranspose (bellProjector (d := d)) =
      (1 / (Fintype.card d : ℝ)) • swapMatrix := by
  ext ⟨x,y⟩ ⟨z,t⟩
  by_cases hx : x = t <;> by_cases hy : y = z <;>
    simp_all [APPT.Quantum.partialTranspose, bellProjector, Matrix.vecMulVec_apply,
      bellVector, swapMatrix, Matrix.smul_apply, Complex.real_smul,
      eq_comm]
  simpa using (bellCoeff_mul_star (d := d)).symm

theorem bellProjector_pt_order [Nonempty d] :
    ((1 / (Fintype.card d : ℝ)) • (1 : Matrix (d × d) (d × d) ℂ) +
      APPT.Quantum.partialTranspose (bellProjector (d := d))).PosSemidef ∧
    ((1 / (Fintype.card d : ℝ)) • (1 : Matrix (d × d) (d × d) ℂ) -
      APPT.Quantum.partialTranspose (bellProjector (d := d))).PosSemidef := by
  rw [partialTranspose_bellProjector]
  constructor
  · simpa only [smul_add] using one_add_swapMatrix_posSemidef.smul
      (show (0 : ℝ) ≤ 1 / (Fintype.card d : ℝ) by positivity)
  · simpa only [smul_sub] using one_sub_swapMatrix_posSemidef.smul
      (show (0 : ℝ) ≤ 1 / (Fintype.card d : ℝ) by positivity)

end Extraction
