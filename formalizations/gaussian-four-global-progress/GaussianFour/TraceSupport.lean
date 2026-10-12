import Mathlib.Analysis.Matrix.Order
open Matrix
open scoped MatrixOrder
namespace GaussianFour
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Positive matrices have a nonnegative trace pairing. -/
theorem trace_psd_mul_nonneg {A B : Matrix n n ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  change 0 ≤ (A * (Cᴴ * C)).trace
  rw [Matrix.trace_mul_cycle']
  simpa only [Matrix.mul_assoc] using (hA.mul_mul_conjTranspose_same C).trace_nonneg

/-- Vanishing trace pairing of positive matrices forces their product to vanish. -/
theorem trace_psd_mul_zero_iff {A B : Matrix n n ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A * B).trace = 0 ↔ A * B = 0 := by
  constructor
  · intro hz
    obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
    obtain ⟨D, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
    change ((Cᴴ * C) * (Dᴴ * D)).trace = 0 at hz
    have ht : ((C * Dᴴ)ᴴ * (C * Dᴴ)).trace = ((Cᴴ * C) * (Dᴴ * D)).trace := by
      calc
        ((C * Dᴴ)ᴴ * (C * Dᴴ)).trace = (D * ((Cᴴ * C) * Dᴴ)).trace := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
        _ = (((Cᴴ * C) * Dᴴ) * D).trace := Matrix.trace_mul_comm _ _
        _ = ((Cᴴ * C) * (Dᴴ * D)).trace := by rw [Matrix.mul_assoc]
    have hCD : C * Dᴴ = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp (ht.trans hz)
    change (Cᴴ * C) * (Dᴴ * D) = 0
    calc
      (Cᴴ * C) * (Dᴴ * D) = Cᴴ * ((C * Dᴴ) * D) := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hCD, zero_mul, mul_zero]
  · intro h; rw [h, Matrix.trace_zero]
end GaussianFour
