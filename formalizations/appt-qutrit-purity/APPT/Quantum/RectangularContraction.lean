import APPT.Quantum.Basic
import Mathlib.Tactic.NoncommRing
open scoped BigOperators ComplexOrder
open Matrix
namespace APPT.Quantum
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- A rectangular matrix is a contraction on either side simultaneously. -/
theorem one_sub_mul_conjTranspose_posSemidef (W : Matrix m n ℂ)
    (h : (1-Wᴴ*W).PosSemidef) : (1-W*Wᴴ).PosSemidef := by
  have hh : (1-W*Wᴴ).IsHermitian := by
    simp [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
  have h1 := Matrix.posSemidef_conjTranspose_mul_self (1-W*Wᴴ)
  have h2 := h.mul_mul_conjTranspose_same W
  have he : (1-W*Wᴴ : Matrix m m ℂ) =
      (1-W*Wᴴ)ᴴ*(1-W*Wᴴ) + W*(1-Wᴴ*W)*Wᴴ := by
    rw [hh.eq]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
    abel
  rw [he]
  exact h1.add h2

end APPT.Quantum
