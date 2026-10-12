import APPT.Quantum.Basic
open scoped BigOperators ComplexOrder
open Matrix
namespace APPT.Quantum
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Complexification of a real matrix reflects positive semidefiniteness. -/
theorem real_posSemidef_of_complex (A : Matrix ι ι ℝ)
    (h : (A.map Complex.ofReal).PosSemidef) : A.PosSemidef := by
  have hh : A.IsHermitian := by
    ext i j
    have he := congrArg (fun B => B i j) h.isHermitian.eq
    simpa [Matrix.conjTranspose_apply, Matrix.map_apply] using he
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hh
  intro v
  have hp := h.dotProduct_mulVec_nonneg (fun i => (v i : ℂ))
  have he : ((star v ⬝ᵥ (A*ᵥv) : ℝ) : ℂ) =
      star (fun i => (v i : ℂ)) ⬝ᵥ ((A.map Complex.ofReal)*ᵥ(fun i => (v i : ℂ))) := by
    simp [dotProduct, Matrix.mulVec, Matrix.map_apply, Complex.ofReal_sum,
      Complex.ofReal_mul, star_trivial]
  rw [← he] at hp
  exact_mod_cast hp

end APPT.Quantum
