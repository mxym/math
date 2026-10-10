import APPT.Quantum.Orbit
import APPT.Quantum.ExtendedConjugate

/-!
The review uses the original physical density-matrix and all-unitary APPT definitions.
The notes transpose the second factor, while the published Lean project transposes the first.
The equivalence below closes that convention bridge for every finite pair of factors.
-/
open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview
variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

def partialTransposeRight (A : Matrix (a × b) (a × b) ℂ) :
    Matrix (a × b) (a × b) ℂ := fun i j => A (i.1,j.2) (j.1,i.2)

@[simp] theorem partialTransposeRight_eq_transpose (A : Matrix (a × b) (a × b) ℂ) :
    partialTransposeRight A = (APPT.Quantum.partialTranspose A)ᵀ := rfl

theorem partialTransposeRight_posSemidef_iff (A : Matrix (a × b) (a × b) ℂ) :
    (partialTransposeRight A).PosSemidef ↔ (APPT.Quantum.partialTranspose A).PosSemidef := by
  rw [partialTransposeRight_eq_transpose, Matrix.posSemidef_transpose_iff]

theorem absolutelyPPT_right_iff (A : Matrix (a × b) (a × b) ℂ) :
    (∀ U : Matrix.unitaryGroup (a × b) ℂ,
      (partialTransposeRight ((U : Matrix (a × b) (a × b) ℂ) * A *
        (U : Matrix (a × b) (a × b) ℂ)ᴴ)).PosSemidef) ↔
    APPT.Quantum.AbsolutelyPPT A := by
  simp only [partialTransposeRight_posSemidef_iff, APPT.Quantum.AbsolutelyPPT]
end APPTReview
