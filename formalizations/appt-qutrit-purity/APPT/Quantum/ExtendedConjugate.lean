import APPT.Quantum.UnitaryExtension
open scoped BigOperators ComplexOrder
open Matrix
namespace APPT.Quantum
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem split_diagonal (e : κ → ι) (he : Function.Injective e) (d : ι → ℂ) :
    Matrix.diagonal (d ∘ splitEquiv e he) =
    Matrix.fromBlocks (Matrix.diagonal (d ∘ e)) 0 0
      (Matrix.diagonal (fun x : {x : ι // x ∉ Set.range e} => d x.val)) := by
  classical
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.diagonal_apply, Matrix.fromBlocks, Function.comp_def]

/-- Extending a unitary by the identity leaves its selected corner conjugation exact. -/
theorem extendedUnitary_conjugate_entry (e : κ → ι) (he : Function.Injective e)
    (U : Matrix.unitaryGroup κ ℂ) (d : ι → ℂ) (i j : κ) :
    ((extendedUnitary e he U : Matrix ι ι ℂ)*Matrix.diagonal d*
      (extendedUnitary e he U : Matrix ι ι ℂ)ᴴ) (e i) (e j) =
    ((U : Matrix κ κ ℂ)*Matrix.diagonal (d ∘ e)*(U : Matrix κ κ ℂ)ᴴ) i j := by
  classical
  let E := splitEquiv e he
  let W : Matrix ι ι ℂ := extendedUnitary e he U
  let B : Matrix (κ ⊕ {x : ι // x ∉ Set.range e})
      (κ ⊕ {x : ι // x ∉ Set.range e}) ℂ := Matrix.fromBlocks (U : Matrix κ κ ℂ) 0 0 1
  have hW : W.submatrix E E = B := extendedUnitary_reindex e he U
  have hfull : (W*Matrix.diagonal d*Wᴴ).submatrix E E =
      B*Matrix.diagonal (d ∘ E)*Bᴴ := by
    rw [← reindex_mul, ← reindex_mul, ← reindex_conjTranspose,
      hW, reindex_diagonal]
  have h := congrArg (fun A => A (Sum.inl i) (Sum.inl j)) hfull
  rw [show E = splitEquiv e he from rfl, split_diagonal] at h
  simp only [B, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_one, Matrix.fromBlocks_multiply, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul] at h
  exact h

end APPT.Quantum
