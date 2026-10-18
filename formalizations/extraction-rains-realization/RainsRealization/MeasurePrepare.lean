import CPInterface.PPT

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace ExtractionRains
noncomputable section
variable {ι ο : Type} [Fintype ι] [Fintype ο] [DecidableEq ι] [DecidableEq ο]

/-- Actual linear measure-and-prepare map, without a CP premise. -/
def measurePrepare (E : Matrix ο ο ℂ) (F : Matrix ι ι ℂ) :
    Matrix ι ι ℂ →ₗ[ℂ] Matrix ο ο ℂ where
  toFun X := (F * X).trace • E
  map_add' X Y := by simp [Matrix.mul_add, Matrix.trace_add, add_smul]
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.trace_smul, smul_smul]

@[simp] theorem measurePrepare_apply (E : Matrix ο ο ℂ) (F X : Matrix ι ι ℂ) :
    measurePrepare E F X = (F * X).trace • E := rfl

theorem choi_measurePrepare (E : Matrix ο ο ℂ) (F : Matrix ι ι ℂ) :
    ExtractionCP.choi (measurePrepare E F) = E ⊗ₖ Fᵀ := by
  ext ⟨o,i⟩ ⟨p,j⟩
  simp [ExtractionCP.choi, measurePrepare, Matrix.trace_mul_single,
    Matrix.kroneckerMap_apply, mul_comm]

/-- Positivity of the actual two matrices proves complete positivity through
its actual Choi matrix, which is the Kronecker product E tensor F-transpose. -/
theorem measurePrepare_completelyPositive (E : Matrix ο ο ℂ) (F : Matrix ι ι ℂ)
    (hE : E.PosSemidef) (hF : F.PosSemidef) :
    ExtractionCP.CompletelyPositive (measurePrepare E F) := by
  apply (ExtractionCP.completelyPositive_iff_choi_posSemidef _).mpr
  rw [choi_measurePrepare]
  exact hE.kronecker hF.transpose

theorem completelyPositive_add {Φ Ψ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ο ο ℂ}
    (hΦ : ExtractionCP.CompletelyPositive Φ) (hΨ : ExtractionCP.CompletelyPositive Ψ) :
    ExtractionCP.CompletelyPositive (Φ + Ψ) := by
  intro τ _ _ X hX
  exact (hΦ τ X hX).add (hΨ τ X hX)

@[simp] theorem measurePrepare_trace (E : Matrix ο ο ℂ) (F X : Matrix ι ι ℂ) :
    (measurePrepare E F X).trace = (F * X).trace * E.trace := by
  simp [Matrix.trace_smul]

end
end ExtractionRains
