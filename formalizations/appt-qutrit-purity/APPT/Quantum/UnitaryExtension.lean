import APPT.Quantum.Reindex
import Mathlib.Data.Matrix.Block
open scoped BigOperators ComplexOrder
open Matrix
namespace APPT.Quantum
variable {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq τ]

noncomputable def splitEquiv (e : κ → ι) (he : Function.Injective e) :
    κ ⊕ {x : ι // x ∉ Set.range e} ≃ ι := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective e he) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range e))

@[simp] theorem splitEquiv_inl (e : κ → ι) (he : Function.Injective e) (i : κ) :
    splitEquiv e he (Sum.inl i)=e i := rfl

@[simp] theorem splitEquiv_inr (e : κ → ι) (he : Function.Injective e)
    (i : {x : ι // x ∉ Set.range e}) : splitEquiv e he (Sum.inr i)=i.val := rfl

@[simp] theorem splitEquiv_symm_embed (e : κ → ι) (he : Function.Injective e) (i : κ) :
    (splitEquiv e he).symm (e i)=Sum.inl i := by
  rw [← splitEquiv_inl e he i, Equiv.symm_apply_apply]

noncomputable def blockUnitary (U : Matrix.unitaryGroup κ ℂ) :
    Matrix.unitaryGroup (κ ⊕ τ) ℂ :=
  ⟨Matrix.fromBlocks (U : Matrix κ κ ℂ) 0 0 1, by
    have hl : (U : Matrix κ κ ℂ)ᴴ*U=1 := by
      simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
    have hr : (U : Matrix κ κ ℂ)*(U : Matrix κ κ ℂ)ᴴ=1 := by
      simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U
    constructor <;> simp [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply, hl, hr]⟩

noncomputable def extendedUnitary (e : κ → ι) (he : Function.Injective e)
    (U : Matrix.unitaryGroup κ ℂ) : Matrix.unitaryGroup ι ℂ := by
  classical
  exact reindexUnitary (splitEquiv e he).symm
    (blockUnitary (τ := {x : ι // x ∉ Set.range e}) U)

@[simp] theorem extendedUnitary_reindex (e : κ → ι) (he : Function.Injective e)
    (U : Matrix.unitaryGroup κ ℂ) :
    (extendedUnitary e he U : Matrix ι ι ℂ).submatrix (splitEquiv e he) (splitEquiv e he) =
    Matrix.fromBlocks (U : Matrix κ κ ℂ) 0 0 1 := by
  classical
  ext i j
  simp [extendedUnitary, reindexUnitary, blockUnitary, Matrix.submatrix]

end APPT.Quantum
