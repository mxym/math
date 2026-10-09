import APPT.Quantum.Permutation
import Mathlib.Logic.Equiv.Set
open scoped BigOperators ComplexOrder
open Matrix
namespace APPT.Quantum
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem reindex_mul (e : κ ≃ ι) (A B : Matrix ι ι ℂ) :
    A.submatrix e e*B.submatrix e e=(A*B).submatrix e e := by
  ext i j
  change (∑ k : κ, A (e i) (e k)*B (e k) (e j)) =
    ∑ k : ι, A (e i) k*B k (e j)
  exact e.sum_comp (fun k : ι => A (e i) k*B k (e j))

@[simp] theorem reindex_one (e : κ ≃ ι) :
    (1 : Matrix ι ι ℂ).submatrix e e=1 := by
  ext i j
  simp [Matrix.submatrix, Matrix.one_apply, e.injective.eq_iff]

@[simp] theorem reindex_conjTranspose (e : κ ≃ ι) (A : Matrix ι ι ℂ) :
    (A.submatrix e e)ᴴ=Aᴴ.submatrix e e := rfl

@[simp] theorem reindex_diagonal (e : κ ≃ ι) (d : ι → ℂ) :
    (Matrix.diagonal d).submatrix e e=Matrix.diagonal (d ∘ e) := by
  ext i j
  simp [Matrix.submatrix, Matrix.diagonal_apply, e.injective.eq_iff, Function.comp_def]

noncomputable def reindexUnitary (e : κ ≃ ι) (U : Matrix.unitaryGroup ι ℂ) :
    Matrix.unitaryGroup κ ℂ :=
  ⟨(U : Matrix ι ι ℂ).submatrix e e, by
    have hl : (U : Matrix ι ι ℂ)ᴴ*U=1 := by
      simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
    have hr : (U : Matrix ι ι ℂ)*(U : Matrix ι ι ℂ)ᴴ=1 := by
      simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U
    constructor <;> simp only [Matrix.star_eq_conjTranspose, reindex_conjTranspose,
      reindex_mul, hl, hr, reindex_one]⟩

end APPT.Quantum
