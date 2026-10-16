import Extraction.RainsBudget
import Mathlib.LinearAlgebra.Matrix.Kronecker

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace Extraction

variable {ι ο κ : Type*} [Fintype ι] [Fintype ο] [Fintype κ]
  [DecidableEq ι] [DecidableEq ο]

/-- The actual finite Kraus map, on complex matrix entries. -/
def krausApply (A : κ → Matrix ο ι ℂ) (X : Matrix ι ι ℂ) : Matrix ο ο ℂ :=
  ∑ j, A j * X * (A j)ᴴ

/-- Every Kraus map is positive on actual positive matrices. -/
theorem krausApply_posSemidef (A : κ → Matrix ο ι ℂ) (X : Matrix ι ι ℂ)
    (hX : X.PosSemidef) : (krausApply A X).PosSemidef := by
  exact Matrix.posSemidef_sum Finset.univ fun j _ =>
    hX.mul_mul_conjTranspose_same (A j)

/-- Completeness implies trace preservation on every complex matrix. -/
theorem krausApply_trace (A : κ → Matrix ο ι ℂ)
    (hA : ∑ j, (A j)ᴴ * A j = 1) (X : Matrix ι ι ℂ) :
    (krausApply A X).trace = X.trace := by
  unfold krausApply
  rw [Matrix.trace_sum]
  calc
    (∑ j, (A j * X * (A j)ᴴ).trace) =
        ∑ j, ((A j)ᴴ * A j * X).trace := by
      apply Finset.sum_congr rfl
      intro j _
      exact Matrix.trace_mul_cycle _ _ _
    _ = ((∑ j, (A j)ᴴ * A j) * X).trace := by
      rw [Matrix.sum_mul, Matrix.trace_sum]
    _ = X.trace := by rw [hA, Matrix.one_mul]

/-- Actual input states remain actual states; no postselection occurs. -/
theorem krausApply_density (A : κ → Matrix ο ι ℂ)
    (hA : ∑ j, (A j)ᴴ * A j = 1) (X : Matrix ι ι ℂ)
    (hX : X.PosSemidef ∧ X.trace = 1) :
    (krausApply A X).PosSemidef ∧ (krausApply A X).trace = 1 :=
  ⟨krausApply_posSemidef A X hX.1, (krausApply_trace A hA X).trans hX.2⟩

/-- The physical auxiliary-system amplification uses identity Kraus factors. -/
def krausAmplification (A : κ → Matrix ο ι ℂ)
    (τ : Type*) [Fintype τ] [DecidableEq τ]
    (X : Matrix (ι × τ) (ι × τ) ℂ) : Matrix (ο × τ) (ο × τ) ℂ :=
  krausApply (fun j => A j ⊗ₖ (1 : Matrix τ τ ℂ)) X

/-- Complete positivity holds for every finite auxiliary system. -/
theorem krausAmplification_posSemidef (A : κ → Matrix ο ι ℂ)
    (τ : Type*) [Fintype τ] [DecidableEq τ]
    (X : Matrix (ι × τ) (ι × τ) ℂ) (hX : X.PosSemidef) :
    (krausAmplification A τ X).PosSemidef :=
  krausApply_posSemidef _ X hX

/-- The auxiliary construction agrees with the usual entrywise amplification
of the original linear map, so positivity is not asserted for a different map. -/
theorem krausAmplification_apply (A : κ → Matrix ο ι ℂ)
    (τ : Type*) [Fintype τ] [DecidableEq τ]
    (X : Matrix (ι × τ) (ι × τ) ℂ) (o p : ο) (s t : τ) :
    krausAmplification A τ X (o,s) (p,t) =
      krausApply A (fun i j => X (i,s) (j,t)) o p := by
  unfold krausAmplification krausApply
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply]
  simp [apply_ite, mul_ite, ite_mul, eq_comm]
  rfl

/-- A Kraus congruence acts on actual pure projectors by acting on their vectors. -/
theorem congruence_pure (A : Matrix ο ι ℂ) (v : ι → ℂ) :
    A * Matrix.vecMulVec v (star v) * Aᴴ =
      Matrix.vecMulVec (A *ᵥ v) (star (A *ᵥ v)) := by
  simp [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_conjTranspose]

end Extraction
