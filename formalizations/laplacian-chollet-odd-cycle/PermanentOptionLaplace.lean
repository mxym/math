import Mathlib.GroupTheory.Perm.Option
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Basic.Real.Basic

namespace Chollet

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The genuine row-deleted and first-column-deleted minor of a matrix
on Option α, with the remaining row indices reindexed canonically by
swapping none with the selected deleted row. -/
def permanentOptionCofactor
    (A : Matrix (Option α) (Option α) ℝ) (j : Option α) :
    Matrix α α ℝ :=
  fun i k => A (Equiv.swap none j (some i)) (some k)

private theorem decomposeOption_none (j : Option α) (τ : Equiv.Perm α) :
    (Equiv.Perm.decomposeOption.symm (j,τ)) none = j := by
  have h := Equiv.Perm.decomposeOption.apply_symm_apply (j, τ)
  simpa only [Equiv.Perm.decomposeOption_apply, Prod.mk.injEq] using
    congrArg Prod.fst h

private theorem decomposeOption_some (j : Option α) (τ : Equiv.Perm α)
    (i : α) :
    (Equiv.Perm.decomposeOption.symm (j,τ)) (some i) =
      Equiv.swap none j (some (τ i)) := by
  simp [Equiv.Perm.decomposeOption, Equiv.optionCongr_apply]

/-- Laplace expansion of the genuine Mathlib permanent along the special
column none; no condition on the real matrix, positive or negative. -/
theorem permanent_option_laplace
    (A : Matrix (Option α) (Option α) ℝ) :
    Matrix.permanent A =
      ∑ j : Option α, A j none * Matrix.permanent (permanentOptionCofactor A j) := by
  classical
  let e := Equiv.Perm.decomposeOption (α := α)
  have hterm (j : Option α) (τ : Equiv.Perm α) :
      (∏ i : Option α, A ((e.symm (j,τ)) i) i) =
      A j none * (∏ i : α, permanentOptionCofactor A j (τ i) i) := by
    rw [Fintype.prod_option, decomposeOption_none]
    apply congrArg (fun r : ℝ => A j none * r)
    apply Finset.prod_congr rfl
    intro i _
    rw [decomposeOption_some]
    rfl
  calc
    Matrix.permanent A =
      (∑ p : Option α × Equiv.Perm α,
        ∏ i : Option α, A ((e.symm p) i) i) := by
        unfold Matrix.permanent
        exact (Equiv.sum_comp e.symm
          (fun σ : Equiv.Perm (Option α) =>
            ∏ i : Option α, A (σ i) i)).symm
    _ = (∑ j : Option α, ∑ τ : Equiv.Perm α,
        A j none * (∏ i : α, permanentOptionCofactor A j (τ i) i)) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro τ _
        exact hterm j τ
    _ = (∑ j : Option α, A j none *
        Matrix.permanent (permanentOptionCofactor A j)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.mul_sum]
        rfl

end Chollet

#print axioms Chollet.permanent_option_laplace
