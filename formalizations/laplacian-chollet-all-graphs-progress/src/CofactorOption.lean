import PermanentDiagonal
import Mathlib.GroupTheory.Perm.Option
import Mathlib.Basic.Real.Basic

namespace Chollet

variable {α : Type*} [Fintype α] [DecidableEq α]

private theorem prod_option_erase_none (f : Option α → ℝ) :
    (∏ i ∈ (Finset.univ : Finset (Option α)).erase none, f i) =
      ∏ i : α, f (some i) := by
  classical
  let g : Option α → ℝ := fun i => if i = none then 1 else f i
  have h1 : (∏ i ∈ (Finset.univ : Finset (Option α)).erase none, f i) =
      (∏ i ∈ (Finset.univ : Finset (Option α)).erase none, g i) := by
    apply Finset.prod_congr rfl
    intro i hi
    have hne : i ≠ none := by simpa using hi
    simp [g, hne]
  rw [h1, Finset.prod_erase (Finset.univ : Finset (Option α))
      (show g none = 1 by simp [g])]
  rw [Fintype.prod_option]
  simp [g]

private theorem decomposeOption_first
    (p : Option α × Equiv.Perm α) :
    (Equiv.Perm.decomposeOption.symm p) none = p.1 := by
  have h := Equiv.Perm.decomposeOption.apply_symm_apply p
  simpa only [Equiv.Perm.decomposeOption_apply, Prod.mk.injEq] using
    congrArg Prod.fst h


/-- The fixed-point coefficient of a permanent on Option α is exactly the
permanent of the principal submatrix obtained by deleting none. -/
theorem fixedDiagonalCoefficient_option (A : Matrix (Option α) (Option α) ℝ) :
    fixedDiagonalCoefficient A none =
      Matrix.permanent (fun i j : α => A (some i) (some j)) := by
  classical
  unfold fixedDiagonalCoefficient Matrix.permanent
  have hsum :
      (∑ σ : Equiv.Perm (Option α),
        if σ none = none then
          ∏ i ∈ (Finset.univ : Finset (Option α)).erase none,
            A (σ i) i else 0) =
      (∑ p : Option α × Equiv.Perm α,
        if (Equiv.Perm.decomposeOption.symm p) none = none then
          ∏ i ∈ (Finset.univ : Finset (Option α)).erase none,
            A ((Equiv.Perm.decomposeOption.symm p) i) i else 0) := by
    apply Fintype.sum_equiv Equiv.Perm.decomposeOption
    intro σ
    simp
  rw [hsum, Fintype.sum_prod_type, Fintype.sum_option]
  simp_rw [decomposeOption_first]
  simp only [ite_true, Option.some_ne_none, ite_false, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr rfl
  intro σ _
  rw [prod_option_erase_none]
  simp only [Equiv.Perm.decomposeOption_symm_of_none_apply, Option.map_some]

#print axioms Chollet.fixedDiagonalCoefficient_option

end Chollet
