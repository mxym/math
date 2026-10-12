import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Basic.Real.Basic

/-!
A useful genuinely quantified subtheorem for the strong Chollet project:
entrywise nonnegative matrices satisfying all two-by-two Gram bounds
obey the strong permanental inequality.  No PSD or graph assumptions
are hidden in the theorem statement.
-/

namespace Chollet

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
private theorem term_bound (A : Matrix n n ℝ)
    (hn : ∀ i j, 0 ≤ A i j)
    (hminor : ∀ i j, (A i j)^2 ≤ A i i * A j j)
    (σ : Equiv.Perm n) :
    (∏ i, A (σ i) i) ≤ (∏ i, A i i) := by
  classical
  have ht : 0 ≤ ∏ i, A (σ i) i :=
    Finset.prod_nonneg (fun i _ => hn (σ i) i)
  have hd : 0 ≤ ∏ i, A i i :=
    Finset.prod_nonneg (fun i _ => hn i i)
  have hs : (∏ i, A (σ i) i)^2 ≤ (∏ i, A i i)^2 := by
    calc
      (∏ i, A (σ i) i)^2 = ∏ i, (A (σ i) i)^2 := by
        rw [← Finset.prod_pow]
      _ ≤ ∏ i, (A (σ i) (σ i) * A i i) := by
        apply Finset.prod_le_prod₀
        · intro i _
          positivity
        · intro i _
          exact hminor (σ i) i
      _ = (∏ i, A (σ i) (σ i)) * (∏ i, A i i) := by
        rw [Finset.prod_mul_distrib]
      _ = (∏ i, A i i)^2 := by
        have hperm : (∏ i, A (σ i) (σ i)) = ∏ i, A i i :=
          Equiv.prod_comp σ (fun i => A i i)
        rw [hperm]
        ring
  nlinarith

/-- Strong Chollet is true for any entrywise nonnegative matrix that satisfies
the pairwise two-by-two determinant constraints. -/
theorem nonnegative_permanent_hadamard_bound (A : Matrix n n ℝ)
    (hn : ∀ i j, 0 ≤ A i j)
    (hminor : ∀ i j, (A i j)^2 ≤ A i i * A j j) :
    (Matrix.permanent (fun i j => A i j * A i j)) ≤
      (Matrix.permanent A) * (∏ i, A i i) := by
  classical
  simp only [Matrix.permanent]
  calc
    (∑ σ : Equiv.Perm n, ∏ i, A (σ i) i * A (σ i) i)
        = (∑ σ : Equiv.Perm n, (∏ i, A (σ i) i)^2) := by
          apply Finset.sum_congr rfl
          intro σ _
          rw [pow_two, Finset.prod_mul_distrib]
    _ ≤ ∑ σ : Equiv.Perm n,
        ((∏ i, A (σ i) i) * (∏ i, A i i)) := by
          apply Finset.sum_le_sum
          intro σ _
          have ht : 0 ≤ ∏ i, A (σ i) i :=
            Finset.prod_nonneg (fun i _ => hn (σ i) i)
          have hp := term_bound A hn hminor σ
          nlinarith [mul_nonneg ht (sub_nonneg.mpr hp)]
    _ = (∑ σ : Equiv.Perm n, ∏ i, A (σ i) i) * (∏ i, A i i) := by
          rw [Finset.sum_mul]

end Chollet
