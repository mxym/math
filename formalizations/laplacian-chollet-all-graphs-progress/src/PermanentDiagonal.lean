import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

namespace Chollet

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Increase exactly one diagonal entry, with NO positivity hypothesis. -/
def diagonalBump (A : Matrix n n ℝ) (v : n) (t : ℝ) : Matrix n n ℝ :=
  fun i j => if i = v ∧ j = v then A i j + t else A i j

/-- The derivative coefficient in the permanent expansion, using
only permutations which fix the distinguished diagonal position. -/
def fixedDiagonalCoefficient (A : Matrix n n ℝ) (v : n) : ℝ :=
  ∑ σ : Equiv.Perm n,
    if σ v = v then ∏ i ∈ (Finset.univ : Finset n).erase v, A (σ i) i else 0

private theorem diagonalBump_perm_term (A : Matrix n n ℝ) (v : n) (t : ℝ)
    (σ : Equiv.Perm n) :
    (∏ i, diagonalBump A v t (σ i) i) =
      (∏ i, A (σ i) i) +
      t * (if σ v = v then
        ∏ i ∈ (Finset.univ : Finset n).erase v, A (σ i) i else 0) := by
  classical
  by_cases hf : σ v = v
  · simp only [if_pos hf]
    have heq :
        (fun i => diagonalBump A v t (σ i) i) =
        Function.update (fun i => A (σ i) i) v (A v v + t) := by
      funext i
      by_cases hi : i = v
      · subst i
        simp [diagonalBump, hf]
      · simp [diagonalBump, Function.update, hi]
    have hconst : A (σ v) v = A v v := by rw [hf]
    rw [show (∏ i, diagonalBump A v t (σ i) i) =
      ∏ i, Function.update (fun i => A (σ i) i) v (A v v + t) i by
        exact Finset.prod_congr rfl (fun i _ => congrFun heq i)]
    rw [Finset.prod_update_of_mem (Finset.mem_univ v)]
    rw [← Finset.mul_prod_erase (Finset.univ : Finset n)
      (fun i => A (σ i) i) (Finset.mem_univ v)]
    rw [hconst]
    simp only [Finset.erase_eq]
    ring
  · simp only [if_neg hf, mul_zero, add_zero]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i = v
    · subst i
      simp [diagonalBump, hf]
    · simp [diagonalBump, hi]

theorem permanent_diagonalBump (A : Matrix n n ℝ) (v : n) (t : ℝ) :
    Matrix.permanent (diagonalBump A v t) =
      Matrix.permanent A + t * fixedDiagonalCoefficient A v := by
  classical
  simp only [Matrix.permanent, fixedDiagonalCoefficient]
  calc
    (∑ σ : Equiv.Perm n, ∏ i, diagonalBump A v t (σ i) i)
      = ∑ σ : Equiv.Perm n,
          ((∏ i, A (σ i) i) +
            t*(if σ v = v then
              ∏ i ∈ (Finset.univ : Finset n).erase v, A (σ i) i else 0)) := by
          apply Finset.sum_congr rfl
          intro σ _
          exact diagonalBump_perm_term A v t σ
    _ = (∑ σ : Equiv.Perm n, ∏ i, A (σ i) i) +
        t*(∑ σ : Equiv.Perm n, if σ v = v then
          ∏ i ∈ (Finset.univ : Finset n).erase v, A (σ i) i else 0) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]

end Chollet

#print axioms Chollet.permanent_diagonalBump
