import OrbitGramPositivity
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Tactic.Ring

namespace Chollet

variable {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ]

private def permutationAssignmentAction :
    MulAction (Equiv.Perm n) (n → κ) where
  smul σ f := fun i => f (σ.symm i)
  one_smul := by
    intro f
    funext i
    rfl
  mul_smul := by
    intro σ τ f
    funext i
    change f ((σ * τ).symm i) = f (τ.symm (σ.symm i))
    simp [Equiv.Perm.mul_def]

private theorem gram_permute_assignment
    (B : κ → n → ℝ) (f : n → κ) (σ : Equiv.Perm n) :
    (∏ i, B (f i) (σ i)) =
      (∏ i, B (f (σ.symm i)) i) := by
  simpa using
    (Equiv.prod_comp σ (fun i => B (f (σ.symm i)) i))


/-- Finite real Gram matrix from an arbitrary rectangular real array. -/
def realGram (B : κ → n → ℝ) : Matrix n n ℝ :=
  fun i j => ∑ k : κ, B k i * B k j

private theorem gram_permanent_orbit_formula (B : κ → n → ℝ) :
    Matrix.permanent (realGram B) =
      ∑ f : n → κ,
        (∏ i : n, B (f i) i) *
          (∑ σ : Equiv.Perm n, ∏ i : n, B (f (σ.symm i)) i) := by
  classical
  have hexpand (σ : Equiv.Perm n) :
      (∏ i : n, ∑ k : κ, B k (σ i) * B k i) =
        ∑ f : n → κ, ∏ i : n, B (f i) (σ i) * B (f i) i :=
    Fintype.prod_sum (f := fun i (k : κ) => B k (σ i) * B k i)
  calc
    Matrix.permanent (realGram B) =
      ∑ σ : Equiv.Perm n, ∏ i : n, ∑ k : κ, B k (σ i) * B k i := by
        rfl
    _ = ∑ σ : Equiv.Perm n, ∑ f : n → κ,
        ∏ i : n, B (f i) (σ i) * B (f i) i := by
          apply Finset.sum_congr rfl
          intro σ _
          exact hexpand σ
    _ = ∑ f : n → κ, ∑ σ : Equiv.Perm n,
        ∏ i : n, B (f i) (σ i) * B (f i) i := by
          rw [Finset.sum_comm]
    _ = ∑ f : n → κ, (∏ i : n, B (f i) i) *
        (∑ σ : Equiv.Perm n, ∏ i : n, B (f (σ.symm i)) i) := by
          apply Finset.sum_congr rfl
          intro f _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro σ _
          rw [Finset.prod_mul_distrib, gram_permute_assignment]
          ring


/-- Every finite real Gram matrix has nonnegative permanent.
This is a general exact sum-of-squares proof, without requiring
entrywise nonnegative matrix entries. -/
theorem permanent_realGram_nonneg (B : κ → n → ℝ) :
    0 ≤ Matrix.permanent (realGram B) := by
  classical
  letI : MulAction (Equiv.Perm n) (n → κ) :=
    permutationAssignmentAction
  let c : (n → κ) → ℝ := fun f => ∏ i : n, B (f i) i
  have h := finiteOrbit_correlation_nonneg (G := Equiv.Perm n) c
  have hrepr :
      (∑ f : n → κ, c f * finiteOrbitSum (G := Equiv.Perm n) c f) =
      Matrix.permanent (realGram B) := by
    rw [gram_permanent_orbit_formula]
    rfl
  rw [← hrepr]
  exact h

#print axioms Chollet.permanent_realGram_nonneg

end Chollet
