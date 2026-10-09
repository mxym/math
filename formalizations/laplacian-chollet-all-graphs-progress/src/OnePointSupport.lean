import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Basic.Real.Basic

namespace Chollet

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- Single-vertex coalescence of two real square matrices,
without any PSD or symmetry hypothesis. Every cross-side entry is zero.
The root diagonal is the sum of the two original root diagonals. -/
def onePointSumMatrix
    (A : Matrix (Option α) (Option α) ℝ)
    (B : Matrix (Option β) (Option β) ℝ) :
    Matrix (Option (α ⊕ β)) (Option (α ⊕ β)) ℝ :=
  fun i j =>
    match i,j with
    | none, none => A none none + B none none
    | none, some (.inl i) => A none (some i)
    | none, some (.inr j) => B none (some j)
    | some (.inl i), none => A (some i) none
    | some (.inr i), none => B (some i) none
    | some (.inl i), some (.inl j) => A (some i) (some j)
    | some (.inr i), some (.inr j) => B (some i) (some j)
    | some (.inl _), some (.inr _) => 0
    | some (.inr _), some (.inl _) => 0

/-- Every left-side column is sent by the permutation to a left-side row. -/
def preservesLeft (σ : Equiv.Perm (Option (α ⊕ β))) : Prop :=
  ∀ i : α, ∃ j : α, σ (some (.inl i)) = some (.inl j)

/-- Every right-side column is sent to a right-side row. -/
def preservesRight (σ : Equiv.Perm (Option (α ⊕ β))) : Prop :=
  ∀ i : β, ∃ j : β, σ (some (.inr i)) = some (.inr j)

/-- In a one-point sum, a nonzero permanent permutation term must preserve
at least one side in full: two distinct side columns cannot both map into the
unique coalesced root row. This holds for all finite side sizes, including zero. -/
theorem onePointSum_term_zero_of_no_preserved_side
    (A : Matrix (Option α) (Option α) ℝ)
    (B : Matrix (Option β) (Option β) ℝ)
    (σ : Equiv.Perm (Option (α ⊕ β)))
    (hL : ¬ preservesLeft σ)
    (hR : ¬ preservesRight σ) :
    (∏ i : Option (α ⊕ β), onePointSumMatrix A B (σ i) i) = 0 := by
  classical
  obtain ⟨u, hu⟩ := not_forall.mp hL
  obtain ⟨v, hv⟩ := not_forall.mp hR
  cases hsu : σ (some (.inl u)) with
  | none =>
    cases hsv : σ (some (.inr v)) with
    | none =>
      have hEq : (some (.inl u) : Option (α ⊕ β)) = some (.inr v) :=
        σ.injective (hsu.trans hsv.symm)
      cases hEq
    | some x =>
      cases x with
      | inl k =>
        have hzero :
            onePointSumMatrix A B (σ (some (.inr v))) (some (.inr v)) = 0 := by
          simp [onePointSumMatrix, hsv]
        exact Finset.prod_eq_zero (Finset.mem_univ (some (.inr v))) hzero
      | inr k =>
        exact (hv ⟨k, hsv⟩).elim
  | some x =>
    cases x with
    | inl k =>
      exact (hu ⟨k, hsu⟩).elim
    | inr k =>
      have hzero :
          onePointSumMatrix A B (σ (some (.inl u))) (some (.inl u)) = 0 := by
        simp [onePointSumMatrix, hsu]
      exact Finset.prod_eq_zero (Finset.mem_univ (some (.inl u))) hzero


attribute [local instance] Classical.propDecidable

/-- Exact inclusion-exclusion decomposition of the permanent of any one-point
sum into terms preserving the left side, preserving the right side, and their
overlap. The off-diagonal inter-side zeros are used through the actual
permutation-sum definition, not an assumed gluing identity. -/
theorem onePointSum_permanent_support_decomposition
    (A : Matrix (Option α) (Option α) ℝ)
    (B : Matrix (Option β) (Option β) ℝ) :
    Matrix.permanent (onePointSumMatrix A B) =
      (∑ σ : Equiv.Perm (Option (α ⊕ β)),
        if preservesLeft σ then
          ∏ i, onePointSumMatrix A B (σ i) i else 0) +
      (∑ σ : Equiv.Perm (Option (α ⊕ β)),
        if preservesRight σ then
          ∏ i, onePointSumMatrix A B (σ i) i else 0) -
      (∑ σ : Equiv.Perm (Option (α ⊕ β)),
        if preservesLeft σ ∧ preservesRight σ then
          ∏ i, onePointSumMatrix A B (σ i) i else 0) := by
  classical
  unfold Matrix.permanent
  calc
    (∑ σ : Equiv.Perm (Option (α ⊕ β)),
        ∏ i, onePointSumMatrix A B (σ i) i)
      = ∑ σ : Equiv.Perm (Option (α ⊕ β)),
        ((if preservesLeft σ then
           ∏ i, onePointSumMatrix A B (σ i) i else 0) +
         (if preservesRight σ then
           ∏ i, onePointSumMatrix A B (σ i) i else 0) -
         (if preservesLeft σ ∧ preservesRight σ then
           ∏ i, onePointSumMatrix A B (σ i) i else 0)) := by
        apply Finset.sum_congr rfl
        intro σ _
        by_cases hL : preservesLeft σ
        · by_cases hR : preservesRight σ <;> simp [hL,hR]
        · by_cases hR : preservesRight σ
          · simp [hL,hR]
          · have hz := onePointSum_term_zero_of_no_preserved_side A B σ hL hR
            simp [hL,hR,hz]
    _ = (∑ σ : Equiv.Perm (Option (α ⊕ β)),
          if preservesLeft σ then
            ∏ i, onePointSumMatrix A B (σ i) i else 0) +
        (∑ σ : Equiv.Perm (Option (α ⊕ β)),
          if preservesRight σ then
            ∏ i, onePointSumMatrix A B (σ i) i else 0) -
        (∑ σ : Equiv.Perm (Option (α ⊕ β)),
          if preservesLeft σ ∧ preservesRight σ then
            ∏ i, onePointSumMatrix A B (σ i) i else 0) := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]

#print axioms Chollet.onePointSum_permanent_support_decomposition

end Chollet

#print axioms Chollet.onePointSum_term_zero_of_no_preserved_side
