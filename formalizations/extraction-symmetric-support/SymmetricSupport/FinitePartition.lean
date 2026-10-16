import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

open scoped BigOperators
open Matrix

namespace SymmetricSupport

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- Number of computational words with a specified occupation. -/
def fiberCard (label : α → β) (s : β) : ℕ :=
  (Finset.univ.filter fun x => label x = s).card

theorem fiberCard_pos (label : α → β) (hsurj : Function.Surjective label) (s : β) :
    0 < fiberCard label s := by
  obtain ⟨x, hx⟩ := hsurj s
  exact Finset.card_pos.mpr ⟨x, by simp [hx]⟩

/-- The unnormalized, mutually disjoint occupation columns. -/
def occupationColumns (label : α → β) : Matrix α β ℂ :=
  fun x s => if label x = s then 1 else 0

/-- Coordinate averages on each nonempty occupation fiber. -/
noncomputable def occupationAverage (label : α → β) : Matrix β α ℂ :=
  fun s x => if label x = s then (fiberCard label s : ℂ)⁻¹ else 0

theorem average_columns (label : α → β) (hsurj : Function.Surjective label) :
    occupationAverage label * occupationColumns label = 1 := by
  classical
  ext s t
  simp only [Matrix.mul_apply, occupationAverage, occupationColumns, Matrix.one_apply]
  by_cases hst : s = t
  · subst t
    have hterm : ∀ x : α,
        (if label x = s then (fiberCard label s : ℂ)⁻¹ else 0) *
          (if label x = s then 1 else 0) =
            if label x = s then (fiberCard label s : ℂ)⁻¹ else 0 := by
      intro x
      by_cases h : label x = s <;> simp [h]
    simp_rw [hterm]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hn : (fiberCard label s : ℂ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (fiberCard_pos label hsurj s)
    change (fiberCard label s : ℂ) * (fiberCard label s : ℂ)⁻¹ = 1
    exact mul_inv_cancel₀ hn
  · rw [if_neg hst]
    apply Finset.sum_eq_zero
    intro x hx
    split_ifs with hxs hxt hxt
    · exact False.elim (hst (hxs.symm.trans hxt))
    all_goals simp

/-- Explicit orthogonal projector onto functions constant on every label fiber. -/
noncomputable def partitionProjector (label : α → β) : Matrix α α ℂ :=
  occupationColumns label * occupationAverage label

theorem partitionProjector_apply (label : α → β) (x y : α) :
    partitionProjector label x y =
      if label x = label y then (fiberCard label (label x) : ℂ)⁻¹ else 0 := by
  classical
  simp only [partitionProjector, Matrix.mul_apply, occupationColumns, occupationAverage,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases h : label x = label y
  · simp [h]
  · simp [h, Ne.symm h]

theorem partitionProjector_idempotent (label : α → β)
    (hsurj : Function.Surjective label) :
    partitionProjector label * partitionProjector label = partitionProjector label := by
  unfold partitionProjector
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (occupationAverage label),
    average_columns label hsurj, Matrix.one_mul]

theorem partitionProjector_hermitian (label : α → β) :
    (partitionProjector label).IsHermitian := by
  change (partitionProjector label)ᴴ = partitionProjector label
  ext x y
  simp only [Matrix.conjTranspose_apply, partitionProjector_apply]
  by_cases h : label x = label y
  · simp [h]
  · simp [h, Ne.symm h]

theorem partitionProjector_rank (label : α → β)
    (hsurj : Function.Surjective label) :
    (partitionProjector label).rank = Fintype.card β := by
  have h : occupationAverage label * partitionProjector label * occupationColumns label = 1 := by
    simp only [partitionProjector, ← Matrix.mul_assoc, average_columns label hsurj,
      Matrix.one_mul]
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)
  · rw [← Matrix.rank_one (R := ℂ) (n := β), ← h]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

theorem partitionProjector_mulVec_constant (label : α → β)
    (hsurj : Function.Surjective label) (v : α → ℂ)
    (hv : ∀ x y, label x = label y → v x = v y) :
    (partitionProjector label).mulVec v = v := by
  classical
  ext x
  simp only [Matrix.mulVec, dotProduct, partitionProjector_apply]
  have hterm : ∀ y, (if label x = label y then (fiberCard label (label x) : ℂ)⁻¹ else 0) * v y =
      if label y = label x then (fiberCard label (label x) : ℂ)⁻¹ * v x else 0 := by
    intro y
    by_cases h : label x = label y
    · simp [h, hv x y h]
    · simp [h, Ne.symm h]
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hn : (fiberCard label (label x) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (fiberCard_pos label hsurj (label x))
  change (fiberCard label (label x) : ℂ) *
    ((fiberCard label (label x) : ℂ)⁻¹ * v x) = v x
  rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]

end SymmetricSupport
