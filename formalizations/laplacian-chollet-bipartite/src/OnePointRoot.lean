import OnePointLeftEquiv
import PermanentDirectSum
import CofactorOption
import Mathlib.GroupTheory.Perm.Finite

namespace Chollet

variable {γ : Type*} [Fintype γ] [DecidableEq γ]

/-- Root-fixed permutation contribution is exactly root diagonal times
the permanent of the actual principal deletion, for arbitrary real matrices. -/
theorem option_root_fixed_contribution
    (M : Matrix (Option γ) (Option γ) ℝ) :
    (∑ σ : Equiv.Perm (Option γ),
       if σ none = none then
         ∏ i : Option γ, M (σ i) i else 0) =
      M none none * Matrix.permanent (fun i j : γ => M (some i) (some j)) := by
  classical
  have hσ (σ : Equiv.Perm (Option γ)) :
      (if σ none = none then ∏ i : Option γ, M (σ i) i else 0) =
        M none none *
          (if σ none = none then
            ∏ i ∈ (Finset.univ : Finset (Option γ)).erase none,
              M (σ i) i else 0) := by
    by_cases hf : σ none = none
    · simp only [if_pos hf]
      rw [← Finset.mul_prod_erase (Finset.univ : Finset (Option γ))
          (fun i => M (σ i) i) (Finset.mem_univ none)]
      rw [hf]
    · simp [hf]
  calc
    (∑ σ : Equiv.Perm (Option γ),
       if σ none = none then
         ∏ i : Option γ, M (σ i) i else 0) =
      (∑ σ : Equiv.Perm (Option γ),
        M none none *
          (if σ none = none then
            ∏ i ∈ (Finset.univ : Finset (Option γ)).erase none,
              M (σ i) i else 0)) := by
        apply Finset.sum_congr rfl
        intro σ _
        exact hσ σ
    _ = M none none * fixedDiagonalCoefficient M none := by
      rw [← Finset.mul_sum]
      rfl
    _ = _ := by rw [fixedDiagonalCoefficient_option]


variable {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]

private theorem rootFixed_term_zero_notLeft
    (A : Matrix (Option α) (Option α) ℝ)
    (B : Matrix (Option β) (Option β) ℝ)
    (σ : Equiv.Perm (Option (α ⊕ β)))
    (hf : σ none = none) (hL : ¬ preservesLeft σ) :
    (∏ i : Option (α ⊕ β), onePointSumMatrix A B (σ i) i) = 0 := by
  classical
  obtain ⟨u,hu⟩ := not_forall.mp hL
  cases hs : σ (some (.inl u)) with
  | none =>
    have hneq : some (Sum.inl u) = (none : Option (α ⊕ β)) :=
      σ.injective (hs.trans hf.symm)
    cases hneq
  | some s =>
    cases s with
    | inl v => exact (hu ⟨v,hs⟩).elim
    | inr v =>
      have hz :
          onePointSumMatrix A B (σ (some (.inl u))) (some (.inl u)) = 0 := by
        simp [hs, onePointSumMatrix]
      exact Finset.prod_eq_zero (Finset.mem_univ (some (.inl u))) hz

private theorem rootFixed_term_zero_notRight
    (A : Matrix (Option α) (Option α) ℝ)
    (B : Matrix (Option β) (Option β) ℝ)
    (σ : Equiv.Perm (Option (α ⊕ β)))
    (hf : σ none = none) (hR : ¬ preservesRight σ) :
    (∏ i : Option (α ⊕ β), onePointSumMatrix A B (σ i) i) = 0 := by
  classical
  obtain ⟨u,hu⟩ := not_forall.mp hR
  cases hs : σ (some (.inr u)) with
  | none =>
    have hneq : some (Sum.inr u) = (none : Option (α ⊕ β)) :=
      σ.injective (hs.trans hf.symm)
    cases hneq
  | some s =>
    cases s with
    | inl v =>
      have hz :
          onePointSumMatrix A B (σ (some (.inr u))) (some (.inr u)) = 0 := by
        simp [hs, onePointSumMatrix]
      exact Finset.prod_eq_zero (Finset.mem_univ (some (.inr u))) hz
    | inr v => exact (hu ⟨v,hs⟩).elim


private theorem preservesBoth_rootFixed
    (σ : Equiv.Perm (Option (α ⊕ β)))
    (hL : preservesLeft σ) (hR : preservesRight σ) :
    σ none = none := by
  let S : Set (Option (α ⊕ β)) :=
    Set.range (Option.some : α ⊕ β → Option (α ⊕ β))
  have hmaps : Set.MapsTo σ S S := by
    rintro _ ⟨i,rfl⟩
    cases i with
    | inl u =>
      obtain ⟨v,hv⟩ := hL u
      exact ⟨Sum.inl v, hv.symm⟩
    | inr u =>
      obtain ⟨v,hv⟩ := hR u
      exact ⟨Sum.inr v, hv.symm⟩
  have hmapsInv : Set.MapsTo σ.symm S S :=
    Equiv.Perm.perm_symm_mapsTo_of_mapsTo σ hmaps
  cases hs : σ none with
  | none => rfl
  | some u =>
    obtain ⟨v,hv⟩ := hmapsInv ⟨u,rfl⟩
    have hInv : σ.symm (some u) = none := by
      rw [←hs]
      exact σ.symm_apply_apply none
    have hContra : (some v : Option (α ⊕ β)) = none :=
      hv.trans hInv
    cases hContra


attribute [local instance] Classical.propDecidable

/-- The overlap contribution when both sides are preserved is exactly
the root-diagonal sum times both deleted-block permanents. This is
the third term needed in a universal one-point-sum permanent identity. -/
theorem onePointSum_overlap_contribution
    (A : Matrix (Option α) (Option α) ℝ)
    (B : Matrix (Option β) (Option β) ℝ) :
    (∑ σ : Equiv.Perm (Option (α ⊕ β)),
       if preservesLeft σ ∧ preservesRight σ then
         ∏ i : Option (α ⊕ β), onePointSumMatrix A B (σ i) i else 0) =
      (A none none + B none none) *
        Matrix.permanent (fun i j : α => A (some i) (some j)) *
        Matrix.permanent (fun i j : β => B (some i) (some j)) := by
  classical
  let M := onePointSumMatrix A B
  have hterm (σ : Equiv.Perm (Option (α ⊕ β))) :
      (if preservesLeft σ ∧ preservesRight σ then
        ∏ i : Option (α ⊕ β), M (σ i) i else 0) =
      (if σ none = none then
        ∏ i : Option (α ⊕ β), M (σ i) i else 0) := by
    by_cases hL : preservesLeft σ
    · by_cases hR : preservesRight σ
      · have hf := preservesBoth_rootFixed σ hL hR
        simp [hL, hR, hf]
      · by_cases hf : σ none = none
        · have hz := rootFixed_term_zero_notRight A B σ hf hR
          simp [hL, hR, hf, hz, M]
        · simp [hL, hR, hf]
    · by_cases hf : σ none = none
      · have hz := rootFixed_term_zero_notLeft A B σ hf hL
        simp [hL, hf, hz, M]
      · simp [hL, hf]
  have hrest :
      (fun i j : α ⊕ β => M (some i) (some j)) =
        directSumMatrix
          (fun i j : α => A (some i) (some j))
          (fun i j : β => B (some i) (some j)) := by
    ext i j
    cases i <;> cases j <;> rfl
  calc
    (∑ σ : Equiv.Perm (Option (α ⊕ β)),
       if preservesLeft σ ∧ preservesRight σ then
         ∏ i : Option (α ⊕ β), onePointSumMatrix A B (σ i) i else 0) =
      (∑ σ : Equiv.Perm (Option (α ⊕ β)),
       if σ none = none then
         ∏ i : Option (α ⊕ β), M (σ i) i else 0) := by
          apply Finset.sum_congr rfl
          intro σ _
          exact hterm σ
    _ = M none none *
        Matrix.permanent (fun i j : α ⊕ β => M (some i) (some j)) :=
      option_root_fixed_contribution M
    _ = (A none none + B none none) *
        (Matrix.permanent (fun i j : α => A (some i) (some j)) *
          Matrix.permanent (fun i j : β => B (some i) (some j))) := by
          rw [hrest]
          have hper :
              Matrix.permanent (directSumMatrix
                (fun i j : α => A (some i) (some j))
                (fun i j : β => B (some i) (some j))) =
                Matrix.permanent (fun i j : α => A (some i) (some j)) *
                Matrix.permanent (fun i j : β => B (some i) (some j)) :=
            permanent_directSumMatrix _ _
          calc
            M none none * Matrix.permanent
                (directSumMatrix
                  (fun i j : α => A (some i) (some j))
                  (fun i j : β => B (some i) (some j))) =
              M none none *
                (Matrix.permanent (fun i j : α => A (some i) (some j)) *
                Matrix.permanent (fun i j : β => B (some i) (some j))) :=
                  congrArg (fun z : ℝ => M none none * z) hper
            _ = _ := by dsimp [M, onePointSumMatrix]
    _ = _ := by ring

#print axioms Chollet.onePointSum_overlap_contribution

end Chollet

#print axioms Chollet.option_root_fixed_contribution
