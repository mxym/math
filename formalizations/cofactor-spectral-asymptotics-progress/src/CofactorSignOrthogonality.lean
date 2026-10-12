import CofactorEntropyProduct
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Exact finite orthogonality of independent sign products, including degree collisions. -/
set_option autoImplicit false
open scoped BigOperators
namespace CofactorSpectral
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

def signFactor (s : Finset V) (i : V) (b : Bool) : ℝ :=
  if i ∈ s then if b then -1 else 1 else 1

def signCharacter (ε : V → Bool) (s : Finset V) : ℝ :=
  ∏ i, signFactor s i (ε i)

theorem signCharacter_orthogonality (s t : Finset V) :
    (∑ ε : V → Bool, signCharacter ε s * signCharacter ε t) =
      if s = t then (2 : ℝ)^Fintype.card V else 0 := by
  classical
  have he : (∑ ε : V → Bool, signCharacter ε s * signCharacter ε t) =
      ∏ i : V, ∑ b : Bool, signFactor s i b * signFactor t i b := by
    unfold signCharacter
    simp_rw [← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun (i : V) (b : Bool) =>
      signFactor s i b * signFactor t i b)).symm
  rw [he]
  by_cases h : s = t
  · subst t
    rw [if_pos rfl]
    have hf : ∀ i, (∑ b : Bool, signFactor s i b * signFactor s i b) = 2 := by
      intro i
      by_cases hi : i ∈ s <;> norm_num [signFactor,hi]
    simp_rw [hf]
    simp
  · rw [if_neg h]
    obtain ⟨i,hi⟩ : ∃ i, ¬ (i ∈ s ↔ i ∈ t) := by
      apply not_forall.mp
      intro hall
      exact h (Finset.ext hall)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all [signFactor]

end
end CofactorSpectral
