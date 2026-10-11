import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! Exact cancellation criterion for an arbitrary finite branch family.
This is field algebra, including repeated zeros and the empty family. -/
noncomputable section
namespace HydrologyTree

variable {K C : Type*} [Field K] [Fintype C] [DecidableEq C]

def branchValueNumerator (p b : C → K) : K :=
  ∑ c, b c * ∏ j ∈ Finset.univ.erase c, p j

/-- At a zero of one denominator, every other summand vanishes exactly. -/
lemma branchValueNumerator_at_zero (p b : C → K) (c : C) (hc : p c = 0) :
    branchValueNumerator p b = b c * ∏ j ∈ Finset.univ.erase c, p j := by
  unfold branchValueNumerator
  rw [Finset.sum_eq_single c]
  · intro j _ hj
    have hz : (∏ i ∈ Finset.univ.erase j, p i) = 0 := by
      apply Finset.prod_eq_zero_iff.mpr
      exact ⟨c, by simp [Ne.symm hj], hc⟩
    rw [hz, mul_zero]
  · simp

/-- A local common zero is exactly either a child common zero or a collision
between two distinct child denominators, provided the connector coefficients are nonzero. -/
theorem finite_branch_cancellation_iff (d : K) (p f a : C → K) (ha : ∀ c, a c ≠ 0) :
    ((∏ c, p c) = 0 ∧ d * (∏ c, p c) - branchValueNumerator p (fun c => a c * f c) = 0) ↔
      ∃ c, p c = 0 ∧ (f c = 0 ∨ ∃ j, j ≠ c ∧ p j = 0) := by
  constructor
  · rintro ⟨hp,hN⟩
    obtain ⟨c,_,hc⟩ := Finset.prod_eq_zero_iff.mp hp
    refine ⟨c,hc,?_⟩
    rw [hp, mul_zero, zero_sub, neg_eq_zero, branchValueNumerator_at_zero p _ c hc] at hN
    have hz : f c = 0 ∨ (∏ j ∈ Finset.univ.erase c, p j) = 0 := by
      rcases mul_eq_zero.mp hN with h | h
      · exact Or.inl ((mul_eq_zero.mp h).resolve_left (ha c))
      · exact Or.inr h
    rcases hz with hf | hz
    · exact Or.inl hf
    · obtain ⟨j,hj,hp⟩ := Finset.prod_eq_zero_iff.mp hz
      exact Or.inr ⟨j, (Finset.mem_erase.mp hj).1, hp⟩
  · rintro ⟨c,hc,h⟩
    have hp : (∏ c, p c) = 0 := Finset.prod_eq_zero_iff.mpr ⟨c,Finset.mem_univ c,hc⟩
    refine ⟨hp,?_⟩
    rw [hp, mul_zero, zero_sub, neg_eq_zero, branchValueNumerator_at_zero p _ c hc]
    rcases h with hf | ⟨j,hjc,hj⟩
    · rw [hf, mul_zero, zero_mul]
    · have he : (∏ i ∈ Finset.univ.erase c, p i) = 0 :=
        Finset.prod_eq_zero_iff.mpr ⟨j, by simp [hjc], hj⟩
      rw [he, mul_zero]

end HydrologyTree
