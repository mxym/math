import InversionBounds
import Mathlib.Tactic.Push

open scoped BigOperators

namespace BapatBounds

theorem inversionCount_one (n : ℕ) : Bapat.inversionCount (1 : Equiv.Perm (Fin n)) = 0 := by
  unfold Bapat.inversionCount
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  simp only [Equiv.Perm.one_apply]
  have hfalse : ¬(i < j ∧ j < i) := fun h => (lt_asymm h.1 h.2)
  simp [hfalse]

theorem diagonal_endpointDerivative_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, i ≠ j → A i j = 0) : Bapat.endpointDerivative A = 0 := by
  classical
  unfold Bapat.endpointDerivative
  apply Finset.sum_eq_zero
  intro σ hσmem
  by_cases hσ : σ = 1
  · subst σ
    simp [inversionCount_one]
  have hex : ∃ i, σ i ≠ i := by
    by_contra hn
    push Not at hn
    apply hσ
    apply Equiv.ext
    intro i
    simpa using hn i
  obtain ⟨i, hi⟩ := hex
  have hz : Bapat.permutationWeight A σ = 0 := by
    unfold Bapat.permutationWeight
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hA i (σ i) hi.symm)
  rw [hz, mul_zero]

theorem negative_endpoint_nondiagonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hneg : (Bapat.endpointDerivative A).re < 0) :
    ∃ i j, i ≠ j ∧ A i j ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  have hz := diagonal_endpointDerivative_zero A hn
  simp [hz] at hneg

end BapatBounds
