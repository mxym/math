import QDefinitions
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Nat.Choose.Basic

open scoped BigOperators

namespace BapatBounds

theorem ordered_pairs_count (n : ℕ) :
    (∑ i : Fin n, ∑ j : Fin n, if i < j then 1 else 0 : ℕ) = n.choose 2 := by
  rw [Finset.sum_comm]
  have inner (j : Fin n) : (∑ i : Fin n, if i < j then 1 else 0 : ℕ) = j.val := by
    rw [Finset.sum_boole]
    have heq : Finset.univ.filter (fun i : Fin n => i < j) = Finset.Iio j := by
      ext i
      simp
    rw [heq, Fin.card_Iio]
    rfl
  simp_rw [inner]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => j), Finset.sum_range_id, Nat.choose_two_right]

/-- Sharp uniform bound on the actual inversion count used by qPermanent. -/
theorem inversionCount_le_choose {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Bapat.inversionCount σ ≤ n.choose 2 := by
  rw [← ordered_pairs_count]
  unfold Bapat.inversionCount
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  split_ifs <;> omega

end BapatBounds
