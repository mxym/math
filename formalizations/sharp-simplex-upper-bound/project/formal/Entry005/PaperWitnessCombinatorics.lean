import Entry005.AnchorCoordinates
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Finset.Prod

noncomputable section
open scoped BigOperators

namespace Entry005

/-- The single-anchor witnesses together with one copy of each pair witness. -/
def PaperWitnessIndex (d : ℕ) : Type :=
  Sum (Fin (d + 1)) {ij : Fin (d + 1) × Fin (d + 1) // ij.1 < ij.2}

instance (d : ℕ) : Fintype (PaperWitnessIndex d) := by
  unfold PaperWitnessIndex
  infer_instance

instance (d : ℕ) : DecidableEq (PaperWitnessIndex d) := by
  unfold PaperWitnessIndex
  infer_instance

theorem paper_witness_index_card_nat (d : ℕ) :
    Fintype.card (PaperWitnessIndex d) = (d + 1) + (d + 1).choose 2 := by
  have hp : Fintype.card {ij : Fin (d + 1) × Fin (d + 1) // ij.1 < ij.2} =
      (d + 1).choose 2 := by
    rw [Fintype.card_subtype]
    simpa only [Finset.univ_product_univ, Finset.card_univ, Fintype.card_fin] using
      (Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin (d + 1)))))
  unfold PaperWitnessIndex
  rw [Fintype.card_sum, Fintype.card_fin, hp]

theorem paper_witness_index_card_real (d : ℕ) :
    (Fintype.card (PaperWitnessIndex d) : ℝ) =
      ((d : ℝ) + 1) * ((d : ℝ) + 2) / 2 := by
  rw [paper_witness_index_card_nat, Nat.cast_add, Nat.cast_choose_two]
  push_cast
  ring

/-- A sum over the strict upper triangle is the sum over the corresponding subtype. -/
theorem strict_pair_sum {n : ℕ} (f : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, if i < j then f i j else 0) =
      ∑ ij : {ij : Fin n × Fin n // ij.1 < ij.2}, f ij.val.1 ij.val.2 := by
  rw [← Fintype.sum_prod_type' (fun i j => if i < j then f i j else 0)]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

/-- Symmetry turns the half-sum over distinct ordered pairs into one sum over pairs. -/
theorem symmetric_half_off_diagonal_sum {n : ℕ} (f : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, f i j = f j i) :
    (1 / 2 : ℝ) * (∑ i, ∑ j, if i = j then 0 else f i j) =
      ∑ ij : {ij : Fin n × Fin n // ij.1 < ij.2}, f ij.val.1 ij.val.2 := by
  have hsplit : (∑ i, ∑ j, if i = j then 0 else f i j) =
      (∑ i, ∑ j, if i < j then f i j else 0) +
        ∑ i, ∑ j, if j < i then f i j else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · simp [h]
    · simp [h, (ne_of_lt h).symm, not_lt_of_ge h.le]
  have hswap : (∑ i, ∑ j, if j < i then f i j else 0) =
      ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym j i]
  rw [hsplit, hswap, ← strict_pair_sum]
  ring

end Entry005
