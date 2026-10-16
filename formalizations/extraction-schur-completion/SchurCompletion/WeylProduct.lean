import SchurCompletion.WeylCrossRatio
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators

namespace ExtractionSchur

noncomputable section

/-- Numerical Weyl product. Its identification with dimensions of actual
Schur modules remains a separate representation-theoretic obligation. -/
def weylProduct (n : ℕ) (rows : Fin n → ℕ) : ℝ :=
  ∏ i : Fin n, ∏ j : Fin n,
    if i.val < j.val then
      ((rows i : ℝ) - (rows j : ℝ) + (j.val : ℝ) - (i.val : ℝ)) /
        ((j.val : ℝ) - (i.val : ℝ)) else 1

def padRows (s t : ℕ) (rows : Fin s → ℕ) : Fin (s+t) → ℕ :=
  Fin.addCases rows (fun _ => 0)

theorem crossShift_real (s t : ℕ) (i : Fin s) (j : Fin t) :
    (crossShift s t i j : ℝ) = (s : ℝ) + (j.val : ℝ) - (i.val : ℝ) := by
  unfold crossShift
  rw [Nat.cast_sub (by omega), Nat.cast_add]

/-- Cancels all within-support and zero-tail Weyl factors in actual finite
products. No positivity, partition sorting or representation formula is assumed. -/
theorem weylProduct_padRows (s t : ℕ) (rows : Fin s → ℕ) :
    weylProduct (s+t) (padRows s t rows) =
      weylProduct s rows * weylCrossRatio s t rows := by
  have hll (i j : Fin s) :
      (if (Fin.castAdd t i).val < (Fin.castAdd t j).val then
        ((padRows s t rows (Fin.castAdd t i) : ℝ) -
          (padRows s t rows (Fin.castAdd t j) : ℝ) +
          ((Fin.castAdd t j).val : ℝ) - ((Fin.castAdd t i).val : ℝ)) /
          (((Fin.castAdd t j).val : ℝ) - ((Fin.castAdd t i).val : ℝ)) else 1) =
      (if i.val < j.val then ((rows i : ℝ) - (rows j : ℝ) +
        (j.val : ℝ) - (i.val : ℝ)) / ((j.val : ℝ) - (i.val : ℝ)) else 1) := by
    simp [padRows]
  have hlr (i : Fin s) (j : Fin t) :
      (if (Fin.castAdd t i).val < (Fin.natAdd s j).val then
        ((padRows s t rows (Fin.castAdd t i) : ℝ) -
          (padRows s t rows (Fin.natAdd s j) : ℝ) +
          ((Fin.natAdd s j).val : ℝ) - ((Fin.castAdd t i).val : ℝ)) /
          (((Fin.natAdd s j).val : ℝ) - ((Fin.castAdd t i).val : ℝ)) else 1) =
      ((rows i : ℝ) + (crossShift s t i j : ℝ)) / (crossShift s t i j : ℝ) := by
    have hij : i.val < s+j.val := by omega
    simp only [Fin.val_castAdd, Fin.val_natAdd, hij, ite_true, padRows,
      Fin.addCases_left, Fin.addCases_right, Nat.cast_zero, sub_zero, Nat.cast_add,
      crossShift_real]
    congr 1 <;> ring
  have hrl (i : Fin t) (j : Fin s) :
      (if (Fin.natAdd s i).val < (Fin.castAdd t j).val then
        ((padRows s t rows (Fin.natAdd s i) : ℝ) -
          (padRows s t rows (Fin.castAdd t j) : ℝ) +
          ((Fin.castAdd t j).val : ℝ) - ((Fin.natAdd s i).val : ℝ)) /
          (((Fin.castAdd t j).val : ℝ) - ((Fin.natAdd s i).val : ℝ)) else 1) = 1 := by
    have hij : ¬s+i.val < j.val := by omega
    simp [hij]
  have hrr (i j : Fin t) :
      (if (Fin.natAdd s i).val < (Fin.natAdd s j).val then
        ((padRows s t rows (Fin.natAdd s i) : ℝ) -
          (padRows s t rows (Fin.natAdd s j) : ℝ) +
          ((Fin.natAdd s j).val : ℝ) - ((Fin.natAdd s i).val : ℝ)) /
          (((Fin.natAdd s j).val : ℝ) - ((Fin.natAdd s i).val : ℝ)) else 1) = 1 := by
    by_cases hij : i.val < j.val
    · have hδ : ((s+j.val : ℕ) : ℝ) - ((s+i.val : ℕ) : ℝ) ≠ 0 := by
        have hlt : ((s+i.val : ℕ) : ℝ) < ((s+j.val : ℕ) : ℝ) := by exact_mod_cast Nat.add_lt_add_left hij s
        exact sub_ne_zero.mpr (ne_of_gt hlt)
      have hδ' : (j.val : ℝ) - (i.val : ℝ) ≠ 0 := by
        exact sub_ne_zero.mpr (ne_of_gt (by exact_mod_cast hij))
      simp [padRows, hij, hδ']
    · simp [hij]
  simp only [weylProduct, Fin.prod_univ_add, hll, hlr, hrl, hrr,
    Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, weylCrossRatio]

theorem weylProduct_pos (n : ℕ) (rows : Fin n → ℕ) (hrows : Antitone rows) :
    0 < weylProduct n rows := by
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j _
  split_ifs with hij
  · have hd : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast hij
    have hr : (rows j : ℝ) ≤ (rows i : ℝ) := by exact_mod_cast hrows (le_of_lt hij)
    apply div_pos <;> linarith
  · exact zero_lt_one

theorem weylProduct_ratio_padRows (s t : ℕ) (rows : Fin s → ℕ)
    (hrows : Antitone rows) :
    weylProduct (s+t) (padRows s t rows) / weylProduct s rows = weylCrossRatio s t rows := by
  rw [weylProduct_padRows, mul_div_cancel_left₀ _ (weylProduct_pos s rows hrows).ne']

end
end ExtractionSchur
