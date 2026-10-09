import APPT.Core

open scoped BigOperators
namespace APPT

/-- First three and last six indices, with M middle positions. -/
def outerIndex (M : ℕ) : Fin 9 → Fin (3+(M+6)) :=
  ![⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩,
    ⟨M+3, by omega⟩, ⟨M+4, by omega⟩, ⟨M+5, by omega⟩,
    ⟨M+6, by omega⟩, ⟨M+7, by omega⟩, ⟨M+8, by omega⟩]

def middleIndex {M : ℕ} (i : Fin M) : Fin (3+(M+6)) :=
  ⟨3+i.val, by omega⟩

theorem outerIndex_monotone (M : ℕ) : Monotone (outerIndex M) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [outerIndex, Fin.le_iff_val_le_val] at * <;> omega

theorem split_outer_middle {M : ℕ} (f : Fin (3+(M+6)) → ℝ) :
    (∑ i, f i) = (∑ i : Fin 9, f (outerIndex M i)) +
      ∑ i : Fin M, f (middleIndex i) := by
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  simp [outerIndex, middleIndex, Fin.castAdd, Fin.natAdd, Fin.castLE]
  -- Numerically identical `Fin` indices remain syntactically distinct until
  -- their natural-number representatives are normalized explicitly.
  have htwo : (2 • (3 : Nat)) = 6 := by decide
  <;> simp only [
    show 3 + (M + 1) = M + 4 by omega,
    show 3 + (M + 2) = M + 5 by omega,
    htwo,
    show 6 + M = M + 6 by omega,
    show 3 + (M + 4) = M + 7 by omega,
    show 3 + (M + 5) = M + 8 by omega]
  <;> abel

end APPT
