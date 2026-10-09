import APPT.UniformBridge

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
  simp [outerIndex, middleIndex, Fin.castAdd, Fin.natAdd]
  <;> ring

/-- Full ordered-spectrum upper bound in every total dimension M+9 ≥27. -/
theorem ordered_spectrum_large {M : ℕ} (hM : 18 ≤ M)
    (lam : Fin (3+(M+6)) → ℝ) (hlam : Antitone lam)
    (hn : ∀ i, 0 ≤ lam i) (hT : (∑ i, lam i)=1)
    (hA : (matA (lam ∘ outerIndex M)).PosSemidef)
    (hB : (matB (lam ∘ outerIndex M)).PosSemidef) :
    (∑ i, (lam i)^2) ≤ 9/(8*(9+(M : ℝ))) := by
  have hy : Antitone (lam ∘ outerIndex M) := hlam.comp_monotone (outerIndex_monotone M)
  have hx : ∀ i : Fin M,
      (lam ∘ outerIndex M) 3 ≤ (lam ∘ middleIndex) i ∧
      (lam ∘ middleIndex) i ≤ (lam ∘ outerIndex M) 2 := by
    intro i
    constructor
    · apply hlam
      simp [Function.comp_def, outerIndex, middleIndex, Fin.le_iff_val_le_val]
      omega
    · apply hlam
      simp [Function.comp_def, outerIndex, middleIndex, Fin.le_iff_val_le_val]
  have hs := split_outer_middle lam
  have hss := split_outer_middle (fun i => (lam i)^2)
  have hp := arbitrary_middle_bound hM (lam ∘ outerIndex M) (lam ∘ middleIndex)
    hy (fun i => hn _) hx hA hB (by simpa only [Function.comp_def] using hs.symm.trans hT)
  simpa only [Function.comp_def, ← hss] using hp

end APPT
