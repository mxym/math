import APPT.UniformBridge
import APPT.SpectrumReindex

open scoped BigOperators
namespace APPT

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
      change 3+i.val ≤ M+3
      omega
    · apply hlam
      change 2 ≤ 3+i.val
      omega
  have hs := split_outer_middle lam
  have hss := split_outer_middle (fun i => (lam i)^2)
  have hp := arbitrary_middle_bound hM (lam ∘ outerIndex M) (lam ∘ middleIndex)
    hy (fun i => hn _) hx hA hB (by simpa only [Function.comp_def] using hs.symm.trans hT)
  simpa only [Function.comp_def, ← hss] using hp

end APPT
