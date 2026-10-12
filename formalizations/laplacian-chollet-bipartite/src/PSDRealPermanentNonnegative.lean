import GramPermanentNonnegative
import PSDRealGramFactor

namespace Chollet

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem posSemidef_permanent_nonneg
    (A : Matrix n n ℝ) (hA : A.PosSemidef) :
    0 ≤ Matrix.permanent A := by
  obtain ⟨B, hB⟩ := posSemidef_realGram_factor A hA
  have heq : A = realGram B := by
    ext i j
    exact hB i j
  rw [heq]
  exact permanent_realGram_nonneg B

end Chollet

#print axioms Chollet.posSemidef_permanent_nonneg
