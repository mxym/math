/-
  Partial Lean 4 formalization of the universal exact subset-action modulus.

  Scope of THIS file:
  If a rational constraint matrix has a first row of ones, any vector in
  its matrix kernel has total signed mass zero. This is a first, generic,
  kernel-checked statement; it does NOT prove the full maximal-minor
  formula, the rank product, or the cycle-index identity.

  No sorry, custom axiom, or external solver assumption occurs.
-/
import Mathlib.Data.Matrix.Basic

open scoped BigOperators

namespace OrbitExact

variable {r p : ℕ}

theorem mass_zero_of_first_row_ones
    (A : Matrix (Fin (r + 1)) (Fin p) ℚ)
    (v : Fin p → ℚ)
    (hrow : ∀ j, A 0 j = 1)
    (hker : A.mulVec v = 0) :
    (∑ j : Fin p, v j) = 0 := by
  have hzero : (A.mulVec v) 0 = 0 := by
    simpa using congrArg (fun f : Fin (r + 1) → ℚ => f 0) hker
  simpa [Matrix.mulVec, dotProduct, hrow] using hzero

end OrbitExact
