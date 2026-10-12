import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Order.IntermediateValue

/-!
Original entropy-polynomial coefficient formula of Wakhare, k=11.
All arithmetic certificates are computations over rational numbers,
checked by Lean's kernel, not by an untrusted arithmetic oracle.
-/

namespace EntropyRoot

/-- Original inner binomial sum, specialized to k=11 and exponent s. -/
def innerCoeff (s j : ℕ) : ℚ :=
  ∑ v ∈ Finset.range (j+1),
    ((-1 : ℚ) ^ (j-v) / (v+1 : ℚ)) *
      (Nat.choose (s*v+11) 11 : ℚ) * (Nat.choose 11 (j-v) : ℚ)

/-- Original h_{11,s}(x), over rational points. -/
def hRat (s : ℕ) (x : ℚ) : ℚ :=
  ∑ j ∈ Finset.range 11, x ^ (s*j) * innerCoeff s j

/-- The positive multiplier of alpha in Wakhare's p_{11,10}. -/
def A (x : ℚ) : ℚ := 11 * (1-x^10)^11 * hRat 11 x

/-- The coefficient subtracted from alpha*A in Wakhare's p_{11,10}. -/
def B (x : ℚ) : ℚ := 10 * (1-x^11)^11 * hRat 10 x

private theorem at_one_fifth_pos : 0 < A (1/5) := by
  norm_num [A, hRat, innerCoeff, Nat.choose, Finset.sum_range_succ]
private theorem at_one_fifth_bound : B (1/5) < (117/125 : ℚ) * A (1/5) := by
  norm_num [A, B, hRat, innerCoeff, Nat.choose, Finset.sum_range_succ]

end EntropyRoot
