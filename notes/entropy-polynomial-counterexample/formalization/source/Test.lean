import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
set_option maxHeartbeats 0
open Finset
namespace EntropyCounterexample
noncomputable def h (k r : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range k, x ^ (r*j) *
    ∑ v ∈ Finset.range (j+1), (-1 : ℝ) ^ (j-v) / (v+1) *
      (Nat.choose (r*v+k) k : ℝ) * (Nat.choose k (j-v) : ℝ)
example : h 11 11 (1/5) = h 11 11 (1/5) := rfl
#check Finset.sum_range_succ
#check Nat.choose
end EntropyCounterexample
