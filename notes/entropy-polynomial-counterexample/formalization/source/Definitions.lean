import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

set_option maxHeartbeats 0
set_option maxRecDepth 10000

namespace EntropyCounterexample

/-- Equation (1.3), including the real-valued alternating coefficients. -/
noncomputable def h (k r : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range k, x ^ (r*j) *
    ∑ v ∈ Finset.range (j+1), (-1 : ℝ) ^ (j-v) / (v+1) *
      (Nat.choose (r*v+k) k : ℝ) * (Nat.choose k (j-v) : ℝ)

/-- Equation (1.4), with its algebraic parameter supplied explicitly. -/
noncomputable def p (k r : ℕ) (a x : ℝ) : ℝ :=
  a * k * (1-x^r)^k * h k k x - r * (1-x^k)^k * h k r x

noncomputable def P (x : ℝ) : ℝ :=
  (1) * x^0 +
  (352705) * x^11 +
  (60632419) * x^22 +
  (1227099358) * x^33 +
  (6330005947) * x^44 +
  (10701243741) * x^55 +
  (6330005947) * x^66 +
  (1227099358) * x^77 +
  (60632419) * x^88 +
  (352705) * x^99 +
  (1) * x^110

noncomputable def Q (x : ℝ) : ℝ :=
  (11) * x^0 +
  (1939817) * x^10 +
  (289126442) * x^20 +
  (5380098482) * x^30 +
  (25959010187) * x^40 +
  (41238382790) * x^50 +
  (22851341183) * x^60 +
  (4098130058) * x^70 +
  (181139618) * x^80 +
  (831413) * x^90 +
  (-1) * x^100

theorem h_eleven_eleven (x : ℝ) : h 11 11 x = P x := by
  norm_num [h, P, Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial, Nat.factorial]
  ring

theorem h_eleven_ten (x : ℝ) : h 11 10 x = Q x / 11 := by
  norm_num [h, Q, Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial, Nat.factorial]
  ring

end EntropyCounterexample
