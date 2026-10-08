import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# The exact entropy counterexample parameter

We construct the unique positive root of `x ^ 10 * (1 + x) = 1`,
prove that it lies in `(0, 1)`, and enclose it between exact rationals.
-/

set_option autoImplicit false

namespace EntropyCounterexample

/-- The polynomial defining the parameter is strictly increasing on positive reals. -/
theorem root_polynomial_strictMono :
    StrictMonoOn (fun x : ℝ => x ^ 10 * (1 + x)) (Set.Ioi 0) := by
  intro a ha b hb hab
  change 0 < a at ha
  change 0 < b at hb
  have hp : a ^ 10 ≤ b ^ 10 := pow_le_pow_left₀ ha.le hab.le 10
  have hpos : 0 < a ^ 10 := pow_pos ha 10
  calc
    a ^ 10 * (1 + a) < a ^ 10 * (1 + b) :=
      mul_lt_mul_of_pos_left (by linarith) hpos
    _ ≤ b ^ 10 * (1 + b) := mul_le_mul_of_nonneg_right hp (by linarith)

/-- Intermediate value existence, with exact rational lower and upper bounds. -/
theorem alpha_exists :
    ∃ a : ℝ, (117 / 125 : ℝ) < a ∧ a < (937 / 1000 : ℝ) ∧
      a ^ 10 * (1 + a) = 1 := by
  have hc : Continuous (fun x : ℝ => x ^ 10 * (1 + x)) := by fun_prop
  have hlo : (117 / 125 : ℝ) ^ 10 * (1 + 117 / 125) < 1 := by norm_num
  have hhi : 1 < (937 / 1000 : ℝ) ^ 10 * (1 + 937 / 1000) := by norm_num
  have hiv := intermediate_value_Icc (show (117 / 125 : ℝ) ≤ 937 / 1000 by norm_num)
    hc.continuousOn (show (1 : ℝ) ∈ Set.Icc
      ((117 / 125 : ℝ) ^ 10 * (1 + 117 / 125))
      ((937 / 1000 : ℝ) ^ 10 * (1 + 937 / 1000)) from ⟨hlo.le, hhi.le⟩)
  obtain ⟨a, ha, heq⟩ := hiv
  refine ⟨a, ?_, ?_, heq⟩
  · exact lt_of_le_of_ne ha.1 (by intro h; subst a; linarith)
  · exact lt_of_le_of_ne ha.2 (by intro h; subst a; linarith)

/-- The positive root, selected from the intermediate value theorem. -/
noncomputable def alpha : ℝ := Classical.choose alpha_exists

theorem alpha_lower : (117 / 125 : ℝ) < alpha :=
  (Classical.choose_spec alpha_exists).1

theorem alpha_upper : alpha < (937 / 1000 : ℝ) :=
  (Classical.choose_spec alpha_exists).2.1

theorem alpha_equation : alpha ^ 10 * (1 + alpha) = 1 :=
  (Classical.choose_spec alpha_exists).2.2

theorem alpha_pos : 0 < alpha := by linarith [alpha_lower]

theorem alpha_lt_one : alpha < 1 := by linarith [alpha_upper]

/-- Positive solutions are unique; the upper bound `x < 1` is unnecessary. -/
theorem alpha_unique {x : ℝ} (hx : 0 < x) (heq : x ^ 10 * (1 + x) = 1) :
    x = alpha := by
  apply root_polynomial_strictMono.injOn hx alpha_pos
  exact heq.trans alpha_equation.symm

/-- There is exactly one solution in the open unit interval. -/
theorem alpha_existsUnique :
    ∃! a : ℝ, a ∈ Set.Ioo 0 1 ∧ a ^ 10 * (1 + a) = 1 := by
  refine ⟨alpha, ⟨⟨alpha_pos, alpha_lt_one⟩, alpha_equation⟩, ?_⟩
  intro a ha
  exact alpha_unique ha.1.1 ha.2

end EntropyCounterexample
