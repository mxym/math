import GaussianRegularValue
import GaussianHalfspaceFlux
import GaussianEquidistantRigidity
import Mathlib.Tactic

/-!
Elementary exact three-label Gaussian width development.
The key identity uses the range of three jointly centered Gaussian scores.
No Gaussian multi-bubble perimeter theorem or geometric regularity axiom
is assumed. The final Gaussian average is developed in another module.
-/

open MeasureTheory ProbabilityTheory Module Matrix
open scoped RealInnerProductSpace

namespace GaussianMeasureBridge

/-- The range of three real numbers equals half the sum of pairwise
absolute differences; the second maximum is the negative minimum. -/
theorem max_three_plus_negative (a b c : ℝ) :
    max a (max b c) + max (-a) (max (-b) (-c)) =
      (|a-b|+|a-c|+|b-c|)/2 := by
  simp only [max_def, abs_def]
  split_ifs <;> linarith

theorem scoreMax_three_zero {d : ℕ}
    (v : Fin 3 → Space d) (x : Space d) :
    scoreMax v 0 x = max (⟪v 0,x⟫) (max (⟪v 1,x⟫) (⟪v 2,x⟫)) := by
  apply le_antisymm
  · unfold scoreMax
    refine Finset.sup'_le _ _ ?_
    intro i _
    fin_cases i
    · simpa only [Pi.zero_apply,sub_zero] using
        (le_max_left (⟪v 0,x⟫) (max (⟪v 1,x⟫) (⟪v 2,x⟫)))
    · simpa only [Pi.zero_apply,sub_zero] using
        ((le_max_left (⟪v 1,x⟫) (⟪v 2,x⟫)).trans
          (le_max_right (⟪v 0,x⟫) (max (⟪v 1,x⟫) (⟪v 2,x⟫))))
    · simpa only [Pi.zero_apply,sub_zero] using
        ((le_max_right (⟪v 1,x⟫) (⟪v 2,x⟫)).trans
          (le_max_right (⟪v 0,x⟫) (max (⟪v 1,x⟫) (⟪v 2,x⟫))))
  · apply max_le
    · simpa only [Pi.zero_apply,sub_zero] using le_scoreMax v 0 x 0
    · apply max_le
      · simpa only [Pi.zero_apply,sub_zero] using le_scoreMax v 0 x 1
      · simpa only [Pi.zero_apply,sub_zero] using le_scoreMax v 0 x 2

theorem expectedScore_three_neg_invariant {d : ℕ} (v : Fin 3 → Space d) :
    expectedScore (fun i => -v i) 0 = expectedScore v 0 := by
  have hg : scoreGram (fun i => -v i) = scoreGram v := by
    ext i j
    simp [scoreGram]
  exact expectedScore_eq_of_gram_eq _ _ hg 0

/-- The scalar Cauchy step for three edge lengths. -/
theorem three_nonneg_sqrt_sum_le_three
    (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (htrace : a^2+b^2+c^2 ≤ 3) : a+b+c ≤ 3 := by
  have hs : (a+b+c)^2 ≤ 3*(a^2+b^2+c^2) := by
    nlinarith [sq_nonneg (a-b),sq_nonneg (a-c),sq_nonneg (b-c)]
  nlinarith

/-- Equality in the scalar triangle Cauchy step forces three equal
edge lengths, without requiring strict positivity. -/
theorem three_nonneg_sqrt_sum_eq_three
    (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (htrace : a^2+b^2+c^2 = 3)
    (he : a+b+c = 3) : a = b ∧ b = c := by
  have h1 : (a-b)^2 + (a-c)^2 + (b-c)^2 = 0 := by
    nlinarith [sq_nonneg (a-b),sq_nonneg (a-c),sq_nonneg (b-c)]
  have hab : (a-b)^2=0 := by nlinarith [sq_nonneg (a-c),sq_nonneg (b-c)]
  have hbc : (b-c)^2=0 := by nlinarith [sq_nonneg (a-b),sq_nonneg (a-c)]
  constructor <;> nlinarith

end GaussianMeasureBridge
