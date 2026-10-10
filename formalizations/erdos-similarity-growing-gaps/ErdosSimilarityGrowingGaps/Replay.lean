import ErdosSimilarityGrowingGaps.Basic
import ErdosSimilarityGrowingGaps.First
import ErdosSimilarityGrowingGaps.Corollary
import ErdosSimilarityGrowingGaps.VariableTree

namespace ErdosSimilarityGrowingGaps
open GrowingGap

/-- Public replay roots for the formally closed sampling layer. -/
theorem replay_first_sample :
    ∀ (Z : LogScale) (v : ℝ),
      ∃ n : ℕ, v ≤ Z.z n ∧ ∀ m : ℕ, m < n → Z.z m < v := by
  intro Z v
  exact exists_first_ge Z v

theorem replay_annular_sampling :
    ∀ (Z : LogScale), ConsecutiveLogGapLittleO Z → AnnularFilling Z := by
  intro Z h
  exact consecutiveGap_implies_annularFilling h

theorem replay_variable_tree_span (b g L : ℝ) (hb : 2 ≤ b) (hg : 0 ≤ g)
    (n : ℕ) : span b g L (n + 1) + 2 * g ≤ b * (2 * b) ^ n * (L + 2 * g) :=
  uniform_span b g L hb hg n

#print axioms replay_first_sample
#print axioms replay_annular_sampling
#print axioms replay_variable_tree_span

end ErdosSimilarityGrowingGaps
