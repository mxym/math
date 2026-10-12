import Duality

open scoped BigOperators

namespace OrbitalMarginals

noncomputable section

variable {I J : Type*} [Fintype I] [Nonempty I] [Fintype J]

def scoreMax (A : J → I → ℝ) (i : I) (coeff : J → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (dualScore A i coeff)

def scoreMin (A : J → I → ℝ) (i : I) (coeff : J → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (dualScore A i coeff)

def oscillation (A : J → I → ℝ) (i : I) (coeff : J → ℝ) : ℝ :=
  scoreMax A i coeff - scoreMin A i coeff

theorem score_range (A : J → I → ℝ) (i : I) (coeff : J → ℝ) (g : I) :
    scoreMin A i coeff ≤ dualScore A i coeff g ∧ dualScore A i coeff g ≤ scoreMax A i coeff := by
  exact ⟨Finset.inf'_le _ (Finset.mem_univ g), Finset.le_sup' _ (Finset.mem_univ g)⟩

theorem oscillation_nonneg (A : J → I → ℝ) (i : I) (coeff : J → ℝ) :
    0 ≤ oscillation A i coeff := by
  have h := score_range A i coeff i
  dsimp [oscillation]
  linarith

theorem oscillation_pairBound (A : J → I → ℝ) (i : I) (coeff : J → ℝ) :
    PairBound A i (oscillation A i coeff) := by
  exact intervalDual_pairBound A i _
    ⟨coeff, scoreMin A i coeff, scoreMax A i coeff, score_range A i coeff, le_rfl⟩

/-- The unreduced real primal and dual attain the same sharp response.
Both the probability variables and every dual coefficient are constructed,
without any assumed strong-duality or optimization premise. -/
theorem exact_oscillation_duality (A : J → I → ℝ) (i : I) :
    ∃ p q : I → ℝ, ∃ coeff : J → ℝ,
      Probability p ∧ Probability q ∧ Match A p q ∧
      p i - q i = oscillation A i coeff ∧
      PairBound A i (p i - q i) ∧ UniformLawBound A i (p i - q i) ∧
      ∀ otherCoeff : J → ℝ, p i - q i ≤ oscillation A i otherCoeff := by
  obtain ⟨C, p, q, coeff, a, b, hC, _, hp, hq, hm, heq, hb, hu, hr, hw⟩ :=
    exact_real_primal_dual A i
  have hmax : scoreMax A i coeff ≤ b := by
    exact Finset.sup'_le _ _ fun g _ => (hr g).2
  have hmin : a ≤ scoreMin A i coeff := by
    exact Finset.le_inf' _ _ fun g _ => (hr g).1
  have hupper : oscillation A i coeff ≤ C := by
    dsimp [oscillation]
    linarith
  have hlow : C ≤ oscillation A i coeff := by
    rw [← heq]
    exact oscillation_pairBound A i coeff p q hp hq hm
  have hosc : C = oscillation A i coeff := le_antisymm hlow hupper
  refine ⟨p, q, coeff, hp, hq, hm, heq.trans hosc, ?_, ?_, ?_⟩
  · simpa only [heq] using hb
  · simpa only [heq] using hu
  · intro otherCoeff
    exact oscillation_pairBound A i otherCoeff p q hp hq hm

end
end OrbitalMarginals
