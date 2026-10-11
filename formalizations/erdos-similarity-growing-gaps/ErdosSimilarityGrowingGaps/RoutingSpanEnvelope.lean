import ErdosSimilarityGrowingGaps.VariableRateSchedule

namespace ErdosSimilarityGrowingGaps

/-! The concrete finite span attached to the late, width-dependent schedule.
  The base length is kept as a natural parameter because the eventual entropy
  argument may choose it after the annulus origin is known. -/
noncomputable def lateRoutingSpan (K : ℕ) (p δ D : ℝ) (L : ℕ) : ℕ :=
  RoutingTemplate.span (lateBranching K p δ D)
    (lateStableGapExplicit K p δ D) L (lateDepth K p δ D)

theorem lateRoutingSpan_upper
    (K : ℕ) (p δ D : ℝ) (L : ℕ)
    (hp : 0 < p) (hδ : 0 < δ) (hD : 0 ≤ D) :
    lateRoutingSpan K p δ D L ≤
      (4 * lateBranching K p δ D) ^ lateDepth K p δ D * L +
        (8 * lateBranching K p δ D) ^ (lateDepth K p δ D + 1) *
          lateStableGapExplicit K p δ D := by
  unfold lateRoutingSpan
  have hM : 1 ≤ lateBranching K p δ D := by
    have hM2 := lateBranching_ge_two K p δ D
    omega
  exact routingTemplate_span_le_pow
    (lateBranching K p δ D) (lateDepth K p δ D)
    (lateStableGapExplicit K p δ D) L
    hM

theorem lateRoutingSpan_upper_real
    (K : ℕ) (p δ D : ℝ) (L : ℕ)
    (hp : 0 < p) (hδ : 0 < δ) (hD : 0 ≤ D) :
    (lateRoutingSpan K p δ D L : ℝ) ≤
      ((4 * lateBranching K p δ D) ^ lateDepth K p δ D : ℕ) * L +
        ((8 * lateBranching K p δ D) ^ (lateDepth K p δ D + 1) : ℕ) *
          lateStableGapExplicit K p δ D := by
  exact_mod_cast lateRoutingSpan_upper K p δ D L hp hδ hD

end ErdosSimilarityGrowingGaps
