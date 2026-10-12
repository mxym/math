import ErdosSimilarityGrowingGaps.VariableRateSchedule

namespace ErdosSimilarityGrowingGaps

open Filter Topology Asymptotics

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

/-! If the two affine span envelopes are sublinear, the actual late span is
  sublinear as well.  The envelope hypotheses are intentionally explicit so
  the remaining schedule proof can discharge them one factor at a time. -/
theorem lateRoutingSpan_littleO_of_envelopes
    {ι : Type*} {l : Filter ι}
    (K : ℕ) (p δ : ℝ) (D U : ι → ℝ) (L : ι → ℕ)
    (hp : 0 < p) (hδ : 0 < δ)
    (hU : Tendsto U l atTop)
    (hD : ∀ᶠ i in l, 0 ≤ D i)
    (hA : (fun i =>
      (((4 * lateBranching K p δ (D i)) ^
        lateDepth K p δ (D i) : ℕ) : ℝ) * (L i : ℝ)) =o[l] U)
    (hB : (fun i =>
      (((8 * lateBranching K p δ (D i)) ^
        (lateDepth K p δ (D i) + 1) : ℕ) : ℝ) *
        (lateStableGapExplicit K p δ (D i) : ℝ)) =o[l] U) :
    (fun i => (lateRoutingSpan K p δ (D i) (L i) : ℝ)) =o[l] U := by
  have hU₀ : ∀ᶠ i in l, 0 ≤ U i :=
    hU.eventually (eventually_ge_atTop (0 : ℝ))
  have hAB : (fun i =>
      (((4 * lateBranching K p δ (D i)) ^
        lateDepth K p δ (D i) : ℕ) : ℝ) * (L i : ℝ) +
      (((8 * lateBranching K p δ (D i)) ^
        (lateDepth K p δ (D i) + 1) : ℕ) : ℝ) *
        (lateStableGapExplicit K p δ (D i) : ℝ)) =o[l] U := hA.add hB
  apply IsLittleO.of_bound
  intro c hc
  have hbound := hAB.bound hc
  filter_upwards [hbound, hU₀, hD] with i hi hUi hDi
  have hupper := lateRoutingSpan_upper_real K p δ (D i) (L i)
    hp hδ hDi
  have hsum : 0 ≤
      (((4 * lateBranching K p δ (D i)) ^
        lateDepth K p δ (D i) : ℕ) : ℝ) * (L i : ℝ) +
      (((8 * lateBranching K p δ (D i)) ^
        (lateDepth K p δ (D i) + 1) : ℕ) : ℝ) *
        (lateStableGapExplicit K p δ (D i) : ℝ) := by positivity
  have hi' :
      (((4 * lateBranching K p δ (D i)) ^
        lateDepth K p δ (D i) : ℕ) : ℝ) * (L i : ℝ) +
      (((8 * lateBranching K p δ (D i)) ^
        (lateDepth K p δ (D i) + 1) : ℕ) : ℝ) *
        (lateStableGapExplicit K p δ (D i) : ℝ) ≤ c * U i := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hsum,
      Real.norm_eq_abs, abs_of_nonneg hUi, mul_one] using hi
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    Real.norm_eq_abs, abs_of_nonneg hUi]
  exact hupper.trans hi'

end ErdosSimilarityGrowingGaps
