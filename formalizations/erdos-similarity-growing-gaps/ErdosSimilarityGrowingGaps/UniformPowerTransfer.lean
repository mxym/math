import ErdosSimilarityGrowingGaps.RoutingSequenceBridge
import ErdosSimilarityGrowingGaps.RobustExhaustion

namespace ErdosSimilarityGrowingGaps

open Set MeasureTheory

/-!
A single typed package for the remaining sequence bridge.  Its `data` field
contains the finite power-routing outcome and the full-tail sample transfer;
`compactRobustSpec_of_uniformPowerTransfer` is a purely logical assembly of
that data into `CompactRobustSpec`.  In particular, the structure does not
hide an existence or probability axiom: every activation, point, tail, error,
and density condition is an explicit field.
-/
structure UniformPowerTransferSpec (Z : LogScale) : Prop where
  data : ∀ (K : ℕ), 2 ≤ K → ∀ (k : ℤ) (N : ℕ) (α q δ : ℝ),
    0 < α → 0 ≤ q → 0 < δ → δ < 1 →
    ∃ (p : ℝ) (G : Set ℝ) (ρ : ℝ) (tests : Finset ℕ) (W : ℕ)
      (windows : Fin W → ℝ × ℝ) (sample : ℕ → ℕ),
      0 < p ∧ 6 * p < δ ∧ OnePeriodic G ∧ 0 < ρ ∧
      (∀ n : ℕ, n ∈ tests →
        ∀ r₀ : PowerParams (1 / (K : ℝ)) K,
          r₀ ∈ windowActivations n k windows →
          r₀ ∈ sequenceWindowActivations Z (sample n) k windows) ∧
      (∀ (n : ℕ), n ∈ tests → ∀ (x : ℝ)
        (r₀ : PowerParams (1 / (K : ℝ)) K),
        powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, r₀) ∈ G →
        powerPoint (input Z (sample n)) ((2 : ℝ) ^ k) (x, r₀) ∈
          Metric.thickening ρ G) ∧
      (∀ n : ℕ, n ∈ tests.image sample → N ≤ n) ∧
      (∀ (r₀ : PowerParams (1 / (K : ℝ)) K) (n : ℕ),
        n ∈ tests.image sample →
        r₀ ∈ sequenceWindowActivations Z n k windows →
          q * (input Z n) ^ (r₀.1.1 + α) < ρ) ∧
      (unitDensity (Metric.thickening (2 * ρ) G) +
        unitDensity (powerMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
          tests k windows G) ≤ ENNReal.ofReal (5 * p))

/-- The explicit finite transfer package implies the full compact robust
specification. -/
theorem compactRobustSpec_of_uniformPowerTransfer
    {Z : LogScale} (hT : UniformPowerTransferSpec Z) :
    CompactRobustSpec Z := by
  intro K hK k N α q hα hq δ hδ hδ₁
  obtain ⟨p, G, ρ, tests, W, windows, sample, hp, hpδ, hGp, hρ,
      hactivate, hpoint, htail, herror, houtcome⟩ :=
    hT.data K hK k N α q δ hα hq hδ hδ₁
  obtain ⟨H, hHo, hHp, hHμ, hHhit⟩ :=
    periodic_sequence_blocker_of_power_transfer (Z := Z) hK tests k windows G hGp
      ρ p hρ hp sample hactivate hpoint N htail α q hα hq herror houtcome
  exact ⟨H, hHo, hHp,
    hHμ.trans ((ENNReal.ofReal_lt_ofReal_iff (by linarith [hpδ])).2 hpδ), hHhit⟩

end ErdosSimilarityGrowingGaps
