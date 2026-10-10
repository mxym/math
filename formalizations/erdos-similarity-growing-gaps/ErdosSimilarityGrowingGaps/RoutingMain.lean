import ErdosSimilarityGrowingGaps.RoutingStableProbability

namespace ErdosSimilarityGrowingGaps

open Set MeasureTheory

/-- The complete finite-routing output for one dyadic power rectangle.
All exceptional-center and table-probability obligations are discharged by the
kernel-checked stable-center and local entropy estimates. -/
theorem exists_compact_power_blocker {K : ℕ} (hK : 2 ≤ K)
    {k : ℤ} {N : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ < 1) :
    ∃ H : Set ℝ, IsOpen H ∧ OnePeriodic H ∧
      unitDensity H < ENNReal.ofReal δ ∧ CompactPowerHits H K k N := by
  let p := δ / 12
  have hp : 0 < p := by dsimp [p]; positivity
  have hp₁ : p ≤ 1 := by dsimp [p]; linarith
  obtain ⟨s⟩ := exists_routing_schedule K hK k N p hp
  obtain ⟨H, hHo, hHp, hHμ, hhit⟩ := actual_routing_blocker_of_actual_stable_miss
    hK hp hp₁ s (by
      intro x _ hx
      exact actual_stable_missed_center_probability_le s hK hp hp₁ x hx)
  refine ⟨H, hHo, hHp, hHμ.trans ?_, hhit⟩
  apply (ENNReal.ofReal_lt_ofReal_iff hδ).2
  dsimp [p]
  linarith

end ErdosSimilarityGrowingGaps
