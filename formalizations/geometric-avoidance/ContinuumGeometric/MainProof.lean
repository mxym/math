import ContinuumGeometric.RoutingStableProbability
import ContinuumGeometric.CountableExhaustion

/-!
Unconditional completion of the original geometric target. The concrete finite
routing law supplies the actual stable-center estimate, so the intermediate
blocker specification is proved here, rather than assumed.
-/
namespace ContinuumGeometric

open Set MeasureTheory

theorem smallCompactBlockerSpec_proved : SmallCompactBlockerSpec := by
  intro K hK k N δ hδ hδ₁
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

/-- The unchanged original target: one large compact set avoids every affine
geometric tail, simultaneously for all real ratios between zero and one. -/
theorem geometric_main_target : MainTarget :=
  mainTarget_of_smallCompactBlockerSpec smallCompactBlockerSpec_proved

end ContinuumGeometric
