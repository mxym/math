import ContinuumRemainder.SampleStableProbability
import ContinuumRemainder.TopologyConclusion

/-! Unconditional completion of the stronger written target. The fixed
countable family precedes E; all real leading powers and all power-controlled
remainders are inside the single-set conclusion. -/
namespace ContinuumRemainder
open ContinuumGeometric Set
set_option autoImplicit false

theorem robustCompactBlockerSpec_proved : RobustCompactBlockerSpec := by
  intro A _hApos hA s₀ s₁ α₀ hs₀ hs₁ hα k q h _hq _hh p hp hp₁₂
  have hp₁ : p≤1 := by linarith
  obtain ⟨S⟩:=exists_sample_routing_schedule A hA s₀ s₁ α₀ hs₀ hs₁ hα k q h p hp
  have hM : 0<S.branching := by have := S.branching_ge_two; omega
  have hcost : 4*(routingFinestGrid S.template:ℝ)*
      errorRadius q k α₀ s₁ S.template.origin≤p := by
    have hn : S.template.origin+RoutingTemplate.span S.branching S.template.gap
      S.template.baseLength S.depth-1+3 = S.template.origin+
      RoutingTemplate.span S.branching S.template.gap S.template.baseLength S.depth+2 := by
        have:=S.origin_ge_four
        omega
    simpa only [routingFinestGrid,routingFinestEndpoint,hn] using S.actual_buffer_small.le
  obtain ⟨H,hHo,hHp,hμ,hhit⟩:=actual_sampled_routing_blocker_of_stable_miss A s₀ s₁ α₀ hs₀ hα
    S.sample.a S.sample.z S.sample.a_mem S.sample.a_pos S.sample.a_eq_rpow S.sample.a_tendsto
    k q h S.sample.a_tail S.template hM S.depth_pos S.length_pos
    (sampledGlobalRoutingTests S.template k) S.origin_shift_nonneg (by
      intro w
      change (S.template.origin:ℝ)≤
        S.template.edgeStart (globalRoutingEdgeEnumeration _ _ w)
      exact_mod_cast S.template.edgeStart_ge_origin (globalRoutingEdgeEnumeration _ _ w))
    p hp hp₁ hcost (sampled_stable_bad_density_le S) (by
      intro x _hx hstable
      exact sampled_stable_missed_center_probability_le S hs₀ hs₁.le hp hp₁ x hstable)
  exact ⟨H,hHo,hHp,hμ.le,hhit⟩

theorem continuum_power_target : ContinuumPowerTarget :=
  continuumPowerTarget_of_robustCompactBlockerSpec robustCompactBlockerSpec_proved

theorem compact_power_avoidance
    {ι : Type} [Countable ι] [Nonempty ι] (A : ι → Set ℝ)
    (hA : ∀ l, A l ⊆ Ioi 0 ∧ LogSyndetic (A l))
    (ε : ℝ) (hε : 0<ε) (hε₁ : ε<1) :
    ∃ K : Set ℝ, IsCompact K ∧ K ⊆ Icc (0:ℝ) 1 ∧ interior K=∅ ∧
      ENNReal.ofReal (1-ε)<MeasureTheory.volume K ∧ AvoidsPowerRemainderTails A K :=
  compact_power_avoidance_of_robustCompactBlockerSpec robustCompactBlockerSpec_proved A hA ε hε hε₁

end ContinuumRemainder
