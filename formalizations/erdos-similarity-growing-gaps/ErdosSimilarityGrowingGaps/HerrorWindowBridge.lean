import ErdosSimilarityGrowingGaps.HerrorActivation
import ErdosSimilarityGrowingGaps.HerrorBufferBridge
import ErdosSimilarityGrowingGaps.SequenceFiniteBlocker

namespace ErdosSimilarityGrowingGaps

/-! Membership in a global routing window supplies the activation half of the
herror estimate.  Thus a single margin bound, uniform over all template
windows, reduces the provider's pointwise herror field to the scalar buffer
comparison. -/
theorem herror_of_global_window_margin
    {Z : LogScale} {M d K : ℕ} {k : ℤ} {p α q : ℝ}
    (c : RoutingTemplate M d) (r : PowerParams (1 / (K : ℝ)) K)
    (n : ℕ) (origin span : ℝ)
    (hα : 0 < α) (hq : 0 ≤ q)
    (hmargin : ∀ i : Fin (Fintype.card (RoutingEdge M d)),
      origin + span ≤ (globalRoutingWindows c i).1 + (k : ℝ) +
        α * Z.z n)
    (hbuffer : q * (2 : ℝ) ^ (-(origin + span)) <
      routingBufferRadius c p)
    (hactive : r ∈ sequenceWindowActivations Z n k
      (globalRoutingWindows c)) :
    q * (input Z n) ^ (r.1.1 + α) < routingBufferRadius c p := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hactive
  exact herror_of_activation_buffer_margin r
    (globalRoutingWindows c i).1 origin span k α q
    (routingBufferRadius c p) hα hq hi.1 (hmargin i) hbuffer

/-! A constant exponent shift handles the finest-grid denominator.  The
margin hypothesis now displays the only genuinely asymptotic obligation:
the extra shift `C` must fit inside the activation slack. -/
theorem herror_of_global_window_margin_shift
    {Z : LogScale} {M d K : ℕ} {k : ℤ} {p α q C : ℝ}
    (c : RoutingTemplate M d) (r : PowerParams (1 / (K : ℝ)) K)
    (n : ℕ) (horigin : 1 ≤ c.origin)
    (hα : 0 < α) (hq : 0 ≤ q) (hp : 0 < p)
    (hC : q * (2 : ℝ) ^ (-C) < p / 32)
    (hmargin : ∀ i : Fin (Fintype.card (RoutingEdge M d)),
      (c.origin : ℝ) +
          (RoutingTemplate.span M c.gap c.baseLength d : ℝ) + C ≤
        (globalRoutingWindows c i).1 + (k : ℝ) + α * Z.z n)
    (hactive : r ∈ sequenceWindowActivations Z n k
      (globalRoutingWindows c)) :
    q * (input Z n) ^ (r.1.1 + α) < routingBufferRadius c p := by
  let X : ℝ := (c.origin : ℝ) +
    (RoutingTemplate.span M c.gap c.baseLength d : ℝ)
  have hbuffer : q * (2 : ℝ) ^ (-(X + C)) <
      p / (8 * (2 : ℝ) ^ (X + 2)) :=
    herror_buffer_compare_bridge p q X C hp hq hC
  have hroute : routingBufferRadius c p =
      p / (8 * (2 : ℝ) ^ (X + 2)) := by
    unfold routingBufferRadius routingFinestGrid routingFinestEndpoint
    have hexp : c.origin + RoutingTemplate.span M c.gap c.baseLength d - 1 + 3 =
        c.origin + RoutingTemplate.span M c.gap c.baseLength d + 2 := by omega
    rw [hexp]
    rw [Nat.cast_pow]
    norm_num only [Nat.cast_ofNat]
    have hpow :
        (2 : ℝ) ^ (c.origin + RoutingTemplate.span M c.gap c.baseLength d + 2) =
          (2 : ℝ) ^ ((c.origin : ℝ) +
            (RoutingTemplate.span M c.gap c.baseLength d : ℝ) + 2) := by
      rw [← Real.rpow_natCast]
      congr 1
      norm_num
    rw [hpow]
  apply herror_of_global_window_margin (Z := Z) (k := k) (p := p) c r n
    (c.origin : ℝ) (RoutingTemplate.span M c.gap c.baseLength d + C)
    hα hq
  · intro i
    simpa [X, add_assoc, add_left_comm, add_comm] using hmargin i
  · rw [hroute]
    simpa [X, add_assoc, add_left_comm, add_comm] using hbuffer
  · exact hactive

end ErdosSimilarityGrowingGaps
