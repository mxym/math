import ErdosSimilarityGrowingGaps.HerrorActivation
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

end ErdosSimilarityGrowingGaps
