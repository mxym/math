import ErdosSimilarityGrowingGaps.VariableProviderAssembly

namespace ErdosSimilarityGrowingGaps

/-! Exact endpoint envelope for a selector window.  The coarse `5/2` envelope
in `VariableProviderAssembly` is useful for quick positivity arguments, but
the candidate-count estimate needs the actual total-span bound. -/
theorem canonical_selector_window_upper_exact
    {M d : ℕ} (c : RoutingTemplate M d) (v : InternalNode M d)
    (hM : 1 ≤ M) (hL : 0 < c.baseLength)
    (U : ℝ) (k : ℤ) (horigin : (c.origin : ℝ) = U)
    (hspan : (RoutingTemplate.span M c.gap c.baseLength d : ℝ) ≤ U) :
    ∀ child : Fin (M - 1),
      (c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩) : ℝ) +
        (vertexWindowLength c v : ℝ) + (k : ℝ) ≤
        U + (RoutingTemplate.span M c.gap c.baseLength d : ℝ) + |(k : ℝ)| := by
  intro child
  let e : RoutingEdge M d :=
    RoutingTemplate.selectorRoutingEdge ⟨v, child⟩
  have hend_nat : c.edgeStart e + c.edgeLength e ≤
      c.origin + RoutingTemplate.span M c.gap c.baseLength d := by
    have hh := (c.edgeEnd_within_total hM hL e).2
    unfold RoutingTemplate.edgeEnd at hh
    omega
  have hend : (c.edgeStart e : ℝ) + (c.edgeLength e : ℝ) ≤
      U + (RoutingTemplate.span M c.gap c.baseLength d : ℝ) := by
    have hh : (c.edgeStart e : ℝ) + (c.edgeLength e : ℝ) ≤
        (c.origin : ℝ) + (RoutingTemplate.span M c.gap c.baseLength d : ℝ) := by
      exact_mod_cast hend_nat
    simpa [horigin] using hh
  have hlen : (c.edgeLength e : ℝ) = vertexWindowLength c v := rfl
  have habs : (k : ℝ) ≤ |(k : ℝ)| := le_abs_self _
  rw [← hlen]
  calc
    (c.edgeStart e : ℝ) + (c.edgeLength e : ℝ) + (k : ℝ) =
        ((c.edgeStart e : ℝ) + (c.edgeLength e : ℝ)) + (k : ℝ) := by ring
    _ ≤ (U + (RoutingTemplate.span M c.gap c.baseLength d : ℝ)) + (k : ℝ) := by
      linarith [hend]
    _ ≤ U + (RoutingTemplate.span M c.gap c.baseLength d : ℝ) + |(k : ℝ)| := by
      linarith

end ErdosSimilarityGrowingGaps
