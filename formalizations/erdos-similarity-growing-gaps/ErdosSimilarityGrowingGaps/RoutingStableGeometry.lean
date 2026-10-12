import ErdosSimilarityGrowingGaps.RoutingPreorder
import ErdosSimilarityGrowingGaps.GridBoundary
import ErdosSimilarityGrowingGaps.RoutingLocalHit
import ErdosSimilarityGrowingGaps.RoutingActiveGeometry

namespace ErdosSimilarityGrowingGaps

def actualStableCenters {M d : ℕ} (c : RoutingTemplate M d) : Set ℝ :=
  routingStableCenters c.predecessorBoundary c.gap

theorem stableDyadicRadius_eq_rpow (b g : ℕ) :
    stableDyadicRadius b g = (2 : ℝ) ^ (-((b : ℝ) + g)) := by
  unfold stableDyadicRadius
  rw [← Real.rpow_intCast]
  congr 1
  push_cast
  ring

theorem measurableSet_actualStableCenters {M d : ℕ} (c : RoutingTemplate M d) :
    MeasurableSet (actualStableCenters c) :=
  measurableSet_routingStableCenters _ _

theorem onePeriodic_actualStableCenters {M d : ℕ} (c : RoutingTemplate M d) :
    OnePeriodic (actualStableCenters c) := onePeriodic_routingStableCenters _ _

/-- The actual complete preorder supplies a concrete predecessor grid for
every edge. The first edge has one harmless extra stability constraint. -/
theorem unitDensity_actualStable_compl_le {M d : ℕ} (c : RoutingTemplate M d) :
    unitDensity (actualStableCenters c)ᶜ ≤
      ENNReal.ofReal ((Fintype.card (RoutingEdge M d) : ℝ) *
        (2 : ℝ) ^ ((3 : ℤ) - (c.gap : ℤ))) :=
  unitDensity_routingStable_compl_le c.predecessorBoundary c.gap

/-- Actual strict-active points at an actual stable center preserve ALL
preceding selector keys. The predecessor and its ordering are proved facts. -/
theorem actual_stable_earlier_address_agreement {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hL : 0 < c.baseLength) (hU : c.gap + 1 ≤ c.origin)
    (s₀ s₁ x : ℝ) (j : ℕ) (k : ℤ) (e : SelectorEdge M d)
    (p : PowerParams s₀ s₁) (hx : x ∈ actualStableCenters c)
    (hp : p ∈ powerActivation j k
      (c.edgeStart (RoutingTemplate.selectorRoutingEdge e))
      ((c.edgeStart (RoutingTemplate.selectorRoutingEdge e) : ℝ) +
        c.edgeLength (RoutingTemplate.selectorRoutingEdge e))) :
    EarlierAddressAgreement c x
      (powerPoint (dyadic j) ((2 : ℝ) ^ k) (x, p)) e := by
  intro f hf
  have hb := c.earlier_edgeEnd_le_predecessorBoundary hM hL
    (RoutingTemplate.selectorRoutingEdge f) (RoutingTemplate.selectorRoutingEdge e) hf
  apply active_power_coarser_preceding_gridAddress_eq s₀ s₁ x
    (c.edgeStart (RoutingTemplate.selectorRoutingEdge e))
    (c.edgeLength (RoutingTemplate.selectorRoutingEdge e)) j (c.selectorEnd f)
    (c.predecessorBoundary (RoutingTemplate.selectorRoutingEdge e)) c.gap k
    (c.predecessorBoundary_start hU _) hb p hp
  have hs := hx (RoutingTemplate.selectorRoutingEdge e)
  simpa only [stableDyadicRadius_eq_rpow] using hs

/-- The complete deterministic routing connection: at any default center node,
an actual active local success lies in B for every outcome of its center atom. -/
theorem actual_stable_local_success_mem_routedSet {M d : ℕ}
    (c : RoutingTemplate M d) (hM : 0 < M) (hd : 0 < d)
    (hL : 0 < c.baseLength) (hU : c.gap + 1 ≤ c.origin)
    (s₀ s₁ x : ℝ) (j : ℕ) (k : ℤ) (p : PowerParams s₀ s₁)
    (ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd))
    (bits : SelectorEdge M d → Bool)
    (hσ : centerExposureAtom (actualCenterExposure c x bits) ω.selectors)
    (v : InternalNode M d) (child : Fin (M - 1))
    (hprefix : (List.ofFn v.2).IsPrefix (List.ofFn (routeLeaf c hM ω.selectors x)))
    (hdefault : ∀ i : Fin (M - 1), bits ⟨v, i⟩ = false)
    (hx : x ∈ actualStableCenters c)
    (hp : p ∈ powerActivation j k
      (c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩))
      ((c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩) : ℝ) +
        c.edgeLength (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩)))
    (hsuccess : ω.selectors (selectorAddress c ⟨v, child⟩
        (powerPoint (dyadic j) ((2 : ℝ) ^ k) (x, p))) = true ∧
      ω.terminals (localTerminalAddress c hM hd ω.selectors ⟨v, child⟩
        (powerPoint (dyadic j) ((2 : ℝ) ^ k) (x, p))) = true) :
    powerPoint (dyadic j) ((2 : ℝ) ^ k) (x, p) ∈ routedSet c hM hd ω := by
  exact actual_local_success_mem_routedSet c hM hd hL ω x _ bits hσ v child hprefix hdefault
    (actual_stable_earlier_address_agreement c hM hL hU s₀ s₁ x j k ⟨v, child⟩ p hx hp)
    hsuccess

end ErdosSimilarityGrowingGaps
