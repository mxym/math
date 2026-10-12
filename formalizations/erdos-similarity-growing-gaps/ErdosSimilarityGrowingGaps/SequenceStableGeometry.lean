import ErdosSimilarityGrowingGaps.RoutingStableGeometry
import ErdosSimilarityGrowingGaps.SequenceGeometry

namespace ErdosSimilarityGrowingGaps

/-- Stable predecessor keys also control points sampled at the actual logarithm.
The proof uses only the open activation range, so no dyadic replacement occurs. -/
theorem sequence_active_preceding_gridAddress_eq
    (Z : LogScale) (s₀ s₁ x : ℝ) (u ell : ℕ) (n : ℕ) (k : ℤ)
    (p : PowerParams s₀ s₁) (hactive :
      sequencePowerActivation Z n k (u : ℝ) ((u : ℝ) + ell) p)
    {b₀ g : ℕ} (hu : u = b₀ + g + 1)
    (hstable : NoGridBoundary (2 ^ (b₀ + 3)) x
      (2 ^ (-((b₀ : ℝ) + g)))) :
    gridAddress b₀ (sequencePoint Z n ((2 : ℝ) ^ k) x p) = gridAddress b₀ x := by
  apply (gridAddress_eq_iff _ _ _).2
  apply periodicGridKey_eq_of_no_boundary _ (by positivity) x
    (2 ^ (-((b₀ : ℝ) + g))) _ ?_ hstable
  have hr := sequence_active_point_range Z s₀ s₁ x (u : ℝ) ((u : ℝ) + ell) n k p hactive
  have he : (1 : ℝ) - (u : ℝ) = -((b₀ : ℝ) + g) := by
    rw [hu]
    push_cast
    ring
  rw [he] at hr
  exact ⟨hr.1.le, hr.2.le⟩

theorem sequence_active_coarser_preceding_gridAddress_eq
    (Z : LogScale) (s₀ s₁ x : ℝ) (u ell : ℕ) (n : ℕ) (b b₀ g : ℕ) (k : ℤ)
    (hbu : b ≤ b₀) (hu : u = b₀ + g + 1)
    (p : PowerParams s₀ s₁)
    (hactive : sequencePowerActivation Z n k (u : ℝ) ((u : ℝ) + ell) p)
    (hstable : NoGridBoundary (2 ^ (b₀ + 3)) x
      (2 ^ (-((b₀ : ℝ) + g)))) :
    gridAddress b (sequencePoint Z n ((2 : ℝ) ^ k) x p) = gridAddress b x :=
  dyadic_grid_eq_of_finer_eq b b₀ hbu _ _
    (sequence_active_preceding_gridAddress_eq Z s₀ s₁ x u ell n k p hactive hu hstable)

/-- Actual stable centers give the earlier-address agreement required by the
routing hit lemma, for every strict active sequence sample. -/
theorem sequence_stable_earlier_address_agreement {M d : ℕ}
    (Z : LogScale) (c : RoutingTemplate M d)
    (hM : 0 < M) (hL : 0 < c.baseLength) (hU : c.gap + 1 ≤ c.origin)
    (s₀ s₁ x : ℝ) (n : ℕ) (k : ℤ) (e : SelectorEdge M d)
    (p : PowerParams s₀ s₁) (hx : x ∈ actualStableCenters c)
    (hp : sequencePowerActivation Z n k
      (c.edgeStart (RoutingTemplate.selectorRoutingEdge e))
      ((c.edgeStart (RoutingTemplate.selectorRoutingEdge e) : ℝ) +
        c.edgeLength (RoutingTemplate.selectorRoutingEdge e)) p) :
    EarlierAddressAgreement c x
      (sequencePoint Z n ((2 : ℝ) ^ k) x p) e := by
  intro f hf
  have hb := c.earlier_edgeEnd_le_predecessorBoundary hM hL
    (RoutingTemplate.selectorRoutingEdge f) (RoutingTemplate.selectorRoutingEdge e) hf
  apply sequence_active_coarser_preceding_gridAddress_eq Z s₀ s₁ x
    (c.edgeStart (RoutingTemplate.selectorRoutingEdge e))
    (c.edgeLength (RoutingTemplate.selectorRoutingEdge e)) n
    (c.selectorEnd f) (c.predecessorBoundary (RoutingTemplate.selectorRoutingEdge e))
    c.gap k (by exact hb) (by
      exact c.predecessorBoundary_start hU _) p hp
  have hs := hx (RoutingTemplate.selectorRoutingEdge e)
  simpa only [stableDyadicRadius_eq_rpow] using hs

/-- A successful sequence local route at a stable center is in the routed set. -/
theorem sequence_stable_local_success_mem_routedSet {M d : ℕ}
    (Z : LogScale) (c : RoutingTemplate M d) (hM : 0 < M) (hd : 0 < d)
    (hL : 0 < c.baseLength) (hU : c.gap + 1 ≤ c.origin)
    (s₀ s₁ x : ℝ) (n : ℕ) (k : ℤ) (p : PowerParams s₀ s₁)
    (ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd))
    (bits : SelectorEdge M d → Bool)
    (hσ : centerExposureAtom (actualCenterExposure c x bits) ω.selectors)
    (v : InternalNode M d) (child : Fin (M - 1))
    (hprefix : (List.ofFn v.2).IsPrefix
      (List.ofFn (routeLeaf c hM ω.selectors x)))
    (hdefault : ∀ i : Fin (M - 1), bits ⟨v, i⟩ = false)
    (hx : x ∈ actualStableCenters c)
    (hactive : sequencePowerActivation Z n k
      (c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩))
      ((c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩) : ℝ) +
        c.edgeLength (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩)) p)
    (hsuccess : ω.selectors (selectorAddress c ⟨v, child⟩
        (sequencePoint Z n ((2 : ℝ) ^ k) x p)) = true ∧
      ω.terminals (localTerminalAddress c hM hd ω.selectors ⟨v, child⟩
        (sequencePoint Z n ((2 : ℝ) ^ k) x p)) = true) :
    sequencePoint Z n ((2 : ℝ) ^ k) x p ∈ routedSet c hM hd ω := by
  exact actual_local_success_mem_routedSet c hM hd hL ω x
    (sequencePoint Z n ((2 : ℝ) ^ k) x p) bits hσ v child hprefix hdefault
    (sequence_stable_earlier_address_agreement Z c hM hL hU s₀ s₁ x n k
      ⟨v, child⟩ p hx hactive) hsuccess

end ErdosSimilarityGrowingGaps
