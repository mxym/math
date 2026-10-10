import ErdosSimilarityGrowingGaps.RoutingTemplate
import ErdosSimilarityGrowingGaps.GridGeometry


/-! Adapted in this repository from the finite geometric routing construction.
The real-logarithm sampler and variable schedule are supplied separately. -/
namespace ErdosSimilarityGrowingGaps

noncomputable def selectorAddress {M d : ℕ} (c : RoutingTemplate M d)
    (e : SelectorEdge M d) (z : ℝ) : SelectorAddress c :=
  ⟨e, gridAddress (c.selectorEnd e) z⟩

noncomputable def terminalAddress {M d : ℕ} (c : RoutingTemplate M d) (hd : 0 < d)
    (p : RoutingLeaf M d) (z : ℝ) : TerminalAddress c hd :=
  ⟨p, gridAddress (c.leafEnd hd p) z⟩

/-- Exactly one exposed address per selector table, including off-route tables. -/
noncomputable def actualCenterExposure {M d : ℕ} (c : RoutingTemplate M d)
    (x : ℝ) (bits : SelectorEdge M d → Bool) : SelectorAddress c → Option Bool := by
  classical
  exact fun s => if s.2 = gridAddress (c.selectorEnd s.1) x then some (bits s.1) else none

theorem centerExposure_reads {M d : ℕ} (c : RoutingTemplate M d) (x : ℝ)
    (bits : SelectorEdge M d → Bool) (σ : SelectorAddress c → Bool)
    (hσ : centerExposureAtom (actualCenterExposure c x bits) σ)
    (e : SelectorEdge M d) : σ (selectorAddress c e x) = bits e := by
  apply hσ (selectorAddress c e x) (bits e)
  simp [actualCenterExposure, selectorAddress]

theorem own_selector_unexposed {M d : ℕ} (c : RoutingTemplate M d) (x z : ℝ)
    (bits : SelectorEdge M d → Bool) (e : SelectorEdge M d)
    (hkey : gridAddress (c.selectorEnd e) z ≠ gridAddress (c.selectorEnd e) x) :
    actualCenterExposure c x bits (selectorAddress c e z) = none := by
  simp [actualCenterExposure, selectorAddress, hkey]

end ErdosSimilarityGrowingGaps
