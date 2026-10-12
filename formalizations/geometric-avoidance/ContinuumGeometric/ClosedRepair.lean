import ContinuumGeometric.ClosedProjection
import ContinuumGeometric.ZeroErrorBuffer

namespace ContinuumGeometric

/-- The closed-projection and full-tail repair module, with actual double open buffers.

V is an arbitrary open cover of the DEFINED missed-center set, not a uniform
blocker hypothesis. Its small-measure construction and the random miss
estimate remain open obligations. The conclusion keeps all real centers,
every compact-rectangle parameter, and the actual original tail index N.
-/
theorem buffered_power_closed_repair (s₀ s₁ : ℝ) (hs₀ : 0 < s₀)
    (tests : Finset ℕ) (k : ℤ) {W : ℕ} (windows : Fin W → ℝ × ℝ)
    (B V : Set ℝ) (r : ℝ) (hr : 0 < r) (hV : IsOpen V)
    (hcover : powerMissedCenters (s₀ := s₀) (s₁ := s₁)
      tests k windows (Metric.thickening r B) ⊆ V)
    (N : ℕ) (htail : ∀ n ∈ tests, N ≤ n) :
    IsClosed (powerMissedCenters (s₀ := s₀) (s₁ := s₁)
      tests k windows (Metric.thickening r B)) ∧
    ∀ (x : ℝ) (p : PowerParams s₀ s₁),
      ∃ n : ℕ, N ≤ n ∧ powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p) ∈
        Metric.thickening (2 * r) B ∪ V := by
  refine ⟨isClosed_powerMissedCenters s₀ s₁ tests k windows _ Metric.isOpen_thickening, ?_⟩
  exact power_repair_all_centers s₀ s₁ hs₀ tests k windows
    (Metric.thickening r B) (Metric.thickening (2 * r) B) V
    (double_open_buffers B r hr).2.2.2 hV hcover N htail

end ContinuumGeometric
