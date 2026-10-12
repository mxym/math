import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Tactic

/-!
Exact-geometric specialization keeps two open buffers. The finite-grid
radius has an actual strict scalar budget; the grid enlargement MEASURE
bound remains a separate routing obligation, not asserted here.
-/
namespace ContinuumGeometric

theorem zero_error_buffer_budget (p : ℝ) (N : ℕ) (hp : 0 < p) (hN : 0 < N) :
    0 < p / (8 * (N : ℝ)) ∧
    4 * (N : ℝ) * (p / (8 * (N : ℝ))) = p / 2 ∧
    4 * (N : ℝ) * (p / (8 * (N : ℝ))) < p := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have heq : 4 * (N : ℝ) * (p / (8 * (N : ℝ))) = p / 2 := by
    field_simp
    ring
  exact ⟨by positivity, heq, by rw [heq]; linarith⟩

theorem double_open_buffers (B : Set ℝ) (r : ℝ) (hr : 0 < r) :
    IsOpen (Metric.thickening r B) ∧ IsOpen (Metric.thickening (2 * r) B) ∧
    B ⊆ Metric.thickening r B ∧
    Metric.thickening r B ⊆ Metric.thickening (2 * r) B := by
  exact ⟨Metric.isOpen_thickening, Metric.isOpen_thickening,
    Metric.self_subset_thickening hr B, Metric.thickening_mono (by linarith) B⟩

/-- The allowed perturbation endpoint is closed; both buffers are open. -/
theorem double_buffer_contains_perturbation (B : Set ℝ) (r z e : ℝ)
    (hz : z ∈ Metric.thickening r B) (he : |e| ≤ r) :
    z + e ∈ Metric.thickening (2 * r) B := by
  obtain ⟨b, hb, hzb⟩ := Metric.mem_thickening_iff.1 hz
  apply Metric.mem_thickening_iff.2
  refine ⟨b, hb, ?_⟩
  have hdist : dist (z + e) z = |e| := by
    rw [Real.dist_eq]
    congr 1
    ring
  calc
    dist (z + e) b ≤ dist (z + e) z + dist z b := dist_triangle _ _ _
    _ = |e| + dist z b := by rw [hdist]
    _ < r + r := add_lt_add_of_le_of_lt he hzb
    _ = 2 * r := by ring

end ContinuumGeometric
