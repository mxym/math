import ContinuumRemainder.ErrorDomination
import ContinuumGeometric.ClosedProjection

/-!
Section 7 for an arbitrary positive null input sequence.  The finite routing
tests and the full infinite input sequence are separate.  An open cover of the
defined closed missed-center set is a deterministic repair input; no blocker
or probability estimate is assumed.  Error families need no regularity.
-/
namespace ContinuumRemainder

open Set Filter Topology
open ContinuumGeometric

/-- Any prescribed power-controlled error along a null sequence tends to zero. -/
theorem power_controlled_error_tendsto (a e : ℕ → ℝ) (s α q : ℝ)
    (ha : Tendsto a atTop (𝓝 0)) (hs : 0 < s) (hα : 0 < α)
    (he : ∀ n, |e n| ≤ q * (a n) ^ (s + α)) :
    Tendsto e atTop (𝓝 0) := by
  have hbound : Tendsto (fun n => q * (a n) ^ (s + α)) atTop (𝓝 0) := by
    simpa using (ha.rpow_const_nhds_zero (add_pos hs hα)).const_mul q
  apply (tendsto_zero_iff_abs_tendsto_zero e).2
  exact squeeze_zero (fun n => abs_nonneg (e n)) he hbound

/-- The perturbed tail approaches its center for arbitrary allowed errors. -/
theorem perturbed_power_tendsto (a e : ℕ → ℝ) (x t C s α q : ℝ)
    (ha : Tendsto a atTop (𝓝 0)) (hs : 0 < s) (hα : 0 < α)
    (he : ∀ n, |e n| ≤ q * (a n) ^ (s + α)) :
    Tendsto (fun n => x + t * C * (a n) ^ s + e n) atTop (𝓝 x) := by
  have herr := power_controlled_error_tendsto a e s α q ha hs hα he
  have hmain := (ha.rpow_const_nhds_zero hs).const_mul (t * C)
  simpa using (hmain.const_add x).add herr

theorem perturbed_power_tail_hits_open (a e : ℕ → ℝ) (x t C s α q : ℝ)
    (ha : Tendsto a atTop (𝓝 0)) (hs : 0 < s) (hα : 0 < α)
    (he : ∀ n, |e n| ≤ q * (a n) ^ (s + α))
    (V : Set ℝ) (hV : IsOpen V) (hx : x ∈ V) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ x + t * C * (a n) ^ s + e n ∈ V := by
  have hev := (perturbed_power_tendsto a e x t C s α q ha hs hα he).eventually
    (hV.mem_nhds hx)
  obtain ⟨n, hhit, hn⟩ := (hev.and (eventually_ge_atTop N)).exists
  exact ⟨n, hn, hhit⟩

/-- Real input logarithms, with both output-window endpoints strictly excluded. -/
def sampledActivation {s₀ s₁ : ℝ} (z : ℝ) (k : ℤ) (u v : ℝ) :
    Set (PowerParams s₀ s₁) :=
  {p | u < p.1.1 * z - k ∧ p.1.1 * z - k < v}

theorem isOpen_sampledActivation (s₀ s₁ z : ℝ) (k : ℤ) (u v : ℝ) :
    IsOpen (sampledActivation (s₀ := s₀) (s₁ := s₁) z k u v) := by
  have hs : Continuous (fun p : PowerParams s₀ s₁ => p.1.1) :=
    continuous_subtype_val.comp continuous_fst
  exact isOpen_Ioo.preimage ((hs.mul continuous_const).sub continuous_const)

def sampledWindowActivations {s₀ s₁ : ℝ} (z : ℝ) (k : ℤ) {W : ℕ}
    (windows : Fin W → ℝ × ℝ) : Set (PowerParams s₀ s₁) :=
  ⋃ w, sampledActivation z k (windows w).1 (windows w).2

theorem isOpen_sampledWindowActivations (s₀ s₁ z : ℝ) (k : ℤ) {W : ℕ}
    (windows : Fin W → ℝ × ℝ) :
    IsOpen (sampledWindowActivations (s₀ := s₀) (s₁ := s₁) z k windows) :=
  isOpen_iUnion fun w => isOpen_sampledActivation s₀ s₁ z k (windows w).1 (windows w).2

noncomputable def sampledMissedCenters {s₀ s₁ : ℝ} (tests : Finset ℕ)
    (a z : ℕ → ℝ) (k : ℤ) {W : ℕ} (windows : Fin W → ℝ × ℝ)
    (B₁ : Set ℝ) : Set ℝ :=
  missedCenters (P := PowerParams s₀ s₁)
    (fun i : {n // n ∈ tests} => sampledWindowActivations (z i.1) k windows)
    B₁ (fun i => powerPoint (a i.1) ((2 : ℝ) ^ k))

/-- Closedness uses continuity of actual powers and open real-log activation. -/
theorem isClosed_sampledMissedCenters (s₀ s₁ : ℝ) (tests : Finset ℕ)
    (a z : ℕ → ℝ) (ha : ∀ n ∈ tests, 0 < a n) (k : ℤ) {W : ℕ}
    (windows : Fin W → ℝ × ℝ) (B₁ : Set ℝ) (hB₁ : IsOpen B₁) :
    IsClosed (sampledMissedCenters (s₀ := s₀) (s₁ := s₁)
      tests a z k windows B₁) := by
  apply isClosed_missedCenters
  · intro i
    exact isOpen_sampledWindowActivations s₀ s₁ (z i.1) k windows
  · exact hB₁
  · intro i
    exact continuous_powerPoint s₀ s₁ (a i.1) _ (ha i.1 i.2).ne'

/-- Actual full-sequence robust repair, including equality in the error bound.

Outside the defined missed-center set an ACTIVE finite test hits the inner
buffer.  Inside that set an arbitrarily late point of the FULL sequence hits
the open cover.  Neither the errors nor their dependence on input are regular.
-/
theorem sampled_robust_repair_all_centers (s₀ s₁ α₀ U : ℝ)
    (hs₀ : 0 < s₀) (hα : 0 < α₀) (tests : Finset ℕ)
    (a z : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (haz : ∀ n, a n = (2 : ℝ) ^ (-(z n)))
    (hanull : Tendsto a atTop (𝓝 0)) (k : ℤ) (q : ℕ)
    (hUk : 0 ≤ U + (k : ℝ)) {W : ℕ} (windows : Fin W → ℝ × ℝ)
    (hwindow : ∀ w, U ≤ (windows w).1) (B V : Set ℝ)
    (hV : IsOpen V)
    (hcover : sampledMissedCenters (s₀ := s₀) (s₁ := s₁) tests a z k windows
      (Metric.thickening (errorRadius q k α₀ s₁ U) B) ⊆ V)
    (N : ℕ) (htail : ∀ n ∈ tests, N ≤ n) :
    IsClosed (sampledMissedCenters (s₀ := s₀) (s₁ := s₁) tests a z k windows
      (Metric.thickening (errorRadius q k α₀ s₁ U) B)) ∧
    ∀ (x : ℝ) (p : PowerParams s₀ s₁) (e : ℕ → ℝ),
      (∀ n, |e n| ≤ (q : ℝ) * (a n) ^ (p.1.1 + α₀)) →
      ∃ n : ℕ, N ≤ n ∧ powerPoint (a n) ((2 : ℝ) ^ k) (x, p) + e n ∈
        Metric.thickening (2 * errorRadius q k α₀ s₁ U) B ∪ V := by
  classical
  refine ⟨isClosed_sampledMissedCenters s₀ s₁ tests a z
    (fun n _ => ha n) k windows _ Metric.isOpen_thickening, ?_⟩
  intro x p e he
  have hs : 0 < p.1.1 := hs₀.trans_le p.1.2.1
  by_cases hx : x ∈ sampledMissedCenters (s₀ := s₀) (s₁ := s₁) tests a z k windows
      (Metric.thickening (errorRadius q k α₀ s₁ U) B)
  · obtain ⟨n, hn, hhit⟩ := perturbed_power_tail_hits_open a e x p.2.1
      ((2 : ℝ) ^ k) p.1.1 α₀ q hanull hs hα he V hV (hcover hx) N
    exact ⟨n, hn, Or.inr hhit⟩
  · have hfinite := (not_mem_missedCenters_iff
      (fun i : {n // n ∈ tests} => sampledWindowActivations (s₀ := s₀) (s₁ := s₁)
        (z i.1) k windows)
      (Metric.thickening (errorRadius q k α₀ s₁ U) B)
      (fun i => powerPoint (a i.1) ((2 : ℝ) ^ k)) x).1 hx
    obtain ⟨i, hactive, hhit⟩ := hfinite p
    obtain ⟨w, hw⟩ := mem_iUnion.1 hactive
    have hUactive : U < p.1.1 * z i.1 - k := (hwindow w).trans_lt hw.1
    refine ⟨i.1, htail i.1 i.2, Or.inl ?_⟩
    exact active_error_in_outer_buffer B q k (a i.1) (z i.1) p.1.1 s₁ α₀ U
      x p.2.1 (e i.1) (haz i.1) hs p.1.2.2 hα hUk hUactive hhit (he i.1)

end ContinuumRemainder
