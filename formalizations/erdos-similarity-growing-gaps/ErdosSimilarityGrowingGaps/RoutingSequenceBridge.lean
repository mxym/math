import ErdosSimilarityGrowingGaps.SequenceTransfer

namespace ErdosSimilarityGrowingGaps

open Set MeasureTheory

/-!
A direct assembly interface from the finite power-routing outcome to the true
logarithmic sequence.  The two hypotheses `hactivate` and `hpoint` are the
precise finite sample-map obligations: activation carries every ideal active
window to the sampled sequence index, and ideal power outputs move only into
the prescribed buffer.  Once supplied, the measured periodic repair is fully
kernel-checked and no abstract transfer axiom remains.
-/
theorem periodic_sequence_blocker_of_power_transfer
    {Z : LogScale} {K : ℕ} (hK : 2 ≤ K)
    (tests : Finset ℕ) (k : ℤ) {W : ℕ}
    (windows : Fin W → ℝ × ℝ) (G : Set ℝ) (hGp : OnePeriodic G)
    (r p : ℝ) (hr : 0 < r) (hp : 0 < p)
    (sample : ℕ → ℕ)
    (hactivate : ∀ n : ℕ, n ∈ tests →
      ∀ q : PowerParams (1 / (K : ℝ)) K,
        q ∈ windowActivations n k windows →
        q ∈ sequenceWindowActivations Z (sample n) k windows)
    (hpoint : ∀ (n : ℕ), n ∈ tests → ∀ (x : ℝ)
      (q : PowerParams (1 / (K : ℝ)) K),
      powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, q) ∈ G →
      powerPoint (input Z (sample n)) ((2 : ℝ) ^ k) (x, q) ∈
        Metric.thickening r G)
    (N : ℕ) (htail : ∀ n ∈ tests.image sample, N ≤ n)
    (α q : ℝ) (hα : 0 < α) (hq : 0 ≤ q)
    (herror : ∀ (q₀ : PowerParams (1 / (K : ℝ)) K) (n : ℕ),
      n ∈ tests.image sample →
      q₀ ∈ sequenceWindowActivations Z n k windows →
        q * (input Z n) ^ (q₀.1.1 + α) < r)
    (houtcome : unitDensity (Metric.thickening (2 * r) G) +
      unitDensity (powerMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
        tests k windows G) ≤ ENNReal.ofReal (5 * p)) :
    ∃ H : Set ℝ, IsOpen H ∧ OnePeriodic H ∧
      unitDensity H < ENNReal.ofReal (6 * p) ∧
      CompactRobustHits Z H K k N α q := by
  have hsubset := sequence_missedCenters_subset_power_missedCenters
    (K := K) tests k windows G r sample hactivate hpoint
  exact periodic_sequence_outcome_repair hK (tests.image sample) k windows G hGp r hr N htail
    α q hα hq herror p hp (by
      exact sequence_outcome_density_of_power_outcome tests k windows G r p sample
        hsubset houtcome)

end ErdosSimilarityGrowingGaps
