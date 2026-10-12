import ErdosSimilarityGrowingGaps.WindowRepair
import ErdosSimilarityGrowingGaps.PowerCore

namespace ErdosSimilarityGrowingGaps

open Set MeasureTheory

theorem sequence_activation_of_sample_interval
    {Z : LogScale} {K : ℕ} {n m : ℕ} {k : ℤ}
    {W : ℕ} (windows : Fin W → ℝ × ℝ) (e : Fin W) (D : ℝ)
    (p : PowerParams (1 / (K : ℝ)) K)
    (hK : 2 ≤ K)
    (hideal : p ∈ powerActivation n k (windows e).1 (windows e).2)
    (hlo : (n : ℝ) ≤ Z.z m) (hhi : Z.z m ≤ (n : ℝ) + D)
    (hmargin : p.1.1 * D < (windows e).2 -
      (p.1.1 * (n : ℝ) - (k : ℝ)))
    : p ∈ sequenceWindowActivations Z m k windows := by
  classical
  apply Set.mem_iUnion.2 ⟨e, ?_⟩
  simp only [powerActivation, sequenceActivation, mem_setOf_eq] at hideal ⊢
  constructor
  · have hKr : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
    have hps : 0 ≤ p.1.1 :=
      (le_trans (by positivity : (0 : ℝ) < 1 / (K : ℝ)).le p.1.2.1)
    have : p.1.1 * (n : ℝ) - (k : ℝ) ≤ p.1.1 * Z.z m - (k : ℝ) := by
      gcongr
    exact lt_of_lt_of_le hideal.1 this
  · have hKr : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
    have hps : 0 ≤ p.1.1 :=
      (le_trans (by positivity : (0 : ℝ) < 1 / (K : ℝ)).le p.1.2.1)
    have hD : p.1.1 * Z.z m ≤ p.1.1 * ((n : ℝ) + D) := by
      gcongr
    have hupper : p.1.1 * ((n : ℝ) + D) - (k : ℝ) < (windows e).2 := by
      linarith
    exact lt_of_le_of_lt (by linarith) hupper

/-!  This is the logical transfer layer.  The analytic work of producing the
sample map is deliberately isolated in its two explicit hypotheses, while the
missed-center inclusion is proved directly from the definitions. -/
theorem sequence_missedCenters_subset_power_missedCenters
    {Z : LogScale} {K : ℕ} (tests : Finset ℕ) (k : ℤ)
    {W : ℕ} (windows : Fin W → ℝ × ℝ) (G : Set ℝ) (r : ℝ)
    (sample : ℕ → ℕ)
    (hactivate : ∀ n : ℕ, n ∈ tests →
      ∀ p : PowerParams (1 / (K : ℝ)) K,
        p ∈ windowActivations n k windows →
        p ∈ sequenceWindowActivations Z (sample n) k windows)
    (hpoint : ∀ (n : ℕ), n ∈ tests → ∀ (x : ℝ)
      (p : PowerParams (1 / (K : ℝ)) K),
      powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p) ∈ G →
      powerPoint (input Z (sample n)) ((2 : ℝ) ^ k) (x, p) ∈
        Metric.thickening r G) :
    sequenceMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
      Z (tests.image sample) k windows (Metric.thickening r G) ⊆
    powerMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
      tests k windows G := by
  classical
  intro x hx
  simp only [sequenceMissedCenters, powerMissedCenters] at hx ⊢
  rw [mem_missedCenters_iff] at hx ⊢
  by_contra hnot
  push_neg at hnot
  obtain ⟨p, hxmiss⟩ := hx
  obtain ⟨i, hi, hhit⟩ := hnot p
  have hseq := hactivate i.1 i.2 p hi
  have hpoint' := hpoint i.1 i.2 x p hhit
  let j : {m // m ∈ tests.image sample} :=
    ⟨sample i.1, Finset.mem_image.2 ⟨i.1, i.2, rfl⟩⟩
  exact hxmiss j hseq hpoint'

theorem sequence_missedCenters_subset_power_missedCenters_of_sampled
    {Z : LogScale} {K : ℕ}
    (tests : Finset ℕ) (k : ℤ) {W : ℕ} (windows : Fin W → ℝ × ℝ)
    (G : Set ℝ) (r : ℝ) (sample : ℕ → ℕ)
    (hactivate : ∀ n : ℕ, n ∈ tests →
      ∀ p : PowerParams (1 / (K : ℝ)) K,
        p ∈ windowActivations n k windows →
        p ∈ sequenceWindowActivations Z (sample n) k windows)
    (hpoint : ∀ (n : ℕ), n ∈ tests → ∀ (x : ℝ)
      (p : PowerParams (1 / (K : ℝ)) K),
      powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p) ∈ G →
      powerPoint (input Z (sample n)) ((2 : ℝ) ^ k) (x, p) ∈
        Metric.thickening r G) :
    sequenceMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
      Z (tests.image sample) k windows (Metric.thickening r G) ⊆
    powerMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
      tests k windows G := by
  exact sequence_missedCenters_subset_power_missedCenters tests k windows G r sample
    hactivate hpoint

theorem sequence_outcome_density_of_power_outcome
    {Z : LogScale} {K : ℕ} (tests : Finset ℕ) (k : ℤ)
    {W : ℕ} (windows : Fin W → ℝ × ℝ) (G : Set ℝ) (r p : ℝ)
    (sample : ℕ → ℕ)
    (hsubset : sequenceMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
      Z (tests.image sample) k windows (Metric.thickening r G) ⊆
      powerMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
        tests k windows G)
    (houtcome : unitDensity (Metric.thickening (2 * r) G) +
      unitDensity (powerMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
        tests k windows G) ≤ ENNReal.ofReal (5 * p)) :
    unitDensity (Metric.thickening (2 * r) G) +
      unitDensity (sequenceMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
        Z (tests.image sample) k windows (Metric.thickening r G)) ≤
      ENNReal.ofReal (5 * p) := by
  have hμ : unitDensity (sequenceMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
        Z (tests.image sample) k windows (Metric.thickening r G)) ≤
      unitDensity (powerMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
        tests k windows G) := by
    unfold unitDensity
    apply measure_mono
    exact Set.inter_subset_inter hsubset (Set.Subset.rfl)
  exact (add_le_add le_rfl hμ).trans houtcome

end ErdosSimilarityGrowingGaps
