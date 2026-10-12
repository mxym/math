import ErdosSimilarityGrowingGaps.PeriodicRepair
import ErdosSimilarityGrowingGaps.TailAnalysis

namespace ErdosSimilarityGrowingGaps

open Set MeasureTheory Filter Topology

/-- Strict output activation for the actual logarithmic sample. -/
def sequenceActivation {s₀ s₁ : ℝ} (Z : LogScale) (n : ℕ)
    (k u v : ℝ) : Set (PowerParams s₀ s₁) :=
  {p | u < p.1.1 * Z.z n - k ∧ p.1.1 * Z.z n - k < v}

def sequenceWindowActivations {s₀ s₁ : ℝ} (Z : LogScale) (n : ℕ) (k : ℤ)
    {W : ℕ} (windows : Fin W → ℝ × ℝ) : Set (PowerParams s₀ s₁) :=
  ⋃ e, sequenceActivation Z n k (windows e).1 (windows e).2

noncomputable def sequenceMissedCenters {s₀ s₁ : ℝ} (Z : LogScale)
    (tests : Finset ℕ) (k : ℤ) {W : ℕ} (windows : Fin W → ℝ × ℝ)
    (B : Set ℝ) : Set ℝ :=
  missedCenters (P := PowerParams s₀ s₁)
    (fun i : {n // n ∈ tests} => sequenceWindowActivations Z i.1 k windows)
    B (fun i => powerPoint (input Z i.1) ((2 : ℝ) ^ k))

theorem isOpen_sequenceWindowActivations (s₀ s₁ : ℝ) (Z : LogScale)
    (n : ℕ) (k : ℤ) {W : ℕ} (windows : Fin W → ℝ × ℝ) :
    IsOpen (sequenceWindowActivations (s₀ := s₀) (s₁ := s₁) Z n k windows) := by
  apply isOpen_iUnion
  intro e
  have hs : Continuous (fun p : PowerParams s₀ s₁ => p.1.1) :=
    continuous_subtype_val.comp continuous_fst
  exact isOpen_Ioo.preimage ((hs.mul continuous_const).sub continuous_const)

theorem isClosed_sequenceMissedCenters (s₀ s₁ : ℝ) (Z : LogScale)
    (tests : Finset ℕ) (k : ℤ) {W : ℕ} (windows : Fin W → ℝ × ℝ)
    (B : Set ℝ) (hB : IsOpen B) :
    IsClosed (sequenceMissedCenters (s₀ := s₀) (s₁ := s₁) Z tests k windows B) := by
  apply isClosed_missedCenters
  · intro i
    exact isOpen_sequenceWindowActivations s₀ s₁ Z i.1 k windows
  · exact hB
  · intro i
    exact continuous_powerPoint s₀ s₁ _ _ (input_pos Z i.1).ne'

theorem onePeriodic_sequenceMissedCenters (s₀ s₁ : ℝ) (Z : LogScale)
    (tests : Finset ℕ) (k : ℤ) {W : ℕ} (windows : Fin W → ℝ × ℝ)
    (B : Set ℝ) (hB : OnePeriodic B) :
    OnePeriodic (sequenceMissedCenters (s₀ := s₀) (s₁ := s₁) Z tests k windows B) := by
  intro x
  simp only [sequenceMissedCenters, mem_missedCenters_iff]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p, fun i hi hhit => hp i hi ?_⟩
    have ht := (hB (powerPoint (input Z i.1) ((2 : ℝ) ^ k) (x, p))).2 hhit
    convert ht using 1 <;> simp only [powerPoint] <;> ring
  · rintro ⟨p, hp⟩
    refine ⟨p, fun i hi hhit => hp i hi ?_⟩
    apply (hB (powerPoint (input Z i.1) ((2 : ℝ) ^ k) (x, p))).1
    convert hhit using 1 <;> simp only [powerPoint] <;> ring

/-- Lemma 5's uniform remainder formulation at one compact rectangle and tail. -/
def CompactRobustHits (Z : LogScale) (H : Set ℝ) (K : ℕ) (k : ℤ)
    (N : ℕ) (α q : ℝ) : Prop :=
  ∀ (x : ℝ) (p : PowerParams (1 / (K : ℝ)) K) (f : ℝ → ℝ),
    (∀ n : ℕ, N ≤ n →
      |f (input Z n) - x - p.2.1 * (2 : ℝ) ^ k * (input Z n) ^ p.1.1| ≤
        q * (input Z n) ^ (p.1.1 + α)) →
    ∃ n : ℕ, N ≤ n ∧ f (input Z n) ∈ H


/-- A compact lower exponent makes the tail remainder uniformly small over the
whole parameter rectangle. -/
theorem uniform_tail_error_budget {Z : LogScale} {K : ℕ} (hK : 2 ≤ K)
    {α q r : ℝ} (hα : 0 < α) (hq : 0 ≤ q) (hr : 0 < r) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ p : PowerParams (1 / (K : ℝ)) K,
        q * (input Z n) ^ (p.1.1 + α) < r := by
  have hs₀ : 0 < (1 / (K : ℝ)) := by positivity
  have hlim : Tendsto (fun n : ℕ => (input Z n) ^ (1 / (K : ℝ))) atTop (𝓝 0) :=
    (input_tendsto_zero Z).rpow_const_nhds_zero hs₀
  have hev : ∀ᶠ n : ℕ in atTop, q * (input Z n) ^ (1 / (K : ℝ)) < r := by
    have hlimq : Tendsto (fun n : ℕ => q * (input Z n) ^ (1 / (K : ℝ))) atTop (𝓝 0) := by
      simpa using hlim.const_mul q
    exact hlimq.eventually (Iio_mem_nhds (by simpa using hr))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, ?_⟩
  intro n hn p
  have hx : 0 < input Z n := input_pos Z n
  have hx1 : input Z n ≤ 1 := (input_lt_one Z n).le
  have hexp : (1 / (K : ℝ)) ≤ p.1.1 + α := by
    have hp : (1 / (K : ℝ)) ≤ p.1.1 := p.1.2.1
    linarith
  have hpow : (input Z n) ^ (p.1.1 + α) ≤
      (input Z n) ^ (1 / (K : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hx hx1 hexp
  have hqnonneg : 0 ≤ q := hq
  have hmul := mul_le_mul_of_nonneg_left hpow hqnonneg
  exact hmul.trans_lt (hN n hn)

/-- Finite active hits survive the remainder buffer, while exceptional centers
are repaired using the true infinite sequence. No injectivity of `f` is used. -/
theorem sequence_repair_all_centers {Z : LogScale} {K : ℕ} (hK : 2 ≤ K)
    (tests : Finset ℕ) (k : ℤ) {W : ℕ} (windows : Fin W → ℝ × ℝ)
    (G V : Set ℝ) (r : ℝ) (hr : 0 < r) (hV : IsOpen V)
    (hcover : sequenceMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
      Z tests k windows (Metric.thickening r G) ⊆ V)
    (N : ℕ) (htail : ∀ n ∈ tests, N ≤ n)
    (α q : ℝ) (hα : 0 < α) (hq : 0 ≤ q)
    (herror : ∀ (p : PowerParams (1 / (K : ℝ)) K) (n : ℕ), n ∈ tests →
      p ∈ sequenceWindowActivations Z n k windows →
        q * (input Z n) ^ (p.1.1 + α) < r) :
    CompactRobustHits Z (Metric.thickening (2 * r) G ∪ V) K k N α q := by
  classical
  intro x p f hf
  have hKr : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hs : 0 < p.1.1 := lt_of_lt_of_le (by positivity : 0 < 1 / (K : ℝ)) p.1.2.1
  let R := sequenceMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
    Z tests k windows (Metric.thickening r G)
  by_cases hx : x ∈ R
  · have happrox : TailApproximation Z f p.1.1 α x (p.2.1 * (2 : ℝ) ^ k) q := ⟨N, hf⟩
    have hev := (tailApproximation_tendsto hs hα hq happrox).eventually
      (hV.mem_nhds (hcover hx))
    obtain ⟨n, hn, hhit⟩ := (eventually_ge_atTop N |>.and hev).exists
    exact ⟨n, hn, Or.inr hhit⟩
  · have hfinite := (not_mem_missedCenters_iff
      (fun i : {n // n ∈ tests} => sequenceWindowActivations Z i.1 k windows)
      (Metric.thickening r G) (fun i => powerPoint (input Z i.1) ((2 : ℝ) ^ k)) x).1 hx
    obtain ⟨i, hactive, hhit⟩ := hfinite p
    obtain ⟨z, hzG, hiz⟩ := Metric.mem_thickening_iff.1 hhit
    have hfi : dist (f (input Z i.1)) (powerPoint (input Z i.1) ((2 : ℝ) ^ k) (x, p)) < r := by
      rw [Real.dist_eq]
      have heq : f (input Z i.1) - powerPoint (input Z i.1) ((2 : ℝ) ^ k) (x, p) =
          f (input Z i.1) - x - p.2.1 * (2 : ℝ) ^ k * (input Z i.1) ^ p.1.1 := by
        simp only [powerPoint]
        ring
      rw [heq]
      exact (hf i.1 (htail i.1 i.2)).trans_lt (herror p i.1 i.2 hactive)
    refine ⟨i.1, htail i.1 i.2, Or.inl (Metric.mem_thickening_iff.2 ⟨z, hzG, ?_⟩)⟩
    exact (dist_triangle _ _ _).trans_lt (by linarith)

/-- The measured finite-grid outcome gives a robust periodic blocker for the
actual logarithmic input sequence, including arbitrary allowed errors. -/
theorem periodic_sequence_outcome_repair {Z : LogScale} {K : ℕ} (hK : 2 ≤ K)
    (tests : Finset ℕ) (k : ℤ) {W : ℕ} (windows : Fin W → ℝ × ℝ)
    (G : Set ℝ) (hGp : OnePeriodic G) (r : ℝ) (hr : 0 < r)
    (N : ℕ) (htail : ∀ n ∈ tests, N ≤ n)
    (α q : ℝ) (hα : 0 < α) (hq : 0 ≤ q)
    (herror : ∀ (p : PowerParams (1 / (K : ℝ)) K) (n : ℕ), n ∈ tests →
      p ∈ sequenceWindowActivations Z n k windows → q * (input Z n) ^ (p.1.1 + α) < r)
    (p : ℝ) (hp : 0 < p)
    (houtcome : unitDensity (Metric.thickening (2 * r) G) +
      unitDensity (sequenceMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
        Z tests k windows (Metric.thickening r G)) ≤ ENNReal.ofReal (5 * p)) :
    ∃ H : Set ℝ, IsOpen H ∧ OnePeriodic H ∧
      unitDensity H < ENNReal.ofReal (6 * p) ∧ CompactRobustHits Z H K k N α q := by
  let R := sequenceMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
    Z tests k windows (Metric.thickening r G)
  obtain ⟨V, hVo, hVp, hRV, hVμ⟩ := closed_onePeriodic_open_cover R
    (isClosed_sequenceMissedCenters _ _ Z tests k windows _ Metric.isOpen_thickening)
    (onePeriodic_sequenceMissedCenters _ _ Z tests k windows _ (onePeriodic_thickening hGp r)) p hp
  refine ⟨Metric.thickening (2 * r) G ∪ V, Metric.isOpen_thickening.union hVo,
    onePeriodic_union (onePeriodic_thickening hGp _) hVp, ?_, ?_⟩
  · calc
      unitDensity (Metric.thickening (2 * r) G ∪ V) ≤
          unitDensity (Metric.thickening (2 * r) G) + unitDensity V := unitDensity_union_le _ _
      _ < unitDensity (Metric.thickening (2 * r) G) + (unitDensity R + ENNReal.ofReal p) :=
        ENNReal.add_lt_add_left (ne_top_of_le_ne_top ENNReal.one_ne_top (unitDensity_le_one _)) hVμ
      _ = (unitDensity (Metric.thickening (2 * r) G) + unitDensity R) + ENNReal.ofReal p :=
        (add_assoc _ _ _).symm
      _ ≤ ENNReal.ofReal (5 * p) + ENNReal.ofReal p := add_le_add houtcome le_rfl
      _ = ENNReal.ofReal (6 * p) := by
        rw [← ENNReal.ofReal_add (by positivity) hp.le]
        congr 1
        ring
  · exact sequence_repair_all_centers hK tests k windows G V r hr hVo hRV N htail α q hα hq herror

end ErdosSimilarityGrowingGaps
