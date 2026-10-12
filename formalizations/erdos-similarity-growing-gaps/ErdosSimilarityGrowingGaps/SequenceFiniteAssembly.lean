import ErdosSimilarityGrowingGaps.RoutingAssembly
import ErdosSimilarityGrowingGaps.RoutingStableProbability
import ErdosSimilarityGrowingGaps.SequenceTransfer
import ErdosSimilarityGrowingGaps.UniformPowerTransfer
import ErdosSimilarityGrowingGaps.SequenceStableProbability

namespace ErdosSimilarityGrowingGaps

open Set MeasureTheory

/-- The finite routing output exposes the actual routed core, its buffer radius,
its test family and the measured failure budget.  This is the data consumed by
both the dyadic and sequential repair layers. -/
theorem exists_power_routing_data {K : ℕ} (hK : 2 ≤ K)
    {k : ℤ} {N : ℕ} {p : ℝ} (hp : 0 < p) (hp₁ : p ≤ 1)
    (s : RoutingSchedule K k N p) :
    ∃ (G : Set ℝ) (ρ : ℝ) (tests : Finset ℕ) (W : ℕ)
      (windows : Fin W → ℝ × ℝ),
      OnePeriodic G ∧ 0 < ρ ∧
      unitDensity (Metric.thickening (2 * ρ) G) +
        unitDensity (powerMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
          tests k windows G) ≤ ENNReal.ofReal (5 * p) := by
  have hM : 0 < s.branching := by have := s.branching_ge_two; omega
  let c := s.template
  let B₁ := routingInnerBuffer c hM s.depth_pos p
  let B₂ := routingOuterBuffer c hM s.depth_pos p
  let w := finiteRoutingWeight (S := SelectorAddress c)
    (T := TerminalAddress c s.depth_pos) p
  have hw := finiteRoutingWeight_nonneg (S := SelectorAddress c)
    (T := TerminalAddress c s.depth_pos) p hp.le hp₁
  have hnorm := finiteRoutingWeight_sum (S := SelectorAddress c)
    (T := TerminalAddress c s.depth_pos) p
  have hB₂ : expectedUnitDensity w B₂ ≤ ENNReal.ofReal (2 * p) := by
    have he := expectedUnitDensity_enlargement_le w hw hnorm
      (routedSet c hM s.depth_pos) B₂ (ENNReal.ofReal p)
      (routingOuterBuffer_density_le c hM s.depth_pos s.length_pos p hp)
    apply he.trans
    rw [actual_routedSet_expected_density c hM s.depth_pos p hp.le hp₁
      (measurableSet_actual_routedSet_of_template c hM s.depth_pos s.length_pos)]
    rw [← ENNReal.ofReal_add hp.le hp.le]
    apply le_of_eq
    congr 1
    ring
  obtain ⟨ω, houtcome⟩ := exists_powerRouting_outcome_density_add_le_of_stable
    w hw hnorm (1 / (K : ℝ)) K (globalRoutingTests c K N k) k
    (globalRoutingWindows c) B₁ B₂ (fun _ => Metric.isOpen_thickening) p hp.le hB₂
    (actualStableCenters c)ᶜ (measurableSet_actualStableCenters c).compl
    (actual_stable_bad_density_le s) (by
      intro x hx hxbad
      rw [← tableProbability_eq_finiteOutcomeProbability]
      exact actual_stable_missed_center_probability_le s hK hp hp₁ x
        (by simpa only [Set.mem_compl_iff, not_not] using hxbad))
  let ρ := routingBufferRadius c p / 2
  refine ⟨B₁ ω, ρ, globalRoutingTests c K N k,
    Fintype.card (RoutingEdge s.branching s.depth), globalRoutingWindows c, ?_, ?_, ?_⟩
  · exact onePeriodic_thickening
      (onePeriodic_actual_routedSet_of_template c hM s.depth_pos s.length_pos ω)
      (routingBufferRadius c p)
  · dsimp [ρ]
    exact (div_pos (routingBufferRadius_pos c p hp) (by norm_num))
  · have hsubset : Metric.thickening (2 * ρ) (B₁ ω) ⊆ B₂ ω := by
      change Metric.thickening (2 * ρ)
          (Metric.thickening (routingBufferRadius c p)
            (routedSet c hM s.depth_pos ω)) ⊆
        Metric.thickening (2 * routingBufferRadius c p)
          (routedSet c hM s.depth_pos ω)
      have h := Metric.thickening_thickening_subset
        (routingBufferRadius c p) (routingBufferRadius c p)
        (routedSet c hM s.depth_pos ω)
      simpa [ρ, two_mul, add_comm, add_left_comm, add_assoc] using h
    have hden : unitDensity (Metric.thickening (2 * ρ) (B₁ ω)) ≤
        unitDensity (B₂ ω) := by
      unfold unitDensity
      exact measure_mono (inter_subset_inter_left _ hsubset)
    exact (add_le_add hden le_rfl).trans (by simpa [B₁, B₂] using houtcome)

/-- The finite outcome selection for actual sequence missed centers.  This
uses their proved closedness, so the measure-theoretic assembly contains no
measurability premise beyond openness of the finite buffers. -/
theorem exists_sequenceRouting_outcome_density_add_le_of_stable
    {Ω : Type*} [Fintype Ω]
    (Z : LogScale) (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hnorm : ∑ ω, w ω = 1) (s₀ s₁ : ℝ)
    (tests : Finset ℕ) (k : ℤ) {W : ℕ}
    (windows : Fin W → ℝ × ℝ) (B₁ B₂ : Ω → Set ℝ)
    (hB₁ : ∀ ω, IsOpen (B₁ ω)) (p : ℝ) (hp : 0 ≤ p)
    (hB₂ : expectedUnitDensity w B₂ ≤ ENNReal.ofReal (2 * p))
    (bad : Set ℝ) (hbad : MeasurableSet bad)
    (hbad_density : unitDensity bad ≤ ENNReal.ofReal p)
    (hstable : ∀ x ∈ Ico (0 : ℝ) 1, x ∉ bad →
      finiteOutcomeProbability w (fun ω =>
        x ∈ sequenceMissedCenters (s₀ := s₀) (s₁ := s₁)
          Z tests k windows (B₁ ω)) ≤ 2 * p) :
    ∃ ω, unitDensity (B₂ ω) +
      unitDensity (sequenceMissedCenters (s₀ := s₀) (s₁ := s₁)
        Z tests k windows (B₁ ω)) ≤ ENNReal.ofReal (5 * p) := by
  apply exists_outcome_density_add_le w hw hnorm B₂ _ p hp hB₂
  have hR := expectedUnitDensity_le_stable_probability w hw hnorm _
    (fun ω => (isClosed_sequenceMissedCenters s₀ s₁ Z tests k windows
      (B₁ ω) (hB₁ ω)).measurableSet)
    bad hbad (2 * p) (by positivity) hstable
  apply hR.trans
  calc
    _ ≤ ENNReal.ofReal (2 * p) + ENNReal.ofReal p :=
      add_le_add le_rfl hbad_density
    _ = ENNReal.ofReal (3 * p) := by
      rw [← ENNReal.ofReal_add (by positivity) hp]
      congr 1
      ring

/-- A finite actual-sequence routing estimate produces an open periodic
blocker with the robust remainder guarantee at the requested input tail. -/
theorem sequence_routing_blocker_of_stable_estimate
    {Z : LogScale} {K : ℕ} (hK : 2 ≤ K)
    {k : ℤ} {Nₛ : ℕ} {p : ℝ} (hp : 0 < p) (hp₁ : p ≤ 1)
    (s : RoutingSchedule K k Nₛ p) (tests : Finset ℕ)
    (N : ℕ) (htail : ∀ n ∈ tests, N ≤ n)
    (α q : ℝ) (hα : 0 < α) (hq : 0 ≤ q)
    (herror : ∀ (r : PowerParams (1 / (K : ℝ)) K) (n : ℕ), n ∈ tests →
      r ∈ sequenceWindowActivations Z n k (globalRoutingWindows s.template) →
        q * (input Z n) ^ (r.1.1 + α) < routingBufferRadius s.template p)
    (hmiss : ∀ x ∈ Ico (0 : ℝ) 1, x ∈ actualStableCenters s.template →
      tableProbability p (fun ω => x ∈ sequenceMissedCenters
        (s₀ := 1 / (K : ℝ)) (s₁ := K)
        Z tests k (globalRoutingWindows s.template)
        (routingInnerBuffer s.template (by have := s.branching_ge_two; omega)
          s.depth_pos p ω)) ≤ 2 * p) :
    ∃ H : Set ℝ, IsOpen H ∧ OnePeriodic H ∧
      unitDensity H < ENNReal.ofReal (6 * p) ∧
      CompactRobustHits Z H K k N α q := by
  have hM : 0 < s.branching := by have := s.branching_ge_two; omega
  let c := s.template
  let B₁ := routingInnerBuffer c hM s.depth_pos p
  let B₂ := routingOuterBuffer c hM s.depth_pos p
  let w := finiteRoutingWeight (S := SelectorAddress c)
    (T := TerminalAddress c s.depth_pos) p
  have hw := finiteRoutingWeight_nonneg (S := SelectorAddress c)
    (T := TerminalAddress c s.depth_pos) p hp.le hp₁
  have hnorm := finiteRoutingWeight_sum (S := SelectorAddress c)
    (T := TerminalAddress c s.depth_pos) p
  have hB₂ : expectedUnitDensity w B₂ ≤ ENNReal.ofReal (2 * p) := by
    have he := expectedUnitDensity_enlargement_le w hw hnorm
      (routedSet c hM s.depth_pos) B₂ (ENNReal.ofReal p)
      (routingOuterBuffer_density_le c hM s.depth_pos s.length_pos p hp)
    apply he.trans
    rw [actual_routedSet_expected_density c hM s.depth_pos p hp.le hp₁
      (measurableSet_actual_routedSet_of_template c hM s.depth_pos s.length_pos)]
    rw [← ENNReal.ofReal_add hp.le hp.le]
    apply le_of_eq
    congr 1
    ring
  obtain ⟨ω, houtcome⟩ := exists_sequenceRouting_outcome_density_add_le_of_stable
    Z w hw hnorm (1 / (K : ℝ)) K tests k (globalRoutingWindows c)
    B₁ B₂ (fun _ => Metric.isOpen_thickening) p hp.le hB₂
    (actualStableCenters c)ᶜ (measurableSet_actualStableCenters c).compl
    (actual_stable_bad_density_le s) (by
      intro x hx hxbad
      rw [← tableProbability_eq_finiteOutcomeProbability]
      exact hmiss x hx (by simpa only [Set.mem_compl_iff, not_not] using hxbad))
  have hperiod := onePeriodic_actual_routedSet_of_template c hM s.depth_pos
    s.length_pos ω
  apply periodic_sequence_outcome_repair hK tests k (globalRoutingWindows c)
    (routedSet c hM s.depth_pos ω) hperiod
    (routingBufferRadius c p) (routingBufferRadius_pos c p hp)
    N htail α q hα hq herror p hp
  simpa [B₁, B₂, routingInnerBuffer, routingOuterBuffer] using houtcome

end ErdosSimilarityGrowingGaps

namespace ErdosSimilarityGrowingGaps

open Set

/-- The first-ge transfer lands in the inner buffer used by finite routing.
This is the buffered version of the missed-center inclusion and matches the
actual output of `exists_power_routing_data`. -/
theorem sequence_missedCenters_subset_power_missedCenters_buffer
    {Z : LogScale} {K : ℕ} (tests : Finset ℕ) (k : ℤ)
    {W : ℕ} (windows : Fin W → ℝ × ℝ) (G : Set ℝ) (ρ : ℝ)
    (sample : ℕ → ℕ)
    (hactivate : ∀ n : ℕ, n ∈ tests →
      ∀ p : PowerParams (1 / (K : ℝ)) K,
        p ∈ windowActivations n k windows →
        p ∈ sequenceWindowActivations Z (sample n) k windows)
    (hpoint : ∀ (n : ℕ), n ∈ tests → ∀ (x : ℝ)
      (p : PowerParams (1 / (K : ℝ)) K),
      powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p) ∈ G →
      powerPoint (input Z (sample n)) ((2 : ℝ) ^ k) (x, p) ∈
        Metric.thickening ρ G) :
    sequenceMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K)
      Z (tests.image sample) k windows (Metric.thickening ρ G) ⊆
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
  let j : {m // m ∈ tests.image sample} :=
    ⟨sample i.1, Finset.mem_image.2 ⟨i.1, i.2, rfl⟩⟩
  exact hxmiss j (hactivate i.1 i.2 p hi)
    (hpoint i.1 i.2 x p hhit)

end ErdosSimilarityGrowingGaps
