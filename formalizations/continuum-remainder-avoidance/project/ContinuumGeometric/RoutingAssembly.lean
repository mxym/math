import ContinuumGeometric.RoutingGlobalGrid
import ContinuumGeometric.FiniteRoutingProbability
import ContinuumGeometric.RoutingSchedule
import ContinuumGeometric.RoutingStableMeasure
import ContinuumGeometric.RoutingStableGeometry

/-!
The actual global test families and the final finite-outcome/repair assembly.
The remaining pointwise stable-center estimate is an explicit premise here;
it must be proved from actual local routing before the blocker specification
or MainTarget can be closed.
-/
namespace ContinuumGeometric

open Set MeasureTheory

noncomputable def globalRoutingEdgeEnumeration (M d : ℕ) :
    Fin (Fintype.card (RoutingEdge M d)) ≃ RoutingEdge M d :=
  (Fintype.equivFin (RoutingEdge M d)).symm

noncomputable def globalRoutingWindows {M d : ℕ} (c : RoutingTemplate M d) :
    Fin (Fintype.card (RoutingEdge M d)) → ℝ × ℝ := fun i =>
  let e := globalRoutingEdgeEnumeration M d i
  ((c.edgeStart e : ℝ), (c.edgeStart e : ℝ) + c.edgeLength e)

noncomputable def globalRoutingTests {M d : ℕ} (c : RoutingTemplate M d)
    (K N : ℕ) (k : ℤ) : Finset ℕ :=
  candidateOriginalIndices (candidateStride (1 / (K : ℝ))) N c.origin
    (RoutingTemplate.span M c.gap c.baseLength d) k

theorem globalRoutingTests_tail {M d : ℕ} (c : RoutingTemplate M d)
    (K N : ℕ) (k : ℤ) : ∀ n ∈ globalRoutingTests c K N k, N ≤ n := by
  intro n hn
  obtain ⟨j, _, htail, heq⟩ := (mem_candidateOriginalIndices_iff _ _ _ _ _ _).1 hn
  simpa only [heq] using htail

noncomputable def routingFinestEndpoint {M d : ℕ} (c : RoutingTemplate M d) : ℕ :=
  c.origin + RoutingTemplate.span M c.gap c.baseLength d - 1

noncomputable def routingFinestGrid {M d : ℕ} (c : RoutingTemplate M d) : ℕ :=
  2 ^ (routingFinestEndpoint c + 3)

noncomputable def routingBufferRadius {M d : ℕ} (c : RoutingTemplate M d) (p : ℝ) : ℝ :=
  p / (8 * (routingFinestGrid c : ℝ))

noncomputable def routingInnerBuffer {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (p : ℝ)
    (ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd)) : Set ℝ :=
  Metric.thickening (routingBufferRadius c p) (routedSet c hM hd ω)

noncomputable def routingOuterBuffer {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (p : ℝ)
    (ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd)) : Set ℝ :=
  Metric.thickening (2 * routingBufferRadius c p) (routedSet c hM hd ω)

theorem routingBufferRadius_pos {M d : ℕ} (c : RoutingTemplate M d) (p : ℝ) (hp : 0 < p) :
    0 < routingBufferRadius c p := by
  unfold routingBufferRadius routingFinestGrid
  positivity

theorem routingOuterBuffer_density_le {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (hL : 0 < c.baseLength) (p : ℝ) (hp : 0 < p)
    (ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd)) :
    unitDensity (routingOuterBuffer c hM hd p ω) ≤
      unitDensity (routedSet c hM hd ω) + ENNReal.ofReal p := by
  unfold routingOuterBuffer routingBufferRadius routingFinestGrid routingFinestEndpoint
  rw [actual_routedSet_finite_grid c hM hd hL ω]
  exact (unitDensity_grid_budget_double_buffer_lt _ (by positivity) _
    (routedCanonicalCells_subset c hM hd _ ω) p hp).le

/-- This is the concrete final assembly, conditional only on the actual stable
miss estimate and its measured exceptional set. It introduces no random law,
address-separation, compactification, or open-cover existence assumption. -/
theorem actual_routing_blocker_of_stable_estimate {K : ℕ} (hK : 2 ≤ K)
    {k : ℤ} {N : ℕ} {p : ℝ} (hp : 0 < p) (hp₁ : p ≤ 1)
    (s : RoutingSchedule K k N p)
    (bad : Set ℝ) (hbad : MeasurableSet bad)
    (hbad_density : unitDensity bad ≤ ENNReal.ofReal p)
    (hmiss : ∀ x ∈ Ico (0 : ℝ) 1, x ∉ bad →
      tableProbability p (fun ω => x ∈ powerMissedCenters
        (s₀ := 1 / (K : ℝ)) (s₁ := K) (globalRoutingTests s.template K N k) k
        (globalRoutingWindows s.template)
        (routingInnerBuffer s.template (by have := s.branching_ge_two; omega)
          s.depth_pos p ω)) ≤ 2 * p) :
    ∃ H : Set ℝ, IsOpen H ∧ OnePeriodic H ∧
      unitDensity H < ENNReal.ofReal (6 * p) ∧ CompactPowerHits H K k N := by
  have hM : 0 < s.branching := by have := s.branching_ge_two; omega
  let c := s.template
  let B₁ := routingInnerBuffer c hM s.depth_pos p
  let B₂ := routingOuterBuffer c hM s.depth_pos p
  let w := finiteRoutingWeight (S := SelectorAddress c) (T := TerminalAddress c s.depth_pos) p
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
    bad hbad hbad_density (by
      intro x hx hxbad
      rw [← tableProbability_eq_finiteOutcomeProbability]
      exact hmiss x hx hxbad)
  have hperiod := onePeriodic_actual_routedSet_of_template c hM s.depth_pos s.length_pos ω
  exact periodic_power_outcome_repair K hK (globalRoutingTests c K N k) k
    (globalRoutingWindows c) (B₁ ω) (B₂ ω)
    Metric.isOpen_thickening Metric.isOpen_thickening
    (onePeriodic_thickening hperiod _) (onePeriodic_thickening hperiod _)
    (Metric.thickening_mono (by have := routingBufferRadius_pos c p hp; linarith) _)
    N (globalRoutingTests_tail c K N k) p hp houtcome

/-- The scheduled concrete predecessor vector also discharges the exceptional
set's measure budget. Only the actual stable-center probability remains. -/
theorem actual_routing_blocker_of_actual_stable_miss {K : ℕ} (hK : 2 ≤ K)
    {k : ℤ} {N : ℕ} {p : ℝ} (hp : 0 < p) (hp₁ : p ≤ 1)
    (s : RoutingSchedule K k N p)
    (hmiss : ∀ x ∈ Ico (0 : ℝ) 1, x ∈ actualStableCenters s.template →
      tableProbability p (fun ω => x ∈ powerMissedCenters
        (s₀ := 1 / (K : ℝ)) (s₁ := K) (globalRoutingTests s.template K N k) k
        (globalRoutingWindows s.template)
        (routingInnerBuffer s.template (by have := s.branching_ge_two; omega)
          s.depth_pos p ω)) ≤ 2 * p) :
    ∃ H : Set ℝ, IsOpen H ∧ OnePeriodic H ∧
      unitDensity H < ENNReal.ofReal (6 * p) ∧ CompactPowerHits H K k N := by
  apply actual_routing_blocker_of_stable_estimate hK hp hp₁ s
    (actualStableCenters s.template)ᶜ (measurableSet_actualStableCenters _).compl
  · apply (unitDensity_actualStable_compl_le s.template).trans
    apply ENNReal.ofReal_le_ofReal
    rw [dyadic_integer_gap_rpow]
    exact s.stable_boundary_small.le
  · intro x hx hxbad
    exact hmiss x hx (by simpa only [Set.mem_compl_iff, not_not] using hxbad)

end ContinuumGeometric
