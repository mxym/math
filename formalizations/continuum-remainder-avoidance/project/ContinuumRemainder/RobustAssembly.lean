import ContinuumRemainder.Specification
import ContinuumRemainder.RobustRepair
import ContinuumGeometric.RoutingAssembly

/-!
Actual finite-law, periodic measure and robust full-sequence repair assembly.
The only probabilistic input to the last theorem is the displayed estimate
for the actual stable-center sampled missed-center event.  It does not assume
the robust blocker specification, an abstract random set, or an open cover.
-/
namespace ContinuumRemainder

open Set MeasureTheory Filter Topology ContinuumGeometric
open scoped ENNReal

theorem onePeriodic_sampledMissedCenters (s₀ s₁ : ℝ) (tests : Finset ℕ)
    (a z : ℕ → ℝ) (k : ℤ) {W : ℕ} (windows : Fin W → ℝ × ℝ)
    (B₁ : Set ℝ) (hperiod : OnePeriodic B₁) :
    OnePeriodic (sampledMissedCenters (s₀ := s₀) (s₁ := s₁)
      tests a z k windows B₁) := by
  intro x
  simp only [sampledMissedCenters, mem_missedCenters_iff]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p, fun i hi hhit => hp i hi ?_⟩
    have ht := (hperiod (powerPoint (a i.1) ((2 : ℝ) ^ k) (x, p))).2 hhit
    convert ht using 1
    simp only [powerPoint]
    ring
  · rintro ⟨p, hp⟩
    refine ⟨p, fun i hi hhit => hp i hi ?_⟩
    apply (hperiod (powerPoint (a i.1) ((2 : ℝ) ^ k) (x, p))).1
    convert hhit using 1
    simp only [powerPoint]
    ring

/-- Actual outer-buffer/missed-center outcome repair for the prescribed input set. -/
theorem periodic_sampled_robust_outcome_repair
    (A : Set ℝ) (s₀ s₁ α₀ U : ℝ) (hs₀ : 0 < s₀) (hα : 0 < α₀)
    (tests : Finset ℕ) (a z : ℕ → ℝ) (hamem : ∀ n, a n ∈ A)
    (ha : ∀ n, 0 < a n) (haz : ∀ n, a n = (2 : ℝ) ^ (-(z n)))
    (hanull : Tendsto a atTop (𝓝 0)) (k : ℤ) (q h : ℕ)
    (hatail : ∀ n, a n < dyadic h) (hUk : 0 ≤ U + (k : ℝ))
    {W : ℕ} (windows : Fin W → ℝ × ℝ) (hwindow : ∀ w, U ≤ (windows w).1)
    (B : Set ℝ) (hperiod : OnePeriodic B) (p : ℝ) (hp : 0 < p)
    (houtcome : unitDensity (Metric.thickening (2 * errorRadius q k α₀ s₁ U) B) +
      unitDensity (sampledMissedCenters (s₀ := s₀) (s₁ := s₁) tests a z k windows
        (Metric.thickening (errorRadius q k α₀ s₁ U) B)) ≤ ENNReal.ofReal (5 * p)) :
    ∃ H : Set ℝ, IsOpen H ∧ OnePeriodic H ∧
      unitDensity H < ENNReal.ofReal (6 * p) ∧ RobustCompactHits H A s₀ s₁ α₀ k q h := by
  let r := errorRadius q k α₀ s₁ U
  let R := sampledMissedCenters (s₀ := s₀) (s₁ := s₁) tests a z k windows
    (Metric.thickening r B)
  obtain ⟨V, hVo, hVp, hRV, hVμ⟩ := closed_onePeriodic_open_cover R
    (isClosed_sampledMissedCenters s₀ s₁ tests a z (fun n _ => ha n)
      k windows _ Metric.isOpen_thickening)
    (onePeriodic_sampledMissedCenters s₀ s₁ tests a z k windows _
      (onePeriodic_thickening hperiod r)) p hp
  refine ⟨Metric.thickening (2 * r) B ∪ V, Metric.isOpen_thickening.union hVo,
    onePeriodic_union (onePeriodic_thickening hperiod (2 * r)) hVp, ?_, ?_⟩
  · calc
      unitDensity (Metric.thickening (2 * r) B ∪ V) ≤
          unitDensity (Metric.thickening (2 * r) B) + unitDensity V := unitDensity_union_le _ _
      _ < unitDensity (Metric.thickening (2 * r) B) +
          (unitDensity R + ENNReal.ofReal p) :=
        ENNReal.add_lt_add_left
          (ne_top_of_le_ne_top ENNReal.one_ne_top (unitDensity_le_one _)) hVμ
      _ = (unitDensity (Metric.thickening (2 * r) B) + unitDensity R) +
          ENNReal.ofReal p := (add_assoc _ _ _).symm
      _ ≤ ENNReal.ofReal (5 * p) + ENNReal.ofReal p := add_le_add houtcome le_rfl
      _ = ENNReal.ofReal (6 * p) := by
        rw [← ENNReal.ofReal_add (by positivity) hp.le]
        congr 1
        ring
  · intro x s t e hs ht he
    let param : PowerParams s₀ s₁ := (⟨s, hs⟩, ⟨t, ht⟩)
    have hseqerror : ∀ n, |e (a n)| ≤ (q : ℝ) * (a n) ^ (param.1.1 + α₀) :=
      fun n => he (a n) (hamem n) (ha n) (hatail n)
    obtain ⟨_, hrepair⟩ := sampled_robust_repair_all_centers s₀ s₁ α₀ U hs₀ hα
      tests a z ha haz hanull k q hUk windows hwindow B V hVo hRV 0
      (fun _ _ => Nat.zero_le _)
    obtain ⟨n, _, hhit⟩ := hrepair x param (fun n => e (a n)) hseqerror
    exact ⟨a n, hamem n, ha n, hatail n, hhit⟩

noncomputable def sampledRoutingInnerBuffer {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (q : ℕ) (k : ℤ) (α₀ s₁ : ℝ)
    (ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd)) : Set ℝ :=
  Metric.thickening (errorRadius q k α₀ s₁ c.origin) (routedSet c hM hd ω)

noncomputable def sampledRoutingOuterBuffer {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (q : ℕ) (k : ℤ) (α₀ s₁ : ℝ)
    (ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd)) : Set ℝ :=
  Metric.thickening (2 * errorRadius q k α₀ s₁ c.origin) (routedSet c hM hd ω)

/-- The verified actual finest-grid representation pays the actual radius cost. -/
theorem sampledRoutingOuterBuffer_density_le {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (hL : 0 < c.baseLength)
    (q : ℕ) (k : ℤ) (α₀ s₁ p : ℝ)
    (hcost : 4 * (routingFinestGrid c : ℝ) * errorRadius q k α₀ s₁ c.origin ≤ p)
    (ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd)) :
    unitDensity (sampledRoutingOuterBuffer c hM hd q k α₀ s₁ ω) ≤
      unitDensity (routedSet c hM hd ω) + ENNReal.ofReal p := by
  unfold sampledRoutingOuterBuffer
  rw [actual_routedSet_finite_grid c hM hd hL ω]
  exact (unitDensity_periodicGridSet_double_buffer_le _ (by positivity) _
    (routedCanonicalCells_subset c hM hd _ ω) _ (errorRadius_pos _ _ _ _ _).le).trans
    (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hcost))

/-- Conditional only on the ACTUAL stable miss estimate; all other measure,
outcome, periodic cover and arbitrary-error repair steps are proved here. -/
theorem actual_sampled_routing_blocker_of_stable_miss
    (A : Set ℝ) (s₀ s₁ α₀ : ℝ) (hs₀ : 0 < s₀) (hα : 0 < α₀)
    (a z : ℕ → ℝ) (hamem : ∀ n, a n ∈ A) (ha : ∀ n, 0 < a n)
    (haz : ∀ n, a n = (2 : ℝ) ^ (-(z n))) (hanull : Tendsto a atTop (𝓝 0))
    (k : ℤ) (q h : ℕ) (hatail : ∀ n, a n < dyadic h)
    {M d : ℕ} (c : RoutingTemplate M d) (hM : 0 < M) (hd : 0 < d)
    (hL : 0 < c.baseLength) (tests : Finset ℕ)
    (hUk : 0 ≤ (c.origin : ℝ) + (k : ℝ))
    (hwindow : ∀ w, (c.origin : ℝ) ≤ (globalRoutingWindows c w).1)
    (p : ℝ) (hp : 0 < p) (hp₁ : p ≤ 1)
    (hcost : 4 * (routingFinestGrid c : ℝ) *
      errorRadius q k α₀ s₁ c.origin ≤ p)
    (hbad : unitDensity (actualStableCenters c)ᶜ ≤ ENNReal.ofReal p)
    (hmiss : ∀ x ∈ Ico (0 : ℝ) 1, x ∈ actualStableCenters c →
      tableProbability p (fun ω => x ∈ sampledMissedCenters
        (s₀ := s₀) (s₁ := s₁) tests a z k (globalRoutingWindows c)
        (sampledRoutingInnerBuffer c hM hd q k α₀ s₁ ω)) ≤ 2 * p) :
    ∃ H : Set ℝ, IsOpen H ∧ OnePeriodic H ∧
      unitDensity H < ENNReal.ofReal (6 * p) ∧ RobustCompactHits H A s₀ s₁ α₀ k q h := by
  let B₁ := sampledRoutingInnerBuffer c hM hd q k α₀ s₁
  let B₂ := sampledRoutingOuterBuffer c hM hd q k α₀ s₁
  let R := fun ω => sampledMissedCenters (s₀ := s₀) (s₁ := s₁)
    tests a z k (globalRoutingWindows c) (B₁ ω)
  let w := finiteRoutingWeight (S := SelectorAddress c) (T := TerminalAddress c hd) p
  have hw := finiteRoutingWeight_nonneg (S := SelectorAddress c)
    (T := TerminalAddress c hd) p hp.le hp₁
  have hnorm := finiteRoutingWeight_sum (S := SelectorAddress c)
    (T := TerminalAddress c hd) p
  have hB₂ : expectedUnitDensity w B₂ ≤ ENNReal.ofReal (2 * p) := by
    have he := expectedUnitDensity_enlargement_le w hw hnorm (routedSet c hM hd)
      B₂ (ENNReal.ofReal p)
      (sampledRoutingOuterBuffer_density_le c hM hd hL q k α₀ s₁ p hcost)
    apply he.trans
    rw [actual_routedSet_expected_density c hM hd p hp.le hp₁
      (measurableSet_actual_routedSet_of_template c hM hd hL)]
    rw [← ENNReal.ofReal_add hp.le hp.le]
    apply le_of_eq
    congr 1
    ring
  have hR : expectedUnitDensity w R ≤ ENNReal.ofReal (3 * p) := by
    have he := expectedUnitDensity_le_stable_probability w hw hnorm R
      (fun ω => (isClosed_sampledMissedCenters s₀ s₁ tests a z
        (fun n _ => ha n) k (globalRoutingWindows c) _ Metric.isOpen_thickening).measurableSet)
      (actualStableCenters c)ᶜ (measurableSet_actualStableCenters c).compl
      (2 * p) (by positivity) (by
        intro x hx hxbad
        rw [← tableProbability_eq_finiteOutcomeProbability]
        exact hmiss x hx (by simpa only [Set.mem_compl_iff, not_not] using hxbad))
    apply he.trans
    calc
      _ ≤ ENNReal.ofReal (2 * p) + ENNReal.ofReal p := add_le_add le_rfl hbad
      _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) hp.le]
        congr 1
        ring
  obtain ⟨ω, houtcome⟩ := exists_outcome_density_add_le w hw hnorm B₂ R p hp.le hB₂ hR
  exact periodic_sampled_robust_outcome_repair A s₀ s₁ α₀ c.origin hs₀ hα tests a z
    hamem ha haz hanull k q h hatail hUk (globalRoutingWindows c) hwindow
    (routedSet c hM hd ω) (onePeriodic_actual_routedSet_of_template c hM hd hL ω)
    p hp houtcome

end ContinuumRemainder
