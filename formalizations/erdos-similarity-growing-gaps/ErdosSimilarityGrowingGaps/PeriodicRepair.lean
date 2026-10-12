import ErdosSimilarityGrowingGaps.Avoidance
import ErdosSimilarityGrowingGaps.GridBoundary
import ErdosSimilarityGrowingGaps.GridGeometry
import ErdosSimilarityGrowingGaps.PowerCore
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Group.Measure

namespace ErdosSimilarityGrowingGaps

open Set MeasureTheory Filter Topology
open scoped ENNReal

def CompactPowerHits (H : Set ℝ) (K : ℕ) (k : ℤ) (N : ℕ) : Prop :=
  ∀ (x : ℝ) (p : PowerParams (1 / (K : ℝ)) K),
    ∃ n : ℕ, N ≤ n ∧ powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p) ∈ H

theorem zero_error_buffer_budget (p : ℝ) (N : ℕ) (hp : 0 < p) (hN : 0 < N) :
    0 < p / (8 * (N : ℝ)) ∧
    4 * (N : ℝ) * (p / (8 * (N : ℝ))) = p / 2 ∧
    4 * (N : ℝ) * (p / (8 * (N : ℝ))) < p := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have heq : 4 * (N : ℝ) * (p / (8 * (N : ℝ))) = p / 2 := by
    field_simp
    ring
  exact ⟨by positivity, heq, by rw [heq]; linarith⟩

theorem onePeriodic_union {A B : Set ℝ} (hA : OnePeriodic A) (hB : OnePeriodic B) :
    OnePeriodic (A ∪ B) := by
  intro x
  exact or_congr (hA x) (hB x)

theorem unitDensity_union_le (A B : Set ℝ) :
    unitDensity (A ∪ B) ≤ unitDensity A + unitDensity B := by
  unfold unitDensity
  rw [union_inter_distrib_right]
  exact measure_union_le _ _

theorem onePeriodic_thickening {A : Set ℝ} (hA : OnePeriodic A) (r : ℝ) :
    OnePeriodic (Metric.thickening r A) := by
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := Metric.mem_thickening_iff.1 hx
    apply Metric.mem_thickening_iff.2
    refine ⟨y - 1, ?_, ?_⟩
    · apply (hA (y - 1)).1
      simpa using hy
    · rw [Real.dist_eq] at hxy ⊢
      convert hxy using 1 <;> congr 1 <;> ring
  · intro hx
    obtain ⟨y, hy, hxy⟩ := Metric.mem_thickening_iff.1 hx
    apply Metric.mem_thickening_iff.2
    refine ⟨y + 1, (hA y).2 hy, ?_⟩
    simpa only [dist_add_right] using hxy

theorem thickening_integerPeriodization_subset (A : Set ℝ) (r : ℝ) :
    Metric.thickening r (integerPeriodization A) ⊆
      integerPeriodization (Metric.thickening r A) := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := Metric.mem_thickening_iff.1 hx
  obtain ⟨n, hn⟩ := mem_iUnion.1 hy
  refine mem_iUnion.2 ⟨n, Metric.mem_thickening_iff.2 ⟨y + (n : ℝ), hn, ?_⟩⟩
  simpa using hxy

theorem integerPeriodization_inter_eq (A : Set ℝ) (hA : A ⊆ Ico 0 1) :
    integerPeriodization A ∩ Ico (0 : ℝ) 1 = A := by
  ext x
  constructor
  · rintro ⟨hx, hx₀, hx₁⟩
    obtain ⟨n, hn⟩ := mem_iUnion.1 hx
    have hb := hA hn
    have hnlo : (-1 : ℝ) < n := by linarith [hb.1]
    have hnhi : (n : ℝ) < 1 := by linarith [hb.2]
    have hn₀ : n = 0 := by
      have hl : (-1 : ℤ) < n := by exact_mod_cast hnlo
      have hh : n < (1 : ℤ) := by exact_mod_cast hnhi
      omega
    simpa [hn₀] using hn
  · intro hx
    exact ⟨mem_iUnion.2 ⟨0, by simpa using hx⟩, hA hx⟩

noncomputable def finiteGridCore (N : ℕ) (cells : Finset ℤ) : Set ℝ :=
  ⋃ j ∈ cells, Ico ((j : ℝ) / N) (((j : ℝ) + 1) / N)

theorem mem_gridCell_iff (N : ℕ) (hN : 0 < N) (j : ℤ) (x : ℝ) :
    x ∈ Ico ((j : ℝ) / N) (((j : ℝ) + 1) / N) ↔ Int.floor ((N : ℝ) * x) = j := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Int.floor_eq_iff]
  simp only [mem_Ico, div_le_iff₀ hNr, lt_div_iff₀ hNr, mul_comm]

theorem finiteGridCore_subset (N : ℕ) (hN : 0 < N) (cells : Finset ℤ)
    (hcells : cells ⊆ Finset.Ico 0 (N : ℤ)) : finiteGridCore N cells ⊆ Ico 0 1 := by
  intro x hx
  obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 hx
  obtain ⟨hj₀, hj₁⟩ := Finset.mem_Ico.1 (hcells hj)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hjr₀ : (0 : ℝ) ≤ j := by exact_mod_cast hj₀
  have hjr₁ : (j : ℝ) + 1 ≤ N := by exact_mod_cast (by omega : j + 1 ≤ (N : ℤ))
  exact ⟨(div_nonneg hjr₀ hNr.le).trans hxj.1,
    hxj.2.trans_le ((div_le_iff₀ hNr).2 (by simpa using hjr₁))⟩

theorem floor_grid_add_int (N : ℕ) (x : ℝ) (n : ℤ) :
    Int.floor ((N : ℝ) * (x + (n : ℝ))) = Int.floor ((N : ℝ) * x) + (N : ℤ) * n := by
  have heq : (N : ℝ) * (x + (n : ℝ)) = (N : ℝ) * x + (((N : ℤ) * n : ℤ) : ℝ) := by
    push_cast
    ring
  rw [heq, Int.floor_add_intCast]

/-- Exact representation of the ACTUAL modulo-floor grid by half-open cells
and integer translates; it includes negative lifts and cell boundaries. -/
theorem periodicGridSet_eq_integerPeriodization (N : ℕ) (hN : 0 < N)
    (cells : Finset ℤ) (hcells : cells ⊆ Finset.Ico 0 (N : ℤ)) :
    periodicGridSet N cells = integerPeriodization (finiteGridCore N cells) := by
  ext x
  constructor
  · intro hx
    let a := Int.floor ((N : ℝ) * x)
    refine mem_iUnion.2 ⟨-(a / (N : ℤ)), ?_⟩
    apply mem_iUnion₂.2
    refine ⟨a % (N : ℤ), hx, (mem_gridCell_iff N hN _ _).2 ?_⟩
    rw [floor_grid_add_int]
    change a + (N : ℤ) * -(a / (N : ℤ)) = a % (N : ℤ)
    rw [Int.emod_def, mul_neg]
    ring
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.1 hx
    obtain ⟨j, hj, hcell⟩ := mem_iUnion₂.1 hn
    have hfloor := (mem_gridCell_iff N hN j _).1 hcell
    rw [floor_grid_add_int] at hfloor
    have hjrange := Finset.mem_Ico.1 (hcells hj)
    have hjmod : j % (N : ℤ) = j := Int.emod_eq_of_lt hjrange.1 hjrange.2
    change Int.floor ((N : ℝ) * x) % (N : ℤ) ∈ cells
    have hmod : Int.floor ((N : ℝ) * x) % (N : ℤ) = j := by
      have := congrArg (fun a : ℤ => a % (N : ℤ)) hfloor
      simpa [Int.add_emod, hjmod] using this
    rw [hmod]
    exact hj

theorem onePeriodic_periodicGridSet (N : ℕ) (hN : 0 < N) (cells : Finset ℤ)
    (hcells : cells ⊆ Finset.Ico 0 (N : ℤ)) : OnePeriodic (periodicGridSet N cells) := by
  rw [periodicGridSet_eq_integerPeriodization N hN cells hcells]
  exact onePeriodic_integerPeriodization _

theorem measurableSet_periodicGridSet (N : ℕ) (hN : 0 < N) (cells : Finset ℤ)
    (hcells : cells ⊆ Finset.Ico 0 (N : ℤ)) : MeasurableSet (periodicGridSet N cells) := by
  rw [periodicGridSet_eq_integerPeriodization N hN cells hcells]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.preimage _ (measurable_id.add_const _)
  exact MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ => measurableSet_Ico

theorem volume_finiteGridCore (N : ℕ) (hN : 0 < N) (cells : Finset ℤ) :
    volume (finiteGridCore N cells) =
      ∑ _j ∈ cells, ENNReal.ofReal (1 / (N : ℝ)) := by
  have hdis : (↑cells : Set ℤ).PairwiseDisjoint
      (fun j => Ico ((j : ℝ) / N) (((j : ℝ) + 1) / N)) := by
    intro i hi j hj hij
    apply disjoint_left.2
    intro x hxi hxj
    exact hij (((mem_gridCell_iff N hN i x).1 hxi).symm.trans
      ((mem_gridCell_iff N hN j x).1 hxj))
  unfold finiteGridCore
  rw [measure_biUnion_finset hdis (fun _ _ => measurableSet_Ico)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Real.volume_Ico]
  congr 1
  ring

theorem unitDensity_periodicGridSet (N : ℕ) (hN : 0 < N) (cells : Finset ℤ)
    (hcells : cells ⊆ Finset.Ico 0 (N : ℤ)) :
    unitDensity (periodicGridSet N cells) =
      ∑ _j ∈ cells, ENNReal.ofReal (1 / (N : ℝ)) := by
  rw [periodicGridSet_eq_integerPeriodization N hN cells hcells]
  unfold unitDensity
  rw [integerPeriodization_inter_eq _ (finiteGridCore_subset N hN cells hcells)]
  exact volume_finiteGridCore N hN cells

theorem volume_thickening_Ico_le (a b r : ℝ) (hr : 0 ≤ r) (hab : a ≤ b) :
    volume (Metric.thickening r (Ico a b)) ≤ ENNReal.ofReal (b - a + 2 * r) := by
  have hsub : Metric.thickening r (Ico a b) ⊆ Ioo (a - r) (b + r) := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Metric.mem_thickening_iff.1 hx
    rw [Real.dist_eq, abs_lt] at hxy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  calc
    volume (Metric.thickening r (Ico a b)) ≤ volume (Ioo (a - r) (b + r)) := measure_mono hsub
    _ = ENNReal.ofReal (b - a + 2 * r) := by rw [Real.volume_Ioo]; congr 1; ring

/-- A finite canonical periodic grid grows by at most 2Nρ under an open
ρ-buffer.  The count can be sharpened to the number of selected cells. -/
theorem unitDensity_periodicGridSet_thickening_le (N : ℕ) (hN : 0 < N)
    (cells : Finset ℤ) (hcells : cells ⊆ Finset.Ico 0 (N : ℤ))
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    unitDensity (Metric.thickening ρ (periodicGridSet N cells)) ≤
      unitDensity (periodicGridSet N cells) + ENNReal.ofReal (2 * (N : ℝ) * ρ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hbound : volume (Metric.thickening ρ (finiteGridCore N cells)) ≤
      (∑ _j ∈ cells, ENNReal.ofReal (1 / (N : ℝ))) +
        cells.card • ENNReal.ofReal (2 * ρ) := by
    unfold finiteGridCore
    rw [Metric.thickening_iUnion]
    simp_rw [Metric.thickening_iUnion]
    calc
      volume (⋃ j ∈ cells, Metric.thickening ρ (Ico ((j : ℝ) / N) (((j : ℝ) + 1) / N)))
          ≤ ∑ j ∈ cells, volume (Metric.thickening ρ (Ico ((j : ℝ) / N) (((j : ℝ) + 1) / N))) :=
        measure_biUnion_finset_le _ _
      _ ≤ ∑ _j ∈ cells, (ENNReal.ofReal (1 / (N : ℝ)) + ENNReal.ofReal (2 * ρ)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hb := volume_thickening_Ico_le ((j : ℝ) / N) (((j : ℝ) + 1) / N) ρ hρ
          ((div_le_div_iff_of_pos_right hNr).2 (by linarith))
        convert hb using 1
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_const]
  have hcard : cells.card ≤ N := by
    simpa [Int.card_Ico] using Finset.card_le_card hcells
  rw [periodicGridSet_eq_integerPeriodization N hN cells hcells]
  calc
    unitDensity (Metric.thickening ρ (integerPeriodization (finiteGridCore N cells)))
        ≤ unitDensity (integerPeriodization (Metric.thickening ρ (finiteGridCore N cells))) :=
      measure_mono (inter_subset_inter_left _ (thickening_integerPeriodization_subset _ _))
    _ ≤ volume (Metric.thickening ρ (finiteGridCore N cells)) :=
      unitDensity_integerPeriodization_le _ Metric.isOpen_thickening.measurableSet
    _ ≤ (∑ _j ∈ cells, ENNReal.ofReal (1 / (N : ℝ))) + cells.card • ENNReal.ofReal (2 * ρ) := hbound
    _ ≤ (∑ _j ∈ cells, ENNReal.ofReal (1 / (N : ℝ))) + N • ENNReal.ofReal (2 * ρ) :=
      add_le_add le_rfl (nsmul_le_nsmul_left (by positivity) hcard)
    _ = unitDensity (integerPeriodization (finiteGridCore N cells)) +
        ENNReal.ofReal (2 * (N : ℝ) * ρ) := by
      rw [unitDensity, integerPeriodization_inter_eq _ (finiteGridCore_subset N hN cells hcells),
        volume_finiteGridCore N hN cells, ← ENNReal.ofReal_nsmul]
      congr 2
      simp only [nsmul_eq_mul]
      ring

/-- The actual DOUBLE open buffer costs at most 4Nr, including wrapping cells. -/
theorem unitDensity_periodicGridSet_double_buffer_le (N : ℕ) (hN : 0 < N)
    (cells : Finset ℤ) (hcells : cells ⊆ Finset.Ico 0 (N : ℤ))
    (r : ℝ) (hr : 0 ≤ r) :
    unitDensity (Metric.thickening (2 * r) (periodicGridSet N cells)) ≤
      unitDensity (periodicGridSet N cells) + ENNReal.ofReal (4 * (N : ℝ) * r) := by
  convert unitDensity_periodicGridSet_thickening_le N hN cells hcells (2 * r) (by positivity) using 1
  congr 2
  ring

theorem unitDensity_grid_budget_double_buffer_lt (N : ℕ) (hN : 0 < N)
    (cells : Finset ℤ) (hcells : cells ⊆ Finset.Ico 0 (N : ℤ))
    (p : ℝ) (hp : 0 < p) :
    unitDensity (Metric.thickening (2 * (p / (8 * (N : ℝ)))) (periodicGridSet N cells)) <
      unitDensity (periodicGridSet N cells) + ENNReal.ofReal p := by
  obtain ⟨hr, heq, hlt⟩ := zero_error_buffer_budget p N hp hN
  calc
    unitDensity (Metric.thickening (2 * (p / (8 * (N : ℝ)))) (periodicGridSet N cells))
        ≤ unitDensity (periodicGridSet N cells) + ENNReal.ofReal (p / 2) := by
      simpa only [heq] using unitDensity_periodicGridSet_double_buffer_le N hN cells hcells
        (p / (8 * (N : ℝ))) hr.le
    _ < unitDensity (periodicGridSet N cells) + ENNReal.ofReal p :=
      ENNReal.add_lt_add_left
        (ne_top_of_le_ne_top ENNReal.one_ne_top (unitDensity_le_one _))
        ((ENNReal.ofReal_lt_ofReal_iff hp).2 (by linarith))

/-- A periodic open outer cover of any closed periodic real set, with an
arbitrarily small strictly positive excess in a fundamental interval.
The finite restricted measure lets ordinary real thickenings handle the
wrap at both endpoints without a separate representative selection. -/
theorem closed_onePeriodic_open_cover (R : Set ℝ) (hR : IsClosed R)
    (hperiod : OnePeriodic R) (p : ℝ) (hp : 0 < p) :
    ∃ V : Set ℝ, IsOpen V ∧ OnePeriodic V ∧ R ⊆ V ∧
      unitDensity V < unitDensity R + ENNReal.ofReal p := by
  let μ : Measure ℝ := volume.restrict (Ico 0 1)
  have hfinite : ∃ r > (0 : ℝ), μ (Metric.thickening r R) ≠ ∞ :=
    ⟨1, zero_lt_one, measure_ne_top _ _⟩
  have ht := tendsto_measure_thickening_of_isClosed hfinite hR
  have hlt : μ R < μ R + ENNReal.ofReal p :=
    ENNReal.lt_add_right (measure_ne_top _ _) (ENNReal.ofReal_pos.2 hp).ne'
  have hevent : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      μ (Metric.thickening r R) < μ R + ENNReal.ofReal p :=
    ht.eventually (eventually_lt_nhds hlt)
  obtain ⟨r, hbound, hr⟩ := (hevent.and self_mem_nhdsWithin).exists
  refine ⟨Metric.thickening r R, Metric.isOpen_thickening,
    onePeriodic_thickening hperiod r, Metric.self_subset_thickening hr R, ?_⟩
  simpa only [μ, Measure.restrict_apply Metric.isOpen_thickening.measurableSet,
    Measure.restrict_apply hR.measurableSet, unitDensity] using hbound

theorem onePeriodic_powerMissedCenters (s₀ s₁ : ℝ) (tests : Finset ℕ)
    (k : ℤ) {W : ℕ} (windows : Fin W → ℝ × ℝ) (B₁ : Set ℝ)
    (hperiod : OnePeriodic B₁) :
    OnePeriodic (powerMissedCenters (s₀ := s₀) (s₁ := s₁) tests k windows B₁) := by
  intro x
  simp only [powerMissedCenters, mem_missedCenters_iff]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p, fun i hi hhit => hp i hi ?_⟩
    have ht := (hperiod (powerPoint (dyadic i.1) ((2 : ℝ) ^ k) (x, p))).2 hhit
    convert ht using 1 <;> simp only [powerPoint] <;> ring
  · rintro ⟨p, hp⟩
    refine ⟨p, fun i hi hhit => hp i hi ?_⟩
    apply (hperiod (powerPoint (dyadic i.1) ((2 : ℝ) ^ k) (x, p))).1
    convert hhit using 1 <;> simp only [powerPoint] <;> ring

/-- An actual B₂/R outcome gives an actual periodic all-center blocker.
Only the displayed finite-outcome density inequality is an input. -/
theorem periodic_power_outcome_repair (K : ℕ) (hK : 2 ≤ K)
    (tests : Finset ℕ) (k : ℤ) {W : ℕ} (windows : Fin W → ℝ × ℝ)
    (B₁ B₂ : Set ℝ) (hopen₁ : IsOpen B₁) (hopen₂ : IsOpen B₂)
    (hperiod₁ : OnePeriodic B₁) (hperiod₂ : OnePeriodic B₂)
    (hB₁₂ : B₁ ⊆ B₂) (N : ℕ) (htail : ∀ n ∈ tests, N ≤ n)
    (p : ℝ) (hp : 0 < p)
    (houtcome : unitDensity B₂ + unitDensity
      (powerMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K) tests k windows B₁) ≤
        ENNReal.ofReal (5 * p)) :
    ∃ H : Set ℝ, IsOpen H ∧ OnePeriodic H ∧
      unitDensity H < ENNReal.ofReal (6 * p) ∧ CompactPowerHits H K k N := by
  let R := powerMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K) tests k windows B₁
  obtain ⟨V, hVo, hVp, hRV, hVμ⟩ := closed_onePeriodic_open_cover R
    (isClosed_powerMissedCenters _ _ tests k windows B₁ hopen₁)
    (onePeriodic_powerMissedCenters _ _ tests k windows B₁ hperiod₁) p hp
  refine ⟨B₂ ∪ V, hopen₂.union hVo, onePeriodic_union hperiod₂ hVp, ?_, ?_⟩
  · calc
      unitDensity (B₂ ∪ V) ≤ unitDensity B₂ + unitDensity V := unitDensity_union_le _ _
      _ < unitDensity B₂ + (unitDensity R + ENNReal.ofReal p) :=
        ENNReal.add_lt_add_left (ne_top_of_le_ne_top ENNReal.one_ne_top (unitDensity_le_one B₂)) hVμ
      _ = (unitDensity B₂ + unitDensity R) + ENNReal.ofReal p := (add_assoc _ _ _).symm
      _ ≤ ENNReal.ofReal (5 * p) + ENNReal.ofReal p := add_le_add houtcome le_rfl
      _ = ENNReal.ofReal (6 * p) := by
        rw [← ENNReal.ofReal_add (by positivity) hp.le]
        congr 1
        ring
  · have hKr : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
    exact power_repair_all_centers (1 / (K : ℝ)) K (by positivity) tests k windows
      B₁ B₂ V hB₁₂ hVo hRV N htail

/-- The actual double-buffer finite-grid specialization of outcome repair. -/
theorem periodic_grid_outcome_repair (K : ℕ) (hK : 2 ≤ K)
    (tests : Finset ℕ) (k : ℤ) {W : ℕ} (windows : Fin W → ℝ × ℝ)
    (G : ℕ) (hG : 0 < G) (cells : Finset ℤ)
    (hcells : cells ⊆ Finset.Ico 0 (G : ℤ)) (r : ℝ) (hr : 0 < r)
    (N : ℕ) (htail : ∀ n ∈ tests, N ≤ n) (p : ℝ) (hp : 0 < p)
    (houtcome : unitDensity (Metric.thickening (2 * r) (periodicGridSet G cells)) +
      unitDensity (powerMissedCenters (s₀ := 1 / (K : ℝ)) (s₁ := K) tests k windows
        (Metric.thickening r (periodicGridSet G cells))) ≤ ENNReal.ofReal (5 * p)) :
    ∃ H : Set ℝ, IsOpen H ∧ OnePeriodic H ∧
      unitDensity H < ENNReal.ofReal (6 * p) ∧ CompactPowerHits H K k N := by
  have hperiod := onePeriodic_periodicGridSet G hG cells hcells
  exact periodic_power_outcome_repair K hK tests k windows
    (Metric.thickening r (periodicGridSet G cells))
    (Metric.thickening (2 * r) (periodicGridSet G cells))
    Metric.isOpen_thickening Metric.isOpen_thickening
    (onePeriodic_thickening hperiod r) (onePeriodic_thickening hperiod (2 * r))
    (Metric.thickening_mono (by linarith) _) N htail p hp houtcome


end ErdosSimilarityGrowingGaps
