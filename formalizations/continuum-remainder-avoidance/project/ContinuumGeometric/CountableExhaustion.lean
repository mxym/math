import ContinuumGeometric.PeriodicRepair
import ContinuumGeometric.CoefficientCover
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Reflected countable exhaustion and compactification.  The final theorem is
explicitly conditional on the OPEN `SmallCompactBlockerSpec` definition.
It does not assert a proof of that construction obligation.
-/
namespace ContinuumGeometric

open Set MeasureTheory Filter Topology
open scoped ENNReal

def reflectedSet (S : Set ℝ) : Set ℝ := Neg.neg ⁻¹' S

theorem onePeriodic_reflectedSet {S : Set ℝ} (hS : OnePeriodic S) :
    OnePeriodic (reflectedSet S) := by
  intro x
  have h := hS (-x - 1)
  simpa [reflectedSet, neg_add, sub_eq_add_neg, add_comm] using h.symm

/-- Reflection preserves fundamental-interval density, including endpoint
changes between Ico and Ioc. -/
theorem unitDensity_reflectedSet (S : Set ℝ) (hS : OnePeriodic S) :
    unitDensity (reflectedSet S) = unitDensity S := by
  have hset : reflectedSet S ∩ Ico (0 : ℝ) 1 =
      Neg.neg ⁻¹' ((fun x : ℝ => x + 1) ⁻¹' (S ∩ Ioc 0 1)) := by
    ext x
    simp only [reflectedSet, mem_inter_iff, mem_preimage, mem_Ico, mem_Ioc]
    rw [hS (-x)]
    constructor <;> rintro ⟨hs, h₀, h₁⟩ <;> refine ⟨hs, ?_, ?_⟩ <;> linarith
  unfold unitDensity
  have hneg (A : Set ℝ) : volume (Neg.neg ⁻¹' A) = volume A := by
    simpa using Real.volume_preimage_mul_left (a := -1) (by norm_num) A
  rw [hset, hneg, measure_preimage_add_right]
  exact measure_congr (ae_eq_set_inter (EventuallyEq.rfl) Ico_ae_eq_Ioc).symm

abbrev CompactBlockerIndex := {K : ℕ // 2 ≤ K} × ℤ × ℕ

theorem unitDensity_iUnion_le {ι : Type*} [Countable ι] (S : ι → Set ℝ) :
    unitDensity (⋃ i, S i) ≤ ∑' i, unitDensity (S i) := by
  unfold unitDensity
  rw [iUnion_inter]
  exact measure_iUnion_le _

/-- Countably many budgets cover all K, all integer coefficient scales,
all natural tails, and both signs.  Their total density is strictly small. -/
theorem smallCompactBlockerSpec_open_exhaustion (hblock : SmallCompactBlockerSpec)
    (ε : ℝ) (hε : 0 < ε) (hε₁ : ε < 1) :
    ∃ U : Set ℝ, IsOpen U ∧ OnePeriodic U ∧ unitDensity U < ENNReal.ofReal ε ∧
      ∀ (a b q : ℝ), a ≠ 0 → 0 < q → q < 1 →
        ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ a * q ^ n + b ∈ U := by
  classical
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable
    (ε := ENNReal.ofReal (ε / 2)) (by positivity) CompactBlockerIndex
  have hδ₁ (i : CompactBlockerIndex) : (δ i : ℝ) < 1 := by
    have hi : (δ i : ENNReal) < 1 :=
      (ENNReal.le_tsum i).trans_lt (hδsum.trans (ENNReal.ofReal_lt_one.2 (by linarith)))
    exact_mod_cast (ENNReal.coe_lt_coe.1 hi)
  have hex (i : CompactBlockerIndex) :=
    hblock i.1.1 i.1.2 i.2.1 i.2.2 (δ i) (hδpos i) (hδ₁ i)
  choose H hopen hperiod hsmall hhits using hex
  let S := fun i => H i ∪ reflectedSet (H i)
  let U := ⋃ i, S i
  have hUo : IsOpen U := isOpen_iUnion fun i =>
    (hopen i).union ((hopen i).preimage continuous_neg)
  have hUp : OnePeriodic U := by
    intro x
    simp only [U, mem_iUnion]
    exact exists_congr fun i => onePeriodic_union (hperiod i) (onePeriodic_reflectedSet (hperiod i)) x
  have hUμ : unitDensity U < ENNReal.ofReal ε := by
    calc
      unitDensity U ≤ ∑' i, unitDensity (S i) := unitDensity_iUnion_le S
      _ ≤ ∑' i, ((δ i : ENNReal) + (δ i : ENNReal)) := by
        apply ENNReal.tsum_le_tsum
        intro i
        calc
          unitDensity (S i) ≤ unitDensity (H i) + unitDensity (reflectedSet (H i)) :=
            unitDensity_union_le _ _
          _ = unitDensity (H i) + unitDensity (H i) := by rw [unitDensity_reflectedSet _ (hperiod i)]
          _ ≤ (δ i : ENNReal) + (δ i : ENNReal) := add_le_add (by simpa using (hsmall i).le) (by simpa using (hsmall i).le)
      _ = (∑' i, (δ i : ENNReal)) + ∑' i, (δ i : ENNReal) := ENNReal.tsum_add
      _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := ENNReal.add_lt_add hδsum hδsum
      _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  refine ⟨U, hUo, hUp, hUμ, ?_⟩
  intro a b q ha hq₀ hq₁ N
  obtain ⟨K, hK, positive, k, p, heq⟩ := affine_geometric_compact_power_cover a b q ha hq₀ hq₁
  let i : CompactBlockerIndex := (⟨K, hK⟩, k, N)
  cases positive
  · obtain ⟨n, hn, hhit⟩ := hhits i (-b) p
    refine ⟨n, hn, mem_iUnion.2 ⟨i, Or.inr ?_⟩⟩
    simpa [reflectedSet, heq n] using hhit
  · obtain ⟨n, hn, hhit⟩ := hhits i b p
    refine ⟨n, hn, mem_iUnion.2 ⟨i, Or.inl ?_⟩⟩
    simpa [heq n] using hhit

/-- Compactification preserves the strict requested volume inequality. -/
theorem compact_complement_of_open_small (U : Set ℝ) (hU : IsOpen U)
    (ε : ℝ) (hε : 0 < ε) (hε₁ : ε < 1)
    (hμ : unitDensity U < ENNReal.ofReal ε) :
    IsCompact (Icc (0 : ℝ) 1 \ U) ∧
      ENNReal.ofReal (1 - ε) < volume (Icc (0 : ℝ) 1 \ U) := by
  refine ⟨isCompact_Icc.diff hU, ?_⟩
  have heqμ : volume (Icc (0 : ℝ) 1 ∩ U) = unitDensity U := by
    rw [inter_comm]
    exact measure_congr (ae_eq_set_inter (EventuallyEq.rfl) Ico_ae_eq_Icc).symm
  have hpartition := measure_inter_add_sdiff (μ := volume) (Icc (0 : ℝ) 1) hU.measurableSet
  rw [heqμ, Real.volume_Icc] at hpartition
  norm_num at hpartition
  have hsum : unitDensity U + ENNReal.ofReal (1 - ε) < 1 := by
    calc
      unitDensity U + ENNReal.ofReal (1 - ε) < ENNReal.ofReal ε + ENNReal.ofReal (1 - ε) :=
        ENNReal.add_lt_add_right (ne_top_of_le_ne_top ENNReal.one_ne_top
          (ENNReal.ofReal_le_one.2 (by linarith))) hμ
      _ = 1 := by rw [← ENNReal.ofReal_add hε.le (by linarith)]; norm_num
  rw [← hpartition] at hsum
  by_contra hnot
  exact (not_le_of_gt hsum) (add_le_add le_rfl (le_of_not_gt hnot))

/-- CONDITIONAL end-to-end bridge.  The construction obligation
`SmallCompactBlockerSpec` is OPEN until the routing lanes prove it. -/
theorem mainTarget_of_smallCompactBlockerSpec (hblock : SmallCompactBlockerSpec) :
    MainTarget := by
  intro ε hε hε₁
  obtain ⟨U, hUo, _, hUμ, hhit⟩ := smallCompactBlockerSpec_open_exhaustion hblock ε hε hε₁
  obtain ⟨hcompact, hvolume⟩ := compact_complement_of_open_small U hUo ε hε hε₁ hUμ
  refine ⟨Icc (0 : ℝ) 1 \ U, hcompact, sdiff_subset, hvolume, ?_⟩
  intro a b q ha hq₀ hq₁ N
  obtain ⟨n, hn, hhitn⟩ := hhit a b q ha hq₀ hq₁ N
  exact ⟨n, hn, fun he => he.2 hhitn⟩

end ContinuumGeometric
