import ErdosSimilarityGrowingGaps.Input
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ErdosSimilarityGrowingGaps

open Filter Set Topology MeasureTheory
open scoped ENNReal

/-- A one-periodic set, written as a membership equivalence so that it is
    usable without choosing a representative of a period. -/
def OnePeriodic (S : Set ℝ) : Prop :=
  ∀ x : ℝ, x + 1 ∈ S ↔ x ∈ S

noncomputable def unitDensity (S : Set ℝ) : ℝ≥0∞ :=
  volume (S ∩ Ico (0 : ℝ) 1)

/-- The tail estimate from the paper, expressed on the canonical input
    sequence attached to a logarithmic scale. -/
def TailApproximation (Z : LogScale) (f : ℝ → ℝ)
    (s α y c M : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    |f (input Z n) - y - c * (input Z n) ^ s| ≤
      M * (input Z n) ^ (s + α)

def TailValuesOutside (Z : LogScale) (f : ℝ → ℝ) (E : Set ℝ)
    (ρ : ℝ) : Set ℝ :=
  {a : ℝ | ∃ n : ℕ, input Z n < ρ ∧ f (input Z n) = a ∧ a ∉ E}

def TailValuesIn (Z : LogScale) (f : ℝ → ℝ) (H : Set ℝ)
    (ρ : ℝ) : Set ℝ :=
  {a : ℝ | ∃ n : ℕ, input Z n < ρ ∧ f (input Z n) = a ∧ a ∈ H}

/-- A blocker already contains the finite routing conclusion.  This is the
    exact interface needed by the topological/countable-exhaustion layer; its
    proof is supplied by finite routing plus annular sampling. -/
def RobustBlocker (Z : LogScale) (H : Set ℝ) : Prop :=
  ∀ s α y c M : ℝ, 0 < s → 0 < α → c ≠ 0 → 0 ≤ M →
    ∀ f : ℝ → ℝ, TailApproximation Z f s α y c M →
      ∀ ρ : ℝ, 0 < ρ → (TailValuesIn Z f H ρ).Infinite

structure BlockerFamily {ι : Type*} [Countable ι]
    (F : ι → LogScale) where
  set : ι → Set ℝ
  budget : ι → ℝ≥0∞
  open_set : ∀ i, IsOpen (set i)
  periodic : ∀ i, OnePeriodic (set i)
  density_le : ∀ i, unitDensity (set i) ≤ budget i
  hits : ∀ i, RobustBlocker (F i) (set i)

def WindowBlockerSpec {ι : Type*} [Countable ι] [Nonempty ι]
    (F : ι → LogScale) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∃ B : BlockerFamily F, ∑' i, B.budget i < ENNReal.ofReal ε

theorem exists_budget_allocation {ι : Type*} [Countable ι] [Nonempty ι]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ b : ι → ℝ≥0∞, (∀ i, 0 < b i) ∧ ∑' i, b i < ENNReal.ofReal ε := by
  exact ENNReal.exists_pos_sum_of_countable'
    (ENNReal.ofReal_pos.mpr hε).ne' ι

theorem blockerFamily_of_budgeted_blockers
    {ι : Type*} [Countable ι] [Nonempty ι]
    {F : ι → LogScale} {ε : ℝ} (_hε : 0 < ε)
    (b : ι → ℝ≥0∞) (hb : ∑' i, b i < ENNReal.ofReal ε)
    (hblock : ∀ i, ∃ S : Set ℝ, IsOpen S ∧ OnePeriodic S ∧
      unitDensity S ≤ b i ∧ RobustBlocker (F i) S) :
    ∃ B : BlockerFamily F, ∑' i, B.budget i < ENNReal.ofReal ε := by
  choose S hSo hSp hSd hSh using hblock
  let B : BlockerFamily F :=
    { set := S
      budget := b
      open_set := hSo
      periodic := hSp
      density_le := hSd
      hits := hSh }
  exact ⟨B, hb⟩

theorem onePeriodic_mem_add_int {S : Set ℝ} (hS : OnePeriodic S)
    (x : ℝ) (n : ℤ) : x + (n : ℝ) ∈ S ↔ x ∈ S := by
  have hp : Function.Periodic (fun z : ℝ => z ∈ S) 1 :=
    fun z => propext (hS z)
  simpa only [mul_one] using iff_of_eq ((hp.int_mul n) x)

theorem unitDensity_iUnion_le {ι : Type*} [Countable ι]
    (S : ι → Set ℝ) :
    unitDensity (⋃ i, S i) ≤ ∑' i, unitDensity (S i) := by
  unfold unitDensity
  rw [iUnion_inter]
  exact measure_iUnion_le _

theorem unitDensity_le_one (S : Set ℝ) : unitDensity S ≤ 1 := by
  calc
    unitDensity S ≤ volume (Ico (0 : ℝ) 1) := measure_mono inter_subset_right
    _ = 1 := by simp [Real.volume_Ico]

theorem onePeriodic_iUnion {ι : Type*} (S : ι → Set ℝ)
    (hS : ∀ i, OnePeriodic (S i)) : OnePeriodic (⋃ i, S i) := by
  intro x
  simp only [mem_iUnion]
  exact exists_congr fun i => hS i x

theorem measure_periodic_interval_split (S : Set ℝ) (hS : MeasurableSet S)
    (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) :
    volume (S ∩ Ico a c) = volume (S ∩ Ico a b) + volume (S ∩ Ico b c) := by
  have hset : S ∩ Ico a c = (S ∩ Ico a b) ∪ (S ∩ Ico b c) := by
    ext x
    simp only [mem_inter_iff, mem_union, mem_Ico]
    constructor
    · rintro ⟨hxS, hxa, hxc⟩
      by_cases hxb : x < b
      · exact Or.inl ⟨hxS, hxa, hxb⟩
      · exact Or.inr ⟨hxS, le_of_not_gt hxb, hxc⟩
    · rintro (⟨hxS, hxa, hxb⟩ | ⟨hxS, hxb, hxc⟩)
      · exact ⟨hxS, hxa, hxb.trans_le hbc⟩
      · exact ⟨hxS, hab.trans hxb, hxc⟩
  have hdis : Disjoint (S ∩ Ico a b) (S ∩ Ico b c) := by
    apply disjoint_left.2
    intro x hx hy
    exact (not_lt_of_ge hy.2.1) hx.2.2
  rw [hset, measure_union hdis (hS.inter measurableSet_Ico)]

theorem volume_onePeriodic_inter_Icc (S : Set ℝ) (hS : MeasurableSet S)
    (hperiod : OnePeriodic S) (x : ℝ) :
    volume (S ∩ Icc x (x + 1)) = unitDensity S := by
  let n := Int.floor x
  let r := x - (n : ℝ)
  have hr₀ : 0 ≤ r := Int.fract_nonneg x
  have hr₁ : r ≤ 1 := (Int.fract_lt_one x).le
  have hshift : S ∩ Ico x (x + 1) =
      (fun z : ℝ => z + (-(n : ℝ))) ⁻¹' (S ∩ Ico r (r + 1)) := by
    ext z
    have hz : z + (-(n : ℝ)) ∈ S ↔ z ∈ S := by
      simpa only [Int.cast_neg] using onePeriodic_mem_add_int hperiod z (-n)
    simp only [mem_inter_iff, mem_preimage, mem_Ico, hz]
    dsimp [r]
    constructor <;> rintro ⟨hzS, hlo, hhi⟩ <;> refine ⟨hzS, ?_, ?_⟩ <;> linarith
  have hwrap : S ∩ Ico 1 (r + 1) =
      (fun z : ℝ => z + (-1)) ⁻¹' (S ∩ Ico 0 r) := by
    ext z
    have hz : z + (-1 : ℝ) ∈ S ↔ z ∈ S := by
      simpa using onePeriodic_mem_add_int hperiod z (-1)
    simp only [mem_inter_iff, mem_preimage, mem_Ico, hz]
    constructor <;> rintro ⟨hzS, hlo, hhi⟩ <;> refine ⟨hzS, ?_, ?_⟩ <;> linarith
  calc
    volume (S ∩ Icc x (x + 1)) = volume (S ∩ Ico x (x + 1)) :=
      measure_congr (ae_eq_set_inter (EventuallyEq.rfl) Ico_ae_eq_Icc).symm
    _ = volume (S ∩ Ico r (r + 1)) := by rw [hshift, measure_preimage_add_right]
    _ = volume (S ∩ Ico r 1) + volume (S ∩ Ico 1 (r + 1)) :=
      measure_periodic_interval_split S hS r 1 (r + 1) hr₁ (by linarith)
    _ = volume (S ∩ Ico r 1) + volume (S ∩ Ico 0 r) := by
      rw [hwrap, measure_preimage_add_right]
    _ = volume (S ∩ Ico 0 r) + volume (S ∩ Ico r 1) := add_comm _ _
    _ = unitDensity S :=
      (measure_periodic_interval_split S hS 0 r 1 hr₀ hr₁).symm

theorem interior_compl_eq_empty_of_hits (U : Set ℝ)
    (hhit : ∀ y ρ : ℝ, 0 < ρ → ∃ z ∈ U, z ∈ Ioo y (y + ρ)) :
    interior Uᶜ = ∅ := by
  apply eq_empty_iff_forall_notMem.2
  intro y hy
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 isOpen_interior y hy
  obtain ⟨z, hzU, hz⟩ := hhit y ρ hρ
  have hnear : z ∈ Metric.ball y ρ := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hz.1, hz.2]
  exact (interior_subset (hball hnear)) hzU

theorem blockerFamily_union_hits {ι : Type*} [Countable ι] [Nonempty ι]
    {F : ι → LogScale} (B : BlockerFamily F)
    (y ρ : ℝ) (hρ : 0 < ρ) :
    ∃ z ∈ ⋃ i, B.set i, z ∈ Ioo y (y + ρ) := by
  classical
  let i : ι := Classical.choice inferInstance
  let f : ℝ → ℝ := fun a => y + a
  have hTail : TailApproximation (F i) f 1 1 y 1 0 := by
    refine ⟨0, ?_⟩
    intro n _
    dsimp [f]
    simp
  have hInf := B.hits i 1 1 y 1 0 (by positivity) (by positivity)
    one_ne_zero (by positivity) f hTail ρ hρ
  obtain ⟨z, hz⟩ := hInf.nonempty
  change ∃ n : ℕ, input (F i) n < ρ ∧ f (input (F i) n) = z ∧ z ∈ B.set i at hz
  rcases hz with ⟨n, hlt, hza, hzU⟩
  refine ⟨z, mem_iUnion.2 ⟨i, ?_⟩, ?_⟩
  · exact hzU
  · dsimp [f] at hza
    rw [← hza]
    exact ⟨by linarith [input_pos (F i) n], by linarith⟩

theorem closed_periodic_avoidance_of_blockers
    {ι : Type*} [Countable ι] [Nonempty ι]
    {F : ι → LogScale} (B : BlockerFamily F)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hsum : ∑' i, B.budget i < ENNReal.ofReal ε) :
    ∃ E : Set ℝ, IsClosed E ∧ OnePeriodic E ∧ interior E = ∅ ∧
      (∀ x : ℝ, ENNReal.ofReal (1 - ε) < volume (E ∩ Icc x (x + 1))) ∧
      (∀ i : ι, ∀ s α y c M : ℝ, 0 < s → 0 < α → c ≠ 0 → 0 ≤ M →
        ∀ f : ℝ → ℝ, TailApproximation (F i) f s α y c M →
        ∀ ρ : ℝ, 0 < ρ → (TailValuesOutside (F i) f E ρ).Infinite) := by
  let U : Set ℝ := ⋃ i, B.set i
  let E : Set ℝ := Uᶜ
  have hUo : IsOpen U := isOpen_iUnion (fun i => B.open_set i)
  have hUp : OnePeriodic U := onePeriodic_iUnion B.set B.periodic
  have hUμ : unitDensity U < ENNReal.ofReal ε := by
    calc
      unitDensity U ≤ ∑' i, unitDensity (B.set i) := unitDensity_iUnion_le B.set
      _ ≤ ∑' i, B.budget i := ENNReal.tsum_le_tsum (fun i => B.density_le i)
      _ < ENNReal.ofReal ε := hsum
  have hEc : IsClosed E := hUo.isClosed_compl
  have hEp : OnePeriodic E := by
    intro x
    exact not_congr (hUp x)
  have hEi : interior E = ∅ := by
    apply interior_compl_eq_empty_of_hits U
    exact blockerFamily_union_hits B
  have hμ0 : ENNReal.ofReal (1 - ε) < volume (E ∩ Icc (0 : ℝ) 1) := by
    have hcomp : volume (E ∩ Icc (0 : ℝ) 1) =
        volume (Icc (0 : ℝ) 1) - volume (U ∩ Icc (0 : ℝ) 1) := by
      rw [show E ∩ Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 \ (U ∩ Icc (0 : ℝ) 1) by
        ext z; simp [E, U, and_assoc, and_comm]]
      rw [measure_sdiff inter_subset_right
        (hUo.measurableSet.inter measurableSet_Icc).nullMeasurableSet]
      · exact ne_top_of_le_ne_top (by simp)
          (measure_mono inter_subset_right)
    rw [hcomp]
    have hshift : volume (U ∩ Icc (0 : ℝ) 1) = unitDensity U := by
      simpa using volume_onePeriodic_inter_Icc U hUo.measurableSet hUp 0
    rw [hshift]
    have hvol : volume (Icc (0 : ℝ) 1) = 1 := by simp [Real.volume_Icc]
    rw [hvol]
    rw [lt_tsub_iff_right]
    calc
      ENNReal.ofReal (1 - ε) + unitDensity U <
          ENNReal.ofReal (1 - ε) + ENNReal.ofReal ε :=
        ENNReal.add_lt_add_left ENNReal.ofReal_ne_top hUμ
      _ = 1 := by
        rw [← ENNReal.ofReal_add (by linarith) (by positivity)]
        have hsumone : (1 - ε : ℝ) + ε = 1 := by ring
        rw [hsumone, ENNReal.ofReal_one]
  refine ⟨E, hEc, hEp, hEi, ?_, ?_⟩
  · intro x
    rw [volume_onePeriodic_inter_Icc E hEc.measurableSet hEp x]
    have h0 := volume_onePeriodic_inter_Icc E hEc.measurableSet hEp 0
    calc
      ENNReal.ofReal (1 - ε) < volume (E ∩ Icc (0 : ℝ) 1) := hμ0
      _ = unitDensity E := by simpa [zero_add] using h0
  · intro i s α y c M hs hα hc hM f hf ρ hρ
    have hsub : TailValuesIn (F i) f (B.set i) ρ ⊆
        TailValuesOutside (F i) f E ρ := by
      intro z hz
      rcases hz with ⟨n, hlt, hza, hHin⟩
      refine ⟨n, hlt, hza, ?_⟩
      intro hzE
      exact hzE (show z ∈ U from mem_iUnion.2 ⟨i, hHin⟩)
    exact (B.hits i s α y c M hs hα hc hM f hf ρ hρ).mono hsub

theorem compact_restriction_of_blockers
    {ι : Type*} [Countable ι] [Nonempty ι]
    {F : ι → LogScale} (B : BlockerFamily F)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hsum : ∑' i, B.budget i < ENNReal.ofReal ε) :
    ∃ K : Set ℝ, IsCompact K ∧ K ⊆ Icc (0 : ℝ) 1 ∧ interior K = ∅ ∧
      ENNReal.ofReal (1 - ε) < volume K ∧
      (∀ i : ι, ∀ s α y c M : ℝ, 0 < s → 0 < α → c ≠ 0 → 0 ≤ M →
        ∀ f : ℝ → ℝ, TailApproximation (F i) f s α y c M →
        ∀ ρ : ℝ, 0 < ρ → (TailValuesOutside (F i) f K ρ).Infinite) := by
  obtain ⟨E, hEc, hEp, hEi, hμ, havoid⟩ :=
    closed_periodic_avoidance_of_blockers B ε hε hε1 hsum
  let K := E ∩ Icc (0 : ℝ) 1
  have hKc : IsCompact K := isCompact_Icc.inter_left hEc
  have hKi : K ⊆ Icc (0 : ℝ) 1 := inter_subset_right
  have hKint : interior K = ∅ := by
    apply subset_empty_iff.1
    exact (interior_mono inter_subset_left).trans (by rw [hEi])
  refine ⟨K, hKc, hKi, hKint, ?_, ?_⟩
  · simpa [K] using hμ 0
  · intro i s α y c M hs hα hc hM f hf ρ hρ
    have hsub : TailValuesOutside (F i) f E ρ ⊆
        TailValuesOutside (F i) f K ρ := by
      intro z hz
      rcases hz with ⟨n, hlt, hza, hzE⟩
      exact ⟨n, hlt, hza, fun hzK => hzE hzK.1⟩
    exact (havoid i s α y c M hs hα hc hM f hf ρ hρ).mono hsub

theorem theorem2_of_windowBlockerSpec
    {ι : Type*} [Countable ι] [Nonempty ι]
    {F : ι → LogScale} (hB : WindowBlockerSpec F)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ E : Set ℝ, IsClosed E ∧ OnePeriodic E ∧ interior E = ∅ ∧
      (∀ x : ℝ, ENNReal.ofReal (1 - ε) < volume (E ∩ Icc x (x + 1))) := by
  obtain ⟨B, hsum⟩ := hB ε hε hε1
  obtain ⟨E, hEc, hEp, hEi, hμ, _⟩ :=
    closed_periodic_avoidance_of_blockers B ε hε hε1 hsum
  exact ⟨E, hEc, hEp, hEi, hμ⟩

end ErdosSimilarityGrowingGaps
