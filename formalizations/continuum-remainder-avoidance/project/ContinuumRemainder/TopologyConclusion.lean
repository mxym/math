import ContinuumRemainder.Exhaustion

/-!
Topology and shifted density for the conditional remainder theorem.  The
compact [0,1] consequence is separate from the periodic real-line target.
-/
namespace ContinuumRemainder

open Set MeasureTheory Filter Topology ContinuumGeometric
open scoped ENNReal

/-- Integer translations preserve membership in a one-periodic set. -/
theorem onePeriodic_mem_add_int {S : Set ℝ} (hS : OnePeriodic S) (x : ℝ) (n : ℤ) :
    x + (n : ℝ) ∈ S ↔ x ∈ S := by
  have hp : Function.Periodic (fun z : ℝ => z ∈ S) 1 := fun z => propext (hS z)
  simpa only [mul_one] using iff_of_eq ((hp.int_mul n) x)

/-- Splitting a half-open interval preserves its exact measure. -/
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

/-- A measurable one-periodic set has the same density in EVERY shifted unit
interval. Half-open splits and null endpoints include all wrap positions. -/
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
    have hz : z + (-1) ∈ S ↔ z ∈ S := by
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

/-- Affine tail hits force the closed complement to have empty interior. -/
theorem interior_compl_eq_empty_of_affine_hits (U A : Set ℝ)
    (hhit : ∀ y ρ : ℝ, 0 < ρ → ∃ a ∈ A, 0 < a ∧ a < ρ ∧ y + a ∈ U) :
    interior Uᶜ = ∅ := by
  apply eq_empty_iff_forall_notMem.2
  intro y hy
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 isOpen_interior y hy
  obtain ⟨a, _, ha₀, haρ, hhit⟩ := hhit y ρ hρ
  have hnear : y + a ∈ Metric.ball y ρ := by
    simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos ha₀] using haρ
  exact (interior_subset (hball hnear)) hhit

/-- A total function represents any tail-defined affine map. -/
theorem affine_powerRemainderOn (A : Set ℝ) (y : ℝ) :
    PowerRemainderOn A (fun a => y + a) y 1 1 1 0 := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro a _ _ _
  simp only [Real.rpow_one, zero_mul]
  have heq : y + a - y - 1 * a = 0 := by ring
  rw [heq, abs_zero]

/-- CONDITIONAL exact-target bridge.  The generalized robust blocker is an
explicit premise; this theorem does not claim that premise has been proved. -/
theorem continuumPowerTarget_of_robustCompactBlockerSpec
    (hblock : RobustCompactBlockerSpec) : ContinuumPowerTarget := by
  intro ι _ _ A hA ε hε hε₁
  obtain ⟨U, hUo, hUp, hUμ, hhit⟩ :=
    robustCompactBlockerSpec_open_exhaustion hblock A hA ε hε hε₁
  let E := Uᶜ
  have hEc : IsClosed E := hUo.isClosed_compl
  have hEp : OnePeriodic E := fun x => not_congr (hUp x)
  have hEi : interior E = ∅ := by
    let l : ι := Classical.choice inferInstance
    apply interior_compl_eq_empty_of_affine_hits U (A l)
    intro y ρ hρ
    exact hhit l 1 1 y 1 0 (fun a => y + a) zero_lt_one zero_lt_one
      one_ne_zero le_rfl (affine_powerRemainderOn (A l) y) ρ hρ
  have hμ₀ : ENNReal.ofReal (1 - ε) < volume (E ∩ Icc (0 : ℝ) 1) := by
    obtain ⟨_, hvolume⟩ := compact_complement_of_open_small U hUo ε hε hε₁ hUμ
    have hset : E ∩ Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 \ U := by
      ext x
      simp only [E, mem_inter_iff, mem_compl_iff, Set.mem_sdiff]
      tauto
    rwa [hset]
  refine ⟨E, hEc, hEi, hEp, ?_, ?_⟩
  · intro x
    rw [volume_onePeriodic_inter_Icc E hEc.measurableSet hEp x]
    have hzero : volume (E ∩ Icc (0 : ℝ) 1) = unitDensity E := by
      simpa using volume_onePeriodic_inter_Icc E hEc.measurableSet hEp 0
    rwa [hzero] at hμ₀
  · intro l s α y c M f hs hα hc hM hf ρ hρ
    apply infinite_tailValuesOutside_of_hits hs hα hc hM hf ?_ ρ hρ
    intro δ hδ
    obtain ⟨a, ha, ha₀, haδ, hfa⟩ := hhit l s α y c M f hs hα hc hM hf δ hδ
    exact ⟨a, ha, ha₀, haδ, fun hcontra => hcontra hfa⟩

/-- The compact [0,1] consequence is a separate conclusion; it is not itself
one-periodic, and its avoidance follows by shrinking the periodic target. -/
theorem compact_power_avoidance_of_robustCompactBlockerSpec
    (hblock : RobustCompactBlockerSpec)
    {ι : Type} [Countable ι] [Nonempty ι] (A : ι → Set ℝ)
    (hA : ∀ l, A l ⊆ Ioi 0 ∧ LogSyndetic (A l))
    (ε : ℝ) (hε : 0 < ε) (hε₁ : ε < 1) :
    ∃ K : Set ℝ, IsCompact K ∧ K ⊆ Icc (0 : ℝ) 1 ∧
      interior K = ∅ ∧ ENNReal.ofReal (1 - ε) < volume K ∧
      AvoidsPowerRemainderTails A K := by
  obtain ⟨E, hEc, hEi, _, hEμ, havoid⟩ :=
    continuumPowerTarget_of_robustCompactBlockerSpec hblock ι A hA ε hε hε₁
  refine ⟨E ∩ Icc (0 : ℝ) 1, isCompact_Icc.inter_left hEc, inter_subset_right, ?_,
    by simpa using hEμ 0, ?_⟩
  · apply subset_empty_iff.1
    exact (interior_mono inter_subset_left).trans (by rw [hEi])
  · intro l s α y c M f hs hα hc hM hf ρ hρ
    apply (havoid l s α y c M f hs hα hc hM hf ρ hρ).mono
    rintro z ⟨a, ha, ha₀, haρ, hfaz, hz⟩
    exact ⟨a, ha, ha₀, haρ, hfaz, fun hzK => hz hzK.1⟩

end ContinuumRemainder
