import ErdosSimilarityGrowingGaps.Avoidance
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace ErdosSimilarityGrowingGaps

open Filter Set Topology
open scoped BigOperators ENNReal

theorem input_lt_one (Z : LogScale) (n : ℕ) : input Z n < 1 := by
  unfold input
  rw [← Real.rpow_zero 2]
  exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (neg_lt_zero.mpr (Z.positive n))

theorem tailApproximation_tendsto {Z : LogScale} {f : ℝ → ℝ}
    {s α y c M : ℝ} (hs : 0 < s) (hα : 0 < α) (_hM : 0 ≤ M)
    (hf : TailApproximation Z f s α y c M) :
    Tendsto (fun n => f (input Z n)) atTop (𝓝 y) := by
  obtain ⟨N, hN⟩ := hf
  have hpow := (input_tendsto_zero Z).rpow_const_nhds_zero (add_pos hs hα)
  have hbound : Tendsto (fun n => M * (input Z n) ^ (s + α)) atTop (𝓝 0) := by
    simpa using hpow.const_mul M
  have herr : Tendsto (fun n => f (input Z n) - y - c * (input Z n) ^ s)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' (by simpa only [Real.norm_eq_abs] using
      (eventually_atTop.2 ⟨N, hN⟩)) hbound
  have hlead : Tendsto (fun n => c * (input Z n) ^ s) atTop (𝓝 0) := by
    simpa using ((input_tendsto_zero Z).rpow_const_nhds_zero hs).const_mul c
  convert (herr.add hlead).add_const y using 1 <;> simp

theorem tailApproximation_eventually_ne {Z : LogScale} {f : ℝ → ℝ}
    {s α y c M : ℝ} (hα : 0 < α) (hc : c ≠ 0)
    (hf : TailApproximation Z f s α y c M) :
    ∀ᶠ n in atTop, f (input Z n) ≠ y := by
  obtain ⟨N, hN⟩ := hf
  have hsmall : ∀ᶠ n in atTop, M * (input Z n) ^ α < |c| := by
    have ht : Tendsto (fun n => M * (input Z n) ^ α) atTop (𝓝 0) := by
      simpa using ((input_tendsto_zero Z).rpow_const_nhds_zero hα).const_mul M
    exact ht.eventually (Iio_mem_nhds (abs_pos.mpr hc))
  filter_upwards [eventually_ge_atTop N, hsmall] with n hn hsm
  intro heq
  have h := hN n hn
  rw [heq, sub_self, zero_sub, abs_neg, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos (input_pos Z n) s),
    Real.rpow_add (input_pos Z n)] at h
  have hpow : 0 < (input Z n) ^ s := Real.rpow_pos_of_pos (input_pos Z n) s
  nlinarith

theorem tailApproximation_mono {Z : LogScale} {f : ℝ → ℝ}
    {s α α₀ y c M M₀ : ℝ} (_hα₀ : 0 < α₀) (hα : α₀ ≤ α)
    (hM : 0 ≤ M) (hMM₀ : M ≤ M₀)
    (hf : TailApproximation Z f s α y c M) :
    TailApproximation Z f s α₀ y c M₀ := by
  obtain ⟨N, hN⟩ := hf
  refine ⟨N, ?_⟩
  intro n hn
  have hx : 0 < input Z n := input_pos Z n
  have hx1 : input Z n ≤ 1 := (input_lt_one Z n).le
  have he : (input Z n) ^ (s + α) ≤ (input Z n) ^ (s + α₀) := by
    apply Real.rpow_le_rpow_of_exponent_ge hx hx1
    linarith
  have hmul : M * (input Z n) ^ (s + α) ≤
      M₀ * (input Z n) ^ (s + α₀) := by
    calc
      M * (input Z n) ^ (s + α) ≤ M₀ * (input Z n) ^ (s + α) :=
        mul_le_mul_of_nonneg_right hMM₀ (Real.rpow_nonneg hx.le _)
      _ ≤ M₀ * (input Z n) ^ (s + α₀) :=
        mul_le_mul_of_nonneg_left he (le_trans hM hMM₀)
  exact (hN n hn).trans hmul

def WeakRobustBlocker (Z : LogScale) (H : Set ℝ) : Prop :=
  ∀ s α y c M : ℝ, 0 < s → 0 < α → c ≠ 0 → 0 ≤ M →
    ∀ f : ℝ → ℝ, TailApproximation Z f s α y c M →
      ∀ ρ : ℝ, 0 < ρ → ∃ n : ℕ, input Z n < ρ ∧ f (input Z n) ∈ H

/-! A countable error-exponent/constant grid is enough.  This is the exact
    reduction used when the analytic construction is enumerated. -/
def GridWeakRobustBlocker (Z : LogScale) (H : Set ℝ) : Prop :=
  ∀ j q : ℕ, ∀ s y c : ℝ, 0 < s → c ≠ 0 →
    ∀ f : ℝ → ℝ,
      TailApproximation Z f s (1 / (j + 1 : ℝ)) y c q →
      ∀ ρ : ℝ, 0 < ρ → ∃ n : ℕ, input Z n < ρ ∧ f (input Z n) ∈ H

theorem gridWeakRobustBlocker_implies_weak {Z : LogScale} {H : Set ℝ}
    (hH : GridWeakRobustBlocker Z H) : WeakRobustBlocker Z H := by
  intro s α y c M hs hα hc hM f hf ρ hρ
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hα
  obtain ⟨q, hq⟩ := exists_nat_ge M
  have hαj : 0 < (1 / (j + 1 : ℝ)) := by positivity
  have hMq : M ≤ (q : ℝ) := hq
  have hfj := tailApproximation_mono hαj hj.le hM hMq hf
  exact hH j q s y c hs hc f hfj ρ hρ

/-- One hit in every input tail suffices for infinitely many distinct values.
    Convergence and exclusion of the leading center replace injectivity. -/
theorem infinite_tailValuesIn_of_hits {Z : LogScale} {f : ℝ → ℝ}
    {s α y c M : ℝ} {H : Set ℝ}
    (hs : 0 < s) (hα : 0 < α) (hc : c ≠ 0) (hM : 0 ≤ M)
    (hf : TailApproximation Z f s α y c M)
    (hhit : ∀ ρ : ℝ, 0 < ρ → ∃ n : ℕ, input Z n < ρ ∧ f (input Z n) ∈ H)
    (ρ : ℝ) (hρ : 0 < ρ) : (TailValuesIn Z f H ρ).Infinite := by
  intro hfin
  let S := TailValuesIn Z f H ρ \ {y}
  have hSfin : S.Finite := by
    dsimp [S]
    exact hfin.sdiff
  have hS : IsClosed S := hSfin.isClosed
  have hy : y ∈ Sᶜ := by simp [S]
  have hout : ∀ᶠ n in atTop, f (input Z n) ∉ S :=
    (tailApproximation_tendsto hs hα hM hf).eventually (hS.isOpen_compl.mem_nhds hy)
  have hne := tailApproximation_eventually_ne hα hc hf
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hout.and hne)
  obtain ⟨n, hn, hhitn⟩ := hhit (min ρ (input Z N)) (lt_min hρ (input_pos Z N))
  have hnρ : input Z n < ρ := hn.trans_le (min_le_left _ _)
  have hnN : N ≤ n := by
    by_contra h
    have hanti := input_strictAnti Z (Nat.lt_of_not_ge h)
    exact (not_lt_of_ge hanti.le) (hn.trans_le (min_le_right _ _))
  exact (hN n hnN).1 ⟨⟨n, hnρ, rfl, hhitn⟩, by simpa using (hN n hnN).2⟩

theorem weakRobustBlocker_implies_robust {Z : LogScale} {H : Set ℝ}
    (hH : WeakRobustBlocker Z H) : RobustBlocker Z H := by
  intro s α y c M hs hα hc hM f hf ρ hρ
  exact infinite_tailValuesIn_of_hits hs hα hc hM hf (by
    intro ρ' hρ'
    exact hH s α y c M hs hα hc hM f hf ρ' hρ') ρ hρ

theorem blockerFamily_of_grid_blockers
    {ι : Type*} [Countable ι] [Nonempty ι]
    {F : ι → LogScale} {ε : ℝ}
    (w : ι × (ℕ × ℕ) → ℝ≥0∞)
    (hw : ∑' p, w p < ENNReal.ofReal ε)
    (hgrid : ∀ (i : ι) (j q : ℕ), ∃ H : Set ℝ,
      IsOpen H ∧ OnePeriodic H ∧ unitDensity H ≤ w (i, (j, q)) ∧
      ∀ s y c : ℝ, 0 < s → c ≠ 0 →
        ∀ f : ℝ → ℝ,
          TailApproximation (F i) f s (1 / (j + 1 : ℝ)) y c q →
          ∀ ρ : ℝ, 0 < ρ →
            ∃ n : ℕ, input (F i) n < ρ ∧ f (input (F i) n) ∈ H) :
    ∃ B : BlockerFamily F, ∑' i, B.budget i < ENNReal.ofReal ε := by
  choose H hHo hHp hHd hHhit using hgrid
  let S : ι → Set ℝ := fun i => ⋃ j, ⋃ q, H i j q
  let b : ι → ℝ≥0∞ := fun i => ∑' k : ℕ × ℕ, w (i, k)
  have hSo : ∀ i, IsOpen (S i) := by
    intro i
    exact isOpen_iUnion fun j => isOpen_iUnion fun q => hHo i j q
  have hSp : ∀ i, OnePeriodic (S i) := by
    intro i x
    simp only [S, mem_iUnion]
    exact exists_congr fun j => exists_congr fun q => hHp i j q x
  have hSd : ∀ i, unitDensity (S i) ≤ b i := by
    intro i
    calc
      unitDensity (S i) ≤ ∑' j, unitDensity (⋃ q, H i j q) :=
        unitDensity_iUnion_le (fun j => ⋃ q, H i j q)
      _ ≤ ∑' j, ∑' q, unitDensity (H i j q) :=
        ENNReal.tsum_le_tsum (fun j => unitDensity_iUnion_le (fun q => H i j q))
      _ ≤ ∑' j, ∑' q, w (i, (j, q)) := by
        refine ENNReal.tsum_le_tsum (fun j => ?_)
        exact ENNReal.tsum_le_tsum (fun q => hHd i j q)
      _ = b i := by
        exact (ENNReal.tsum_prod' (f := fun k : ℕ × ℕ => w (i, k))).symm
  have hSh : ∀ i, RobustBlocker (F i) (S i) := by
    intro i
    apply weakRobustBlocker_implies_robust
    apply gridWeakRobustBlocker_implies_weak
    intro j q s y c hs hc f hf ρ hρ
    obtain ⟨n, hnρ, hval⟩ := hHhit i j q s y c hs hc f hf ρ hρ
    exact ⟨n, hnρ, mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨q, hval⟩⟩⟩
  let B : BlockerFamily F :=
    { set := S
      budget := b
      open_set := hSo
      periodic := hSp
      density_le := hSd
      hits := hSh }
  refine ⟨B, ?_⟩
  change (∑' i, ∑' k : ℕ × ℕ, w (i, k)) < ENNReal.ofReal ε
  exact (ENNReal.tsum_prod' (f := w)).symm ▸ hw

end ErdosSimilarityGrowingGaps
