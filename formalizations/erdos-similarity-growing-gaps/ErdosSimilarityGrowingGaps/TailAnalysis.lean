import ErdosSimilarityGrowingGaps.Avoidance
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace ErdosSimilarityGrowingGaps

open Filter Set Topology

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

end ErdosSimilarityGrowingGaps
