import Entry002.PrimeIdealSplitDirichlet

/-! Removing a finite initial segment from the actual splitting-prime
Dirichlet series preserves its logarithmic limit and positive upper supply. -/

namespace Entry002

open NumberField Filter
open scoped NumberField Classical Topology

noncomputable section

/-- Exact finite removal for the genuine membership-indicator Dirichlet
series of any set. -/
theorem supplyPrimeDirichletSeries_sub_aboveCutoff_eq_finite_sum
    (P : Set ℕ) (f : ℕ) {s : ℝ} (hs : 1 < s) :
    supplyPrimeDirichletSeries P s -
        supplyPrimeDirichletSeries {p | p ∈ P ∧ f < p} s =
      ∑ n ∈ Finset.Iic f, supplyPrimeCoefficient P n / (n : ℝ) ^ s := by
  unfold supplyPrimeDirichletSeries
  calc
    _ = ∑' n : ℕ, (supplyPrimeCoefficient P n / (n : ℝ) ^ s -
        supplyPrimeCoefficient {p | p ∈ P ∧ f < p} n / (n : ℝ) ^ s) :=
      ((supplyPrimeDirichletSeries_summable P hs).tsum_sub
        (supplyPrimeDirichletSeries_summable {p | p ∈ P ∧ f < p} hs)).symm
    _ = ∑ n ∈ Finset.Iic f, (supplyPrimeCoefficient P n / (n : ℝ) ^ s -
        supplyPrimeCoefficient {p | p ∈ P ∧ f < p} n / (n : ℝ) ^ s) := by
      apply tsum_eq_sum
      intro n hn
      have hfn : f < n := lt_of_not_ge (by simpa using hn)
      simp [supplyPrimeCoefficient, Set.mem_ofPred_eq, hfn]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      have hfn : ¬ f < n := not_lt_of_ge (Finset.mem_Iic.mp hn)
      simp [supplyPrimeCoefficient, Set.mem_ofPred_eq, hfn]

theorem supplyPrimeCoefficient_div_rpow_le_one
    (P : Set ℕ) {s : ℝ} (hs : 1 < s) (n : ℕ) :
    supplyPrimeCoefficient P n / (n : ℝ) ^ s ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simp [Real.zero_rpow (zero_lt_one.trans hs).ne']
  · have hnOne : (1 : ℝ) ≤ n := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hd : 1 ≤ (n : ℝ) ^ s := Real.one_le_rpow hnOne (zero_le_one.trans hs.le)
    apply (div_le_iff₀ (zero_lt_one.trans_le hd)).mpr
    by_cases hp : n ∈ P <;> simp [supplyPrimeCoefficient, hp] <;> linarith

/-- The removed initial-prime terms are nonnegative and uniformly bounded
by the actual size of the finite index interval. -/
theorem supplyPrimeDirichletSeries_aboveCutoff_difference_bounds
    (P : Set ℕ) (f : ℕ) {s : ℝ} (hs : 1 < s) :
    0 ≤ supplyPrimeDirichletSeries P s -
        supplyPrimeDirichletSeries {p | p ∈ P ∧ f < p} s ∧
      supplyPrimeDirichletSeries P s -
        supplyPrimeDirichletSeries {p | p ∈ P ∧ f < p} s ≤ (f + 1 : ℝ) := by
  rw [supplyPrimeDirichletSeries_sub_aboveCutoff_eq_finite_sum P f hs]
  constructor
  · apply Finset.sum_nonneg
    intro n hn
    apply div_nonneg
    · unfold supplyPrimeCoefficient
      split_ifs <;> norm_num
    · exact Real.rpow_nonneg (Nat.cast_nonneg n) s
  · have h := (Finset.Iic f).sum_le_card_nsmul
      (fun n ↦ supplyPrimeCoefficient P n / (n : ℝ) ^ s) 1
      (fun n _ ↦ supplyPrimeCoefficient_div_rpow_le_one P hs n)
    simpa using h

theorem supplyPrimeDirichletSeries_aboveCutoff_difference_div_log_tendsto_zero
    (P : Set ℕ) (f : ℕ) :
    Tendsto
      (fun s : ℝ ↦ (supplyPrimeDirichletSeries P s -
        supplyPrimeDirichletSeries {p | p ∈ P ∧ f < p} s) / Real.log (1 / (s - 1)))
      (𝓝[>] 1) (𝓝 0) := by
  have hden := tendsto_log_one_div_sub_one_nhdsGT
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (tendsto_const_nhds.div_atTop hden)
  · filter_upwards [self_mem_nhdsWithin,
      hden.eventually (eventually_gt_atTop (0 : ℝ))] with s hs hd
    exact div_nonneg (supplyPrimeDirichletSeries_aboveCutoff_difference_bounds P f hs).1 hd.le
  · filter_upwards [self_mem_nhdsWithin,
      hden.eventually (eventually_gt_atTop (0 : ℝ))] with s hs hd
    exact div_le_div_of_nonneg_right
      (supplyPrimeDirichletSeries_aboveCutoff_difference_bounds P f hs).2 hd.le

/-- A proved positive normalized Dirichlet limit supplies the cofinal
lower values required by the explicit upper-supply interface. -/
theorem positiveUpperDirichletSupply_of_normalized_tendsto
    (P : Set ℕ) {c : ℝ} (hc : 0 < c)
    (hlim : Tendsto
      (fun s : ℝ ↦ supplyPrimeDirichletSeries P s / Real.log (1 / (s - 1)))
      (𝓝[>] 1) (𝓝 c)) : PositiveUpperDirichletSupply P := by
  let d : ℝ := c / 2
  have hd : 0 < d := div_pos hc (by norm_num)
  have hdlt : d < c := half_lt_self hc
  have hlow : ∀ᶠ s : ℝ in 𝓝[>] 1,
      d ≤ supplyPrimeDirichletSeries P s / Real.log (1 / (s - 1)) :=
    hlim.eventually (eventually_ge_nhds hdlt)
  refine ⟨d, hd, ?_⟩
  intro η hη
  have hmin : 0 < min η (1 / 2 : ℝ) := lt_min hη (by norm_num)
  have hupp : ∀ᶠ s : ℝ in 𝓝[>] 1, s < 1 + min η (1 / 2 : ℝ) :=
    (eventually_lt_nhds (lt_add_of_pos_right (1 : ℝ) hmin)).filter_mono nhdsWithin_le_nhds
  have hev : ∀ᶠ s : ℝ in 𝓝[>] 1,
      1 < s ∧ s < 1 + min η (1 / 2 : ℝ) ∧ 0 < Real.log (1 / (s - 1)) ∧
      d ≤ supplyPrimeDirichletSeries P s / Real.log (1 / (s - 1)) := by
    filter_upwards [self_mem_nhdsWithin, hupp,
      tendsto_log_one_div_sub_one_nhdsGT.eventually (eventually_gt_atTop (0 : ℝ)), hlow]
      with s hs hu hl hd'
    exact ⟨hs, hu, hl, hd'⟩
  obtain ⟨s, hs, hu, hl, hd'⟩ := hev.exists
  refine ⟨s - 1, sub_pos.mpr hs, by linarith, ?_⟩
  have h := (le_div_iff₀ hl).mp hd'
  simpa only [show 1 + (s - 1) = s by ring] using h

variable (K : Type*) [Field K] [NumberField K]

theorem completelySplittingRationalPrimes_aboveCutoff_DirichletSeries_normalized_tendsto
    [IsGalois ℚ K] (f : ℕ) :
    Tendsto
      (fun s : ℝ ↦ supplyPrimeDirichletSeries
        {p | p ∈ completelySplittingRationalPrimes K ∧ f < p} s /
        Real.log (1 / (s - 1)))
      (𝓝[>] 1) (𝓝 (1 / (Module.finrank ℚ K : ℝ))) := by
  have h := (completelySplittingRationalPrimes_DirichletSeries_normalized_tendsto K).sub
    (supplyPrimeDirichletSeries_aboveCutoff_difference_div_log_tendsto_zero
      (completelySplittingRationalPrimes K) f)
  simp only [sub_zero] at h
  convert h using 1
  funext s
  ring

/-- Actual completely splitting unramified rational primes retain positive
upper Dirichlet supply after any fixed finite initial-prime removal. -/
theorem completelySplittingRationalPrimes_aboveCutoff_positiveUpperDirichletSupply
    [IsGalois ℚ K] (f : ℕ) :
    PositiveUpperDirichletSupply
      {p | p ∈ completelySplittingRationalPrimes K ∧ f < p} := by
  apply positiveUpperDirichletSupply_of_normalized_tendsto
    {p | p ∈ completelySplittingRationalPrimes K ∧ f < p}
    (c := 1 / (Module.finrank ℚ K : ℝ))
  · apply one_div_pos.mpr
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  · exact completelySplittingRationalPrimes_aboveCutoff_DirichletSeries_normalized_tendsto K f

end

end Entry002
