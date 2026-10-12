import Entry002.PrimeIdealEulerLogRemainder
import Entry002.PrimeIdealEulerLogRealPole
import Entry002.WeakSupplyInterfaces
import Entry002.ArithmeticSplittingAsymptotics

/-! Actual completely splitting rational-prime Dirichlet supply from the
genuine Euler-logarithm identity, positive real pole, and bounded remainder. -/

namespace Entry002

open NumberField Ideal Filter
open scoped NumberField Classical Topology

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem completelySplitPrimeCoefficient_eq_supplyPrimeCoefficient (n : ℕ) :
    completelySplitPrimeCoefficient K n =
      supplyPrimeCoefficient (completelySplittingRationalPrimes K) n := by
  simp only [completelySplitPrimeCoefficient, supplyPrimeCoefficient,
    completelySplittingRationalPrimes, Set.mem_setOf_eq]

/-- Real transport for the genuine Euler-logarithm L-series. -/
theorem primeIdealEulerLogLSeries_re_eq_real_tsum {s : ℝ} (hs : 1 < s) :
    (LSeries (fun n ↦ (primeIdealLogCoefficient K n : ℂ)) (s : ℂ)).re =
      ∑' n : ℕ, primeIdealLogCoefficient K n / (n : ℝ) ^ s := by
  rw [LSeries, Complex.re_tsum
    (primeIdealEulerLogLSeriesSummable K (s := (s : ℂ)) (by simpa using hs))]
  apply tsum_congr
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [primeIdealLogCoefficient_eq_zero_of_lt_two K 0 (by norm_num)]
  · simp only [LSeries.term_of_ne_zero hn, ← Complex.ofReal_natCast n,
      ← Complex.ofReal_cpow n.cast_nonneg, ← Complex.ofReal_div, Complex.ofReal_re]

theorem primeIdealLogCoefficient_div_rpow_summable {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ ↦ primeIdealLogCoefficient K n / (n : ℝ) ^ s) :=
  LSeries.summable_real_of_abscissaOfAbsConv_lt
    ((primeIdealEulerLogLSeries_abscissa_le_one K).trans_lt (by exact_mod_cast hs))

/-- Exact decomposition into the actual completely splitting rational
prime series and its genuine nonnegative bounded remainder. -/
theorem primeIdealEulerLogLSeries_re_eq_split_add_remainder [IsGalois ℚ K]
    {s : ℝ} (hs : 1 < s) :
    (LSeries (fun n ↦ (primeIdealLogCoefficient K n : ℂ)) (s : ℂ)).re =
      (Module.finrank ℚ K : ℝ) *
        supplyPrimeDirichletSeries (completelySplittingRationalPrimes K) s +
      ∑' n : ℕ, primeIdealEulerLogRemainderCoefficient K n / (n : ℝ) ^ s := by
  rw [primeIdealEulerLogLSeries_re_eq_real_tsum K hs]
  have hsplit := supplyPrimeDirichletSeries_summable (completelySplittingRationalPrimes K) hs
  have hrem := primeIdealEulerLogRemainderCoefficient_div_rpow_summable K hs
  calc
    _ = ∑' n : ℕ, (
        (Module.finrank ℚ K : ℝ) *
          (supplyPrimeCoefficient (completelySplittingRationalPrimes K) n / (n : ℝ) ^ s) +
        primeIdealEulerLogRemainderCoefficient K n / (n : ℝ) ^ s) := by
      apply tsum_congr
      intro n
      rw [primeIdealEulerLogRemainderCoefficient,
        completelySplitPrimeCoefficient_eq_supplyPrimeCoefficient K n]
      ring
    _ = _ := by
      rw [(hsplit.mul_left _).tsum_add hrem, tsum_mul_left]
      rfl

theorem actualDedekindZeta_real_log_eq_split_add_remainder [IsGalois ℚ K]
    {s : ℝ} (hs : 1 < s) :
    Real.log (dedekindZeta K (s : ℂ)).re =
      (Module.finrank ℚ K : ℝ) *
        supplyPrimeDirichletSeries (completelySplittingRationalPrimes K) s +
      ∑' n : ℕ, primeIdealEulerLogRemainderCoefficient K n / (n : ℝ) ^ s := by
  rw [actualDedekindZeta_real_log_eq_eulerLog K hs,
    primeIdealEulerLogLSeries_re_eq_split_add_remainder K hs]

/-- Both one-sided logarithmic bounds have the actual residual constant. -/
theorem completelySplittingRationalPrimes_DirichletSeries_log_bounds [IsGalois ℚ K]
    {s : ℝ} (hs : 1 < s) :
    Real.log (dedekindZeta K (s : ℂ)).re - primeIdealEulerLogRemainderBound K ≤
        (Module.finrank ℚ K : ℝ) *
          supplyPrimeDirichletSeries (completelySplittingRationalPrimes K) s ∧
      (Module.finrank ℚ K : ℝ) *
          supplyPrimeDirichletSeries (completelySplittingRationalPrimes K) s ≤
        Real.log (dedekindZeta K (s : ℂ)).re := by
  have h := actualDedekindZeta_real_log_eq_split_add_remainder K hs
  have hb := primeIdealEulerLogRemainderSeries_bounds K hs
  constructor <;> linarith

theorem tendsto_log_one_div_sub_one_nhdsGT :
    Tendsto (fun s : ℝ ↦ Real.log (1 / (s - 1))) (𝓝[>] 1) atTop := by
  have hid : Tendsto (fun s : ℝ ↦ s) (𝓝[>] 1) (𝓝 1) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hsub : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using hid.sub_const 1
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact sub_pos.mpr (show (1 : ℝ) < s from hs)
  simpa only [Function.comp_def, one_div] using
    Real.tendsto_log_atTop.comp (tendsto_inv_nhdsGT_zero.comp hsub)

theorem primeIdealEulerLogLSeries_div_log_one_div_sub_one_tendsto :
    Tendsto
      (fun s : ℝ ↦ (LSeries (fun n ↦ (primeIdealLogCoefficient K n : ℂ)) (s : ℂ)).re /
        Real.log (1 / (s - 1)))
      (𝓝[>] 1) (𝓝 1) := by
  have hden := tendsto_log_one_div_sub_one_nhdsGT
  have h := (primeIdealEulerLogLSeries_add_log_sub_one_tendsto_nhdsGT K).div_atTop hden
  have h' : Tendsto
      (fun s : ℝ ↦
        ((LSeries (fun n ↦ (primeIdealLogCoefficient K n : ℂ)) (s : ℂ)).re +
          Real.log (s - 1)) / Real.log (1 / (s - 1)) + 1)
      (𝓝[>] 1) (𝓝 1) := by
    simpa using h.add_const 1
  apply h'.congr'
  filter_upwards [hden.eventually (eventually_gt_atTop (0 : ℝ))] with s hs
  have hne : Real.log (1 / (s - 1)) ≠ 0 := hs.ne'
  rw [one_div, Real.log_inv] at hne ⊢
  have hne' : Real.log (s - 1) ≠ 0 := neg_ne_zero.mp hne
  field_simp [hne']
  ring

theorem primeIdealEulerLogRemainderSeries_div_log_one_div_sub_one_tendsto_zero
    [IsGalois ℚ K] :
    Tendsto
      (fun s : ℝ ↦
        (∑' n : ℕ, primeIdealEulerLogRemainderCoefficient K n / (n : ℝ) ^ s) /
          Real.log (1 / (s - 1)))
      (𝓝[>] 1) (𝓝 0) := by
  have hden := tendsto_log_one_div_sub_one_nhdsGT
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (tendsto_const_nhds.div_atTop hden)
  · filter_upwards [self_mem_nhdsWithin,
      hden.eventually (eventually_gt_atTop (0 : ℝ))] with s hs hd
    exact div_nonneg (primeIdealEulerLogRemainderSeries_bounds K hs).1 hd.le
  · filter_upwards [self_mem_nhdsWithin,
      hden.eventually (eventually_gt_atTop (0 : ℝ))] with s hs hd
    exact div_le_div_of_nonneg_right (primeIdealEulerLogRemainderSeries_bounds K hs).2 hd.le

/-- Genuine Dirichlet density of the actual completely splitting prime
set, obtained from the actual positive real pole and bounded remainder. -/
theorem completelySplittingRationalPrimes_DirichletSeries_normalized_tendsto
    [IsGalois ℚ K] :
    Tendsto
      (fun s : ℝ ↦ supplyPrimeDirichletSeries (completelySplittingRationalPrimes K) s /
        Real.log (1 / (s - 1)))
      (𝓝[>] 1) (𝓝 (1 / (Module.finrank ℚ K : ℝ))) := by
  have hdeg : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  have h := ((primeIdealEulerLogLSeries_div_log_one_div_sub_one_tendsto K).sub
    (primeIdealEulerLogRemainderSeries_div_log_one_div_sub_one_tendsto_zero K)).div_const
      (Module.finrank ℚ K : ℝ)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [primeIdealEulerLogLSeries_re_eq_split_add_remainder K hs]
  field_simp
  ring

/-- Positive upper Dirichlet supply for the actual unramified completely
splitting rational primes, with no natural prime-counting asymptotic premise. -/
theorem completelySplittingRationalPrimes_positiveUpperDirichletSupply [IsGalois ℚ K] :
    PositiveUpperDirichletSupply (completelySplittingRationalPrimes K) := by
  have hdeg : 0 < (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  let d : ℝ := (1 / (Module.finrank ℚ K : ℝ)) / 2
  have hd : 0 < d := div_pos (one_div_pos.mpr hdeg) (by norm_num)
  have hdlt : d < 1 / (Module.finrank ℚ K : ℝ) :=
    half_lt_self (one_div_pos.mpr hdeg)
  have hlow : ∀ᶠ s : ℝ in 𝓝[>] 1,
      d ≤ supplyPrimeDirichletSeries (completelySplittingRationalPrimes K) s /
        Real.log (1 / (s - 1)) :=
    (completelySplittingRationalPrimes_DirichletSeries_normalized_tendsto K).eventually
      (eventually_ge_nhds hdlt)
  refine ⟨d, hd, ?_⟩
  intro η hη
  have hmin : 0 < min η (1 / 2 : ℝ) := lt_min hη (by norm_num)
  have hupp : ∀ᶠ s : ℝ in 𝓝[>] 1, s < 1 + min η (1 / 2 : ℝ) :=
    (eventually_lt_nhds (lt_add_of_pos_right (1 : ℝ) hmin)).filter_mono nhdsWithin_le_nhds
  have hev : ∀ᶠ s : ℝ in 𝓝[>] 1,
      1 < s ∧ s < 1 + min η (1 / 2 : ℝ) ∧ 0 < Real.log (1 / (s - 1)) ∧
      d ≤ supplyPrimeDirichletSeries (completelySplittingRationalPrimes K) s /
        Real.log (1 / (s - 1)) := by
    filter_upwards [self_mem_nhdsWithin, hupp,
      tendsto_log_one_div_sub_one_nhdsGT.eventually (eventually_gt_atTop (0 : ℝ)), hlow]
      with s hs hu hl hd'
    exact ⟨hs, hu, hl, hd'⟩
  obtain ⟨s, hs, hu, hl, hd'⟩ := hev.exists
  refine ⟨s - 1, sub_pos.mpr hs, by linarith, ?_⟩
  have h := (le_div_iff₀ hl).mp hd'
  simpa only [show 1 + (s - 1) = s by ring] using h

end

end Entry002
