import Entry002.PrimeIdealAnalyticDefs
import Entry002.PrimeIdealVonMangoldtBound
import Entry002.PrimeIdealPowerSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Linearity

/-! Elementary estimates for the genuine prime-ideal coefficients.

The lemmas with `_of_coefficient_bound` expose their elementary domination
premise. No prime-ideal PNT or analytic continuation statement is assumed.
-/

namespace Entry002

open NumberField Ideal Filter
open scoped NumberField Classical Topology

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem primeIdealPsi_nonneg (x : ℝ) : 0 ≤ primeIdealPsi K x := by
  exact Finset.sum_nonneg fun n _ => primeIdealVonMangoldt_nonneg K n

theorem primeIdealTheta_nonneg (x : ℝ) : 0 ≤ primeIdealTheta K x := by
  apply Finset.sum_nonneg
  intro P hP
  obtain ⟨_, hprime, hne⟩ := (mem_nonzeroPrimeIdealsUpTo K ⌊x⌋₊ P).mp hP
  apply Real.log_nonneg
  exact_mod_cast (show 1 ≤ Ideal.absNorm P from
    (by omega : 1 ≤ 2).trans (primeIdeal_absNorm_two_le K P hprime hne))

theorem primeIdealTheta_monotone : Monotone (primeIdealTheta K) := by
  intro x y hxy
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro P hP
    obtain ⟨hPnorm, hprime, hne⟩ := (mem_nonzeroPrimeIdealsUpTo K ⌊x⌋₊ P).mp hP
    exact (mem_nonzeroPrimeIdealsUpTo K ⌊y⌋₊ P).mpr
      ⟨hPnorm.trans (Nat.floor_mono hxy), hprime, hne⟩
  · intro P hP _
    obtain ⟨_, hprime, hne⟩ := (mem_nonzeroPrimeIdealsUpTo K ⌊y⌋₊ P).mp hP
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ Ideal.absNorm P from
      (by omega : 1 ≤ 2).trans (primeIdeal_absNorm_two_le K P hprime hne))

/-- The logarithmic count bounds the actual number of nonzero prime ideals. -/
theorem primeIdeal_count_mul_log_two_le_theta (x : ℝ) :
    ((nonzeroPrimeIdealsUpTo K ⌊x⌋₊).card : ℝ) * Real.log 2 ≤
      primeIdealTheta K x := by
  calc
    ((nonzeroPrimeIdealsUpTo K ⌊x⌋₊).card : ℝ) * Real.log 2 =
        ∑ P ∈ nonzeroPrimeIdealsUpTo K ⌊x⌋₊, Real.log 2 := by simp
    _ ≤ primeIdealTheta K x := by
      apply Finset.sum_le_sum
      intro P hP
      obtain ⟨_, hprime, hne⟩ := (mem_nonzeroPrimeIdealsUpTo K ⌊x⌋₊ P).mp hP
      apply Real.log_le_log (by norm_num)
      exact_mod_cast primeIdeal_absNorm_two_le K P hprime hne

/-- Every logarithmic weight below `x` is at most `log x`. -/
theorem primeIdealTheta_le_count_mul_log {x : ℝ} (hx : 0 ≤ x) :
    primeIdealTheta K x ≤
      ((nonzeroPrimeIdealsUpTo K ⌊x⌋₊).card : ℝ) * Real.log x := by
  calc
    primeIdealTheta K x ≤ ∑ P ∈ nonzeroPrimeIdealsUpTo K ⌊x⌋₊, Real.log x := by
      apply Finset.sum_le_sum
      intro P hP
      obtain ⟨hPnorm, hprime, hne⟩ := (mem_nonzeroPrimeIdealsUpTo K ⌊x⌋₊ P).mp hP
      have htwo := primeIdeal_absNorm_two_le K P hprime hne
      apply Real.log_le_log (by exact_mod_cast (by omega : 0 < Ideal.absNorm P))
      have hPnorm' : (Ideal.absNorm P : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hPnorm
      exact hPnorm'.trans (Nat.floor_le hx)
    _ = _ := by simp

theorem primeIdealPsi_monotone : Monotone (primeIdealPsi K) := by
  intro x y hxy
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Ioc_subset_Ioc le_rfl (Nat.floor_mono hxy)
  · intro n _ _
    exact primeIdealVonMangoldt_nonneg K n

theorem primeIdealPsi_eq_zero_of_lt_two {x : ℝ} (hx : x < 2) :
    primeIdealPsi K x = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  have hn' := (Finset.mem_Ioc.mp hn).2
  have hx' : ⌊x⌋₊ < 2 := (Nat.floor_lt' (by norm_num : (2 : ℕ) ≠ 0)).mpr hx
  exact primeIdealVonMangoldt_eq_zero_of_lt_two K n (hn'.trans_lt hx')

/-- At a rational prime, positive norm powers reduce to the norm itself. -/
theorem primeIdealVonMangoldt_eq_norm_fiber_of_prime {p N : ℕ}
    (hp : p.Prime) (hpN : p ≤ N) :
    primeIdealVonMangoldt K p =
      ∑ P ∈ (nonzeroPrimeIdealsUpTo K N).filter (fun P => Ideal.absNorm P = p),
        Real.log (Ideal.absNorm P : ℝ) := by
  unfold primeIdealVonMangoldt
  congr 1
  ext P
  simp only [mem_primeIdealPowerSupport, Finset.mem_filter, mem_nonzeroPrimeIdealsUpTo]
  constructor
  · rintro ⟨hpnorm, hprime, hne, k, _, hpow⟩
    have hnorm := (hp.pow_eq_iff.mp hpow).1
    exact ⟨⟨hpnorm.trans hpN, hprime, hne⟩, hnorm⟩
  · rintro ⟨⟨_, hprime, hne⟩, hnorm⟩
    exact ⟨hnorm ▸ le_rfl, hprime, hne, 1, by norm_num, by simpa using hnorm⟩

/-- Retaining only rational-prime coefficients gives a subcount of `θ_K`. -/
theorem primeIdeal_sum_prime_coefficients_le_theta (x : ℝ) :
    (∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime, primeIdealVonMangoldt K n) ≤
      primeIdealTheta K x := by
  calc
    (∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime, primeIdealVonMangoldt K n) =
        ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime,
          ∑ P ∈ (nonzeroPrimeIdealsUpTo K ⌊x⌋₊).filter
            (fun P => Ideal.absNorm P = n), Real.log (Ideal.absNorm P : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact primeIdealVonMangoldt_eq_norm_fiber_of_prime K (Finset.mem_filter.mp hn).2
        (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).2
    _ = ∑ P ∈ (nonzeroPrimeIdealsUpTo K ⌊x⌋₊).filter
          (fun P => Ideal.absNorm P ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime),
          Real.log (Ideal.absNorm P : ℝ) := by
      exact Finset.sum_fiberwise_eq_sum_filter _ _ _ _
    _ ≤ primeIdealTheta K x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro P hP _
      obtain ⟨_, hprime, hne⟩ := (mem_nonzeroPrimeIdealsUpTo K ⌊x⌋₊ P).mp hP
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ Ideal.absNorm P from
        (by omega : 1 ≤ 2).trans (primeIdeal_absNorm_two_le K P hprime hne))

/-- Coefficient domination transfers to the genuine prime-power weighted count. -/
theorem primeIdealPsi_le_degree_mul_of_coefficient_bound
    (hcoeff : ∀ n : ℕ, primeIdealVonMangoldt K n ≤
      (Module.finrank ℚ K : ℝ) * ArithmeticFunction.vonMangoldt n) (x : ℝ) :
    primeIdealPsi K x ≤ (Module.finrank ℚ K : ℝ) * Chebyshev.psi x := by
  unfold primeIdealPsi Chebyshev.psi
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun n _ => hcoeff n

/-- An explicit elementary linear bound, with its domination premise visible. -/
theorem primeIdealPsi_le_const_mul_self_of_coefficient_bound
    (hcoeff : ∀ n : ℕ, primeIdealVonMangoldt K n ≤
      (Module.finrank ℚ K : ℝ) * ArithmeticFunction.vonMangoldt n)
    {x : ℝ} (hx : 0 ≤ x) :
    primeIdealPsi K x ≤ (Module.finrank ℚ K : ℝ) * (Real.log 4 + 4) * x := by
  calc
    primeIdealPsi K x ≤ (Module.finrank ℚ K : ℝ) * Chebyshev.psi x :=
      primeIdealPsi_le_degree_mul_of_coefficient_bound K hcoeff x
    _ ≤ (Module.finrank ℚ K : ℝ) * ((Real.log 4 + 4) * x) :=
      mul_le_mul_of_nonneg_left (Chebyshev.psi_le_const_mul_self hx) (by positivity)
    _ = _ := by ring

/-- The actual coefficient L-series converges absolutely to the right of one. -/
theorem primeIdealLSeriesSummable_of_coefficient_bound
    (hcoeff : ∀ n : ℕ, primeIdealVonMangoldt K n ≤
      (Module.finrank ℚ K : ℝ) * ArithmeticFunction.vonMangoldt n)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (primeIdealVonMangoldt K n : ℂ)) s := by
  have hsum := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).smul
    (Module.finrank ℚ K : ℂ)
  rw [LSeriesSummable, ← summable_norm_iff] at hsum ⊢
  refine hsum.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
  apply LSeries.norm_term_le s
  simpa [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_natCast,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg,
    primeIdealVonMangoldt_nonneg K n, ArithmeticFunction.vonMangoldt_nonneg] using hcoeff n

/-- The coefficient series has abscissa of absolute convergence at most one. -/
theorem primeIdealLSeries_abscissa_le_one_of_coefficient_bound
    (hcoeff : ∀ n : ℕ, primeIdealVonMangoldt K n ≤
      (Module.finrank ℚ K : ℝ) * ArithmeticFunction.vonMangoldt n) :
    LSeries.abscissaOfAbsConv (fun n => (primeIdealVonMangoldt K n : ℂ)) ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro y hy
  exact primeIdealLSeriesSummable_of_coefficient_bound K hcoeff (by simpa using hy)

/-- The corresponding real Dirichlet series is summable for real `s > 1`. -/
theorem primeIdeal_realSeries_summable_of_coefficient_bound
    (hcoeff : ∀ n : ℕ, primeIdealVonMangoldt K n ≤
      (Module.finrank ℚ K : ℝ) * ArithmeticFunction.vonMangoldt n)
    {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => primeIdealVonMangoldt K n / (n : ℝ) ^ s) := by
  apply LSeries.summable_real_of_abscissaOfAbsConv_lt
  exact (primeIdealLSeries_abscissa_le_one_of_coefficient_bound K hcoeff).trans_lt
    (by exact_mod_cast hs)

/-- Absolute convergence gives holomorphy on the open half-plane `Re(s) > 1`.
This asserts no extension across its boundary. -/
theorem primeIdealLSeries_analyticOnNhd_of_coefficient_bound
    (hcoeff : ∀ n : ℕ, primeIdealVonMangoldt K n ≤
      (Module.finrank ℚ K : ℝ) * ArithmeticFunction.vonMangoldt n) :
    AnalyticOnNhd ℂ (LSeries (fun n => (primeIdealVonMangoldt K n : ℂ)))
      {s : ℂ | 1 < s.re} := by
  apply (LSeries_analyticOnNhd (fun n => (primeIdealVonMangoldt K n : ℂ))).mono
  intro s hs
  exact (primeIdealLSeries_abscissa_le_one_of_coefficient_bound K hcoeff).trans_lt
    (by exact_mod_cast hs)

/-- Unconditional comparison with the ordinary Chebyshev function. -/
theorem primeIdealPsi_le_degree_mul (x : ℝ) :
    primeIdealPsi K x ≤ (Module.finrank ℚ K : ℝ) * Chebyshev.psi x :=
  primeIdealPsi_le_degree_mul_of_coefficient_bound K
    (primeIdealVonMangoldt_le_degree_mul K) x

/-- An explicit unconditional linear upper bound for the genuine `ψ_K`. -/
theorem primeIdealPsi_le_const_mul_self {x : ℝ} (hx : 0 ≤ x) :
    primeIdealPsi K x ≤ (Module.finrank ℚ K : ℝ) * (Real.log 4 + 4) * x :=
  primeIdealPsi_le_const_mul_self_of_coefficient_bound K
    (primeIdealVonMangoldt_le_degree_mul K) hx

theorem primeIdealPsi_le_log_four_mul_add_sqrt_mul_log {x : ℝ} (hx : 1 ≤ x) :
    primeIdealPsi K x ≤ (Module.finrank ℚ K : ℝ) *
      (Real.log 4 * x + 2 * Real.sqrt x * Real.log x) := by
  exact (primeIdealPsi_le_degree_mul K x).trans
    (mul_le_mul_of_nonneg_left (Chebyshev.psi_le hx) (by positivity))

/-- The additional prime-power weights are bounded by the rational
prime-power weights, multiplied by the number-field degree. -/
theorem primeIdealPsi_sub_theta_le_degree_mul (x : ℝ) :
    primeIdealPsi K x - primeIdealTheta K x ≤
      (Module.finrank ℚ K : ℝ) * (Chebyshev.psi x - Chebyshev.theta x) := by
  let s := Finset.Ioc 0 ⌊x⌋₊
  have hsplit := Finset.sum_filter_add_sum_filter_not s Nat.Prime
    (primeIdealVonMangoldt K)
  have hsplitRat := Finset.sum_filter_add_sum_filter_not s Nat.Prime
    (fun n => ArithmeticFunction.vonMangoldt n)
  have hprimeRat : (∑ n ∈ s.filter Nat.Prime, ArithmeticFunction.vonMangoldt n) =
      Chebyshev.theta x := by
    apply Finset.sum_congr rfl
    intro n hn
    exact ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hn).2
  have hnotRat : (∑ n ∈ s.filter (fun n => ¬ n.Prime),
      ArithmeticFunction.vonMangoldt n) = Chebyshev.psi x - Chebyshev.theta x := by
    rw [hprimeRat] at hsplitRat
    change Chebyshev.theta x + _ = Chebyshev.psi x at hsplitRat
    linarith
  calc
    primeIdealPsi K x - primeIdealTheta K x ≤
        primeIdealPsi K x - ∑ n ∈ s.filter Nat.Prime, primeIdealVonMangoldt K n :=
      sub_le_sub_left (primeIdeal_sum_prime_coefficients_le_theta K x) _
    _ = ∑ n ∈ s.filter (fun n => ¬ n.Prime), primeIdealVonMangoldt K n := by
      change _ + _ = primeIdealPsi K x at hsplit
      linarith
    _ ≤ (Module.finrank ℚ K : ℝ) *
        ∑ n ∈ s.filter (fun n => ¬ n.Prime), ArithmeticFunction.vonMangoldt n := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun n _ => primeIdealVonMangoldt_le_degree_mul K n
    _ = _ := by rw [hnotRat]

/-- An explicit error bound between genuine prime-power and prime-ideal
logarithmic counts; it includes all residue degrees and ramification. -/
theorem primeIdeal_abs_psi_sub_theta_le_sqrt_mul_log {x : ℝ} (hx : 1 ≤ x) :
    |primeIdealPsi K x - primeIdealTheta K x| ≤
      2 * (Module.finrank ℚ K : ℝ) * Real.sqrt x * Real.log x := by
  rw [abs_of_nonneg (sub_nonneg.mpr (primeIdealTheta_le_primeIdealPsi K x))]
  calc
    primeIdealPsi K x - primeIdealTheta K x ≤
        (Module.finrank ℚ K : ℝ) * (Chebyshev.psi x - Chebyshev.theta x) :=
      primeIdealPsi_sub_theta_le_degree_mul K x
    _ ≤ (Module.finrank ℚ K : ℝ) * (2 * Real.sqrt x * Real.log x) :=
      mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx))
        (by positivity)
    _ = _ := by ring

/-- The genuine higher-prime-power contribution is `o(x)`. -/
theorem primeIdeal_psi_sub_theta_isLittleO :
    (fun x : ℝ => primeIdealPsi K x - primeIdealTheta K x) =o[atTop]
      (fun x : ℝ => x) := by
  have hbound : (fun x : ℝ => primeIdealPsi K x - primeIdealTheta K x) =O[atTop]
      (fun x : ℝ => Real.sqrt x * Real.log x) := by
    apply Asymptotics.IsBigO.of_bound (2 * (Module.finrank ℚ K : ℝ))
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg x) (Real.log_nonneg hx))]
    simpa only [mul_assoc] using primeIdeal_abs_psi_sub_theta_le_sqrt_mul_log K hx
  have hlog : Real.log =o[atTop] Real.sqrt := by
    change Real.log =o[atTop] (fun x : ℝ => Real.sqrt x)
    simp_rw [Real.sqrt_eq_rpow]
    exact isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)
  have hsmall := (Asymptotics.isBigO_refl Real.sqrt atTop).mul_isLittleO hlog
  have hsmall' : (fun x : ℝ => Real.sqrt x * Real.log x) =o[atTop]
      (fun x : ℝ => x) := by
    apply hsmall.congr' (Filter.Eventually.of_forall fun _ => rfl)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact Real.mul_self_sqrt hx
  exact hbound.trans_isLittleO hsmall'

/-- The higher-prime-power error vanishes after normalization by `x`. -/
theorem primeIdeal_psi_sub_theta_div_tendsto_zero :
    Tendsto (fun x : ℝ => (primeIdealPsi K x - primeIdealTheta K x) / x)
      atTop (nhds 0) :=
  (primeIdeal_psi_sub_theta_isLittleO K).tendsto_div_nhds_zero

/-- A `ψ_K` PNT and a `θ_K` PNT are equivalent. Neither asymptotic is
asserted here; the equivalence uses the unconditional prime-power error. -/
theorem primeIdeal_psi_asymptotic_iff_theta_asymptotic :
    Tendsto (fun x : ℝ => primeIdealPsi K x / x) atTop (nhds 1) ↔
      Tendsto (fun x : ℝ => primeIdealTheta K x / x) atTop (nhds 1) := by
  constructor
  · intro hpsi
    have h := hpsi.sub (primeIdeal_psi_sub_theta_div_tendsto_zero K)
    convert h using 1 <;> first | (funext x; ring) | norm_num
  · intro htheta
    have h := htheta.add (primeIdeal_psi_sub_theta_div_tendsto_zero K)
    convert h using 1 <;> first | (funext x; ring) | norm_num

theorem primeIdealTheta_le_const_mul_self {x : ℝ} (hx : 0 ≤ x) :
    primeIdealTheta K x ≤ (Module.finrank ℚ K : ℝ) * (Real.log 4 + 4) * x :=
  (primeIdealTheta_le_primeIdealPsi K x).trans (primeIdealPsi_le_const_mul_self K hx)

/-- An elementary linear bound for the actual prime-ideal count. -/
theorem primeIdeal_count_le_const_mul_self {x : ℝ} (hx : 0 ≤ x) :
    ((nonzeroPrimeIdealsUpTo K ⌊x⌋₊).card : ℝ) ≤
      ((Module.finrank ℚ K : ℝ) * (Real.log 4 + 4) * x) / Real.log 2 := by
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  exact (primeIdeal_count_mul_log_two_le_theta K x).trans
    (primeIdealTheta_le_const_mul_self K hx)

theorem primeIdealLSeriesSummable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (primeIdealVonMangoldt K n : ℂ)) s :=
  primeIdealLSeriesSummable_of_coefficient_bound K
    (primeIdealVonMangoldt_le_degree_mul K) hs

theorem primeIdealLSeries_abscissa_le_one :
    LSeries.abscissaOfAbsConv (fun n => (primeIdealVonMangoldt K n : ℂ)) ≤ 1 :=
  primeIdealLSeries_abscissa_le_one_of_coefficient_bound K
    (primeIdealVonMangoldt_le_degree_mul K)

theorem primeIdeal_realSeries_summable {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => primeIdealVonMangoldt K n / (n : ℝ) ^ s) :=
  primeIdeal_realSeries_summable_of_coefficient_bound K
    (primeIdealVonMangoldt_le_degree_mul K) hs

theorem primeIdealLSeries_analyticOnNhd :
    AnalyticOnNhd ℂ (LSeries (fun n => (primeIdealVonMangoldt K n : ℂ)))
      {s : ℂ | 1 < s.re} :=
  primeIdealLSeries_analyticOnNhd_of_coefficient_bound K
    (primeIdealVonMangoldt_le_degree_mul K)

end

end Entry002
