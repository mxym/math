import Entry002.PrimeIdealEulerLogAnalytic
import Entry002.PrimeIdealChebyshev
import Entry002.ArithmeticPrimeIdealCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Entry002

open NumberField Ideal Filter Asymptotics
open scoped NumberField Classical Topology

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- At a rational prime, the actual Euler-log coefficient counts prime
ideals of that norm, with no Galois hypothesis. -/
theorem primeIdealLogCoefficient_eq_primeNormFiber_card {p : ℕ} (hp : p.Prime) :
    primeIdealLogCoefficient K p = ((primeNormFiber K p).ncard : ℝ) := by
  have hfiber : (nonzeroPrimeIdealsUpTo K p).filter
      (fun P => Ideal.absNorm P = p) = (primeNormFiber_finite K p).toFinset := by
    ext P
    simp only [Finset.mem_filter, mem_nonzeroPrimeIdealsUpTo,
      Set.Finite.mem_toFinset, primeNormFiber, Set.mem_ofPred_eq]
    constructor
    · exact fun h => ⟨h.1.2.1, h.2⟩
    · rintro ⟨hprime, hnorm⟩
      refine ⟨⟨hnorm ▸ le_rfl, hprime, ?_⟩, hnorm⟩
      intro hzero
      exact hp.ne_zero (by simpa [hzero] using hnorm.symm)
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  unfold primeIdealLogCoefficient
  rw [primeIdealVonMangoldt_eq_norm_fiber_of_prime K hp le_rfl, hfiber]
  have hsum : (∑ P ∈ (primeNormFiber_finite K p).toFinset,
      Real.log (Ideal.absNorm P : ℝ)) =
      ((primeNormFiber_finite K p).toFinset.card : ℝ) * Real.log (p : ℝ) := by
    calc
      _ = ∑ P ∈ (primeNormFiber_finite K p).toFinset, Real.log (p : ℝ) := by
        apply Finset.sum_congr rfl
        intro P hP
        rw [((primeNormFiber_finite K p).mem_toFinset.mp hP).2]
      _ = _ := by simp
  rw [hsum, mul_div_cancel_right₀ _ hlog,
    ← Set.ncard_eq_toFinset_card (primeNormFiber K p) (primeNormFiber_finite K p)]

theorem primeIdealLogCoefficient_eq_split_indicator [IsGalois ℚ K]
    {p : ℕ} (hp : p.Prime)
    (hunram : Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)})) :
    primeIdealLogCoefficient K p =
      if RationalPrimeSplitsCompletely K p then (Module.finrank ℚ K : ℝ) else 0 := by
  rw [primeIdealLogCoefficient_eq_primeNormFiber_card K hp,
    primeNormFiber_card K p hp hunram]
  split_ifs <;> simp

/-- Completely split unramified rational primes, as an actual coefficient. -/
def completelySplitPrimeCoefficient (n : ℕ) : ℝ :=
  if n.Prime ∧ Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(n : ℤ)}) ∧
      RationalPrimeSplitsCompletely K n then 1 else 0

/-- The genuine residual after removing the completely split prime terms. -/
def primeIdealEulerLogRemainderCoefficient (n : ℕ) : ℝ :=
  primeIdealLogCoefficient K n -
    (Module.finrank ℚ K : ℝ) * completelySplitPrimeCoefficient K n

/-- The part supported on composite indices (including totalized zero/one). -/
def primeIdealCompositeLogCoefficient (n : ℕ) : ℝ :=
  if n.Prime then 0 else primeIdealLogCoefficient K n

/-- The remaining rational-prime terms are supported on ramified primes. -/
def primeIdealRamifiedLogCoefficient (n : ℕ) : ℝ :=
  if n.Prime ∧ ¬ Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(n : ℤ)}) then
    primeIdealLogCoefficient K n else 0

theorem primeIdealEulerLogRemainderCoefficient_eq_parts [IsGalois ℚ K] (n : ℕ) :
    primeIdealEulerLogRemainderCoefficient K n =
      primeIdealCompositeLogCoefficient K n + primeIdealRamifiedLogCoefficient K n := by
  by_cases hp : n.Prime
  · by_cases hu : Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(n : ℤ)})
    · rw [primeIdealEulerLogRemainderCoefficient,
        primeIdealLogCoefficient_eq_split_indicator K hp hu]
      by_cases hs : RationalPrimeSplitsCompletely K n <;>
        simp [completelySplitPrimeCoefficient, primeIdealCompositeLogCoefficient,
          primeIdealRamifiedLogCoefficient, hp, hu, hs]
    · simp [primeIdealEulerLogRemainderCoefficient, completelySplitPrimeCoefficient,
        primeIdealCompositeLogCoefficient, primeIdealRamifiedLogCoefficient, hp, hu]
  · simp [primeIdealEulerLogRemainderCoefficient, completelySplitPrimeCoefficient,
      primeIdealCompositeLogCoefficient, primeIdealRamifiedLogCoefficient, hp]

theorem primeIdealCompositeLogCoefficient_nonneg (n : ℕ) :
    0 ≤ primeIdealCompositeLogCoefficient K n := by
  unfold primeIdealCompositeLogCoefficient
  split_ifs <;> first | exact le_rfl | exact primeIdealLogCoefficient_nonneg K n

theorem primeIdealRamifiedLogCoefficient_nonneg (n : ℕ) :
    0 ≤ primeIdealRamifiedLogCoefficient K n := by
  unfold primeIdealRamifiedLogCoefficient
  split_ifs <;> first | exact le_rfl | exact primeIdealLogCoefficient_nonneg K n

theorem primeIdealEulerLogRemainderCoefficient_nonneg [IsGalois ℚ K] (n : ℕ) :
    0 ≤ primeIdealEulerLogRemainderCoefficient K n := by
  rw [primeIdealEulerLogRemainderCoefficient_eq_parts K n]
  exact add_nonneg (primeIdealCompositeLogCoefficient_nonneg K n)
    (primeIdealRamifiedLogCoefficient_nonneg K n)

theorem ramifiedRationalPrimes_finite :
    {n : ℕ | n.Prime ∧
      ¬ Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(n : ℤ)})}.Finite := by
  apply (Set.finite_Iic (NumberField.discr K).natAbs).subset
  intro p hp
  have hdiv : (p : ℤ) ∣ NumberField.discr K := by
    by_contra hnot
    exact hp.2 ((NumberField.not_dvd_discr_iff_isUnramifiedIn K (𝓞 K)
      (Nat.prime_iff_prime_int.mp hp.1)).mp hnot)
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr (NumberField.discr_ne_zero K))
    (by simpa using Int.natAbs_dvd_natAbs.mpr hdiv)

theorem primeIdealRamifiedLogCoefficient_div_summable (s : ℝ) :
    Summable (fun n : ℕ => primeIdealRamifiedLogCoefficient K n / (n : ℝ) ^ s) := by
  apply summable_of_ne_finset_zero (s := (ramifiedRationalPrimes_finite K).toFinset)
  intro n hn
  have hnot : ¬ (n.Prime ∧
      ¬ Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(n : ℤ)})) := by
    simpa using hn
  simp [primeIdealRamifiedLogCoefficient, hnot]

/-- Logarithms at indices at least two permit comparison with the actual
rational von Mangoldt coefficient. -/
theorem primeIdealLogCoefficient_le_degree_div_log_two_mul_vonMangoldt (n : ℕ) :
    primeIdealLogCoefficient K n ≤ (Module.finrank ℚ K : ℝ) / Real.log 2 *
      ArithmeticFunction.vonMangoldt n := by
  have hlogtwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  by_cases hn : n < 2
  · rw [primeIdealLogCoefficient_eq_zero_of_lt_two K n hn]
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) hlogtwo.le)
      ArithmeticFunction.vonMangoldt_nonneg
  · have hlog : Real.log (2 : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ n by omega))
    have hmul : primeIdealLogCoefficient K n * Real.log 2 ≤
        (Module.finrank ℚ K : ℝ) * ArithmeticFunction.vonMangoldt n := by
      calc
        _ ≤ primeIdealLogCoefficient K n * Real.log (n : ℝ) :=
          mul_le_mul_of_nonneg_left hlog (primeIdealLogCoefficient_nonneg K n)
        _ = primeIdealVonMangoldt K n := by
          rw [mul_comm, primeIdealLogCoefficient_log_mul K n]
        _ ≤ _ := primeIdealVonMangoldt_le_degree_mul K n
    have hdiv := (le_div_iff₀ hlogtwo).mpr hmul
    simpa only [div_mul_eq_mul_div, mul_comm] using hdiv

/-- The rational composite contribution is exactly the elementary
Chebyshev prime-power error. -/
theorem sum_nonprime_vonMangoldt_eq_psi_sub_theta (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n,
      if k.Prime then 0 else ArithmeticFunction.vonMangoldt k) =
      Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ) := by
  let s := Finset.Icc 1 n
  have hsplit := Finset.sum_filter_add_sum_filter_not s Nat.Prime
    (fun k => ArithmeticFunction.vonMangoldt k)
  have hprime : (∑ k ∈ s.filter Nat.Prime, ArithmeticFunction.vonMangoldt k) =
      Chebyshev.theta (n : ℝ) := by
    rw [Chebyshev.theta, Nat.floor_natCast]
    change (∑ k ∈ (Finset.Icc 1 n).filter Nat.Prime, _) = _
    rw [show (1 : ℕ) = 0 + 1 from rfl, Finset.Icc_add_one_left_eq_Ioc]
    apply Finset.sum_congr rfl
    intro k hk
    exact ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hk).2
  have hnot : (∑ k ∈ s.filter (fun k => ¬ k.Prime),
      ArithmeticFunction.vonMangoldt k) =
      ∑ k ∈ s, if k.Prime then 0 else ArithmeticFunction.vonMangoldt k := by
    simp only [Finset.sum_filter, ite_not]
  have hpsi : (∑ k ∈ s, ArithmeticFunction.vonMangoldt k) =
      Chebyshev.psi (n : ℝ) := by
    rw [Chebyshev.psi, Nat.floor_natCast]
    change (∑ k ∈ Finset.Icc 1 n, _) = _
    rw [show (1 : ℕ) = 0 + 1 from rfl, Finset.Icc_add_one_left_eq_Ioc]
  rw [hprime, hnot, hpsi] at hsplit
  change (∑ k ∈ s, if k.Prime then 0 else _) = _
  linarith

theorem primeIdealCompositeLogCoefficient_sum_le (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, primeIdealCompositeLogCoefficient K k) ≤
      (Module.finrank ℚ K : ℝ) / Real.log 2 *
        (Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ)) := by
  rw [← sum_nonprime_vonMangoldt_eq_psi_sub_theta, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  unfold primeIdealCompositeLogCoefficient
  by_cases hp : k.Prime
  · simp [hp]
  · simp only [ite_eq_right hp]
    exact primeIdealLogCoefficient_le_degree_div_log_two_mul_vonMangoldt K k

/-- A power strictly below one dominates the elementary rational
prime-power error. No prime number theorem is needed. -/
theorem rational_psi_sub_theta_isBigO_three_quarters :
    (fun x : ℝ => Chebyshev.psi x - Chebyshev.theta x) =O[atTop]
      (fun x : ℝ => x ^ (3 / 4 : ℝ)) := by
  have hbound : (fun x : ℝ => Chebyshev.psi x - Chebyshev.theta x) =O[atTop]
      (fun x : ℝ => Real.sqrt x * Real.log x) := by
    apply Asymptotics.IsBigO.of_bound 2
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg x) (Real.log_nonneg hx))]
    simpa only [mul_assoc] using Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx
  have hlog : Real.log =o[atTop] (fun x : ℝ => x ^ (1 / 4 : ℝ)) :=
    isLittleO_log_rpow_atTop (by norm_num)
  have hsmall := (Asymptotics.isBigO_refl Real.sqrt atTop).mul_isLittleO hlog
  have hsmall' : (fun x : ℝ => Real.sqrt x * Real.log x) =o[atTop]
      (fun x : ℝ => x ^ (3 / 4 : ℝ)) := by
    apply hsmall.congr' (Filter.Eventually.of_forall fun _ => rfl)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
    congr 1
    norm_num
  exact hbound.trans hsmall'.isBigO

/-- Partial sums of actual composite Euler-log coefficients have a
sublinear power bound sufficient for convergence at exponent one. -/
theorem primeIdealCompositeLogCoefficient_sum_isBigO :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, primeIdealCompositeLogCoefficient K k)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (3 / 4 : ℝ)) := by
  have hrat := rational_psi_sub_theta_isBigO_three_quarters.comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hupper := hrat.const_mul_left ((Module.finrank ℚ K : ℝ) / Real.log 2)
  apply Asymptotics.IsBigO.trans _ hupper
  apply Asymptotics.IsBigO.of_bound 1
  apply Filter.Eventually.of_forall
  intro n
  rw [one_mul, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun k _ =>
      primeIdealCompositeLogCoefficient_nonneg K k)]
  exact (primeIdealCompositeLogCoefficient_sum_le K n).trans (le_abs_self _)

theorem primeIdealCompositeLogCoefficient_abscissa_le_three_quarters :
    LSeries.abscissaOfAbsConv (fun n => (primeIdealCompositeLogCoefficient K n : ℂ)) ≤
      (3 / 4 : ℝ) := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro s hs
  exact LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (primeIdealCompositeLogCoefficient_sum_isBigO K)
    (primeIdealCompositeLogCoefficient_nonneg K) (by norm_num) (by simpa using hs)

theorem primeIdealCompositeLogCoefficient_div_summable :
    Summable (fun n : ℕ => primeIdealCompositeLogCoefficient K n / (n : ℝ)) := by
  have h := LSeries.summable_real_of_abscissaOfAbsConv_lt
    ((primeIdealCompositeLogCoefficient_abscissa_le_three_quarters K).trans_lt
      (show ((3 / 4 : ℝ) : EReal) < ((1 : ℝ) : EReal) by
        exact_mod_cast (show (3 / 4 : ℝ) < 1 by norm_num)))
  simpa only [Real.rpow_one] using h

theorem primeIdealEulerLogRemainderCoefficient_div_summable [IsGalois ℚ K] :
    Summable (fun n : ℕ => primeIdealEulerLogRemainderCoefficient K n / (n : ℝ)) := by
  have hram := primeIdealRamifiedLogCoefficient_div_summable K 1
  simp only [Real.rpow_one] at hram
  have hsum := (primeIdealCompositeLogCoefficient_div_summable K).add hram
  simpa only [primeIdealEulerLogRemainderCoefficient_eq_parts K, add_div] using hsum

/-- A finite, field-dependent bound obtained from the actual residual series. -/
def primeIdealEulerLogRemainderBound : ℝ :=
  ∑' n : ℕ, primeIdealEulerLogRemainderCoefficient K n / (n : ℝ)

theorem primeIdealEulerLogRemainderBound_nonneg [IsGalois ℚ K] :
    0 ≤ primeIdealEulerLogRemainderBound K := by
  exact tsum_nonneg fun n => div_nonneg
    (primeIdealEulerLogRemainderCoefficient_nonneg K n) (Nat.cast_nonneg n)

theorem primeIdealEulerLogRemainderCoefficient_div_rpow_le [IsGalois ℚ K]
    {s : ℝ} (hs : 1 < s) (n : ℕ) :
    primeIdealEulerLogRemainderCoefficient K n / (n : ℝ) ^ s ≤
      primeIdealEulerLogRemainderCoefficient K n / (n : ℝ) := by
  by_cases hn : n = 0
  · have hp0 : ¬ Nat.Prime 0 := by norm_num
    simp [hn, hp0, primeIdealEulerLogRemainderCoefficient, completelySplitPrimeCoefficient,
      primeIdealLogCoefficient_eq_zero_of_lt_two K 0 (by norm_num)]
  · have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    have hnOne : 1 ≤ (n : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    have hpow : (n : ℝ) ≤ (n : ℝ) ^ s := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hnOne hs.le
    exact div_le_div_of_nonneg_left (primeIdealEulerLogRemainderCoefficient_nonneg K n)
      hnpos hpow

theorem primeIdealEulerLogRemainderCoefficient_div_rpow_summable [IsGalois ℚ K]
    {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => primeIdealEulerLogRemainderCoefficient K n / (n : ℝ) ^ s) := by
  exact (primeIdealEulerLogRemainderCoefficient_div_summable K).of_nonneg_of_le
    (fun n => div_nonneg (primeIdealEulerLogRemainderCoefficient_nonneg K n)
      (Real.rpow_nonneg (Nat.cast_nonneg n) s))
    (primeIdealEulerLogRemainderCoefficient_div_rpow_le K hs)

/-- The residual is nonnegative and uniformly bounded throughout `s > 1`. -/
theorem primeIdealEulerLogRemainderSeries_bounds [IsGalois ℚ K]
    {s : ℝ} (hs : 1 < s) :
    0 ≤ (∑' n : ℕ, primeIdealEulerLogRemainderCoefficient K n / (n : ℝ) ^ s) ∧
      (∑' n : ℕ, primeIdealEulerLogRemainderCoefficient K n / (n : ℝ) ^ s) ≤
        primeIdealEulerLogRemainderBound K := by
  constructor
  · exact tsum_nonneg fun n => div_nonneg
      (primeIdealEulerLogRemainderCoefficient_nonneg K n)
      (Real.rpow_nonneg (Nat.cast_nonneg n) s)
  · exact Summable.tsum_le_tsum
      (primeIdealEulerLogRemainderCoefficient_div_rpow_le K hs)
      (primeIdealEulerLogRemainderCoefficient_div_rpow_summable K hs)
      (primeIdealEulerLogRemainderCoefficient_div_summable K)

end
end Entry002
