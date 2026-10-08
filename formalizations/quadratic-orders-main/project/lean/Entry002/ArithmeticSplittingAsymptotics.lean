import Entry002.ArithmeticSplittingCount
import Entry002.GenericCumulativeDyadicDensity
import Mathlib.NumberTheory.PrimeCounting

/-! Supporting reduction, with the missing number-field prime-ideal
theorem stated as an explicit premise. The rational completely splitting
set and every count below are actual ideal/prime counts. This file does not
prove or assume a natural Chebotarev density as a black box. -/

namespace Entry002

open NumberField Ideal Filter
open scoped NumberField Classical Topology

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- Actual unramified rational primes splitting completely in `K/ℚ`. -/
def completelySplittingRationalPrimes : Set ℕ :=
  {p | p.Prime ∧ Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)}) ∧
    RationalPrimeSplitsCompletely K p}

omit [NumberField K] in
theorem completelySplittingRationalPrimes_cumulative_count (x : ℝ) (hx : 0 ≤ x) :
    cumulativePrimeCount (completelySplittingRationalPrimes K) x =
      ((unramifiedRationalPrimes K ⌊x⌋₊).filter
        (RationalPrimeSplitsCompletely K)).card := by
  unfold cumulativePrimeCount
  congr 1
  ext p
  simp only [mem_cumulativePrimeSet, Finset.mem_filter, mem_unramifiedRationalPrimes,
    completelySplittingRationalPrimes, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hp, hu, hs⟩, hpx⟩
    exact ⟨⟨Nat.le_floor hpx, hp, hu⟩, hs⟩
  · rintro ⟨⟨hpx, hp, hu⟩, hs⟩
    refine ⟨⟨hp, hu, hs⟩, ?_⟩
    exact (show (p : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast hpx).trans (Nat.floor_le hx)

theorem arithmeticSupply_sqrt_normalized_tendsto_zero :
    Tendsto (fun x : ℝ => Real.sqrt x / (x / Real.log x)) atTop (nhds 0) := by
  have h : Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (nhds 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := (zero_lt_one.trans hx).ne'
  have hs0 : Real.sqrt x ≠ 0 := (Real.sqrt_pos_of_pos (zero_lt_one.trans hx)).ne'
  have hl0 : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  field_simp
  nlinarith [Real.sq_sqrt (le_of_lt (zero_lt_one.trans hx))]

/-- The two genuine prime-ideal error counts are negligible on the
`x/log x` scale. This theorem has no prime-ideal asymptotic premise. -/
theorem arithmeticSupply_prime_ideal_error_tendsto_zero [IsGalois ℚ K] :
    Tendsto (fun x : ℝ =>
      ((ramifiedDegreeOnePrimeIdeals K ⌊x⌋₊).card +
        (higherDegreePrimeIdeals K ⌊x⌋₊).card : ℝ) / (x / Real.log x))
      atTop (nhds 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hupper := (hlog.const_mul
    ((discriminantIdealCount K : ℝ) + Module.finrank ℚ K)).add
      (arithmeticSupply_sqrt_normalized_tendsto_zero.const_mul
        (Module.finrank ℚ K : ℝ))
  simp only [mul_zero, zero_add] at hupper
  apply squeeze_zero' _ _ hupper
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_nonneg (by positivity) (div_nonneg (by linarith) (Real.log_pos hx).le)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hnorm : 0 < x / Real.log x := div_pos (by linarith) (Real.log_pos hx)
    have hsqrt : (Nat.sqrt ⌊x⌋₊ : ℝ) ≤ Real.sqrt x := by
      have hsq : (Nat.sqrt ⌊x⌋₊ : ℝ) ^ 2 ≤ (⌊x⌋₊ : ℝ) := by
        exact_mod_cast Nat.sqrt_le' ⌊x⌋₊
      have hfloor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
      have hreal := Real.sq_sqrt (show 0 ≤ x by linarith)
      have hnonneg := Real.sqrt_nonneg x
      have hnat : (0 : ℝ) ≤ Nat.sqrt ⌊x⌋₊ := Nat.cast_nonneg _
      nlinarith
    have hram : ((ramifiedDegreeOnePrimeIdeals K ⌊x⌋₊).card : ℝ) ≤
        discriminantIdealCount K := by exact_mod_cast ramifiedDegreeOnePrimeIdeals_card_le K ⌊x⌋₊
    have hhigh : ((higherDegreePrimeIdeals K ⌊x⌋₊).card : ℝ) ≤
        (Module.finrank ℚ K : ℝ) * (Real.sqrt x + 1) := by
      have h := higherDegreePrimeIdeals_card_le K ⌊x⌋₊
      have hcast : ((higherDegreePrimeIdeals K ⌊x⌋₊).card : ℝ) ≤
          (Module.finrank ℚ K : ℝ) * ((Nat.sqrt ⌊x⌋₊ : ℝ) + 1) := by exact_mod_cast h
      exact hcast.trans (mul_le_mul_of_nonneg_left (add_le_add hsqrt le_rfl)
        (Nat.cast_nonneg _))
    have hle := div_le_div_of_nonneg_right (add_le_add hram hhigh) hnorm.le
    calc
      _ ≤ ((discriminantIdealCount K : ℝ) +
          (Module.finrank ℚ K : ℝ) * (Real.sqrt x + 1)) / (x / Real.log x) := hle
      _ = _ := by field_simp; ring

/-- A real mathematical reduction: if the actual number-field prime-ideal
count is asymptotic to `x/log x`, the actual completely splitting rational
prime count is asymptotic to `(1/[K:ℚ]) x/log x`. The displayed `hPrimeIdeal`
is an OPEN analytic foundation, not a theorem proved by this declaration. -/
theorem arithmeticSupply_splitting_asymptotic_of_prime_ideal_theorem [IsGalois ℚ K]
    (hPrimeIdeal : Tendsto (fun x : ℝ =>
      ((nonzeroPrimeIdealsUpTo K ⌊x⌋₊).card : ℝ) / (x / Real.log x))
        atTop (nhds 1)) :
    Tendsto (fun x : ℝ =>
      (cumulativePrimeCount (completelySplittingRationalPrimes K) x : ℝ) /
        (x / Real.log x)) atTop (nhds (1 / (Module.finrank ℚ K : ℝ))) := by
  have hsub := hPrimeIdeal.sub (arithmeticSupply_prime_ideal_error_tendsto_zero K)
  simp only [sub_zero] at hsub
  have h := hsub.div_const (Module.finrank ℚ K : ℝ)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [completelySplittingRationalPrimes_cumulative_count K x (by linarith)]
  have hcard := nonzeroPrimeIdealsUpTo_card K ⌊x⌋₊
  have hcardReal : ((nonzeroPrimeIdealsUpTo K ⌊x⌋₊).card : ℝ) =
      (Module.finrank ℚ K : ℝ) *
        ((unramifiedRationalPrimes K ⌊x⌋₊).filter (RationalPrimeSplitsCompletely K)).card +
      (ramifiedDegreeOnePrimeIdeals K ⌊x⌋₊).card +
      (higherDegreePrimeIdeals K ⌊x⌋₊).card := by exact_mod_cast hcard
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  rw [hcardReal]
  field_simp
  ring

/-- Natural density relative to the actual rational prime count follows
from the actual prime-ideal theorem and the displayed rational PNT input.
The latter has a separately audited proof in `ArithmeticSupplyPNT.lean`;
the former remains open. -/
theorem arithmeticSupply_splitting_relative_density_of_prime_ideal_theorem
    [IsGalois ℚ K]
    (hPrimeIdeal : Tendsto (fun x : ℝ =>
      ((nonzeroPrimeIdealsUpTo K ⌊x⌋₊).card : ℝ) / (x / Real.log x))
        atTop (nhds 1))
    (hRationalPrime : Tendsto (fun x : ℝ =>
      (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x)) atTop (nhds 1)) :
    Tendsto (fun x : ℝ =>
      (cumulativePrimeCount (completelySplittingRationalPrimes K) x : ℝ) /
        (Nat.primeCounting ⌊x⌋₊ : ℝ)) atTop
      (nhds (1 / (Module.finrank ℚ K : ℝ))) := by
  have h := (arithmeticSupply_splitting_asymptotic_of_prime_ideal_theorem K
    hPrimeIdeal).div hRationalPrime (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact div_div_div_cancel_right₀
    (div_pos (by linarith : (0 : ℝ) < x) (Real.log_pos hx)).ne' _ _

/-- The literal inclusive A5 dyadic count for the actual splitting set,
with the number-field prime-ideal theorem still an explicit open premise. -/
theorem arithmeticSupply_splitting_dyadic_of_prime_ideal_theorem [IsGalois ℚ K]
    (hPrimeIdeal : Tendsto (fun x : ℝ =>
      ((nonzeroPrimeIdealsUpTo K ⌊x⌋₊).card : ℝ) / (x / Real.log x))
        atTop (nhds 1)) :
    0 < 1 / (Module.finrank ℚ K : ℝ) ∧
    Tendsto (fun T : ℝ =>
      (dyadicPrimeCount (completelySplittingRationalPrimes K) T : ℝ) /
        (T / Real.log T)) atTop (nhds (1 / (Module.finrank ℚ K : ℝ))) := by
  refine ⟨one_div_pos.mpr ?_, ?_⟩
  · exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  · exact dyadicPrimeCount_tendsto_of_cumulative _ _
      (arithmeticSupply_splitting_asymptotic_of_prime_ideal_theorem K hPrimeIdeal)

end

end Entry002
