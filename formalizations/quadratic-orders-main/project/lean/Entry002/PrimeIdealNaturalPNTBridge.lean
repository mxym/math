import Entry002.PrimeIdealChebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Elementary reductions for the genuine prime-ideal counting asymptotic.

These theorems are conditional reductions. In particular, the hypothesis that
`θ_K(x) / x` tends to one is explicitly retained; it is not asserted here.
-/

namespace Entry002

open NumberField Ideal Filter
open scoped NumberField Classical Topology

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- Cutting the actual prime-ideal count at `y` bounds the larger-norm ideals
by their logarithmic weights. -/
theorem primeIdeal_count_le_cutoff {x y : ℝ} (hy : 1 < y) :
    ((nonzeroPrimeIdealsUpTo K ⌊x⌋₊).card : ℝ) ≤
      ((nonzeroPrimeIdealsUpTo K ⌊y⌋₊).card : ℝ) +
        primeIdealTheta K x / Real.log y := by
  let s := nonzeroPrimeIdealsUpTo K ⌊x⌋₊
  let t := nonzeroPrimeIdealsUpTo K ⌊y⌋₊
  have hy0 : 0 ≤ y := by linarith
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hhigh : ((s \ t).card : ℝ) * Real.log y ≤ primeIdealTheta K x := by
    calc
      ((s \ t).card : ℝ) * Real.log y = ∑ P ∈ s \ t, Real.log y := by simp
      _ ≤ ∑ P ∈ s \ t, Real.log (Ideal.absNorm P : ℝ) := by
        apply Finset.sum_le_sum
        intro P hP
        obtain ⟨hPs, hPt⟩ := Finset.mem_sdiff.mp hP
        obtain ⟨_, hprime, hne⟩ := (mem_nonzeroPrimeIdealsUpTo K ⌊x⌋₊ P).mp hPs
        have hnorm : y < (Ideal.absNorm P : ℝ) := by
          by_contra h
          have hle : (Ideal.absNorm P : ℝ) ≤ y := le_of_not_gt h
          exact hPt ((mem_nonzeroPrimeIdealsUpTo K ⌊y⌋₊ P).mpr
            ⟨(Nat.le_floor_iff hy0).mpr hle, hprime, hne⟩)
        exact Real.log_le_log (by linarith) hnorm.le
      _ ≤ primeIdealTheta K x := by
        apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
        intro P hP _
        obtain ⟨_, hprime, hne⟩ := (mem_nonzeroPrimeIdealsUpTo K ⌊x⌋₊ P).mp hP
        apply Real.log_nonneg
        exact_mod_cast (show 1 ≤ Ideal.absNorm P from
          (by omega : 1 ≤ 2).trans (primeIdeal_absNorm_two_le K P hprime hne))
  have hcard : (s.card : ℝ) ≤ ((s \ t).card : ℝ) + (t.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card_sdiff_add_card (s := s) (t := t))
  have hhigh' := (le_div_iff₀ hlog).mpr hhigh
  change (s.card : ℝ) ≤ (t.card : ℝ) + primeIdealTheta K x / Real.log y
  linarith

/-- A cutoff at `x^a` gives an upper estimate whose limit is `1/a` when
`θ_K(x)/x` tends to one. -/
theorem primeIdeal_count_normalized_le_rpow_cutoff {x a : ℝ}
    (hx : 1 < x) (ha : 0 < a) :
    ((nonzeroPrimeIdealsUpTo K ⌊x⌋₊).card : ℝ) / (x / Real.log x) ≤
      ((Module.finrank ℚ K : ℝ) * (Real.log 4 + 4) / Real.log 2) *
        (Real.log x / x ^ (1 - a)) + (primeIdealTheta K x / x) / a := by
  have hx0 : 0 < x := by linarith
  have hxpow : 1 < x ^ a := Real.one_lt_rpow hx ha
  have hcount := (primeIdeal_count_le_cutoff K (x := x) hxpow).trans
    (add_le_add (primeIdeal_count_le_const_mul_self K
      (Real.rpow_nonneg hx0.le a)) le_rfl)
  have hlog : 0 < Real.log x := Real.log_pos hx
  calc
    ((nonzeroPrimeIdealsUpTo K ⌊x⌋₊).card : ℝ) / (x / Real.log x) =
        ((nonzeroPrimeIdealsUpTo K ⌊x⌋₊).card : ℝ) * Real.log x / x := by
      rw [div_div_eq_mul_div]
    _ ≤ (((Module.finrank ℚ K : ℝ) * (Real.log 4 + 4) * x ^ a) / Real.log 2 +
        primeIdealTheta K x / Real.log (x ^ a)) * Real.log x / x :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcount hlog.le) hx0.le
    _ = _ := by
      rw [Real.log_rpow hx0, Real.rpow_sub hx0, Real.rpow_one]
      field_simp

/-- The genuine logarithmically weighted prime-ideal PNT implies the exact
natural prime-ideal counting PNT, by an elementary cutoff argument. -/
theorem primeIdealNaturalPNT_of_theta
    (hθ : Tendsto (fun x : ℝ => primeIdealTheta K x / x) atTop (nhds 1)) :
    PrimeIdealNaturalPNT K := by
  unfold PrimeIdealNaturalPNT
  apply tendsto_order.mpr
  constructor
  · intro b hb
    filter_upwards [hθ.eventually_const_lt hb, eventually_gt_atTop (1 : ℝ)] with x hbx hx
    apply hbx.trans_le
    have hx0 : 0 < x := by linarith
    have hle := div_le_div_of_nonneg_right
      (primeIdealTheta_le_count_mul_log K hx0.le) hx0.le
    simpa only [div_div_eq_mul_div] using hle
  · intro b hb
    have hb0 : 0 < b := by linarith
    have hinv : 1 / b < (1 : ℝ) := (div_lt_one hb0).mpr hb
    obtain ⟨a, ha_low, ha_one⟩ := exists_between hinv
    have ha : 0 < a := (div_pos one_pos hb0).trans ha_low
    have hab : 1 / a < b := by
      apply (div_lt_iff₀ ha).mpr
      have := (div_lt_iff₀ hb0).mp ha_low
      nlinarith
    have hsmall : Tendsto (fun x : ℝ => Real.log x / x ^ (1 - a)) atTop (nhds 0) :=
      (isLittleO_log_rpow_atTop (by linarith : 0 < 1 - a)).tendsto_div_nhds_zero
    have hupper : Tendsto (fun x : ℝ =>
        ((Module.finrank ℚ K : ℝ) * (Real.log 4 + 4) / Real.log 2) *
          (Real.log x / x ^ (1 - a)) + (primeIdealTheta K x / x) / a)
        atTop (nhds (1 / a)) := by
      simpa using (hsmall.const_mul
        ((Module.finrank ℚ K : ℝ) * (Real.log 4 + 4) / Real.log 2)).add
        (hθ.div_const a)
    filter_upwards [hupper.eventually_lt_const hab, eventually_gt_atTop (1 : ℝ)] with x hxb hx
    exact (primeIdeal_count_normalized_le_rpow_cutoff K hx ha).trans_lt hxb

/-- The genuine prime-power weighted PNT also implies the natural count PNT,
using the elementary higher-power error estimate. -/
theorem primeIdealNaturalPNT_of_psi
    (hψ : Tendsto (fun x : ℝ => primeIdealPsi K x / x) atTop (nhds 1)) :
    PrimeIdealNaturalPNT K :=
  primeIdealNaturalPNT_of_theta K
    ((primeIdeal_psi_asymptotic_iff_theta_asymptotic K).mp hψ)

end

end Entry002
