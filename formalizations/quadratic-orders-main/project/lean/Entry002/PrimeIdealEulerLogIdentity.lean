import Entry002.PrimeIdealEulerLogAnalytic

/-! The actual real Euler-logarithm identity in the convergent half-plane,
proved by the logarithmic derivative and the limits at positive infinity. -/

namespace Entry002

open NumberField Ideal Filter
open scoped NumberField Classical Topology ComplexOrder

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- On the real axis, the log of the actual zeta value and the actual
Euler-logarithm series have the same derivative. -/
theorem actualDedekindZeta_log_sub_eulerLog_hasDerivAt_zero {x : ℝ} (hx : 1 < x) :
    HasDerivAt
      (fun y : ℝ ↦ Real.log (dedekindZeta K (y : ℂ)).re -
        (LSeries (fun n ↦ (primeIdealLogCoefficient K n : ℂ)) (y : ℂ)).re)
      0 x := by
  have hzpos := (Complex.pos_iff.mp (actualDedekindZeta_pos_real K hx)).1
  have hzim := (Complex.pos_iff.mp (actualDedekindZeta_pos_real K hx)).2.symm
  have hdz : HasDerivAt (dedekindZeta K) (deriv (dedekindZeta K) (x : ℂ)) (x : ℂ) :=
    ((dedekindZeta_analyticOnNhd_re_gt_one K) (x : ℂ) (by simpa using hx)).differentiableAt.hasDerivAt
  have hlog := hdz.real_of_complex.log hzpos.ne'
  have hq := (primeIdealEulerLogLSeries_hasDerivAt K (s := (x : ℂ))
    (by simpa using hx)).real_of_complex
  have hd : (deriv (dedekindZeta K) (x : ℂ)).re / (dedekindZeta K (x : ℂ)).re =
      -(LSeries (fun n ↦ (primeIdealVonMangoldt K n : ℂ)) (x : ℂ)).re := by
    apply (div_eq_iff hzpos.ne').mpr
    have h := congrArg Complex.re
      (actualDedekindZeta_mul_primeIdealLSeries_eq_neg_deriv K (s := (x : ℂ))
        (by simpa using hx))
    simp only [Complex.mul_re, hzim, zero_mul, sub_zero, Complex.neg_re] at h
    calc
      _ = -((dedekindZeta K (x : ℂ)).re *
          (LSeries (fun n ↦ (primeIdealVonMangoldt K n : ℂ)) (x : ℂ)).re) := by linarith
      _ = _ := by ring
  convert hlog.sub hq using 1
  simp only [Complex.neg_re, hd, sub_self]

theorem actualDedekindZeta_log_sub_eulerLog_tendsto_zero_atTop :
    Tendsto
      (fun x : ℝ ↦ Real.log (dedekindZeta K (x : ℂ)).re -
        (LSeries (fun n ↦ (primeIdealLogCoefficient K n : ℂ)) (x : ℂ)).re)
      atTop (𝓝 0) := by
  have hz : Tendsto (fun x : ℝ ↦ (dedekindZeta K (x : ℂ)).re) atTop (𝓝 1) := by
    simpa [Function.comp_def] using Complex.continuous_re.tendsto (1 : ℂ) |>.comp
      (actualDedekindZeta_tendsto_one_atTop K)
  have hq : Tendsto
      (fun x : ℝ ↦ (LSeries (fun n ↦ (primeIdealLogCoefficient K n : ℂ)) (x : ℂ)).re)
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using Complex.continuous_re.tendsto (0 : ℂ) |>.comp
      (primeIdealEulerLogLSeries_tendsto_zero_atTop K)
  simpa using (hz.log one_ne_zero).sub hq

/-- The real logarithm of the genuine Dedekind zeta function is the
genuine Euler-logarithm L-series for every real `s > 1`. -/
theorem actualDedekindZeta_real_log_eq_eulerLog {s : ℝ} (hs : 1 < s) :
    Real.log (dedekindZeta K (s : ℂ)).re =
      (LSeries (fun n ↦ (primeIdealLogCoefficient K n : ℂ)) (s : ℂ)).re := by
  let F : ℝ → ℝ := fun x ↦ Real.log (dedekindZeta K (x : ℂ)).re -
    (LSeries (fun n ↦ (primeIdealLogCoefficient K n : ℂ)) (x : ℂ)).re
  have hd (x : ℝ) (hx : x ∈ Set.Ioi (1 : ℝ)) : HasDerivAt F 0 x :=
    actualDedekindZeta_log_sub_eulerLog_hasDerivAt_zero K hx
  have hc (x : ℝ) (hx : 1 < x) : F x = F s :=
    isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun y hy ↦ (hd y hy).differentiableAt.differentiableWithinAt)
      (fun y hy ↦ (hd y hy).deriv) hx hs
  have hlim : Tendsto F atTop (𝓝 0) :=
    actualDedekindZeta_log_sub_eulerLog_tendsto_zero_atTop K
  have hlim' : Tendsto F atTop (𝓝 (F s)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact (hc x hx).symm
  have hzero : F s = 0 := tendsto_nhds_unique hlim' hlim
  exact sub_eq_zero.mp hzero

end

end Entry002
