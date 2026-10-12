import Entry002.PrimeIdealLogDerivative
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! The actual prime-ideal Euler-logarithm coefficients and their convergent
L-series. No prime-ideal PNT or complex continuation premise is used. -/

namespace Entry002

open NumberField Ideal Filter Asymptotics
open scoped NumberField Classical Topology ComplexOrder

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- The genuine Euler-logarithm coefficient, with totalized division at
zero and one. The actual von Mangoldt coefficient vanishes there. -/
def primeIdealLogCoefficient (n : ℕ) : ℝ :=
  primeIdealVonMangoldt K n / Real.log (n : ℝ)

theorem primeIdealLogCoefficient_eq_zero_of_lt_two (n : ℕ) (hn : n < 2) :
    primeIdealLogCoefficient K n = 0 := by
  simp [primeIdealLogCoefficient, primeIdealVonMangoldt_eq_zero_of_lt_two K n hn]

theorem primeIdealLogCoefficient_nonneg (n : ℕ) :
    0 ≤ primeIdealLogCoefficient K n :=
  div_nonneg (primeIdealVonMangoldt_nonneg K n) (Real.log_natCast_nonneg n)

/-- The genuine Euler-logarithm coefficient is bounded by the field degree. -/
theorem primeIdealLogCoefficient_le_degree (n : ℕ) :
    primeIdealLogCoefficient K n ≤ (Module.finrank ℚ K : ℝ) := by
  by_cases hn : n < 2
  · rw [primeIdealLogCoefficient_eq_zero_of_lt_two K n hn]
    exact Nat.cast_nonneg _
  · have hlog : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    apply (div_le_iff₀ hlog).mpr
    exact (primeIdealVonMangoldt_le_degree_mul K n).trans
      (mul_le_mul_of_nonneg_left ArithmeticFunction.vonMangoldt_le_log (Nat.cast_nonneg _))

theorem primeIdealLogCoefficient_log_mul (n : ℕ) :
    Real.log (n : ℝ) * primeIdealLogCoefficient K n = primeIdealVonMangoldt K n := by
  by_cases hn : n < 2
  · rw [primeIdealLogCoefficient_eq_zero_of_lt_two K n hn,
      primeIdealVonMangoldt_eq_zero_of_lt_two K n hn, mul_zero]
  · have hlog : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).ne'
    unfold primeIdealLogCoefficient
    field_simp

theorem primeIdealLogCoefficient_complex_logMul :
    LSeries.logMul (fun n ↦ (primeIdealLogCoefficient K n : ℂ)) =
      (fun n ↦ (primeIdealVonMangoldt K n : ℂ)) := by
  funext n
  simpa only [LSeries.logMul, Complex.natCast_log, Complex.ofReal_mul] using
    congrArg (fun x : ℝ ↦ (x : ℂ)) (primeIdealLogCoefficient_log_mul K n)

/-- Bounded actual coefficients give abscissa at most one. -/
theorem primeIdealEulerLogLSeries_abscissa_le_one :
    LSeries.abscissaOfAbsConv (fun n ↦ (primeIdealLogCoefficient K n : ℂ)) ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_one_of_isBigO_one
  apply isBigO_iff.mpr
  refine ⟨(Module.finrank ℚ K : ℝ), Filter.Eventually.of_forall fun n ↦ ?_⟩
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (primeIdealLogCoefficient_nonneg K n), norm_one, mul_one] using
    primeIdealLogCoefficient_le_degree K n

theorem primeIdealEulerLogLSeriesSummable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (primeIdealLogCoefficient K n : ℂ)) s :=
  LSeriesSummable_of_abscissaOfAbsConv_lt_re
    ((primeIdealEulerLogLSeries_abscissa_le_one K).trans_lt (by exact_mod_cast hs))

/-- Differentiating the actual Euler-logarithm series recovers the actual
prime-ideal von Mangoldt series. -/
theorem primeIdealEulerLogLSeries_hasDerivAt {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (LSeries (fun n ↦ (primeIdealLogCoefficient K n : ℂ)))
      (-LSeries (fun n ↦ (primeIdealVonMangoldt K n : ℂ)) s) s := by
  simpa only [primeIdealLogCoefficient_complex_logMul K] using
    LSeries_hasDerivAt
      ((primeIdealEulerLogLSeries_abscissa_le_one K).trans_lt (by exact_mod_cast hs))

theorem primeIdealEulerLogLSeries_tendsto_zero_atTop :
    Tendsto (fun x : ℝ ↦ LSeries (fun n ↦ (primeIdealLogCoefficient K n : ℂ)) x)
      atTop (𝓝 (0 : ℂ)) := by
  simpa [primeIdealLogCoefficient_eq_zero_of_lt_two K 1 (by norm_num)] using
    LSeries.tendsto_atTop
      ((primeIdealEulerLogLSeries_abscissa_le_one K).trans_lt (EReal.coe_lt_top 1))

/-- The actual Dedekind zeta series approaches one on the real axis. -/
theorem actualDedekindZeta_tendsto_one_atTop :
    Tendsto (fun x : ℝ ↦ dedekindZeta K x) atTop (𝓝 (1 : ℂ)) := by
  have h := LSeries.tendsto_atTop
    ((idealNormCoefficient_abscissaOfAbsConv_le_one K).trans_lt (EReal.coe_lt_top 1))
  simpa [dedekindZeta,
    idealNormCoefficient, idealNormCount, Ideal.absNorm_eq_one_iff] using h

end

end Entry002
