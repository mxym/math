import Entry002.PrimeIdealLogConvolution
import Entry002.IdealNormAnalytic
import Entry002.PrimeIdealChebyshev

/-! The logarithmic derivative bridge for the genuine Dedekind zeta series.
Only its absolutely convergent half-plane is used. -/

namespace Entry002

open NumberField Ideal
open scoped NumberField Classical

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- Casting the true finite convolution identity to the coefficient field
used by LSeries. -/
theorem idealNormCoefficient_complex_convolution_eq_logMul (n : ℕ) :
    LSeries.convolution (fun n => (idealNormCoefficient K n : ℂ))
      (fun n => (primeIdealVonMangoldt K n : ℂ)) n =
        LSeries.logMul (fun n => (idealNormCoefficient K n : ℂ)) n := by
  have h := congrArg (fun x : ℝ => (x : ℂ))
    (idealNormCoefficient_log_eq_convolution K n)
  simpa only [LSeries.convolution_def, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.natCast_log, mul_comm, LSeries.logMul] using h.symm

/-- Actual prime-ideal coefficients produce the negative derivative of the
actual Dedekind zeta function, with no prime-ideal PNT premise. -/
theorem actualDedekindZeta_mul_primeIdealLSeries_eq_neg_deriv {s : ℂ}
    (hs : 1 < s.re) :
    dedekindZeta K s * LSeries (fun n => (primeIdealVonMangoldt K n : ℂ)) s =
      -deriv (dedekindZeta K) s := by
  have habsc : LSeries.abscissaOfAbsConv
      (fun n => (idealNormCoefficient K n : ℂ)) < s.re :=
    (idealNormCoefficient_abscissaOfAbsConv_le_one K).trans_lt (by exact_mod_cast hs)
  calc
    _ = LSeries (LSeries.convolution (fun n => (idealNormCoefficient K n : ℂ))
        (fun n => (primeIdealVonMangoldt K n : ℂ))) s := by
      rw [dedekindZeta_eq_idealNormCoefficient_LSeries K]
      exact (LSeries_convolution' (idealNormCoefficient_LSeriesSummable K hs)
        (primeIdealLSeriesSummable K hs)).symm
    _ = LSeries (LSeries.logMul (fun n => (idealNormCoefficient K n : ℂ))) s := by
      apply LSeries_congr
      intro n _
      exact idealNormCoefficient_complex_convolution_eq_logMul K n
    _ = -deriv (dedekindZeta K) s := by
      rw [funext (dedekindZeta_eq_idealNormCoefficient_LSeries K),
        LSeries_deriv habsc, neg_neg]

/-- On the positive real axis the proved coefficient positivity justifies
division by the true zeta value. -/
theorem primeIdealLSeries_eq_neg_dedekindZeta_logDerivative_real {x : ℝ}
    (hx : 1 < x) :
    LSeries (fun n => (primeIdealVonMangoldt K n : ℂ)) (x : ℂ) =
      -deriv (dedekindZeta K) (x : ℂ) / dedekindZeta K (x : ℂ) := by
  apply (eq_div_iff (actualDedekindZeta_ne_zero_real K hx)).mpr
  rw [mul_comm]
  exact actualDedekindZeta_mul_primeIdealLSeries_eq_neg_deriv K
    (by simpa using hx)

end

end Entry002
