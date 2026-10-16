import Deviation.InformationQuantile
import Mathlib.Analysis.Complex.ExponentialBounds

open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory ExtractionSpectrum

namespace ExtractionDeviation
noncomputable section

def quadraticChar (x : ℝ) : ℂ := 1+(x:ℂ)*Complex.I-(x:ℂ)^2/2

/-- A global cubic remainder for imaginary exponentials. The generous absolute
constant is deliberate; this is a proved quantitative ingredient, not a claimed
Berry--Esseen bound or an assumed smoothing inequality. -/
theorem imaginary_exp_cubic_remainder (x : ℝ) :
    ‖Complex.exp ((x:ℂ)*Complex.I)-quadraticChar x‖ ≤ 4*|x|^3 := by
  have hz : ‖(x:ℂ)*Complex.I‖ = |x| := by simp
  have hpoly : (∑ m ∈ Finset.range 3, (((x:ℂ)*Complex.I)^m)/(m.factorial:ℂ)) =
      quadraticChar x := by
    norm_num [Finset.sum_range_succ, quadraticChar, mul_pow, Complex.I_sq]
    ring
  by_cases hx : |x| ≤ 1
  · have h := Complex.norm_exp_sub_sum_le_norm_mul_exp ((x:ℂ)*Complex.I) 3
    rw [hpoly,hz] at h
    have he : Real.exp |x| ≤ 3 :=
      (Real.exp_le_exp.mpr hx).trans Real.exp_one_lt_three.le
    have hmul := mul_le_mul_of_nonneg_left he (pow_nonneg (abs_nonneg x) 3)
    nlinarith [pow_nonneg (abs_nonneg x) 3]
  · have hr : 1 ≤ |x| := (lt_of_not_ge hx).le
    have hquad : ‖quadraticChar x‖ ≤ 1+|x|+|x|^2/2 := by
      calc
        _ ≤ ‖(1:ℂ)+(x:ℂ)*Complex.I‖+‖(x:ℂ)^2/2‖ := norm_sub_le _ _
        _ ≤ (‖(1:ℂ)‖+‖(x:ℂ)*Complex.I‖)+‖(x:ℂ)^2/2‖ :=
          add_le_add (norm_add_le _ _) le_rfl
        _ = _ := by simp
    have hnorm := norm_sub_le (Complex.exp ((x:ℂ)*Complex.I)) (quadraticChar x)
    rw [Complex.norm_exp_ofReal_mul_I] at hnorm
    have hr2 : |x| ≤ |x|^2 := by nlinarith [abs_nonneg x]
    have hr3 : |x|^2 ≤ |x|^3 := by
      have h := mul_le_mul_of_nonneg_right hr (sq_nonneg |x|)
      nlinarith
    nlinarith

variable {ι : Type*} [Fintype ι]

def finiteChar (p f : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ i, (p i:ℂ)*Complex.exp (((t*f i:ℝ):ℂ)*Complex.I)

def centeredObservable (p f : ι → ℝ) (i : ι) : ℝ := f i-finiteMean p f

def thirdAbsoluteMoment (p f : ι → ℝ) : ℝ :=
  ∑ i, p i*|centeredObservable p f i|^3

theorem centeredObservable_mean (p f : ι → ℝ) (hs : ∑ i, p i = 1) :
    ∑ i, p i*centeredObservable p f i = 0 := by
  simp only [centeredObservable, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hs, one_mul,
    finiteMean, sub_self]

theorem thirdAbsoluteMoment_nonneg (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    0 ≤ thirdAbsoluteMoment p f :=
  Finset.sum_nonneg (fun i hi => mul_nonneg (hp i) (pow_nonneg (abs_nonneg _) 3))

theorem finiteChar_norm_le_one (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (t : ℝ) : ‖finiteChar p f t‖ ≤ 1 := by
  calc
    _ ≤ ∑ i, ‖(p i:ℂ)*Complex.exp (((t*f i:ℝ):ℂ)*Complex.I)‖ := norm_sum_le _ _
    _ = ∑ i, p i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp i),
        Complex.norm_exp_ofReal_mul_I, mul_one]
    _ = 1 := hs

theorem centered_quadratic_average (p f : ι → ℝ) (hs : ∑ i, p i = 1) (t : ℝ) :
    (∑ i, (p i:ℂ)*quadraticChar (t*centeredObservable p f i)) =
      1-(finiteVariance p f:ℂ)*(t:ℂ)^2/2 := by
  have hcenter : (∑ i, (p i:ℂ)*(centeredObservable p f i:ℂ)) = 0 := by
    exact_mod_cast centeredObservable_mean p f hs
  have hsum : (∑ i, (p i:ℂ)) = 1 := by exact_mod_cast hs
  have hvar : (∑ i, (p i:ℂ)*(centeredObservable p f i:ℂ)^2) = (finiteVariance p f:ℂ) := by
    simp only [finiteVariance, centeredObservable, Complex.ofReal_sum, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_sub]
  calc
    _ = (∑ i, (p i:ℂ))+(t:ℂ)*Complex.I*(∑ i, (p i:ℂ)*(centeredObservable p f i:ℂ))-
        (t:ℂ)^2/2*(∑ i, (p i:ℂ)*(centeredObservable p f i:ℂ)^2) := by
      simp only [quadraticChar, Complex.ofReal_mul, Finset.mul_sum,
        ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by rw [hcenter,hsum,hvar]; ring

/-- A fully finite, quantitative characteristic-function approximation for an
arbitrary actual normalized law. The third absolute centred moment is computed
from the original finite law, including zero-probability letters. -/
theorem finiteChar_centered_cubic_bound (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (t : ℝ) :
    ‖finiteChar p (centeredObservable p f) t-
      (1-(finiteVariance p f:ℂ)*(t:ℂ)^2/2)‖ ≤ 4*|t|^3*thirdAbsoluteMoment p f := by
  rw [← centered_quadratic_average p f hs t]
  unfold finiteChar
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖(p i:ℂ)*Complex.exp (((t*centeredObservable p f i:ℝ):ℂ)*Complex.I)-
        (p i:ℂ)*quadraticChar (t*centeredObservable p f i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, p i*(4*|t*centeredObservable p f i|^3) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp i)]
      exact mul_le_mul_of_nonneg_left (imaginary_exp_cubic_remainder _) (hp i)
    _ = _ := by
      simp only [thirdAbsoluteMoment, abs_mul, mul_pow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Exact bridge from the finite formula to Mathlib's characteristic function
of the pushforward of the actual finite probability measure. -/
theorem finiteChar_eq_charFun (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (t : ℝ) :
    finiteChar p f t = charFun ((finiteMeasure p hp hs).map f) t := by
  rw [charFun_apply_real, integral_map (measurable_of_countable f).aemeasurable (by fun_prop),
    integral_fintype Integrable.of_finite]
  simp only [Measure.real, finiteMeasure_singleton, ENNReal.toReal_ofReal (hp _),
    Complex.real_smul, finiteChar, Complex.ofReal_mul]

end
end ExtractionDeviation
