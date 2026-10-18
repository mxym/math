import Deviation.FourierMoment

open scoped BigOperators NNReal ENNReal Topology
open ExtractionSpectrum MeasureTheory ProbabilityTheory

namespace ExtractionDeviation
noncomputable section

def gaussianChar (v t : ℝ) : ℂ := (Real.exp (-v*t^2/2):ℝ)

theorem gaussianChar_norm (v t : ℝ) : ‖gaussianChar v t‖ = Real.exp (-v*t^2/2) := by
  rw [gaussianChar, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem exp_neg_quadratic_remainder (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) :
    ‖((Real.exp (-x):ℝ):ℂ)-((1-x:ℝ):ℂ)‖ ≤ x^2 := by
  have h := Real.norm_exp_sub_one_sub_id_le (x := -x) (by
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg hx]
    exact hx')
  have heq : ((Real.exp (-x):ℝ):ℂ)-((1-x:ℝ):ℂ) =
      ((Real.exp (-x)-1-(-x):ℝ):ℂ) := by push_cast; ring
  rw [heq, Complex.norm_real]
  simpa only [norm_neg, Real.norm_eq_abs, abs_of_nonneg hx] using h

/-- Explicit telescoping bound, retaining a common exponential damping factor. -/
theorem norm_pow_sub_pow_le (a b : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (n : ℕ) :
    ‖a^(n+1)-b^(n+1)‖ ≤ (n+1:ℝ)*‖a-b‖*r^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have heq : a^(n+1+1)-b^(n+1+1) = a*(a^(n+1)-b^(n+1))+(a-b)*b^(n+1) := by
      rw [pow_succ,pow_succ]
      ring
    rw [heq]
    calc
      _ ≤ ‖a*(a^(n+1)-b^(n+1))‖+‖(a-b)*b^(n+1)‖ := norm_add_le _ _
      _ = ‖a‖*‖a^(n+1)-b^(n+1)‖+‖a-b‖*‖b‖^(n+1) := by rw [norm_mul,norm_mul,norm_pow]
      _ ≤ r*((n+1:ℝ)*‖a-b‖*r^n)+‖a-b‖*r^(n+1) :=
        add_le_add (mul_le_mul ha ih (norm_nonneg _) hr)
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb _) (norm_nonneg _))
      _ = _ := by push_cast; rw [pow_succ]; ring

variable {ι : Type*} [Fintype ι]

theorem finiteVariance_nonneg (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    0 ≤ finiteVariance p f :=
  Finset.sum_nonneg (fun i hi => mul_nonneg (hp i) (sq_nonneg _))

/-- A non-asymptotic characteristic-function comparison to a Gaussian on the
computable frequency range `V t²≤1`; no CDF conclusion is hidden in a premise. -/
theorem finiteChar_gaussian_bound (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (t : ℝ) (ht : finiteVariance p f*t^2 ≤ 1) :
    ‖finiteChar p (centeredObservable p f) t-gaussianChar (finiteVariance p f) t‖ ≤
      4*|t|^3*thirdAbsoluteMoment p f+(finiteVariance p f)^2*t^4/4 := by
  let v := finiteVariance p f
  have hv := finiteVariance_nonneg p f hp
  have hx : 0 ≤ v*t^2/2 := by positivity
  have hx' : v*t^2/2 ≤ 1 := by dsimp [v]; nlinarith
  have hreal := exp_neg_quadratic_remainder (v*t^2/2) hx hx'
  have hG : ‖gaussianChar v t-(1-(v:ℂ)*(t:ℂ)^2/2)‖ ≤ v^2*t^4/4 := by
    have heq : gaussianChar v t-(1-(v:ℂ)*(t:ℂ)^2/2) =
        ((Real.exp (-(v*t^2/2)):ℝ):ℂ)-((1-v*t^2/2:ℝ):ℂ) := by
      unfold gaussianChar
      push_cast
      congr 2 <;> ring
    rw [heq]
    convert hreal using 1 <;> ring
  calc
    _ ≤ ‖finiteChar p (centeredObservable p f) t-(1-(v:ℂ)*(t:ℂ)^2/2)‖+
        ‖(1-(v:ℂ)*(t:ℂ)^2/2)-gaussianChar v t‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add (finiteChar_centered_cubic_bound p f hp hs t)
      (by rw [norm_sub_rev]; exact hG)

/-- Small-frequency Gaussian damping, derived from the actual third moment. -/
theorem finiteChar_gaussian_damping (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (t : ℝ) (ht : finiteVariance p f*t^2 ≤ 1)
    (hthird : 16*thirdAbsoluteMoment p f*|t| ≤ finiteVariance p f) :
    ‖finiteChar p (centeredObservable p f) t‖ ≤ Real.exp (-(finiteVariance p f)*t^2/4) := by
  let v := finiteVariance p f
  let T := thirdAbsoluteMoment p f
  have hv := finiteVariance_nonneg p f hp
  have hnear := finiteChar_centered_cubic_bound p f hp hs t
  have hnorm : ‖(1-(v:ℂ)*(t:ℂ)^2/2:ℂ)‖ = 1-v*t^2/2 := by
    have heq : (1-(v:ℂ)*(t:ℂ)^2/2:ℂ) = ((1-v*t^2/2:ℝ):ℂ) := by push_cast; rfl
    rw [heq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
    dsimp [v]
    nlinarith
  have htriangle := norm_le_norm_sub_add
    (finiteChar p (centeredObservable p f) t) (1-(v:ℂ)*(t:ℂ)^2/2)
  rw [hnorm] at htriangle
  have hbudget := mul_le_mul_of_nonneg_right hthird (sq_nonneg t)
  have hcube : |t| * t^2 = |t|^3 := by rw [← sq_abs]; ring
  have hsmall : ‖finiteChar p (centeredObservable p f) t‖ ≤ 1-v*t^2/4 := by
    change 16*T*|t| * t^2 ≤ v*t^2 at hbudget
    rw [mul_assoc (16*T) |t| (t^2),hcube] at hbudget
    change ‖finiteChar p (centeredObservable p f) t-(1-(v:ℂ)*(t:ℂ)^2/2)‖ ≤
      4*|t|^3*T at hnear
    nlinarith
  have hexp := Real.add_one_le_exp (-v*t^2/4)
  exact hsmall.trans (by linarith)

/-- Explicit finite-block Fourier estimate for the actual iid sum. This is
the analytic input of Esseen smoothing, with the latter still a separate task. -/
theorem finiteChar_power_gaussian_bound (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (t : ℝ) (ht : finiteVariance p f*t^2 ≤ 1) (n : ℕ) :
    ‖(finiteChar p (centeredObservable p f) t)^(n+1)-
      gaussianChar (finiteVariance p f) t^(n+1)‖ ≤
      (n+1:ℝ)*(4*|t|^3*thirdAbsoluteMoment p f+(finiteVariance p f)^2*t^4/4) := by
  have hG : ‖gaussianChar (finiteVariance p f) t‖ ≤ 1 := by
    rw [gaussianChar_norm,Real.exp_le_one_iff]
    nlinarith [finiteVariance_nonneg p f hp,sq_nonneg t,
      mul_nonneg (finiteVariance_nonneg p f hp) (sq_nonneg t)]
  have h := norm_pow_sub_pow_le _ _ 1 zero_le_one
    (finiteChar_norm_le_one p (centeredObservable p f) hp hs t) hG n
  simp only [one_pow,mul_one] at h
  exact h.trans (mul_le_mul_of_nonneg_left (finiteChar_gaussian_bound p f hp hs t ht) (by positivity))

theorem finiteChar_power_gaussian_damped (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (t : ℝ) (ht : finiteVariance p f*t^2 ≤ 1)
    (hthird : 16*thirdAbsoluteMoment p f*|t| ≤ finiteVariance p f) (n : ℕ) :
    ‖(finiteChar p (centeredObservable p f) t)^(n+1)-
      gaussianChar (finiteVariance p f) t^(n+1)‖ ≤
      (n+1:ℝ)*(4*|t|^3*thirdAbsoluteMoment p f+(finiteVariance p f)^2*t^4/4)*
        Real.exp (-(n:ℝ)*(finiteVariance p f)*t^2/4) := by
  let r := Real.exp (-(finiteVariance p f)*t^2/4)
  have hG : ‖gaussianChar (finiteVariance p f) t‖ ≤ r := by
    rw [gaussianChar_norm]
    apply Real.exp_le_exp.mpr
    have h := mul_nonneg (finiteVariance_nonneg p f hp) (sq_nonneg t)
    nlinarith
  have h := norm_pow_sub_pow_le _ _ r (Real.exp_pos _).le
    (finiteChar_gaussian_damping p f hp hs t ht hthird) hG n
  have hrpow : r^n = Real.exp (-(n:ℝ)*(finiteVariance p f)*t^2/4) := by
    dsimp [r]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hrpow] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_left (finiteChar_gaussian_bound p f hp hs t ht) (by positivity)

end
end ExtractionDeviation
