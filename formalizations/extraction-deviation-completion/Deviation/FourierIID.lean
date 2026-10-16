import Deviation.FourierPower

open scoped BigOperators NNReal ENNReal Topology
open ExtractionSpectrum MeasureTheory ProbabilityTheory

namespace ExtractionDeviation
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact finite-word tensor factorization of the characteristic function. -/
theorem finiteChar_iid (p f : ι → ℝ) (k : ℕ) (t : ℝ) :
    finiteChar (iidLaw p k) (fun w => ∑ j, f (w j)) t = (finiteChar p f t)^k := by
  unfold finiteChar
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro w hw
  have hexp : Complex.exp (((t*(∑ j, f (w j)):ℝ):ℂ)*Complex.I) =
      ∏ j : Fin k, Complex.exp (((t*f (w j):ℝ):ℂ)*Complex.I) := by
    rw [← Complex.exp_sum]
    congr 1
    simp only [Finset.mul_sum,Complex.ofReal_sum,Complex.ofReal_mul,Finset.sum_mul]
  rw [hexp,iidLaw,Complex.ofReal_prod,← Finset.prod_mul_distrib]

theorem finiteChar_div_observable (p f : ι → ℝ) (a t : ℝ) :
    finiteChar p (fun i => f i/a) t = finiteChar p f (t/a) := by
  unfold finiteChar
  apply Finset.sum_congr rfl
  intro i hi
  congr 3
  ring

def standardizedWordSum (p f : ι → ℝ) (k : ℕ) (w : Fin k → ι) : ℝ :=
  (∑ j, centeredObservable p f (w j))/Real.sqrt ((k:ℝ)*finiteVariance p f)

theorem standardizedWordSum_eq (p f : ι → ℝ) (k : ℕ) (w : Fin k → ι) :
    standardizedWordSum p f k w =
      ((∑ j, f (w j))-(k:ℝ)*finiteMean p f)/Real.sqrt ((k:ℝ)*finiteVariance p f) := by
  simp only [standardizedWordSum,centeredObservable,Finset.sum_sub_distrib,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem finiteChar_standardized_iid (p f : ι → ℝ) (k : ℕ) (t : ℝ) :
    finiteChar (iidLaw p k) (standardizedWordSum p f k) t =
      (finiteChar p (centeredObservable p f) (t/Real.sqrt ((k:ℝ)*finiteVariance p f)))^k := by
  unfold standardizedWordSum
  rw [finiteChar_div_observable,finiteChar_iid]

def lyapunovRatio (p f : ι → ℝ) (k : ℕ) : ℝ :=
  (k:ℝ)*thirdAbsoluteMoment p f/(Real.sqrt ((k:ℝ)*finiteVariance p f))^3

theorem lyapunovRatio_eq (p f : ι → ℝ) (hv : 0 < finiteVariance p f)
    (k : ℕ) (hk : 0 < k) :
    lyapunovRatio p f k = thirdAbsoluteMoment p f /
      (finiteVariance p f*Real.sqrt (finiteVariance p f)*Real.sqrt k) := by
  have hkR : (k:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have hv0 : finiteVariance p f ≠ 0 := ne_of_gt hv
  have hks : Real.sqrt (k:ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hk)
  have hvs : Real.sqrt (finiteVariance p f) ≠ 0 := Real.sqrt_ne_zero'.mpr hv
  have hk3 : (Real.sqrt (k:ℝ))^3 = (k:ℝ)*Real.sqrt k := by
    rw [pow_succ,Real.sq_sqrt (Nat.cast_nonneg k)]
  have hv3 : (Real.sqrt (finiteVariance p f))^3 = finiteVariance p f*Real.sqrt (finiteVariance p f) := by
    rw [pow_succ,Real.sq_sqrt hv.le]
  rw [lyapunovRatio,Real.sqrt_mul (Nat.cast_nonneg k),mul_pow,hk3,hv3]
  field_simp

theorem gaussianChar_eq_charFun (v : ℝ≥0) (t : ℝ) :
    gaussianChar v t = charFun (gaussianReal 0 v) t := by
  rw [charFun_gaussianReal]
  simp only [Complex.ofReal_zero,mul_zero,zero_mul,zero_sub,gaussianChar]
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem scaled_variance_identity (v : ℝ) (hv : 0 < v) (k : ℕ) (hk : 0 < k) (t : ℝ) :
    v*(t/Real.sqrt ((k:ℝ)*v))^2 = t^2/k := by
  rw [div_pow,Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg k) hv.le)]
  have hkR : (k:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  field_simp

theorem gaussianChar_standardized_power (v : ℝ) (hv : 0 < v) (k : ℕ) (hk : 0 < k) (t : ℝ) :
    gaussianChar v (t/Real.sqrt ((k:ℝ)*v))^k = gaussianChar 1 t := by
  have hkR : (k:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  rw [gaussianChar,← Complex.ofReal_pow,← Real.exp_nat_mul]
  have hid := scaled_variance_identity v hv k hk t
  have hex : (k:ℝ)*(-v*(t/Real.sqrt ((k:ℝ)*v))^2/2) = -t^2/2 := by
    calc
      _ = -(k:ℝ)*(v*(t/Real.sqrt ((k:ℝ)*v))^2)/2 := by ring
      _ = -(k:ℝ)*(t^2/k)/2 := by rw [hid]
      _ = _ := by field_simp
  rw [hex]
  simp only [gaussianChar,neg_mul,one_mul]

/-- A fully quantitative normalized finite iid Fourier bound. In particular it
can be used for a varying alphabet, variance, and input law at every block. -/
theorem standardized_iid_fourier_bound (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (hv : 0 < finiteVariance p f)
    (k : ℕ) (hk : 0 < k) (t : ℝ) (ht : t^2 ≤ k) :
    ‖finiteChar (iidLaw p k) (standardizedWordSum p f k) t-gaussianChar 1 t‖ ≤
      4*|t|^3*lyapunovRatio p f k+t^4/(4*k) := by
  let v := finiteVariance p f
  let s := Real.sqrt ((k:ℝ)*v)
  have hkR : (0:ℝ) < k := Nat.cast_pos.mpr hk
  have hsR : 0 < s := Real.sqrt_pos.mpr (mul_pos hkR hv)
  have hs2 : s^2 = (k:ℝ)*v := Real.sq_sqrt (mul_pos hkR hv).le
  have hfreq : v*(t/s)^2 ≤ 1 := by
    rw [scaled_variance_identity v hv k hk t]
    exact (div_le_iff₀ hkR).mpr (by simpa only [one_mul] using ht)
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  have h := finiteChar_power_gaussian_bound p f hp hs (t/s) hfreq n
  rw [← finiteChar_standardized_iid p f (n+1) t,
    gaussianChar_standardized_power v hv (n+1) (Nat.succ_pos _) t] at h
  apply h.trans_eq
  have hsa : |s| = s := abs_of_pos hsR
  have hs4 : s^4 = ((n+1:ℝ)*v)^2 := by
    rw [show (4:ℕ) = 2*2 by norm_num,pow_mul,hs2]
    push_cast
    rfl
  unfold lyapunovRatio
  change (n+1:ℝ)*(4*|t/s|^3*thirdAbsoluteMoment p f+v^2*(t/s)^4/4) =
    4*|t|^3*((n.succ:ℝ)*thirdAbsoluteMoment p f/s^3)+t^4/(4*(n.succ:ℝ))
  simp only [Nat.cast_succ]
  rw [abs_div,hsa,div_pow,div_pow,hs4]
  have hv0 : v ≠ 0 := ne_of_gt hv
  have hn0 : (n+1:ℝ) ≠ 0 := by positivity
  field_simp

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

def standardizedIIDMeasure (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (k : ℕ) : Measure ℝ :=
  (finiteMeasure (iidLaw p k) (iidLaw_nonneg p hp k) (iidLaw_sum p hs k)).map
    (standardizedWordSum p f k)

instance standardizedIIDMeasure_isProbabilityMeasure (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (k : ℕ) : IsProbabilityMeasure (standardizedIIDMeasure p f hp hs k) := by
  unfold standardizedIIDMeasure
  constructor
  rw [Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
  simp

theorem charFun_standardizedIIDMeasure (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (k : ℕ) (t : ℝ) :
    charFun (standardizedIIDMeasure p f hp hs k) t =
      finiteChar (iidLaw p k) (standardizedWordSum p f k) t :=
  (finiteChar_eq_charFun (iidLaw p k) (standardizedWordSum p f k)
    (iidLaw_nonneg p hp k) (iidLaw_sum p hs k) t).symm

theorem charFun_standardizedIIDMeasure_bound (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (hv : 0 < finiteVariance p f)
    (k : ℕ) (hk : 0 < k) (t : ℝ) (ht : t^2 ≤ k) :
    ‖charFun (standardizedIIDMeasure p f hp hs k) t-gaussianChar 1 t‖ ≤
      4*|t|^3*lyapunovRatio p f k+t^4/(4*k) := by
  rw [charFun_standardizedIIDMeasure]
  exact standardized_iid_fourier_bound p f hp hs hv k hk t ht

end
end ExtractionDeviation
