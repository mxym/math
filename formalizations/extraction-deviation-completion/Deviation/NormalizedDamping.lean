import Deviation.LyapunovMoment

open scoped BigOperators NNReal ENNReal Topology
open ExtractionSpectrum

namespace ExtractionDeviation
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem standardized_fourier_prefactor (p f : ι → ℝ) (hv : 0 < finiteVariance p f)
    (k : ℕ) (hk : 0 < k) (t : ℝ) :
    (k:ℝ)*(4*|t/Real.sqrt ((k:ℝ)*finiteVariance p f)|^3*thirdAbsoluteMoment p f+
      (finiteVariance p f)^2*(t/Real.sqrt ((k:ℝ)*finiteVariance p f))^4/4) =
      4*|t|^3*lyapunovRatio p f k+t^4/(4*k) := by
  let v := finiteVariance p f
  let s := Real.sqrt ((k:ℝ)*v)
  have hkR : (0:ℝ) < k := Nat.cast_pos.mpr hk
  have hsR : 0 < s := Real.sqrt_pos.mpr (mul_pos hkR hv)
  have hs2 : s^2 = (k:ℝ)*v := Real.sq_sqrt (mul_pos hkR hv).le
  have hs4 : s^4 = ((k:ℝ)*v)^2 := by rw [show (4:ℕ)=2*2 by norm_num,pow_mul,hs2]
  unfold lyapunovRatio
  change (k:ℝ)*(4*|t/s|^3*thirdAbsoluteMoment p f+v^2*(t/s)^4/4) =
    4*|t|^3*((k:ℝ)*thirdAbsoluteMoment p f/s^3)+t^4/(4*k)
  rw [abs_div,abs_of_pos hsR,div_pow,div_pow,hs4]
  have hv0 : v ≠ 0 := ne_of_gt hv
  field_simp

/-- A computable Berry--Esseen frequency condition already implies the
quadratic small-frequency condition, by the internally proved moment bound. -/
theorem lyapunov_frequency_bounds (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (hv : 0 < finiteVariance p f) (k : ℕ) (hk : 0 < k)
    (t : ℝ) (ht : 16*lyapunovRatio p f k*|t| ≤ 1) :
    t^2 ≤ k ∧ 16*thirdAbsoluteMoment p f*|t/Real.sqrt ((k:ℝ)*finiteVariance p f)| ≤
      finiteVariance p f ∧ t^4/(4*k) ≤ lyapunovRatio p f k*|t|^3 := by
  let β := lyapunovRatio p f k
  let s := Real.sqrt (k:ℝ)
  have hsR : 0 < s := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hk)
  have hβ := lyapunovRatio_pos p f hp hs hv k hk
  have hβs : 1 ≤ β*s := by
    have h := mul_le_mul_of_nonneg_right (lyapunovRatio_ge_inv_sqrt p f hp hs hv k hk) hsR.le
    change s⁻¹*s ≤ β*s at h
    simpa only [inv_mul_cancel₀ (ne_of_gt hsR)] using h
  have h16 : 16*|t| ≤ s := by
    calc
      _ ≤ (β*s)*(16*|t|) := by nlinarith [mul_nonneg (sub_nonneg.mpr hβs) (by positivity : 0 ≤ 16*|t|)]
      _ = (16*β*|t|)*s := by ring
      _ ≤ 1*s := mul_le_mul_of_nonneg_right ht hsR.le
      _ = s := one_mul _
  have hs2 : s^2 = (k:ℝ) := Real.sq_sqrt (Nat.cast_nonneg k)
  have htk : t^2 ≤ k := by nlinarith [sq_abs t,abs_nonneg t]
  have hβk : s ≤ β*(k:ℝ) := by
    have h := mul_le_mul_of_nonneg_right hβs hsR.le
    simp only [one_mul] at h
    change s ≤ β*s*s at h
    nlinarith [congrArg (fun x : ℝ => β*x) hs2]
  have hrβ : |t| ≤ β*(k:ℝ) := by linarith [abs_nonneg t]
  have hquarter : t^4/(4*k) ≤ β*|t|^3 := by
    apply (div_le_iff₀ (show (0:ℝ) < 4*k by exact mul_pos (by norm_num) (Nat.cast_pos.mpr hk))).mpr
    have h := mul_le_mul_of_nonneg_right hrβ (pow_nonneg (abs_nonneg t) 3)
    have hr4 : |t|^4 = t^4 := by rw [show (4:ℕ)=2*2 by norm_num,pow_mul,pow_mul,sq_abs]
    have hnn : 0 ≤ β*(k:ℝ)*|t|^3 := by positivity
    nlinarith
  refine ⟨htk,?_,hquarter⟩
  let v := finiteVariance p f
  let a := Real.sqrt ((k:ℝ)*v)
  have ha : 0 < a := Real.sqrt_pos.mpr (mul_pos (Nat.cast_pos.mpr hk) hv)
  have hβeq : β = thirdAbsoluteMoment p f/(v*a) := lyapunovRatio_eq_variance_scale p f hv k hk
  have hv0 : v ≠ 0 := ne_of_gt hv
  have hcancel : β*(v*a) = thirdAbsoluteMoment p f := by rw [hβeq]; field_simp
  have hbudget : 16*thirdAbsoluteMoment p f*|t| ≤ v*a := by
    calc
      _ = (16*β*|t|)*(v*a) := by rw [← hcancel]; ring
      _ ≤ 1*(v*a) := mul_le_mul_of_nonneg_right ht (mul_pos hv ha).le
      _ = v*a := one_mul _
  rw [abs_div,abs_of_pos ha]
  change 16*thirdAbsoluteMoment p f*(|t|/a) ≤ v
  have heq : 16*thirdAbsoluteMoment p f*(|t|/a) =
      (16*thirdAbsoluteMoment p f*|t|)/a := by ring
  rw [heq,div_le_iff₀ ha]
  exact hbudget

/-- The normalized finite iid characteristic function has a Gaussian-decaying
cubic error throughout the explicit Berry--Esseen frequency window. -/
theorem standardized_iid_fourier_damped (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (hv : 0 < finiteVariance p f) (k : ℕ) (hk : 2 ≤ k)
    (t : ℝ) (ht : 16*lyapunovRatio p f k*|t| ≤ 1) :
    ‖finiteChar (iidLaw p k) (standardizedWordSum p f k) t-gaussianChar 1 t‖ ≤
      5*lyapunovRatio p f k*|t|^3*Real.exp (-t^2/8) := by
  have hkpos : 0 < k := lt_of_lt_of_le (by norm_num : 0 < 2) hk
  obtain ⟨htk,hthird,hquarter⟩ := lyapunov_frequency_bounds p f hp hs hv k hkpos t ht
  let v := finiteVariance p f
  let s := Real.sqrt ((k:ℝ)*v)
  have hfreq : v*(t/s)^2 ≤ 1 := by
    rw [scaled_variance_identity v hv k hkpos t]
    exact (div_le_iff₀ (Nat.cast_pos.mpr hkpos)).mpr (by simpa only [one_mul] using htk)
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
  have hn : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have h := finiteChar_power_gaussian_damped p f hp hs (t/s) hfreq hthird n
  rw [← finiteChar_standardized_iid p f (n+1) t,
    gaussianChar_standardized_power v hv (n+1) (Nat.succ_pos _) t] at h
  have hpref := standardized_fourier_prefactor p f hv (n+1) (Nat.succ_pos _) t
  have hpref' : (n+1:ℝ)*(4*|t/s|^3*thirdAbsoluteMoment p f+
      (finiteVariance p f)^2*(t/s)^4/4) =
      4*|t|^3*lyapunovRatio p f (n+1)+t^4/(4*(n+1:ℝ)) := by
    simpa only [s,v,Nat.cast_add,Nat.cast_one,Nat.cast_succ] using hpref
  rw [hpref'] at h
  have hexp : -(n:ℝ)*v*(t/s)^2/4 ≤ -t^2/8 := by
    let w := v*(t/s)^2
    have hw : 0 ≤ w := mul_nonneg hv.le (sq_nonneg _)
    have hid : (n+1:ℝ)*w = t^2 := by
      dsimp [w]
      rw [scaled_variance_identity v hv (n+1) (Nat.succ_pos _) t]
      push_cast
      field_simp
    have hnn := mul_nonneg (sub_nonneg.mpr hn) hw
    change -(n:ℝ)*v*(t/s)^2/4 ≤ -t^2/8
    dsimp [w] at hid hnn
    nlinarith
  have hβ := lyapunovRatio_pos p f hp hs hv (n+1) (Nat.succ_pos _)
  have hpre : 4*|t|^3*lyapunovRatio p f (n+1)+t^4/(4*(n+1:ℝ)) ≤
      5*lyapunovRatio p f (n+1)*|t|^3 := by
    push_cast at hquarter
    linarith
  exact h.trans (mul_le_mul hpre (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le
    (by positivity))

end
end ExtractionDeviation
