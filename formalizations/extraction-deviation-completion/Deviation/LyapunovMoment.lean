import Deviation.FourierIID
import Mathlib.Analysis.MeanInequalitiesPow

open scoped BigOperators Topology NNReal ENNReal
open ExtractionSpectrum

namespace ExtractionDeviation
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Jensen's inequality gives the universal lower bound on the standardized
third absolute moment required for the Berry--Esseen frequency scale. -/
theorem variance_three_halves_le_thirdAbsoluteMoment (p f : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    (finiteVariance p f)^(3/2:ℝ) ≤ thirdAbsoluteMoment p f := by
  have h := Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ p
    (fun i => (centeredObservable p f i)^2) (fun i hi => hp i) hs
    (fun i hi => sq_nonneg _) (by norm_num : (1:ℝ) ≤ 3/2)
  have hpow (x : ℝ) : (x^2)^(3/2:ℝ) = |x|^3 := by
    rw [← sq_abs]
    rw [← Real.rpow_natCast_mul (abs_nonneg x) 2 (3/2)]
    norm_num
  simpa only [finiteVariance,centeredObservable,thirdAbsoluteMoment,hpow] using h

theorem variance_mul_sqrt_le_thirdAbsoluteMoment (p f : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    finiteVariance p f*Real.sqrt (finiteVariance p f) ≤ thirdAbsoluteMoment p f := by
  have hv := finiteVariance_nonneg p f hp
  have hpow : (finiteVariance p f)^(3/2:ℝ) = finiteVariance p f*Real.sqrt (finiteVariance p f) := by
    by_cases hz : finiteVariance p f = 0
    · simp only [hz,Real.zero_rpow (by norm_num : (3/2:ℝ) ≠ 0),zero_mul]
    · have hvpos := lt_of_le_of_ne hv (Ne.symm hz)
      rw [show (3/2:ℝ) = 1+1/2 by ring,Real.rpow_add hvpos,Real.rpow_one,← Real.sqrt_eq_rpow]
  rw [← hpow]
  exact variance_three_halves_le_thirdAbsoluteMoment p f hp hs

theorem thirdAbsoluteMoment_pos (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (hv : 0 < finiteVariance p f) :
    0 < thirdAbsoluteMoment p f :=
  (mul_pos hv (Real.sqrt_pos.mpr hv)).trans_le (variance_mul_sqrt_le_thirdAbsoluteMoment p f hp hs)

theorem lyapunovRatio_pos (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (hv : 0 < finiteVariance p f) (k : ℕ) (hk : 0 < k) :
    0 < lyapunovRatio p f k := by
  unfold lyapunovRatio
  exact div_pos (mul_pos (Nat.cast_pos.mpr hk) (thirdAbsoluteMoment_pos p f hp hs hv))
    (pow_pos (Real.sqrt_pos.mpr (mul_pos (Nat.cast_pos.mpr hk) hv)) _)

theorem lyapunovRatio_ge_inv_sqrt (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (hv : 0 < finiteVariance p f) (k : ℕ) (hk : 0 < k) :
    (Real.sqrt (k:ℝ))⁻¹ ≤ lyapunovRatio p f k := by
  rw [lyapunovRatio_eq p f hv k hk]
  have hvs : 0 < finiteVariance p f*Real.sqrt (finiteVariance p f) :=
    mul_pos hv (Real.sqrt_pos.mpr hv)
  have hks : 0 < Real.sqrt (k:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hk)
  have h := variance_mul_sqrt_le_thirdAbsoluteMoment p f hp hs
  apply (le_div_iff₀ (mul_pos hvs hks)).mpr
  have heq : (Real.sqrt (k:ℝ))⁻¹*(finiteVariance p f*Real.sqrt (finiteVariance p f)*Real.sqrt k) =
      finiteVariance p f*Real.sqrt (finiteVariance p f) := by field_simp
  rw [heq]
  exact h

theorem lyapunovRatio_eq_variance_scale (p f : ι → ℝ) (hv : 0 < finiteVariance p f)
    (k : ℕ) (hk : 0 < k) :
    lyapunovRatio p f k = thirdAbsoluteMoment p f /
      (finiteVariance p f*Real.sqrt ((k:ℝ)*finiteVariance p f)) := by
  rw [lyapunovRatio_eq p f hv k hk,Real.sqrt_mul (Nat.cast_nonneg k)]
  congr 1
  ring

end
end ExtractionDeviation
