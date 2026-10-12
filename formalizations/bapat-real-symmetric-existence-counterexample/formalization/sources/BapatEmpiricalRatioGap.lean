import BapatRatioLowerApprox
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology

namespace BapatRealExistence
noncomputable section

theorem empiricalAverage_mono {K : Type*} (u : ℕ → K) (n : ℕ) (f g : K → ℝ)
    (h : ∀ x, f x≤g x) : empiricalAverage u n f≤empiricalAverage u n g := by
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg n))
  exact Finset.sum_le_sum (fun i hi => h (u i))

/-- The needed lower bound, using only continuous lower tests and their actual
Gaussian integral. No unbounded empirical-moment convergence is assumed. -/
theorem triangular_real_ratio_lower_bound
    (w : ℕ → ℕ → RealUnitSphere4)
    (hw : ∀ f : C(RealUnitSphere4,ℝ), Tendsto (fun n => empiricalAverage (w n) n f) atTop
      (𝓝 (∫ x, f x ∂normalizedSphere (volume : Measure RealSpace4))))
    (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 (1/2:ℝ)))
    (c : ℝ) (hc : c<Real.pi/2) :
    ∀ᶠ n in atTop, c < empiricalAverage (w n) n
      (fun x => empiricalAverage (w n) n (fun y => |realRowRatio (t n) x-realRowRatio (t n) y|)) := by
  let σ := normalizedSphere (volume : Measure RealSpace4)
  obtain ⟨k,hk⟩ := ((tendsto_order.mp ratioLowerApprox_integral_tendsto).1 c hc).exists
  have hφ : Continuous (fun p : (RealUnitSphere4 × RealUnitSphere4) × ℝ =>
      ratioLowerApprox k p.2 p.1.1 p.1.2) := by
    unfold ratioLowerApprox
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro p
      exact ne_of_gt ((Real.exp_pos _).trans_le (le_max_right _ _))
  have hi : Integrable (fun p : RealUnitSphere4 × RealUnitSphere4 => ratioLowerApprox k (1/2) p.1 p.2)
      (σ.prod σ) :=
    (hφ.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_prod _ hi] at hk
  have h := triangular_empirical_pairs_moving σ w hw
    (fun p : (RealUnitSphere4 × RealUnitSphere4) × ℝ => ratioLowerApprox k p.2 p.1.1 p.1.2)
    hφ t (1/2) ht
  filter_upwards [(tendsto_order.mp h).1 c hk] with n hn
  apply hn.trans_le
  apply empiricalAverage_mono
  intro x
  apply empiricalAverage_mono
  intro y
  exact ratioLowerApprox_le k (t n) x y

theorem triangular_real_ratio_three_halves
    (w : ℕ → ℕ → RealUnitSphere4)
    (hw : ∀ f : C(RealUnitSphere4,ℝ), Tendsto (fun n => empiricalAverage (w n) n f) atTop
      (𝓝 (∫ x, f x ∂normalizedSphere (volume : Measure RealSpace4))))
    (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 (1/2:ℝ))) :
    ∀ᶠ n in atTop, (3/2:ℝ) < empiricalAverage (w n) n
      (fun x => empiricalAverage (w n) n (fun y => |realRowRatio (t n) x-realRowRatio (t n) y|)) :=
  triangular_real_ratio_lower_bound w hw t ht (3/2) (by linarith [Real.pi_gt_three])

end
end BapatRealExistence
