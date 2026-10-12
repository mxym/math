import GaussianDualNormalCoefficients

/-! The actual gradient-integral upper bound converges to the facet-flux
sum for each full simplicial cell. This proves the needed upper limit without
requiring convergence of the derivative norm integrals themselves. -/
open MeasureTheory ProbabilityTheory Module Set Filter
open scoped Topology ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

noncomputable def simplicialGradientUpper (v : Fin (d+2) → Space (d+1))
    (b : Fin (d+2) → ℝ) (N : ℕ) : ℝ :=
  ∑ j : Fin (d+1),(∫ x,smoothWinningCoefficient v b 0 N j.succ x ∂gaussian (d+1))*
    ‖v 0-v j.succ‖

theorem simplicial_gradient_integral_le_upper
    (v : Fin (d+2) → Space (d+1)) (b : Fin (d+2) → ℝ)
    (B : Basis (Fin (d+1)) ℝ (Space (d+1))) (hB : ∀ l,B l=v 0-v l.succ) (N : ℕ) :
    (∫ x,‖fderiv ℝ (smoothWinningApprox v b 0 N) x‖ ∂gaussian (d+1)) ≤
      simplicialGradientUpper v b N := by
  have hi (j : Fin (d+1)) : Integrable
      (fun x => smoothWinningCoefficient v b 0 N j.succ x*‖v 0-v j.succ‖) (gaussian (d+1)) :=
    (smoothWinningCoefficient_integrable v b B hB j N).mul_const _
  have hsum : Integrable (fun x => ∑ j : Fin (d+1),
      smoothWinningCoefficient v b 0 N j.succ x*‖v 0-v j.succ‖) (gaussian (d+1)) :=
    integrable_finsetSum Finset.univ (fun j _ => hi j)
  have hle : (∫ x,‖fderiv ℝ (smoothWinningApprox v b 0 N) x‖ ∂gaussian (d+1)) ≤
      ∫ x,(∑ j : Fin (d+1),smoothWinningCoefficient v b 0 N j.succ x*‖v 0-v j.succ‖)
        ∂gaussian (d+1) := by
    apply integral_mono_ae (smoothWinningApprox_gradient_integrable v b 0 N) hsum
    exact ae_of_all _ fun x => by
      simpa only [sum_erase_zero_eq_sum_succ] using
        smoothWinningApprox_coefficient_gradient_bound v b 0 N x
  apply hle.trans_eq
  rw [integral_finsetSum Finset.univ (fun j _ => hi j)]
  simp only [simplicialGradientUpper,integral_mul_const]

theorem simplicialGradientUpper_tendsto
    (v : Fin (d+2) → Space (d+1)) (b : Fin (d+2) → ℝ)
    (B : Basis (Fin (d+1)) ℝ (Space (d+1))) (hB : ∀ l,B l=v 0-v l.succ)
    (w : Fin (d+1) → ℝ)
    (hf : rawWinningMoment v b 0=∑ l,w l • (v 0-v l.succ)) :
    Tendsto (simplicialGradientUpper v b) atTop (𝓝 (∑ l,w l*‖v 0-v l.succ‖)) := by
  exact tendsto_finsetSum Finset.univ (fun j _ =>
    (smoothWinningCoefficient_integral_tendsto v b B hB w hf j).mul_const _)

end GaussianMeasureBridge
