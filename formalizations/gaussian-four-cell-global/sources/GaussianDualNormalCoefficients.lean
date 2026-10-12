import GaussianSmoothWinningCoefficients
import GaussianSmoothMomentLimit
import GaussianNormalCoordinates

/-! Dual normal directions recover the nonnegative smooth gradient
coefficients. Their actual Gaussian integrals converge to the already proved
normal decomposition of the genuine cell moment. -/
open MeasureTheory ProbabilityTheory Module Set Filter
open scoped Topology ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

lemma sum_erase_zero_eq_sum_succ {n : ℕ} (f : Fin (n+1) → ℝ) :
    (∑ i ∈ Finset.univ.erase 0,f i) = ∑ j : Fin n,f j.succ := by
  have h := Finset.sum_erase_add Finset.univ f (Finset.mem_univ (0 : Fin (n+1)))
  rw [Fin.sum_univ_succ] at h
  linarith

lemma smoothWinningCoefficient_eq_directional
    (v : Fin (d+2) → Space (d+1)) (b : Fin (d+2) → ℝ)
    (B : Basis (Fin (d+1)) ℝ (Space (d+1))) (hB : ∀ l,B l=v 0-v l.succ)
    (j : Fin (d+1)) (u : Space (d+1))
    (hu : ∀ l,⟪u,B l⟫=if l=j then 1 else 0) (N : ℕ) (x : Space (d+1)) :
    fderiv ℝ (smoothWinningApprox v b 0 N) x u =
      smoothWinningCoefficient v b 0 N j.succ x := by
  rw [smoothWinningApprox_fderiv]
  simp only [sum_apply,smul_apply,innerSL_apply_apply,smul_eq_mul]
  rw [sum_erase_zero_eq_sum_succ]
  have he (l : Fin (d+1)) : ⟪v 0-v l.succ,u⟫=if l=j then 1 else 0 := by
    rw [← hB l,real_inner_comm u,hu l]
  simp_rw [he]
  simp

lemma smoothWinningCoefficient_integrable
    (v : Fin (d+2) → Space (d+1)) (b : Fin (d+2) → ℝ)
    (B : Basis (Fin (d+1)) ℝ (Space (d+1))) (hB : ∀ l,B l=v 0-v l.succ)
    (j : Fin (d+1)) (N : ℕ) :
    Integrable (smoothWinningCoefficient v b 0 N j.succ) (gaussian (d+1)) := by
  obtain ⟨u,hu⟩ := basis_inner_interpolate B (fun l => if l=j then 1 else 0)
  obtain ⟨C,_,hC⟩ := smoothWinningApprox_gradient_bound v b 0 N
  have hi := bounded_smooth_directional_integrable _ (smoothWinningApprox_contDiff v b 0 N) C hC u
  simpa only [smoothWinningCoefficient_eq_directional v b B hB j u hu] using hi

theorem smoothWinningCoefficient_integral_tendsto
    (v : Fin (d+2) → Space (d+1)) (b : Fin (d+2) → ℝ)
    (B : Basis (Fin (d+1)) ℝ (Space (d+1))) (hB : ∀ l,B l=v 0-v l.succ)
    (w : Fin (d+1) → ℝ)
    (hf : rawWinningMoment v b 0=∑ l,w l • (v 0-v l.succ)) (j : Fin (d+1)) :
    Tendsto (fun N => ∫ x,smoothWinningCoefficient v b 0 N j.succ x ∂gaussian (d+1))
      atTop (𝓝 (w j)) := by
  obtain ⟨u,hu⟩ := basis_inner_interpolate B (fun l => if l=j then 1 else 0)
  have hm : ⟪u,rawWinningMoment v b 0⟫=w j := by
    rw [hf,inner_sum]
    simp_rw [real_inner_smul_right,← hB,hu]
    simp
  have ht := smoothWinningApprox_directional_integral_tendsto v b 0 u
  simpa only [smoothWinningCoefficient_eq_directional v b B hB j u hu,hm] using ht

end GaussianMeasureBridge
