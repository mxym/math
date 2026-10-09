import CofactorPositiveDefiniteLower
import CofactorSpectralExtrema

/-! Theorem 1 at the fixed mathematical source: all six largest-eigenvalue limits. -/
set_option autoImplicit false
open scoped Topology
open Filter
namespace CofactorSpectral
noncomputable section

theorem complexSpectralExtremum_log_tendsto :
    Tendsto (fun N : ℕ => complexSpectralExtremum N/Real.log (N : ℝ)) atTop (𝓝 1) := by
  simp_rw [complexSpectralExtremum_eq]
  exact complexExtremum_log_tendsto

theorem realSpectralExtremum_log_tendsto :
    Tendsto (fun N : ℕ => realSpectralExtremum N/Real.log (N : ℝ)) atTop (𝓝 (1/2)) := by
  simp_rw [realSpectralExtremum_eq]
  exact realExtremum_log_tendsto

theorem rankTwoComplexSpectralExtremum_log_tendsto :
    Tendsto (fun N : ℕ => rankTwoComplexSpectralExtremum N/Real.log (N : ℝ)) atTop (𝓝 1) := by
  simp_rw [rankTwoComplexSpectralExtremum_eq]
  exact rankTwoComplexExtremum_log_tendsto

theorem rankTwoRealSpectralExtremum_log_tendsto :
    Tendsto (fun N : ℕ => rankTwoRealSpectralExtremum N/Real.log (N : ℝ)) atTop (𝓝 (1/2)) := by
  simp_rw [rankTwoRealSpectralExtremum_eq]
  exact rankTwoRealExtremum_log_tendsto

theorem pdComplexSpectralExtremum_log_tendsto :
    Tendsto (fun N : ℕ => pdComplexSpectralExtremum N/Real.log (N : ℝ)) atTop (𝓝 1) := by
  simp_rw [pdComplexSpectralExtremum_eq]
  exact pdComplexExtremum_log_tendsto

theorem pdRealSpectralExtremum_log_tendsto :
    Tendsto (fun N : ℕ => pdRealSpectralExtremum N/Real.log (N : ℝ)) atTop (𝓝 (1/2)) := by
  simp_rw [pdRealSpectralExtremum_eq]
  exact pdRealExtremum_log_tendsto

theorem sharp_cofactor_spectral_asymptotics :
    Tendsto (fun N : ℕ => complexSpectralExtremum N/Real.log (N : ℝ)) atTop (𝓝 1) ∧
    Tendsto (fun N : ℕ => realSpectralExtremum N/Real.log (N : ℝ)) atTop (𝓝 (1/2)) ∧
    Tendsto (fun N : ℕ => rankTwoComplexSpectralExtremum N/Real.log (N : ℝ)) atTop (𝓝 1) ∧
    Tendsto (fun N : ℕ => rankTwoRealSpectralExtremum N/Real.log (N : ℝ)) atTop (𝓝 (1/2)) ∧
    Tendsto (fun N : ℕ => pdComplexSpectralExtremum N/Real.log (N : ℝ)) atTop (𝓝 1) ∧
    Tendsto (fun N : ℕ => pdRealSpectralExtremum N/Real.log (N : ℝ)) atTop (𝓝 (1/2)) :=
  ⟨complexSpectralExtremum_log_tendsto,realSpectralExtremum_log_tendsto,
    rankTwoComplexSpectralExtremum_log_tendsto,rankTwoRealSpectralExtremum_log_tendsto,
    pdComplexSpectralExtremum_log_tendsto,pdRealSpectralExtremum_log_tendsto⟩

end
end CofactorSpectral
