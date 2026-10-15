import APPTReview.EntropySpectralPenalty
import APPTReview.EntropyGlobalControls

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- The tail radius reaches the excluded singular value at m=9. -/
theorem uniform_entropy_radius_boundary :
    entropyBulkRadius 7=1 ∧ entropyUniformMeanRadius 7=(3/8:ℝ) := by
  norm_num [entropyBulkRadius,entropyUniformMeanRadius]

/-- The finite m=10 threshold has positive denominators without decimal tests. -/
theorem uniform_entropy_first_admissible :
    entropyBulkRadius 8<1 ∧ entropyUniformMeanRadius 8<1 :=
  entropy_uniform_radii_admissible (by decide)

/-- Constants in the unconditional head split leave a strict rational margin. -/
theorem entropy_unconditional_margin_control :
    (8:ℝ)<300*(37/1344) ∧ (37/1344:ℝ)<9/325 := by norm_num

/-- The moderate-head comparison is an exact polynomial identity. -/
theorem entropy_moderate_head_factorization (x : ℝ) :
    325*x^3-27*x-54=(5*x-3)*(65*x^2+39*x+18) := by ring

/-- Dropping trace one from the mean-error lemma is false, even for a
constant nonnegative ordered vector; here its mass is two, not one. -/
theorem uniform_mean_trace_condition_necessary :
    |1-(2:ℝ)*1| > (∑ _i : Fin 1,((1:ℝ)-1))+(2:ℝ)*(1-1) := by norm_num

/-- Zero eigenvalues are in the true logarithmic domain. -/
theorem entropy_kernel_singular_endpoint : entropyKernel (-1)=1 := by
  norm_num [entropyKernel]

/-- An actual-matrix regression at the first allowed smaller dimension. -/
theorem entropy_physical_ten_by_ten_control
    {A : Matrix (Fin 10 × Fin 10) (Fin 10 × Fin 10) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (hP : APPT.Quantum.AbsolutelyPPT A) :
    ∀ i, 100*vonNeumannDeficit hρ+|100*hρ.1.isHermitian.eigenvalues₀ i-1|^3/300≤
      4*entropyUniformFactor 8 := by
  have hh:=density_appt_finite_entropy_contrast (m:=10) (n:=10) (by decide) (by decide) hρ hP
  norm_num at hh
  exact hh

end APPTReview
