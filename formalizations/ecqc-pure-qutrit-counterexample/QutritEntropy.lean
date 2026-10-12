import QutritBorn
import QuantumInfo

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix
noncomputable section

namespace ECQC.Qutrit

theorem log_half : Real.log (1/2 : ℝ) = -Real.log 2 := by
  rw [one_div, Real.log_inv]

theorem log_quarter : Real.log (1/4 : ℝ) = -2 * Real.log 2 := by
  rw [show (1/4 : ℝ) = (1/2 : ℝ)^2 by norm_num, Real.log_pow, log_half]
  ring

/-- The actual marginal operator is itself a density matrix. -/
theorem reduced_density : IsDensity reduced := by
  refine ⟨reduced_hermitian.posSemidef_iff_eigenvalues_nonneg.mpr ?_, reduced_trace⟩
  intro i
  rcases eigenvalue_zero_or_scale reduced_hermitian (1/2) reduced_scaled_projection i with h | h
  · simp [h]
  · rw [h]; norm_num

/-- The global pure state's entropy is proved through Mathlib's actual eigenvalues. -/
theorem rho_spectral_entropy : vonNeumannEntropy rho rho_hermitian = 0 := by
  simpa using entropy_scaled_projection rho_hermitian (1 : ℝ)
    (by simpa using rho_idempotent) rho_trace

/-- Each reduced density operator has entropy log 2. -/
theorem reduced_spectral_entropy : vonNeumannEntropy reduced reduced_hermitian = Real.log 2 := by
  simpa [log_half] using entropy_scaled_projection reduced_hermitian (1/2 : ℝ)
    reduced_scaled_projection reduced_trace

theorem rho_quantum_mutual_information : quantumMutualInformation rho = 2 * Real.log 2 := by
  rw [quantumMutualInformation, partialTraceRight_rho, partialTraceLeft_rho,
    matrixEntropy_eq reduced reduced_hermitian, matrixEntropy_eq rho rho_hermitian,
    rho_spectral_entropy, reduced_spectral_entropy]
  ring

theorem probabilityTable_row_entropy :
    shannon (fun i => ∑ j, probabilityTable i j) = (3/2 : ℝ) * Real.log 2 := by
  norm_num [shannon, probabilityTable, Fin.sum_univ_succ, log_half, log_quarter]
  ring

theorem probabilityTable_column_entropy :
    shannon (fun j => ∑ i, probabilityTable i j) = (3/2 : ℝ) * Real.log 2 := by
  norm_num [shannon, probabilityTable, Fin.sum_univ_succ, log_half, log_quarter]
  ring

theorem probabilityTable_joint_entropy :
    shannon (fun x : QQ => probabilityTable x.1 x.2) = 2 * Real.log 2 := by
  norm_num [shannon, probabilityTable, Fintype.sum_prod_type, Fin.sum_univ_succ,
    log_half, log_quarter]
  ring

theorem probabilityTable_mutual_information :
    mutualInformation probabilityTable = Real.log 2 := by
  rw [mutualInformation, probabilityTable_row_entropy, probabilityTable_column_entropy,
    probabilityTable_joint_entropy]
  ring

/-- Every actual local MUB measurement has exactly one bit of mutual information. -/
theorem measured_mutual_information (a : Fin 4) :
    mutualInformation (bornTable rho (basis a) (basis a)) = Real.log 2 := by
  rw [bornTable_eq, probabilityTable_mutual_information]

end ECQC.Qutrit
