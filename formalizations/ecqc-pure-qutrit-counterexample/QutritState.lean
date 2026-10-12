import QuantumCore

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix

noncomputable section

namespace ECQC.Qutrit

abbrev Q := Fin 3
abbrev QQ := Q × Q

/-- Coefficients of (|01> + |02> - |10> - |20>)/2. -/
def coefficients : Matrix Q Q ℂ :=
  !![0, 1/2, 1/2; -1/2, 0, 0; -1/2, 0, 0]

def psi : QQ → ℂ := fun i => coefficients i.1 i.2

def rho : Matrix QQ QQ ℂ := pureState psi

def reduced : Matrix Q Q ℂ :=
  !![1/2, 0, 0; 0, 1/4, 1/4; 0, 1/4, 1/4]

theorem psi_normalized : dotProduct (star psi) psi = 1 := by
  norm_num [map_ofNat, dotProduct, psi, coefficients, Fintype.sum_prod_type, Fin.sum_univ_succ]

theorem rho_posSemidef : rho.PosSemidef := pureState_posSemidef psi

theorem rho_trace : rho.trace = 1 := by
  norm_num [map_ofNat, rho, pureState, Matrix.trace, Matrix.diag, Matrix.vecMulVec,
    psi, coefficients, Fintype.sum_prod_type, Fin.sum_univ_succ]

theorem rho_density : IsDensity rho := ⟨rho_posSemidef, rho_trace⟩

theorem rho_hermitian : rho.IsHermitian := rho_posSemidef.isHermitian

theorem rho_idempotent : rho * rho = rho := by
  simp only [rho, pureState, Matrix.vecMulVec_mul_vecMulVec, psi_normalized, one_smul]

theorem partialTraceRight_rho : partialTraceRight rho = reduced := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [map_ofNat, partialTraceRight, rho, pureState, Matrix.vecMulVec,
      psi, coefficients, reduced, Fin.sum_univ_succ]

theorem partialTraceLeft_rho : partialTraceLeft rho = reduced := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [map_ofNat, partialTraceLeft, rho, pureState, Matrix.vecMulVec,
      psi, coefficients, reduced, Fin.sum_univ_succ]

theorem reduced_hermitian : reduced.IsHermitian := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [map_ofNat, Matrix.conjTranspose_apply, reduced]

theorem reduced_trace : reduced.trace = 1 := by
  norm_num [map_ofNat, Matrix.trace, Matrix.diag, reduced, Fin.sum_univ_succ]

theorem reduced_scaled_projection : reduced * reduced = (1/2 : ℝ) • reduced := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [map_ofNat, Matrix.mul_apply, reduced, Fin.sum_univ_succ, RCLike.real_smul_eq_coe_mul]

end ECQC.Qutrit
