import APPT.Quantum.PureProjector
open scoped BigOperators ComplexOrder
open Matrix
namespace APPT.Quantum
variable {b : Type*} [Fintype b] [DecidableEq b]

theorem unitary_preserves_squared_length
    (U : Matrix.unitaryGroup (Fin 3 × b) ℂ) (v : Fin 3 × b → ℂ) :
    (∑ k, star ((U : Matrix (Fin 3 × b) (Fin 3 × b) ℂ) *ᵥ v) k *
      ((U : Matrix (Fin 3 × b) (Fin 3 × b) ℂ) *ᵥ v) k) =
    ∑ k, star (v k)*v k := by
  have hu : (U : Matrix (Fin 3 × b) (Fin 3 × b) ℂ)ᴴ*U=1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  change star ((U : Matrix (Fin 3 × b) (Fin 3 × b) ℂ)*ᵥv) ⬝ᵥ
    ((U : Matrix (Fin 3 × b) (Fin 3 × b) ℂ)*ᵥv) = star v ⬝ᵥ v
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hu,
    Matrix.vecMul_one]

theorem rankOne_conjugate (U : Matrix.unitaryGroup (Fin 3 × b) ℂ)
    (v : Fin 3 × b → ℂ) :
    (U : Matrix (Fin 3 × b) (Fin 3 × b) ℂ)*rankOne v*
      (U : Matrix (Fin 3 × b) (Fin 3 × b) ℂ)ᴴ =
    rankOne ((U : Matrix (Fin 3 × b) (Fin 3 × b) ℂ)*ᵥv) := by
  simp [rankOne, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_conjTranspose]

/-- Full global-unitary APPT for the rank-one attaining orbit. -/
theorem absolutelyPPT_one_add_twice_rankOne (v : Fin 3 × b → ℂ)
    (hv : (∑ k, star (v k)*v k) = 1) :
    AbsolutelyPPT (1+(2 : ℝ) • rankOne v) := by
  intro U
  have hn := (unitary_preserves_squared_length U v).trans hv
  have h := one_add_twice_pure_partialTranspose_posSemidef _ hn
  have hu : (U : Matrix (Fin 3 × b) (Fin 3 × b) ℂ)*
      (U : Matrix (Fin 3 × b) (Fin 3 × b) ℂ)ᴴ = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U
  simpa [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    hu, rankOne_conjugate] using h

end APPT.Quantum
