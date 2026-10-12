import GaussianPrincipalNondegeneracy
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-! Simultaneous congruence factorization of a positive covariance and an
arbitrary Hermitian direction. It supplies an explicit diagonal-variance lift
without differentiating the matrix square root. -/
open MeasureTheory ProbabilityTheory Set Module Matrix Unitary
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GaussianMeasureBridge
variable {n : ℕ} [NeZero n]

theorem affine_matrix_diagonal_factorization
    (A E : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (hE : E.IsHermitian) :
    ∃ M : Matrix (Fin n) (Fin n) ℝ, ∃ a : Fin n → ℝ,
      IsUnit M ∧ M*Mᴴ = A ∧ M*Matrix.diagonal a*Mᴴ = E := by
  let R := CFC.sqrt A
  have hR : R.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  have hRR : R*R = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hRu : IsUnit R := (CFC.isUnit_sqrt_iff A hA.posSemidef.nonneg).mpr hA.isUnit
  let B := R⁻¹ * E * (R⁻¹)ᴴ
  have hB : B.IsHermitian := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      Matrix.isHermitian_conjTranspose_mul_mul (R⁻¹)ᴴ hE
  let U := hB.eigenvectorUnitary
  have hU : (U : Matrix (Fin n) (Fin n) ℝ) * (U : Matrix (Fin n) (Fin n) ℝ)ᴴ = 1 := by
    simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U
  have hspec : B = (U : Matrix (Fin n) (Fin n) ℝ) *
      Matrix.diagonal hB.eigenvalues * (U : Matrix (Fin n) (Fin n) ℝ)ᴴ := by
    simpa only [conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,
      Function.comp_def,RCLike.ofReal_real_eq_id,id_eq,U] using hB.spectral_theorem
  let M := R * (U : Matrix (Fin n) (Fin n) ℝ)
  refine ⟨M,hB.eigenvalues,hRu.mul Unitary.isUnit_coe,?_,?_⟩
  · change (R*(U:Matrix (Fin n) (Fin n) ℝ)) *
      (R*(U:Matrix (Fin n) (Fin n) ℝ))ᴴ = A
    rw [Matrix.conjTranspose_mul]
    calc
      _ = R * ((U:Matrix (Fin n) (Fin n) ℝ) * (U:Matrix (Fin n) (Fin n) ℝ)ᴴ) * Rᴴ := by
        simp only [Matrix.mul_assoc]
      _ = A := by rw [hU,Matrix.mul_one,hR.eq,hRR]
  · change (R*(U:Matrix (Fin n) (Fin n) ℝ)) * Matrix.diagonal hB.eigenvalues *
      (R*(U:Matrix (Fin n) (Fin n) ℝ))ᴴ = E
    rw [Matrix.conjTranspose_mul]
    calc
      _ = R * ((U:Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal hB.eigenvalues *
          (U:Matrix (Fin n) (Fin n) ℝ)ᴴ) * Rᴴ := by simp only [Matrix.mul_assoc]
      _ = R * B * Rᴴ := congrArg (fun X => R*X*Rᴴ) hspec.symm
      _ = E := by
        dsimp [B]
        have hleft : R*R⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det R).mp hRu)
        have hright : (R⁻¹)ᴴ*Rᴴ = 1 := by rw [← Matrix.conjTranspose_mul,hleft]; simp
        calc
          R*(R⁻¹*E*(R⁻¹)ᴴ)*Rᴴ = (R*R⁻¹)*E*((R⁻¹)ᴴ*Rᴴ) := by simp only [Matrix.mul_assoc]
          _ = E := by rw [hleft,hright,Matrix.one_mul,Matrix.mul_one]

end GaussianMeasureBridge
