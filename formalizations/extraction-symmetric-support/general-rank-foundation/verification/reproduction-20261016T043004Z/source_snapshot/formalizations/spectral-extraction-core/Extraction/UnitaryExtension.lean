import Extraction.KrausRains
import Mathlib.Analysis.Normed.Module.FiniteDimension

open scoped BigOperators ComplexOrder
open Matrix
namespace Extraction

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- An actual rectangular matrix with E*E=I induces a genuine Euclidean isometry. -/
noncomputable def matrixIsometry (E : Matrix ι κ ℂ) (hE : Eᴴ * E = 1) :
    EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ ι where
  toLinearMap := Matrix.toEuclideanLin E
  norm_map' := (LinearMap.norm_map_iff_inner_map_map (Matrix.toEuclideanLin E)).mpr (by
    intro x y
    simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply]
    rw [dotProduct_comm, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      hE, Matrix.vecMul_one, dotProduct_comm])

/-- Any two actual isometries with the same logical domain are related by one
global unitary on the original space, without adding an input ancilla. -/
theorem exists_unitary_between_isometries (C E : Matrix ι κ ℂ)
    (hC : Cᴴ * C = 1) (hE : Eᴴ * E = 1) :
    ∃ U : Matrix.unitaryGroup ι ℂ, (U : Matrix ι ι ℂ) * C = E := by
  let c := matrixIsometry C hC
  let e := matrixIsometry E hE
  let L : LinearMap.range c.toLinearMap →ₗᵢ[ℂ] EuclideanSpace ℂ ι :=
    e.comp c.equivRange.symm.toLinearIsometry
  let T : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι :=
    L.extend.toLinearIsometryEquiv rfl
  let b := EuclideanSpace.basisFun ι ℂ
  let U : Matrix.unitaryGroup ι ℂ :=
    ⟨T.toMatrix b.toBasis b.toBasis, T.toMatrix_mem_unitaryGroup b b⟩
  refine ⟨U, ?_⟩
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro x
  have hL : T (c x) = e x := by
    change L.extend (c x) = e x
    calc
      L.extend (c x) = L (c.equivRange x) := by
        simpa using L.extend_apply (c.equivRange x)
      _ = e (c.equivRange.symm (c.equivRange x)) := rfl
      _ = e x := congrArg e (c.equivRange.symm_apply_apply x)
  change Matrix.toLin (EuclideanSpace.basisFun κ ℂ).toBasis b.toBasis
      ((U : Matrix ι ι ℂ) * C) x = Matrix.toEuclideanLin E x
  rw [Matrix.toLin_mul_apply (EuclideanSpace.basisFun κ ℂ).toBasis b.toBasis b.toBasis]
  change Matrix.toLin b.toBasis b.toBasis (T.toMatrix b.toBasis b.toBasis)
      (Matrix.toEuclideanLin C x) = Matrix.toEuclideanLin E x
  rw [Matrix.toLin_toMatrix]
  exact hL

end Extraction
