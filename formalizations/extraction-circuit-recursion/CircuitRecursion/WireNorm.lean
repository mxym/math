import CircuitRecursion.SKSynthesis
import Mathlib.Analysis.CStarAlgebra.Spectrum

open scoped Kronecker Matrix.Norms.L2Operator
open Matrix CircuitCompletion
namespace CircuitRecursion

def matrixReindexStarAlgEquiv {ι ο : Type*} [Fintype ι] [Fintype ο]
    [DecidableEq ι] [DecidableEq ο] (e : ι ≃ ο) :
    Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix ο ο ℂ :=
  { Matrix.reindexAlgEquiv ℂ ℂ e with
    map_smul' := by intro c A; ext i j; rfl
    map_star' := by intro A; ext i j; rfl }

theorem matrixReindex_norm {ι ο : Type*} [Fintype ι] [Fintype ο]
    [DecidableEq ι] [DecidableEq ο] (e : ι ≃ ο) (A : Matrix ι ι ℂ) :
    ‖Matrix.reindexAlgEquiv ℂ ℂ e A‖=‖A‖ :=
  StarAlgEquiv.norm_map (matrixReindexStarAlgEquiv e) A

noncomputable def wireStarAlgHom {n : ℕ} (i : Fin n) :
    Matrix Bool Bool ℂ →⋆ₐ[ℂ] Matrix (Bits n) (Bits n) ℂ where
  toFun A := Matrix.reindexAlgEquiv ℂ ℂ (wireCoordinates i).symm
    (A ⊗ₖ (1 : Matrix ({j : Fin n // j≠i} → Bool) ({j : Fin n // j≠i} → Bool) ℂ))
  map_zero' := by simp
  map_one' := by rw [Matrix.one_kronecker_one,map_one]
  map_add' A B := by rw [Matrix.add_kronecker,map_add]
  map_mul' A B := by rw [← map_mul,← Matrix.mul_kronecker_mul,Matrix.one_mul]
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one,Matrix.smul_kronecker,Matrix.one_kronecker_one,
      map_smul,map_one]
  map_star' A := by
    ext b c
    by_cases h : ((wireCoordinates i) b).2=((wireCoordinates i) c).2 <;>
      simp [Matrix.coe_reindexAlgEquiv,Matrix.reindex_apply,Matrix.submatrix_apply,
        Matrix.conjTranspose_apply,Matrix.kronecker_apply,Matrix.one_apply,eq_comm,h]

theorem singleWire_eq_hom {n : ℕ} (i : Fin n) (U : Matrix.unitaryGroup Bool ℂ) :
    (singleWire i U : Matrix (Bits n) (Bits n) ℂ)=wireStarAlgHom i (U : Matrix Bool Bool ℂ) := rfl

theorem singleWire_error {n : ℕ} (i : Fin n) (U V : Matrix.unitaryGroup Bool ℂ) :
    ‖(singleWire i U : Matrix (Bits n) (Bits n) ℂ)-singleWire i V‖≤
      ‖(U : Matrix Bool Bool ℂ)-V‖ := by
  rw [singleWire_eq_hom,singleWire_eq_hom,← map_sub]
  exact NonUnitalStarAlgHom.norm_apply_le (wireStarAlgHom i) _

theorem singleWire_phase {n : ℕ} (i : Fin n) (U V : Matrix.unitaryGroup Bool ℂ)
    (c : ℂ) (he : (U : Matrix Bool Bool ℂ)=c • (V : Matrix Bool Bool ℂ)) :
    (singleWire i U : Matrix (Bits n) (Bits n) ℂ)=c •
      (singleWire i V : Matrix (Bits n) (Bits n) ℂ) := by
  rw [singleWire_eq_hom,singleWire_eq_hom,he,map_smul]

noncomputable def su2ToBool (U : SU2) : Matrix.unitaryGroup Bool ℂ :=
  reindexUnitary finTwoEquiv (su2AsUnitary U)

theorem su2ToBool_error (U V : SU2) :
    ‖(su2ToBool U : Matrix Bool Bool ℂ)-su2ToBool V‖=‖U.val-V.val‖ := by
  change ‖Matrix.reindexAlgEquiv ℂ ℂ finTwoEquiv U.val-
    Matrix.reindexAlgEquiv ℂ ℂ finTwoEquiv V.val‖=_
  rw [← map_sub,matrixReindex_norm]

end CircuitRecursion
