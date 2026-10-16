import UniversalOrbit.OrbitDimension
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Produce actual Hermitian projectors from arbitrary known subspaces. The
Gram formula avoids imposing an incompatible Hilbert norm on plain Pi types. -/
open scoped BigOperators ComplexOrder
open Matrix Module
namespace UniversalOrbit
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_subspace_projection (S : Submodule ℂ (ι → ℂ)) :
    ∃ P : Matrix ι ι ℂ, P.IsHermitian ∧ P * P = P ∧
      LinearMap.range P.mulVecLin = S ∧ P.rank = Module.finrank ℂ S ∧
      ∀ v ∈ S, P *ᵥ v = v := by
  classical
  let e := (Module.finBasis ℂ S).equivFun.symm
  let L : (Fin (Module.finrank ℂ S) → ℂ) →ₗ[ℂ] (ι → ℂ) := S.subtype.comp e.toLinearMap
  let C := LinearMap.toMatrix' L
  have hC : C.mulVecLin = L := Matrix.toLin'_toMatrix' L
  have hLin : Function.Injective L := Subtype.val_injective.comp e.injective
  have hCinj : Function.Injective C.mulVec := by
    change Function.Injective C.mulVecLin
    rw [hC]
    exact hLin
  have hG : (Cᴴ * C).PosDef := Matrix.PosDef.conjTranspose_mul_self C hCinj
  let G := Cᴴ * C
  letI : Invertible G := hG.isUnit.invertible
  have hinv : G⁻¹ * G = 1 := Matrix.inv_mul_of_invertible G
  have hGH : G⁻¹.IsHermitian := hG.isHermitian.inv
  let P := C * G⁻¹ * Cᴴ
  have hPC : P * C = C := by
    calc
      P * C = C * (G⁻¹ * G) := by dsimp only [P,G]; simp only [Matrix.mul_assoc]
      _ = C := by rw [hinv,Matrix.mul_one]
  have hPH : P.IsHermitian := by
    change Pᴴ = P
    simp only [P, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hGH.eq, Matrix.mul_assoc]
  have hPP : P * P = P := by
    calc
      P * P = (P * C) * G⁻¹ * Cᴴ := by simp only [P,Matrix.mul_assoc]
      _ = P := by rw [hPC]
  have hRangeC : LinearMap.range C.mulVecLin = S := by
    rw [hC]
    ext v
    constructor
    · rintro ⟨x,rfl⟩
      exact (e x).property
    · intro hv
      exact ⟨e.symm ⟨v,hv⟩, by simp [L]⟩
  have hfix (v : ι → ℂ) (hv : v ∈ S) : P *ᵥ v = v := by
    rw [← hRangeC] at hv
    obtain ⟨x,rfl⟩ := hv
    change P *ᵥ (C *ᵥ x) = C *ᵥ x
    rw [Matrix.mulVec_mulVec, hPC]
  have hRangeP : LinearMap.range P.mulVecLin = S := by
    ext v
    constructor
    · rintro ⟨x,rfl⟩
      rw [← hRangeC]
      refine ⟨G⁻¹ *ᵥ (Cᴴ *ᵥ x), ?_⟩
      change C *ᵥ (G⁻¹ *ᵥ (Cᴴ *ᵥ x)) = P *ᵥ x
      simp only [P,Matrix.mulVec_mulVec,Matrix.mul_assoc]
    · intro hv
      exact ⟨v,hfix v hv⟩
  refine ⟨P,hPH,hPP,hRangeP,?_,hfix⟩
  change Module.finrank ℂ (LinearMap.range P.mulVecLin) = _
  rw [hRangeP]

/-- The fixed universal orbit span therefore has an actual matrix projector
with the proved polynomial dimension bound. -/
theorem universalSpace_actual_projection (D k : ℕ) (S : Finset (SymmetricSupport.Word D k)) :
    ∃ P : Matrix (SymmetricSupport.Word D k) (SymmetricSupport.Word D k) ℂ,
      P.IsHermitian ∧ P * P = P ∧
      P.rank ≤ S.card * (D*D+k-1).choose k ∧
      ∀ (M : Matrix (Fin D) (Fin D) ℂ) (x : SymmetricSupport.Word D k), x ∈ S →
        P *ᵥ tensorAction M (Pi.single x 1) = tensorAction M (Pi.single x 1) := by
  obtain ⟨P,hPH,hPP,hRange,hRank,hfix⟩ := exists_subspace_projection (universalSpace S)
  refine ⟨P,hPH,hPP,hRank.le.trans (finrank_universalSpace_le S),?_⟩
  intro M x hx
  exact hfix _ (tensorAction_single_mem_universalSpace S x hx M)

end
end UniversalOrbit
