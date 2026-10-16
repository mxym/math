import UniversalOrbit.OrbitDimension
import MatrixSubspace

open scoped BigOperators ComplexOrder
open Matrix Module
namespace UniversalOrbit
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_subspace_projection (S : Submodule ℂ (ι → ℂ)) :
    ∃ P : Matrix ι ι ℂ, P.IsHermitian ∧ P * P = P ∧
      LinearMap.range P.mulVecLin = S ∧ P.rank = Module.finrank ℂ S ∧
      ∀ v ∈ S, P *ᵥ v = v := MatrixSubspace.exists_subspace_projection S

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
