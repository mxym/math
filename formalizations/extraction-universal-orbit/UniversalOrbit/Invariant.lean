import UniversalOrbit.ProjectionFactory
import SymmetricSupport.PureSpan
import Spectrum.Tensor

open scoped BigOperators ComplexOrder
open Matrix SymmetricSupport Module
namespace UniversalOrbit
noncomputable section

theorem entryVector_surjective (D : ℕ) :
    Function.Surjective (entryVector : Matrix (Fin D) (Fin D) ℂ → (Fin (D*D) → ℂ)) := by
  intro z
  refine ⟨fun i j => z ((entryEquiv D).symm (i,j)), ?_⟩
  ext i
  simp [entryVector]

theorem orbitSpace_eq_span {D k : ℕ} (v : Word D k → ℂ) :
    orbitSpace v = Submodule.span ℂ
      (Set.range (fun M : Matrix (Fin D) (Fin D) ℂ => tensorAction M v)) := by
  rw [orbitSpace, symmetricProjector_range_eq_purePower_span, Submodule.map_span]
  congr 1
  ext w
  constructor
  · rintro ⟨_,⟨z,rfl⟩,rfl⟩
    obtain ⟨M,rfl⟩ := entryVector_surjective D z
    exact ⟨M,(contraction_purePower M v).symm⟩
  · rintro ⟨M,rfl⟩
    exact ⟨_,⟨entryVector M,rfl⟩,contraction_purePower M v⟩

theorem tensorAction_mul {D k : ℕ} (M N : Matrix (Fin D) (Fin D) ℂ)
    (v : Word D k → ℂ) : tensorAction M (tensorAction N v) = tensorAction (M*N) v := by
  change (ExtractionSpectrum.tensorMatrix M k).mulVec
      ((ExtractionSpectrum.tensorMatrix N k).mulVec v) =
    (ExtractionSpectrum.tensorMatrix (M*N) k).mulVec v
  rw [Matrix.mulVec_mulVec, ExtractionSpectrum.tensorMatrix_mul]

theorem tensorAction_orbit_invariant {D k : ℕ} (M : Matrix (Fin D) (Fin D) ℂ)
    (v w : Word D k → ℂ) (hw : w ∈ orbitSpace v) : tensorAction M w ∈ orbitSpace v := by
  rw [orbitSpace_eq_span] at hw
  let L := (ExtractionSpectrum.tensorMatrix M k).mulVecLin
  have hle : Submodule.span ℂ
      (Set.range (fun N : Matrix (Fin D) (Fin D) ℂ => tensorAction N v)) ≤
      (orbitSpace v).comap L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨N,rfl⟩
    change tensorAction M (tensorAction N v) ∈ orbitSpace v
    rw [tensorAction_mul]
    exact tensorAction_mem_orbitSpace _ _
  exact hle hw

theorem tensorAction_universal_invariant {D k : ℕ}
    (S : Finset (Word D k)) (M : Matrix (Fin D) (Fin D) ℂ)
    (w : Word D k → ℂ) (hw : w ∈ universalSpace S) :
    tensorAction M w ∈ universalSpace S := by
  let L := (ExtractionSpectrum.tensorMatrix M k).mulVecLin
  have hle : universalSpace S ≤ (universalSpace S).comap L := by
    apply Finset.sup_le
    intro x hx v hv
    exact (Finset.le_sup (f := fun x => orbitSpace (Pi.single x (1:ℂ))) hx)
      (tensorAction_orbit_invariant M _ _ hv)
  exact hle hw

end
end UniversalOrbit
