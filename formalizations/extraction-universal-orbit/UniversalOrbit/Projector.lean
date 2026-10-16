import UniversalOrbit.Invariant

open scoped BigOperators ComplexOrder
open Matrix SymmetricSupport Module
namespace UniversalOrbit
noncomputable section

def universalProjection (D k : ℕ) (S : Finset (Word D k)) :
    Matrix (Word D k) (Word D k) ℂ :=
  (exists_subspace_projection (universalSpace S)).choose

theorem universalProjection_properties (D k : ℕ) (S : Finset (Word D k)) :
    (universalProjection D k S).IsHermitian ∧
    universalProjection D k S * universalProjection D k S = universalProjection D k S ∧
    LinearMap.range (universalProjection D k S).mulVecLin = universalSpace S ∧
    (universalProjection D k S).rank = Module.finrank ℂ (universalSpace S) ∧
    ∀ v ∈ universalSpace S, universalProjection D k S *ᵥ v = v :=
  (exists_subspace_projection (universalSpace S)).choose_spec

theorem universalProjection_hermitian (D k : ℕ) (S : Finset (Word D k)) :
    (universalProjection D k S).IsHermitian := (universalProjection_properties D k S).1

theorem universalProjection_idempotent (D k : ℕ) (S : Finset (Word D k)) :
    universalProjection D k S * universalProjection D k S = universalProjection D k S :=
  (universalProjection_properties D k S).2.1

theorem universalProjection_rank_le (D k : ℕ) (S : Finset (Word D k)) :
    (universalProjection D k S).rank ≤ S.card * (D*D+k-1).choose k :=
  (universalProjection_properties D k S).2.2.2.1.le.trans (finrank_universalSpace_le S)

theorem universalProjection_fixes (D k : ℕ) (S : Finset (Word D k))
    (v : Word D k → ℂ) (hv : v ∈ universalSpace S) :
    universalProjection D k S *ᵥ v = v :=
  (universalProjection_properties D k S).2.2.2.2 v hv

theorem universalProjection_column_mem (D k : ℕ) (S : Finset (Word D k)) (w : Word D k) :
    (universalProjection D k S).col w ∈ universalSpace S := by
  rw [← (universalProjection_properties D k S).2.2.1, Matrix.range_mulVecLin]
  exact Submodule.subset_span ⟨w,rfl⟩

theorem mul_eq_of_fixes_columns {ι : Type*} [Fintype ι]
    (P B : Matrix ι ι ℂ) (h : ∀ j, P *ᵥ B.col j = B.col j) : P*B=B := by
  ext i j
  exact congrArg (fun v => v i) (h j)

theorem universalProjection_tensor_compress (D k : ℕ) (S : Finset (Word D k))
    (M : Matrix (Fin D) (Fin D) ℂ) :
    universalProjection D k S * ExtractionSpectrum.tensorMatrix M k * universalProjection D k S =
      ExtractionSpectrum.tensorMatrix M k * universalProjection D k S := by
  rw [Matrix.mul_assoc]
  apply mul_eq_of_fixes_columns
  intro w
  have hc : (ExtractionSpectrum.tensorMatrix M k * universalProjection D k S).col w =
      ExtractionSpectrum.tensorMatrix M k *ᵥ (universalProjection D k S).col w := rfl
  rw [hc]
  exact universalProjection_fixes D k S _
    (tensorAction_universal_invariant S M _ (universalProjection_column_mem D k S w))

/-- A single fixed, spectrum-independent projector commutes with every actual
identical matrix tensor power. This is proved from its actual invariant range. -/
theorem universalProjection_commutes_tensor (D k : ℕ) (S : Finset (Word D k))
    (M : Matrix (Fin D) (Fin D) ℂ) :
    universalProjection D k S * ExtractionSpectrum.tensorMatrix M k =
      ExtractionSpectrum.tensorMatrix M k * universalProjection D k S := by
  have h := congrArg Matrix.conjTranspose (universalProjection_tensor_compress D k S Mᴴ)
  have h' : universalProjection D k S * ExtractionSpectrum.tensorMatrix M k *
      universalProjection D k S = universalProjection D k S * ExtractionSpectrum.tensorMatrix M k := by
    simpa only [Matrix.conjTranspose_mul, ← ExtractionSpectrum.tensorMatrix_conjTranspose,
      Matrix.conjTranspose_conjTranspose,(universalProjection_hermitian D k S).eq,
      ← Matrix.mul_assoc] using h
  exact h'.symm.trans (universalProjection_tensor_compress D k S M)

theorem universalProjection_nested (D k : ℕ) (S T : Finset (Word D k)) (hST : S ⊆ T) :
    universalProjection D k T * universalProjection D k S = universalProjection D k S ∧
    universalProjection D k S * universalProjection D k T = universalProjection D k S := by
  have h : universalProjection D k T * universalProjection D k S = universalProjection D k S := by
    apply mul_eq_of_fixes_columns
    intro w
    apply universalProjection_fixes
    exact universalSpace_mono hST (universalProjection_column_mem D k S w)
  refine ⟨h,?_⟩
  have hc := congrArg Matrix.conjTranspose h
  simpa only [Matrix.conjTranspose_mul, (universalProjection_hermitian D k S).eq,
    (universalProjection_hermitian D k T).eq] using hc

end
end UniversalOrbit
