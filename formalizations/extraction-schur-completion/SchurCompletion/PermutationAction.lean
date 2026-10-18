import SchurCompletion.TensorCommutant

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix MeasureTheory

namespace ExtractionSchur

open SymmetricSupport ExtractionSpectrum

noncomputable section

def positionWordEquiv (D k : ℕ) (σ : Equiv.Perm (Fin k)) : Equiv.Perm (Word D k) where
  toFun w := w ∘ σ
  invFun w := w ∘ σ.symm
  left_inv w := by ext i; simp
  right_inv w := by ext i; simp

def copyPermutationMatrix (D k : ℕ) (σ : Equiv.Perm (Fin k)) :
    Matrix (Word D k) (Word D k) ℂ := (positionWordEquiv D k σ).permMatrix ℂ

theorem copyPermutationMatrix_unitary (D k : ℕ) (σ : Equiv.Perm (Fin k)) :
    copyPermutationMatrix D k σ ∈ Matrix.unitaryGroup (Word D k) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  unfold copyPermutationMatrix
  rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul, mul_inv_cancel,
    Matrix.permMatrix_one]

def copyPermutationUnitary (D k : ℕ) (σ : Equiv.Perm (Fin k)) :
    Matrix.unitaryGroup (Word D k) ℂ :=
  ⟨copyPermutationMatrix D k σ, copyPermutationMatrix_unitary D k σ⟩

theorem copyPermutationMatrix_conjugate (D k : ℕ) (σ : Equiv.Perm (Fin k))
    (M : Matrix (Word D k) (Word D k) ℂ) :
    copyPermutationMatrix D k σ * M * (copyPermutationMatrix D k σ)ᴴ =
      M.submatrix (fun w => w ∘ σ) (fun w => w ∘ σ) := by
  unfold copyPermutationMatrix
  rw [Matrix.conjTranspose_permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  ext x y
  rfl

theorem mem_tensorPowerSpan_iff_commutes (D k : ℕ)
    (M : Matrix (Word D k) (Word D k) ℂ) :
    M ∈ tensorPowerSpan D k ↔ ∀ σ : Equiv.Perm (Fin k),
      copyPermutationMatrix D k σ * M = M * copyPermutationMatrix D k σ := by
  rw [mem_tensorPowerSpan_iff_position_invariant]
  constructor
  · intro h σ
    have he : copyPermutationMatrix D k σ * M * (copyPermutationMatrix D k σ)ᴴ = M := by
      rw [copyPermutationMatrix_conjugate]
      exact Matrix.ext (h σ)
    have hUnit := (copyPermutationMatrix_unitary D k σ).1
    simp only [Matrix.star_eq_conjTranspose] at hUnit
    have hmul := congrArg (fun N => N * copyPermutationMatrix D k σ) he
    simpa only [Matrix.mul_assoc, hUnit, Matrix.mul_one] using hmul
  · intro h σ
    have hUnit := (copyPermutationMatrix_unitary D k σ).2
    simp only [Matrix.star_eq_conjTranspose] at hUnit
    have he : M.submatrix (fun w => w ∘ σ) (fun w => w ∘ σ) = M := by
      rw [← copyPermutationMatrix_conjugate, h σ, Matrix.mul_assoc, hUnit, Matrix.mul_one]
    exact fun x y => congrFun (congrFun he x) y

theorem tensorPowerSpan_finrank (D k : ℕ) :
    Module.finrank ℂ (tensorPowerSpan D k) = (D*D+k-1).choose k := by
  rw [← (flattenTensorMatrix D k).finrank_map_eq, flatten_tensorPowerSpan]
  exact symmetricProjector_rank_choose (D*D) k

theorem tensorMatrix_commutes_copyPermutation (D k : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) (σ : Equiv.Perm (Fin k)) :
    copyPermutationMatrix D k σ * tensorMatrix X k =
      tensorMatrix X k * copyPermutationMatrix D k σ :=
  (mem_tensorPowerSpan_iff_commutes D k _).mp (Submodule.subset_span ⟨X,rfl⟩) σ

theorem haarOrbitAverage_mem_tensorPowerSpan (D k : ℕ) (X : Matrix (Fin D) (Fin D) ℂ) :
    haarOrbitAverage D k X ∈ tensorPowerSpan D k := by
  apply (mem_tensorPowerSpan_iff_commutes D k _).mpr
  intro σ
  have hUnit := (copyPermutationMatrix_unitary D k σ).1
  simp only [Matrix.star_eq_conjTranspose] at hUnit
  have hUnit' := (copyPermutationMatrix_unitary D k σ).2
  simp only [Matrix.star_eq_conjTranspose] at hUnit'
  have he : copyPermutationMatrix D k σ * haarOrbitAverage D k X *
      (copyPermutationMatrix D k σ)ᴴ = haarOrbitAverage D k X := by
    calc
      _ = ∫ U, copyPermutationMatrix D k σ * orbitTensor D k X U *
          (copyPermutationMatrix D k σ)ᴴ ∂unitaryHaar D :=
        ((conjugateLinear _).toContinuousLinearMap.integral_comp_comm
          (integrable_orbitTensor D k X)).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with U
        rw [orbitTensor, tensorMatrix_commutes_copyPermutation, Matrix.mul_assoc,
          hUnit', Matrix.mul_one]
  have hmul := congrArg (fun N => N * copyPermutationMatrix D k σ) he
  simpa only [Matrix.mul_assoc, hUnit, Matrix.mul_one] using hmul

end
end ExtractionSchur
