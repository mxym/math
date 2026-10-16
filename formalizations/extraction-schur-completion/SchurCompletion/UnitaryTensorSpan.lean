import SchurCompletion.GramUnitary
import SymmetricSupport.GaussianFrame

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace ExtractionSchur

open SymmetricSupport ExtractionSpectrum ExtractionRankSupport

noncomputable section

def finitePhaseVector (D L : ℕ) (θ : Fin D → Fin L) : Fin D → ℂ :=
  fun d => phaseRoot L ^ (θ d).val

theorem finitePhaseVector_norm (D L : ℕ) (hL : 0 < L) (θ : Fin D → Fin L) (d : Fin D) :
    ‖finitePhaseVector D L θ d‖ = 1 := by
  simp only [finitePhaseVector, norm_pow,
    (phaseRoot_primitive L hL).norm'_eq_one hL.ne', one_pow]

def phaseCoordinateMatrix (D k L : ℕ) : Matrix (Sym (Fin D) k) (Fin D → Fin L) ℂ :=
  fun s θ => monomialCoordinates D k (finitePhaseVector D L θ) s

theorem phaseCoordinateMatrix_gram (D k L : ℕ) (hL : k < L) :
    phaseCoordinateMatrix D k L * (phaseCoordinateMatrix D k L)ᴴ =
      ((L^D : ℕ) : ℂ) • 1 := by
  classical
  ext s t
  have hmc (q : Sym (Fin D) k) (θ : Fin D → Fin L) :
      monomialCoordinates D k (finitePhaseVector D L θ) q =
        ∏ d : Fin D, (finitePhaseVector D L θ d)^occupationExponent q d := by
    rw [monomialCoordinates, show occupationExponent q = q.val.toFinsupp from rfl,
      eval_monomial_multiset, occupation_amplitude_eq_product]
    rfl
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, phaseCoordinateMatrix,
    hmc, finitePhaseVector, star_prod, ← Finset.prod_mul_distrib,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [phase_multi_correlation D L (by omega) _ _
    (fun d => (occupationExponent_le s d).trans_lt hL)
    (fun d => (occupationExponent_le t d).trans_lt hL)]
  have heq : (fun d => occupationExponent s d) = (fun d => occupationExponent t d) ↔ s = t := by
    constructor
    · intro h
      exact occupationExponent_injective D k (Finsupp.ext (fun d => congrFun h d))
    · intro h; subst t; rfl
  simp only [heq, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

theorem finitePhaseCoordinates_span_top (D k L : ℕ) (hL : k < L) :
    Submodule.span ℂ (Set.range (fun θ => monomialCoordinates D k (finitePhaseVector D L θ))) = ⊤ := by
  classical
  let A := phaseCoordinateMatrix D k L
  have hc : ((L^D : ℕ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero D (by omega : L ≠ 0)
  have hr : A * ((((L^D : ℕ) : ℂ)⁻¹) • Aᴴ) = 1 := by
    rw [Matrix.mul_smul, phaseCoordinateMatrix_gram D k L hL, smul_smul,
      inv_mul_cancel₀ hc, one_smul]
  have hsurj : Function.Surjective A.mulVec :=
    Matrix.mulVec_surjective_iff_exists_right_inverse.mpr ⟨_,hr⟩
  have ht : LinearMap.range A.mulVecLin = ⊤ := LinearMap.range_eq_top.mpr hsurj
  rw [Matrix.range_mulVecLin] at ht
  convert ht using 2
  ext f
  constructor <;> rintro ⟨θ,rfl⟩ <;> exact ⟨θ,rfl⟩

theorem finitePhasePurePower_span (D k L : ℕ) (hL : k < L) (z : Fin D → ℂ) :
    purePower D k z ∈
      Submodule.span ℂ (Set.range (fun θ => purePower D k (finitePhaseVector D L θ))) := by
  have hz : monomialCoordinates D k z ∈
      Submodule.span ℂ (Set.range (fun θ => monomialCoordinates D k (finitePhaseVector D L θ))) := by
    rw [finitePhaseCoordinates_span_top D k L hL]
    exact Submodule.mem_top
  let E := (occupationColumns (occupation D k)).mulVecLin
  have hm := Submodule.mem_map_of_mem (f := E) hz
  rw [Submodule.map_span] at hm
  have he : E '' Set.range (fun θ => monomialCoordinates D k (finitePhaseVector D L θ)) =
      Set.range (fun θ => purePower D k (finitePhaseVector D L θ)) := by
    ext f
    constructor
    · rintro ⟨_,⟨θ,rfl⟩,rfl⟩
      exact ⟨θ,(purePower_occupationCoordinates D k _).symm⟩
    · rintro ⟨θ,rfl⟩
      exact ⟨_,⟨θ,rfl⟩,purePower_occupationCoordinates D k _⟩
  rw [he] at hm
  change (occupationColumns (occupation D k)).mulVec (monomialCoordinates D k z) ∈ _ at hm
  rwa [purePower_occupationCoordinates] at hm

def unitaryTensorSpan (D k : ℕ) : Submodule ℂ (Matrix (Word D k) (Word D k) ℂ) :=
  Submodule.span ℂ (Set.range (fun U : OneCopyUnitary D =>
    tensorMatrix (U : Matrix (Fin D) (Fin D) ℂ) k))

theorem unitaryTensorSpan_mul_mem (D k : ℕ)
    {A B : Matrix (Word D k) (Word D k) ℂ}
    (hA : A ∈ unitaryTensorSpan D k) (hB : B ∈ unitaryTensorSpan D k) :
    A*B ∈ unitaryTensorSpan D k := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨U,rfl⟩ := hA
    induction hB using Submodule.span_induction with
    | mem B hB =>
      obtain ⟨V,rfl⟩ := hB
      exact Submodule.subset_span ⟨U*V, tensorMatrix_mul _ _ k⟩
    | zero => simpa only [Matrix.mul_zero] using (Submodule.zero_mem (unitaryTensorSpan D k))
    | add B C hB hC ihB ihC => simpa only [Matrix.mul_add] using Submodule.add_mem _ ihB ihC
    | smul c B hB ihB => simpa only [Matrix.mul_smul] using Submodule.smul_mem _ c ihB
  | zero => simpa only [Matrix.zero_mul] using (Submodule.zero_mem (unitaryTensorSpan D k))
  | add A C hA hC ihA ihC => simpa only [Matrix.add_mul] using Submodule.add_mem _ ihA ihC
  | smul c A hA ihA => simpa only [Matrix.smul_mul] using Submodule.smul_mem _ c ihA

def diagonalLinear (D k : ℕ) : (Word D k → ℂ) →ₗ[ℂ] Matrix (Word D k) (Word D k) ℂ where
  toFun := Matrix.diagonal
  map_add' f g := (Matrix.diagonal_add _ _).symm
  map_smul' c f := Matrix.diagonal_smul _ _

theorem tensorMatrix_diagonal_complex (D k : ℕ) (z : Fin D → ℂ) :
    tensorMatrix (Matrix.diagonal z) k = Matrix.diagonal (purePower D k z) := by
  classical
  ext w v
  by_cases h : w = v
  · subst v; simp [tensorMatrix,purePower]
  · obtain ⟨j,hj⟩ := Function.ne_iff.mp h
    simp only [tensorMatrix, Matrix.diagonal_apply, h, ite_false]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

theorem tensorDiagonal_mem_unitaryTensorSpan (D k : ℕ) (z : Fin D → ℂ) :
    tensorMatrix (Matrix.diagonal z) k ∈ unitaryTensorSpan D k := by
  have hle : Submodule.span ℂ
      (Set.range (fun θ => purePower D k (finitePhaseVector D (k+1) θ))) ≤
      (unitaryTensorSpan D k).comap (diagonalLinear D k) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨θ,rfl⟩
    let V := Matrix.diagonal (finitePhaseVector D (k+1) θ)
    have hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
      dsimp only [V]
      rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j
      · subst j
        simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
        have hn : Complex.normSq (finitePhaseVector D (k+1) θ i) = 1 := by
          rw [Complex.normSq_eq_norm_sq, finitePhaseVector_norm D (k+1) (by omega) θ i]
          norm_num
        simp only [Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, hn,
          Complex.ofReal_one]
      · simp [hij]
    change Matrix.diagonal (purePower D k _) ∈ unitaryTensorSpan D k
    rw [← tensorMatrix_diagonal_complex]
    exact Submodule.subset_span ⟨⟨V,hV⟩,rfl⟩
  rw [tensorMatrix_diagonal_complex]
  exact hle (finitePhasePurePower_span D k (k+1) (by omega) z)

theorem hermitianTensor_mem_unitaryTensorSpan (D k : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) (hX : X.IsHermitian) :
    tensorMatrix X k ∈ unitaryTensorSpan D k := by
  rw [tensorMatrix_spectral X hX k]
  apply unitaryTensorSpan_mul_mem
  · apply unitaryTensorSpan_mul_mem
    · exact Submodule.subset_span ⟨hX.eigenvectorUnitary,rfl⟩
    · rw [← tensorMatrix_diagonal]
      exact tensorDiagonal_mem_unitaryTensorSpan D k _
  · change (tensorMatrix (hX.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ) k)ᴴ ∈ _
    rw [← tensorMatrix_conjTranspose]
    exact Submodule.subset_span ⟨star hX.eigenvectorUnitary,rfl⟩

/-- Genuine unitary tensor powers span every genuine matrix tensor power.
Finite Fourier phases handle diagonal powers; an internally proved singular
polar factorization handles all matrices. -/
theorem unitaryTensorSpan_eq_tensorPowerSpan (D k : ℕ) :
    unitaryTensorSpan D k = tensorPowerSpan D k := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨U,rfl⟩
    exact Submodule.subset_span ⟨(U : Matrix (Fin D) (Fin D) ℂ),rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨X,rfl⟩
    change tensorMatrix X k ∈ _
    obtain ⟨U,H,hH,hUH⟩ := exists_unitary_mul_posSemidef X
    rw [← hUH, tensorMatrix_mul]
    exact unitaryTensorSpan_mul_mem D k (Submodule.subset_span ⟨U,rfl⟩)
      (hermitianTensor_mem_unitaryTensorSpan D k H hH.isHermitian)

end
end ExtractionSchur
