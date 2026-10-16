import SchurCompletion.ColumnCutoff

open scoped BigOperators ComplexOrder
open Matrix

namespace ExtractionSchur

open SymmetricSupport ExtractionSpectrum ExtractionRankSupport

noncomputable section

theorem copyPermutation_preserves_rankBudgetSpace (D k s : ℕ)
    (σ : Equiv.Perm (Fin k)) (v : Word D k → ℂ) (hv : v ∈ rankBudgetSpace D k s) :
    copyPermutationMatrix D k σ *ᵥ v ∈ rankBudgetSpace D k s := by
  have hle : rankBudgetSpace D k s ≤
      (rankBudgetSpace D k s).comap (copyPermutationMatrix D k σ).mulVecLin := by
    apply Submodule.span_le.mpr
    rintro _ ⟨z,hz,rfl⟩
    change copyPermutationMatrix D k σ *ᵥ productVector D k z ∈ rankBudgetSpace D k s
    have hp := copyPermutation_productVector D k σ⁻¹ z
    simp only [inv_inv] at hp
    rw [hp]
    apply productVector_mem_rankBudgetSpace
    calc
      _ ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range z)) := by
        apply Submodule.finrank_mono
        apply Submodule.span_mono
        rintro _ ⟨i,rfl⟩
        exact ⟨σ.symm i,rfl⟩
      _ ≤ s := hz
  exact hle hv

theorem rankBudgetProjector_commutes_copyPermutation (D k s : ℕ)
    (σ : Equiv.Perm (Fin k)) :
    rankBudgetProjector D k s * copyPermutationMatrix D k σ =
      copyPermutationMatrix D k σ * rankBudgetProjector D k s := by
  apply hermitian_projector_commutes_of_invariant
    (rankBudgetProjector D k s) _ (rankBudgetProjector_isHermitian D k s)
  · intro v hv
    apply rankBudgetProjector_fixes
    rwa [rankBudgetProjector_range] at hv
  · intro v hv
    rw [rankBudgetProjector_range] at hv ⊢
    exact copyPermutation_preserves_rankBudgetSpace D k s σ v hv
  · rw [copyPermutationMatrix_star]
    intro v hv
    rw [rankBudgetProjector_range] at hv ⊢
    exact copyPermutation_preserves_rankBudgetSpace D k s σ⁻¹ v hv

theorem rankBudgetProjector_mem_tensorPowerSpan (D k s : ℕ) :
    rankBudgetProjector D k s ∈ tensorPowerSpan D k := by
  apply (mem_tensorPowerSpan_iff_commutes D k _).mpr
  intro σ
  exact (rankBudgetProjector_commutes_copyPermutation D k s σ).symm

theorem rankBudgetProjector_mem_permutationSpan (D k s : ℕ) :
    rankBudgetProjector D k s ∈ permutationSpan D k := by
  apply (mem_permutationSpan_iff_commutes_unitaryTensor D k _).mpr
  intro U
  exact rankBudgetProjector_commutes_tensorMatrix D k s _

theorem rankBudgetProjector_central (D k s : ℕ)
    (M : Matrix (Word D k) (Word D k) ℂ) (hM : M ∈ permutationSpan D k) :
    rankBudgetProjector D k s * M = M * rankBudgetProjector D k s := by
  apply commutes_of_mem_matrix_span _ _ ?_ hM
  rintro _ ⟨σ,rfl⟩
  exact rankBudgetProjector_commutes_copyPermutation D k s σ

/-- Arbitrary selected-position column cutoffs follow by conjugating the
actual prefix cutoff. The intrinsic support projector is permutation central. -/
theorem conjugate_prefixAntisymmetrizer_mul_rankBudgetProjector
    (D l t s : ℕ) (hsl : s < l) (τ : Equiv.Perm (Fin (l+t))) :
    (copyPermutationMatrix D (l+t) τ * prefixAntisymmetrizer D l t *
      (copyPermutationMatrix D (l+t) τ)ᴴ) * rankBudgetProjector D (l+t) s = 0 := by
  rw [copyPermutationMatrix_star]
  simp only [Matrix.mul_assoc]
  rw [← rankBudgetProjector_commutes_copyPermutation]
  rw [← Matrix.mul_assoc (prefixAntisymmetrizer D l t),
    prefixAntisymmetrizer_mul_rankBudgetProjector D l t s hsl,
    Matrix.zero_mul,Matrix.mul_zero]

end
end ExtractionSchur
