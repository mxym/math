import SchurCompletion.CycleCharacter

open scoped BigOperators ComplexOrder
open Matrix

namespace ExtractionSchur

open SymmetricSupport ExtractionSpectrum ExtractionRankSupport

noncomputable section

/-- The original copy-permutation matrices, with arbitrary finite complex coefficients. -/
def permutationCombination (D k : ℕ) (c : Equiv.Perm (Fin k) → ℂ) :
    Matrix (Word D k) (Word D k) ℂ := ∑ σ, c σ • copyPermutationMatrix D k σ

theorem permutationCombination_mem (D k : ℕ) (c : Equiv.Perm (Fin k) → ℂ) :
    permutationCombination D k c ∈ permutationSpan D k := by
  apply Submodule.sum_mem
  intro σ _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ,rfl⟩)

theorem permutationCombination_gram (D k : ℕ) (c : Equiv.Perm (Fin k) → ℂ)
    (σ : Equiv.Perm (Fin k)) :
    ((copyPermutationMatrix D k σ)ᴴ * permutationCombination D k c).trace =
      ∑ τ, c τ * (D : ℂ)^positionCycleCount k (σ⁻¹*τ) := by
  simp only [permutationCombination,Matrix.mul_sum,Matrix.mul_smul,Matrix.trace_sum,
    Matrix.trace_smul,smul_eq_mul,copyPermutation_cycle_gram]

/-- Trace tests by the actual permutation matrices determine every element of
 their span, even when D < k and these generators are linearly dependent. -/
theorem permutationSpan_pairing_ext (D k : ℕ)
    (A B : Matrix (Word D k) (Word D k) ℂ)
    (hA : A ∈ permutationSpan D k) (hB : B ∈ permutationSpan D k)
    (hTest : ∀ σ, (copyPermutationMatrix D k σ * A).trace =
      (copyPermutationMatrix D k σ * B).trace) : A = B := by
  have hAll (C : Matrix (Word D k) (Word D k) ℂ) (hC : C ∈ permutationSpan D k) :
      (C*A).trace = (C*B).trace := by
    change C ∈ Submodule.span ℂ (Set.range (copyPermutationMatrix D k)) at hC
    induction hC using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨σ,rfl⟩ := hx
      exact hTest σ
    | zero => simp
    | add x y hx hy ix iy => simp only [Matrix.add_mul,Matrix.trace_add,ix,iy]
    | smul a x hx ix => simp only [Matrix.smul_mul,Matrix.trace_smul,ix]
  have hZ := Submodule.sub_mem (permutationSpan D k) hA hB
  have ht : ((A-B)ᴴ*(A-B)).trace = 0 := by
    rw [Matrix.mul_sub,Matrix.trace_sub,
      hAll _ (permutationSpan_star_mem D k hZ),sub_self]
  exact sub_eq_zero.mp (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp ht)

/-- A finite Gram system completely characterizes the literal Haar average.
 The Gram matrix is allowed to be singular. No invertibility premise or
 representation-theoretic decomposition is supplied by the caller. -/
theorem flatHaarAverage_eq_combination_iff (D s k : ℕ) (hsD : s ≤ D)
    (c : Equiv.Perm (Fin k) → ℂ) :
    permutationCombination D k c = flatHaarAverage D s k hsD ↔
      ∀ σ, (∑ τ, c τ * (D : ℂ)^positionCycleCount k (σ⁻¹*τ)) =
        ((s : ℝ)^k)⁻¹ • (s : ℂ)^positionCycleCount k σ⁻¹ := by
  constructor
  · intro h σ
    rw [← permutationCombination_gram D k c σ,h,copyPermutationMatrix_star]
    exact flatHaarAverage_permutation_cycle_moment D s k hsD σ⁻¹
  · intro h
    apply permutationSpan_pairing_ext D k _ _ (permutationCombination_mem D k c)
      (haarOrbitAverage_mem_permutationSpan D k _)
    intro σ
    have hh := h σ⁻¹
    rw [← permutationCombination_gram,copyPermutationMatrix_star,inv_inv] at hh
    rw [hh]
    exact (flatHaarAverage_permutation_cycle_moment D s k hsD σ).symm

/-- Coefficients of the actual average exist and solve its explicit cycle Gram
 equations at every D,s,k. The matrix, rather than the possibly nonunique
 coefficient vector, is uniquely specified by these equations. -/
theorem flatHaarAverage_finite_gram_solution (D s k : ℕ) (hsD : s ≤ D) :
    ∃ c : Equiv.Perm (Fin k) → ℂ,
      permutationCombination D k c = flatHaarAverage D s k hsD ∧
      ∀ σ, (∑ τ, c τ * (D : ℂ)^positionCycleCount k (σ⁻¹*τ)) =
        ((s : ℝ)^k)⁻¹ • (s : ℂ)^positionCycleCount k σ⁻¹ := by
  have hm := haarOrbitAverage_mem_permutationSpan D k (flatCoordinateDensity D s hsD)
  change flatHaarAverage D s k hsD ∈
    Submodule.span ℂ (Set.range (copyPermutationMatrix D k)) at hm
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hm
  exact ⟨c,hc,(flatHaarAverage_eq_combination_iff D s k hsD c).mp hc⟩

/-- Literal purity recovered from any solution of the internally derived finite
 Gram equations. This is an exact finite-k identity, not an asymptotic claim. -/
theorem flatHaarAverage_purity_of_gram_solution (D s k : ℕ) (hsD : s ≤ D)
    (c : Equiv.Perm (Fin k) → ℂ)
    (hc : ∀ σ, (∑ τ, c τ * (D : ℂ)^positionCycleCount k (σ⁻¹*τ)) =
        ((s : ℝ)^k)⁻¹ • (s : ℂ)^positionCycleCount k σ⁻¹) :
    (flatHaarAverage D s k hsD * flatHaarAverage D s k hsD).trace =
      ∑ σ, c σ * (((s : ℝ)^k)⁻¹ • (s : ℂ)^positionCycleCount k σ) := by
  have heq := (flatHaarAverage_eq_combination_iff D s k hsD c).mpr hc
  calc
    _ = (permutationCombination D k c * flatHaarAverage D s k hsD).trace := by rw [heq]
    _ = _ := by
      simp only [permutationCombination,Matrix.sum_mul,Matrix.smul_mul,Matrix.trace_sum,
        Matrix.trace_smul,smul_eq_mul,flatHaarAverage_permutation_cycle_moment]

end
end ExtractionSchur
