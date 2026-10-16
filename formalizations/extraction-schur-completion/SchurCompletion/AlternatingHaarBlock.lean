import SchurCompletion.AlternatingReynolds

open scoped BigOperators ComplexOrder
open Matrix

namespace ExtractionSchur

open SymmetricSupport ExtractionSpectrum ExtractionRankSupport

noncomputable section

theorem copyPermutation_mul_tensorAntisymmetrizer (D k : ℕ) (σ : Equiv.Perm (Fin k)) :
    copyPermutationMatrix D k σ * tensorAntisymmetrizer D k =
      (Equiv.Perm.sign σ : ℤ) • tensorAntisymmetrizer D k := by
  have h := congrArg Matrix.conjTranspose (tensorAntisymmetrizer_mul_copyPermutation D k σ⁻¹)
  simpa only [Matrix.conjTranspose_mul,Matrix.conjTranspose_smul,star_trivial,
    (tensorAntisymmetrizer_hermitian D k).eq,copyPermutationMatrix_star,inv_inv,
    Equiv.Perm.sign_inv] using h

theorem copyPermutation_mul_alternatingProjector (D k : ℕ) (σ : Equiv.Perm (Fin k)) :
    copyPermutationMatrix D k σ * alternatingProjector D k =
      (Equiv.Perm.sign σ : ℤ) • alternatingProjector D k := by
  rw [alternatingProjector,Matrix.mul_smul,copyPermutation_mul_tensorAntisymmetrizer,smul_comm]

theorem alternatingProjector_mem_permutationSpan (D k : ℕ) :
    alternatingProjector D k ∈ permutationSpan D k := by
  rw [alternatingProjector,tensorAntisymmetrizer]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro σ _
  rw [← Int.cast_smul_eq_zsmul ℂ]
  exact Submodule.smul_mem (permutationSpan D k) _ (Submodule.subset_span ⟨σ⁻¹,rfl⟩)

theorem permutationSpan_alternating_scalar (D k : ℕ)
    (A : Matrix (Word D k) (Word D k) ℂ) (hA : A ∈ permutationSpan D k) :
    ∃ a : ℂ, A * alternatingProjector D k = a • alternatingProjector D k := by
  change A ∈ Submodule.span ℂ (Set.range (copyPermutationMatrix D k)) at hA
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hA
  refine ⟨∑ σ, c σ * (Equiv.Perm.sign σ : ℤ), ?_⟩
  rw [← hc]
  simp only [Matrix.sum_mul,Matrix.smul_mul,copyPermutation_mul_alternatingProjector,
    Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro σ _
  rw [← Int.cast_smul_eq_zsmul ℂ,smul_smul]

theorem flatCoordinateDensity_alternating_moment (D s k : ℕ) (hsD : s ≤ D) :
    (alternatingProjector D k * tensorMatrix (flatCoordinateDensity D s hsD) k).trace =
      ((s : ℝ)^k)⁻¹ • (s.choose k : ℂ) := by
  calc
    _ = ((s : ℝ)^k)⁻¹ • (alternatingProjector s k).trace := by
      simp only [alternatingProjector,tensorAntisymmetrizer,Matrix.smul_mul,Matrix.sum_mul,
        Matrix.trace_smul,Matrix.trace_sum,flatCoordinateDensity_permutation_moment,
        copyPermutation_trace]
      rw [smul_comm ((s : ℝ)^k)⁻¹]
      congr 1
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      exact smul_comm _ _ _
    _ = _ := by rw [alternatingProjector_trace_choose]

theorem flatHaarAverage_alternating_moment (D s k : ℕ) (hsD : s ≤ D) :
    (alternatingProjector D k * flatHaarAverage D s k hsD).trace =
      ((s : ℝ)^k)⁻¹ • (s.choose k : ℂ) := by
  rw [flatHaarAverage,haarOrbitAverage_eq_haarTwirl,
    haarTwirl_pairing D k _ _ (alternatingProjector_mem_permutationSpan D k)]
  exact flatCoordinateDensity_alternating_moment D s k hsD

/-- Actual one-column Schur block of the literal Haar average: its binomial
 dimension and the finite-k Weyl ratio have both been proved on tensor coordinates. -/
theorem flatHaarAverage_alternating_block (D s k : ℕ) (hkd : k ≤ D) (hsD : s ≤ D) :
    flatHaarAverage D s k hsD * alternatingProjector D k =
      ((((s : ℝ)^k)⁻¹ • (s.choose k : ℂ)) / (D.choose k : ℂ)) • alternatingProjector D k := by
  obtain ⟨a,ha⟩ := permutationSpan_alternating_scalar D k _
    (haarOrbitAverage_mem_permutationSpan D k (flatCoordinateDensity D s hsD))
  have hn : (D.choose k : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hkd)
  have ht := congrArg Matrix.trace ha
  change (flatHaarAverage D s k hsD * alternatingProjector D k).trace = _ at ht
  rw [Matrix.trace_mul_comm,flatHaarAverage_alternating_moment,Matrix.trace_smul,
    alternatingProjector_trace_choose,smul_eq_mul] at ht
  rw [(eq_div_iff hn).mpr ht.symm] at ha
  exact ha

end
end ExtractionSchur
