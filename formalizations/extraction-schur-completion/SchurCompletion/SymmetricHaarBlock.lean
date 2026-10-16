import SchurCompletion.SymmetricReynolds

open scoped BigOperators ComplexOrder
open Matrix

namespace ExtractionSchur

open SymmetricSupport ExtractionSpectrum ExtractionRankSupport

noncomputable section

theorem permutationSpan_symmetric_scalar (D k : ℕ)
    (A : Matrix (Word D k) (Word D k) ℂ) (hA : A ∈ permutationSpan D k) :
    ∃ a : ℂ, A * symmetricProjector D k = a • symmetricProjector D k := by
  change A ∈ Submodule.span ℂ (Set.range (copyPermutationMatrix D k)) at hA
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hA
  refine ⟨∑ σ, c σ, ?_⟩
  rw [← hc]
  simp only [Matrix.sum_mul,Matrix.smul_mul,copyPermutation_mul_symmetricProjector,
    Finset.sum_smul]

theorem flatCoordinateDensity_symmetric_moment (D s k : ℕ) (hsD : s ≤ D) :
    (symmetricProjector D k * tensorMatrix (flatCoordinateDensity D s hsD) k).trace =
      ((s : ℝ)^k)⁻¹ • ((s+k-1).choose k : ℂ) := by
  calc
    _ = ((s : ℝ)^k)⁻¹ • (symmetricProjector s k).trace := by
      rw [symmetricProjector_eq_copyPermutationAverage D k,
        symmetricProjector_eq_copyPermutationAverage s k]
      simp only [copyPermutationAverage,Matrix.smul_mul,Matrix.sum_mul,Matrix.trace_smul,
        Matrix.trace_sum,flatCoordinateDensity_permutation_moment,copyPermutation_trace]
      rw [← Finset.smul_sum,smul_comm]
    _ = _ := by rw [symmetricProjector_trace_choose]

theorem flatHaarAverage_symmetric_moment (D s k : ℕ) (hsD : s ≤ D) :
    (symmetricProjector D k * flatHaarAverage D s k hsD).trace =
      ((s : ℝ)^k)⁻¹ • ((s+k-1).choose k : ℂ) := by
  rw [flatHaarAverage,haarOrbitAverage_eq_haarTwirl,
    haarTwirl_pairing D k _ _ (symmetricProjector_mem_permutationSpan D k)]
  exact flatCoordinateDensity_symmetric_moment D s k hsD

/-- Actual one-row Schur block of the literal rank-s Haar average, including
 every finite k. Its dimension and scalar action are both derived internally. -/
theorem flatHaarAverage_symmetric_block (D s k : ℕ) (hD : 0 < D) (hsD : s ≤ D) :
    flatHaarAverage D s k hsD * symmetricProjector D k =
      ((((s : ℝ)^k)⁻¹ • ((s+k-1).choose k : ℂ)) / ((D+k-1).choose k : ℂ)) •
        symmetricProjector D k := by
  obtain ⟨a,ha⟩ := permutationSpan_symmetric_scalar D k _
    (haarOrbitAverage_mem_permutationSpan D k (flatCoordinateDensity D s hsD))
  have hn : ((D+k-1).choose k : ℂ) ≠ 0 := by
    have hc := occupation_card_pos D k hD
    rw [Sym.card_sym_eq_choose,Fintype.card_fin] at hc
    exact_mod_cast Nat.ne_of_gt hc
  have ht := congrArg Matrix.trace ha
  change (flatHaarAverage D s k hsD * symmetricProjector D k).trace = _ at ht
  rw [Matrix.trace_mul_comm,flatHaarAverage_symmetric_moment,Matrix.trace_smul,
    symmetricProjector_trace_choose,smul_eq_mul] at ht
  have heq : a = (((s : ℝ)^k)⁻¹ • ((s+k-1).choose k : ℂ)) / ((D+k-1).choose k : ℂ) := by
    exact (eq_div_iff hn).mpr ht.symm
  rw [heq] at ha
  exact ha

/-- The genuine normalized unitary Haar average of a flat rank-one input is
 exactly the pre-existing occupation state, not merely a state with the same
 support dimension. -/
theorem flatHaarAverage_one_eq_symmetricState (D k : ℕ) (hD : 0 < D) :
    flatHaarAverage D 1 k (by omega) = symmetricState D k := by
  have hD1 : 1 ≤ D := by omega
  have hs := haarOrbitAverage_common_support D k (flatCoordinateDensity D 1 hD1)
  rw [flatCoordinateDensity_rank D 1 (by omega) hD1,
    rankBudgetProjector_one_eq_symmetricProjector] at hs
  have hΩ := (flatHaarAverage_density D 1 k (by omega) hD1).1.isHermitian
  have hRight := congrArg Matrix.conjTranspose hs
  change (symmetricProjector D k * flatHaarAverage D 1 k hD1)ᴴ =
    (flatHaarAverage D 1 k hD1)ᴴ at hRight
  change flatHaarAverage D 1 k hD1 = _
  have hr : flatHaarAverage D 1 k hD1 * symmetricProjector D k =
      flatHaarAverage D 1 k hD1 := by
    simpa only [Matrix.conjTranspose_mul,(symmetricProjector_hermitian D k).eq,hΩ.eq]
      using hRight
  rw [← hr,flatHaarAverage_symmetric_block D 1 k hD hD1]
  simp only [one_pow,inv_one,one_smul,Nat.one_add,Nat.add_sub_cancel,Nat.choose_self,
    Nat.cast_one,one_div,symmetricState]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  congr 1
  simp [Sym.card_sym_eq_choose,Nat.add_comm]

end
end ExtractionSchur
