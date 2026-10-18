import SchurCompletion.CycleFrame

open scoped BigOperators ComplexOrder
open Matrix

namespace ExtractionSchur

open SymmetricSupport ExtractionSpectrum ExtractionRankSupport

noncomputable section

theorem permutationFrame_flatHaarAverage (D s k : ℕ) (hsD : s ≤ D) :
    permutationFrame D k (flatHaarAverage D s k hsD) =
      ((s : ℂ)^k)⁻¹ • cycleOperator D s k := by
  change (∑ σ, ((copyPermutationMatrix D k σ)ᴴ * flatHaarAverage D s k hsD).trace •
    copyPermutationMatrix D k σ) = _
  calc
    _ = ∑ τ : Equiv.Perm (Fin k),
        ((copyPermutationMatrix D k τ⁻¹)ᴴ * flatHaarAverage D s k hsD).trace •
          copyPermutationMatrix D k τ⁻¹ :=
      (Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin k))) _).symm
    _ = _ := by
      simp only [copyPermutationMatrix_star,inv_inv,flatHaarAverage_permutation_cycle_moment,
        cycleOperator,Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro τ _
      rw [RCLike.real_smul_eq_coe_mul,RCLike.ofReal_inv,RCLike.ofReal_pow,RCLike.ofReal_natCast,mul_smul]

/-- Actual finite-dimensional Haar normal equation, proved for the genuine
 average and internally constructed cycle operators. -/
theorem flatHaarAverage_mul_cycleOperator (D s k : ℕ) (hsD : s ≤ D) :
    flatHaarAverage D s k hsD * cycleOperator D D k =
      ((s : ℂ)^k)⁻¹ • cycleOperator D s k := by
  have hm : flatHaarAverage D s k hsD ∈ permutationSpan D k :=
    haarOrbitAverage_mem_permutationSpan D k (flatCoordinateDensity D s hsD)
  rw [← permutationFrame_eq_mul_cycleOperator D k (flatHaarAverage D s k hsD) hm]
  exact permutationFrame_flatHaarAverage D s k hsD

/-- A literal matrix ratio formula for the genuine Haar orbit average. The
 denominator's invertibility is proved internally for every D,k; no Schur
 spectrum, asymptotic formula, or invertible Gram certificate is assumed. -/
theorem flatHaarAverage_cycle_ratio (D s k : ℕ) (hsD : s ≤ D) :
    flatHaarAverage D s k hsD =
      ((s : ℂ)^k)⁻¹ • (cycleOperator D s k * (cycleOperator D D k)⁻¹) := by
  have h := congrArg (fun A => A * (cycleOperator D D k)⁻¹)
    (flatHaarAverage_mul_cycleOperator D s k hsD)
  rw [Matrix.mul_assoc,Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (cycleOperator_self_det_ne_zero D k)),Matrix.mul_one,
    Matrix.smul_mul] at h
  exact h

/-- The support rank of the explicit cycle-character matrix equals the actual
 minimal rank-budget support rank, for all physical rank budgets and all k. -/
theorem cycleOperator_rank_eq_rankBudget (D s k : ℕ) (hs : 0 < s) (hsD : s ≤ D) :
    (cycleOperator D s k).rank = (rankBudgetProjector D k s).rank := by
  have h := congrArg Matrix.rank (flatHaarAverage_mul_cycleOperator D s k hsD)
  rw [Matrix.rank_mul_eq_left_of_det_ne_zero _ _ (cycleOperator_self_det_ne_zero D k),
    Matrix.rank_smul_of_mem_nonZeroDivisors] at h
  · exact h.symm.trans (flatHaarAverage_rank D s k hs hsD)
  · apply mem_nonZeroDivisors_iff_ne_zero.mpr
    apply inv_ne_zero
    apply pow_ne_zero
    exact_mod_cast Nat.ne_of_gt hs

/-- Exact purity expressed solely through the two explicit finite cycle
 operators. This is the unclassified matrix counterpart of the Weyl-ratio
 formula; its sharp asymptotic still requires spectral analysis. -/
theorem flatHaarAverage_purity_cycle_ratio (D s k : ℕ) (hsD : s ≤ D) :
    (flatHaarAverage D s k hsD * flatHaarAverage D s k hsD).trace =
      (((s : ℂ)^k)⁻¹)^2 *
        ((cycleOperator D s k * (cycleOperator D D k)⁻¹) *
          (cycleOperator D s k * (cycleOperator D D k)⁻¹)).trace := by
  rw [flatHaarAverage_cycle_ratio]
  simp only [Matrix.smul_mul,Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul]
  ring

end
end ExtractionSchur
