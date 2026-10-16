import SchurCompletion.CycleCentral

open scoped BigOperators ComplexOrder
open Matrix

namespace ExtractionSchur

open SymmetricSupport ExtractionSpectrum ExtractionRankSupport

noncomputable section

theorem cycleOperator_self_posDef (D k : ℕ) : (cycleOperator D D k).PosDef := by
  apply (cycleOperator_posSemidef D D k).posDef_iff_isUnit.mpr
  exact (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (cycleOperator_self_det_ne_zero D k))

/-- Every actual nonzero joint eigenvector has a nonzero ambient denominator.
 This is deduced from the internally proved matrix invertibility. -/
theorem jointCycle_denominator_ne_zero (D k : ℕ) (v : Word D k → ℂ) (hv : v ≠ 0)
    (χ : ℕ → ℂ) (he : ∀ t, cycleOperator D t k *ᵥ v = χ t • v) : χ D ≠ 0 := by
  intro hz
  have h0 : cycleOperator D D k *ᵥ v = 0 := by rw [he D,hz,zero_smul]
  have hU : IsUnit (cycleOperator D D k) := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (cycleOperator_self_det_ne_zero D k))
  apply hv
  apply Matrix.mulVec_injective_of_isUnit hU
  simpa only [Matrix.mulVec_zero] using h0

/-- Exact eigenvalue ratio on every actual joint eigenspace. All matrices and
 Haar averages are literal coordinate objects. Only the choice of a joint
 vector is quantified; no spectrum or dimension formula is assumed. -/
theorem flatHaarAverage_jointCycle_eigenvalue (D s k : ℕ) (hsD : s ≤ D)
    (v : Word D k → ℂ) (hv : v ≠ 0) (χ : ℕ → ℂ)
    (he : ∀ t, cycleOperator D t k *ᵥ v = χ t • v) :
    flatHaarAverage D s k hsD *ᵥ v =
      (((s : ℂ)^k)⁻¹ * (χ s / χ D)) • v := by
  have hd := jointCycle_denominator_ne_zero D k v hv χ he
  have hm := congrArg (fun A => A *ᵥ v) (flatHaarAverage_mul_cycleOperator D s k hsD)
  rw [← Matrix.mulVec_mulVec,he D,Matrix.mulVec_smul,Matrix.smul_mulVec,he s] at hm
  calc
    _ = (χ D)⁻¹ • (χ D • (flatHaarAverage D s k hsD *ᵥ v)) := by
      rw [← mul_smul,inv_mul_cancel₀ hd,one_smul]
    _ = (χ D)⁻¹ • (((s : ℂ)^k)⁻¹ • (χ s • v)) := by rw [hm]
    _ = _ := by
      simp only [← mul_smul,div_eq_mul_inv]
      congr 1
      ring

/-- The full positive cycle matrix has no kernel. -/
theorem cycleOperator_self_kernel_eq_bot (D k : ℕ) :
    LinearMap.ker (cycleOperator D D k).mulVecLin = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  exact Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (cycleOperator_self_det_ne_zero D k)))

end
end ExtractionSchur
