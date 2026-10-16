import SymmetricSupport.UnitSpan

open scoped BigOperators ComplexOrder
open Matrix

namespace SymmetricSupport

noncomputable section

/-- An actual effect with unit expectation fixes the actual input vector. -/
theorem unit_effect_fixes_purePower (D k : ℕ)
    (M : Matrix (Word D k) (Word D k) ℂ) (hM : (1 - M).PosSemidef)
    (z : Fin D → ℂ) (hz : IsUnitVector z)
    (hfit : (M * purePowerDensity D k z).trace.re = 1) :
    M.mulVec (purePower D k z) = purePower D k z := by
  classical
  let v := purePower D k z
  let Q := 1 - M
  have ht : (Q * purePowerDensity D k z).trace.re = 0 := by
    simp only [Q, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re,
      unitVector_trace D k z hz, Complex.one_re, hfit, sub_self]
  have hq : (Q * purePowerDensity D k z).trace = star v ⬝ᵥ Q.mulVec v := by
    rw [purePowerDensity, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
    exact dotProduct_comm _ _
  rw [hq] at ht
  have hnonneg : 0 ≤ star v ⬝ᵥ Q.mulVec v := hM.dotProduct_mulVec_nonneg v
  have him : (star v ⬝ᵥ Q.mulVec v).im = 0 := (Complex.nonneg_iff.mp hnonneg).2.symm
  have hzero : star v ⬝ᵥ Q.mulVec v = 0 := Complex.ext ht him
  have hv : Q.mulVec v = 0 := hM.dotProduct_mulVec_zero_iff.mp hzero
  change (1 - M).mulVec v = 0 at hv
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hv
  exact (sub_eq_zero.mp hv).symm

/-- Perfect performance on normalized pure iid inputs forces identity on their whole
common support. No Haar formula or caller-provided support spanning premise is used. -/
theorem exact_unitPurePower_effect_mul_symmetricProjector (D k : ℕ) (hD : 0 < D)
    (M : Matrix (Word D k) (Word D k) ℂ) (hM : (1 - M).PosSemidef)
    (hfit : ∀ z : Fin D → ℂ, IsUnitVector z →
      (M * purePowerDensity D k z).trace.re = 1) :
    M * symmetricProjector D k = symmetricProjector D k := by
  apply fixes_unitPurePower_mul_symmetricProjector D k hD M
  intro z hz
  exact unit_effect_fixes_purePower D k M hM z hz (hfit z hz)

end
end SymmetricSupport
