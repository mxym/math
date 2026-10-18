import CircuitRecursion.WireNorm
import Mathlib.Analysis.Complex.Polynomial.Basic

open scoped Matrix.Norms.L2Operator
open Matrix CircuitCompletion
namespace CircuitRecursion

theorem unitary_two_phase_special (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ (c : ℂ) (_ : Complex.normSq c=1) (V : SU2),U.val=c • V.val := by
  let d := U.val.det
  have hdunit : star d*d=1 := (Matrix.det_of_mem_unitary U.property).1
  have hd : Complex.normSq d=1 := by
    have ht := congrArg Complex.re hdunit
    simpa [Complex.normSq_apply,Complex.mul_re] using ht
  obtain ⟨c,hroot⟩ := IsAlgClosed.exists_pow_nat_eq d (by decide : 0<2)
  have hc : Complex.normSq c=1 := by
    have ht := congrArg Complex.normSq hroot
    simp only [map_pow,hd] at ht
    nlinarith [Complex.normSq_nonneg c]
  have hc0 : c≠0 := by intro h; simp [h] at hc
  have hci : Complex.normSq c⁻¹=1 := by simp only [map_inv₀,hc,inv_one]
  let W := phaseUnitary c⁻¹ hci U
  have hdet : W.val.det=1 := by
    change (c⁻¹ • U.val).det=1
    rw [Matrix.det_smul,Fintype.card_fin]
    change c⁻¹^2*d=1
    rw [← hroot]
    field_simp
  let V : SU2 := ⟨W.val,W.property,hdet⟩
  refine ⟨c,hc,V,?_⟩
  change U.val=c • (c⁻¹ • U.val)
  rw [smul_smul,mul_inv_cancel₀ hc0,one_smul]

/-- Every physical one-qubit unitary has an SU(2) representative in the
fixed Fin2/Bool coordinates, with an explicitly harmless unit-modulus phase. -/
theorem qubit_phase_special (U : Matrix.unitaryGroup Bool ℂ) :
    ∃ (c : ℂ) (_ : Complex.normSq c=1) (V : SU2),
      (U : Matrix Bool Bool ℂ)=c • (su2ToBool V : Matrix Bool Bool ℂ) := by
  let W := reindexUnitary finTwoEquiv.symm U
  obtain ⟨c,hc,V,he⟩ := unitary_two_phase_special W
  refine ⟨c,hc,V,?_⟩
  have ht := congrArg (fun A => Matrix.reindexAlgEquiv ℂ ℂ finTwoEquiv A) he
  rw [map_smul] at ht
  convert ht using 1
  · ext i j
    simp [W,reindexUnitary,Matrix.coe_reindexAlgEquiv,Matrix.reindex_apply,Matrix.submatrix_apply]
  · rfl

end CircuitRecursion
