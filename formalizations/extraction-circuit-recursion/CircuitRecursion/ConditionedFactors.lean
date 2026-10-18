import CircuitRecursion.NormalizedIntertwinerOracle

open scoped Matrix.Norms.L2Operator
open Matrix
namespace CircuitRecursion

def quaternionConjugateOracle (f g : QuaternionOracle) : QuaternionOracle :=
  quaternionOracleMul (quaternionOracleMul f g) (quaternionOracleInverse f)

theorem quaternionConjugateOracle_correct (f g : QuaternionOracle) (U V : SU2)
    (hf : QApproximates f U) (hg : QApproximates g V) :
    QApproximates (quaternionConjugateOracle f g) (U*V*U⁻¹) :=
  quaternionOracleMul_correct _ _ _ _ (quaternionOracleMul_correct _ _ _ _ hf hg)
    (quaternionOracleInverse_correct _ _ hf)

def conditionedConjugatorOracle (f : QuaternionOracle) (t : ℕ) : QuaternionOracle :=
  let g := balancedReferenceOracle f
  let j := chooseChart f g t
  quaternionOracleMul (normalizedIntertwinerOracle f g t j) (frameOracle j)

def conditionedFactorXOracle (f : QuaternionOracle) (t : ℕ) : QuaternionOracle :=
  quaternionConjugateOracle (conditionedConjugatorOracle f t) (referenceXOracle f)

def conditionedFactorYOracle (f : QuaternionOracle) (t : ℕ) : QuaternionOracle :=
  quaternionConjugateOracle (conditionedConjugatorOracle f t) (referenceYOracle f)

/-- The numerical factor programs use only finite rational arithmetic,
integer square roots and finite rational comparisons. Their semantic
commutator and balance properties are proved internally. -/
theorem conditionedFactors_correct (f : QuaternionOracle) (U : SU2)
    (hf : QApproximates f U) (t : ℕ)
    (hσ : (1/2:ℝ)^t≤unitaryDistance (su2AsUnitary U) 1)
    (hd : unitaryDistance (su2AsUnitary U) 1≤1) :
    ∃ A B : SU2,QApproximates (conditionedFactorXOracle f t) A ∧
      QApproximates (conditionedFactorYOracle f t) B ∧
      U=su2Commutator A B ∧
      unitaryDistance (su2AsUnitary A) 1≤Real.sqrt (unitaryDistance (su2AsUnitary U) 1) ∧
      unitaryDistance (su2AsUnitary B) 1≤Real.sqrt (unitaryDistance (su2AsUnitary U) 1) := by
  let V := balancedReference U
  let g := balancedReferenceOracle f
  let j := chooseChart f g t
  have hg : QApproximates g V := balancedReferenceOracle_correct f U hf
  have hscalar : (U.val 0 0).re=(V.val 0 0).re := (balancedReference_scalar U).symm
  have hroot : (1/2:ℝ)^(t+1)≤Real.sqrt (intertwinerMass U V j) :=
    chooseChart_denominator f g U V hf hg hscalar t hσ hd
  have hp : 0 < intertwinerMass U V j := Real.sqrt_pos.mp
    (lt_of_lt_of_le (by positivity : (0:ℝ)<(1/2)^(t+1)) hroot)
  let P : SU2 := normalizedIntertwiner U V j hp*conjugacyFrame j
  have hPoracle : QApproximates (conditionedConjugatorOracle f t) P :=
    quaternionOracleMul_correct _ _ _ _
      (normalizedIntertwinerOracle_correct f g U V hf hg t j hp hroot) (frameOracle_correct j)
  have hP : su2AsUnitary P=chartConjugator U V j hp := by
    simp only [P,su2AsUnitary_mul,normalizedIntertwiner,chartConjugator]
    exact congrArg (fun Q : Matrix.unitaryGroup (Fin 2) ℂ => Q*su2AsUnitary (conjugacyFrame j))
      (normalizedQuaternionSU2_unitary _ _ hp)
  have hact : su2AsUnitary U=su2AsUnitary P*su2AsUnitary V*star (su2AsUnitary P) := by
    rw [hP]
    exact chartConjugator_action U V j hscalar hp
  let A := P*referenceX U*P⁻¹
  let B := P*referenceY U*P⁻¹
  have hA : su2AsUnitary A=su2AsUnitary P*su2AsUnitary (referenceX U)*star (su2AsUnitary P) := by
    simp only [A,su2AsUnitary_mul,su2AsUnitary_inv,Unitary.star_eq_inv]
  have hB : su2AsUnitary B=su2AsUnitary P*su2AsUnitary (referenceY U)*star (su2AsUnitary P) := by
    simp only [B,su2AsUnitary_mul,su2AsUnitary_inv,Unitary.star_eq_inv]
  have hcomm : su2AsUnitary (su2Commutator A B)=
      su2AsUnitary P*su2AsUnitary V*star (su2AsUnitary P) := by
    rw [su2Commutator_unitary,hA,hB,unitaryCommutator_conjugate]
    rfl
  refine ⟨A,B,?_,?_,?_,?_,?_⟩
  · exact quaternionConjugateOracle_correct _ _ _ _ hPoracle (referenceXOracle_correct f U hf)
  · exact quaternionConjugateOracle_correct _ _ _ _ hPoracle (referenceYOracle_correct f U hf)
  · apply Subtype.ext
    exact congrArg (fun Q : Matrix.unitaryGroup (Fin 2) ℂ => Q.val) (hact.trans hcomm.symm)
  · rw [hA,unitaryDistance_conjugate_one]
    exact referenceX_distance U
  · rw [hB,unitaryDistance_conjugate_one]
    exact referenceY_distance U

end CircuitRecursion
