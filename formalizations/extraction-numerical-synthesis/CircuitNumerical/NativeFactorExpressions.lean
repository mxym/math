import CircuitNumerical.NativeOracleExpressions

namespace CircuitRecursion

def nativeExpressionBalancedS (f : NativePacketExpressionOracle) : NativeScalarExpressionOracle :=
  nativeExpressionSqrt (nativeExpressionSqrt (nativeExpressionMeanMinus (nativeExpressionCoordinate f 0)))
def nativeExpressionBalancedC (f : NativePacketExpressionOracle) : NativeScalarExpressionOracle :=
  nativeExpressionSqrt (nativeExpressionAdd (fun _ => .literal wordScalarOne)
    (nativeExpressionNeg (nativeExpressionMul 0 (nativeExpressionBalancedS f) (nativeExpressionBalancedS f))))
def nativeExpressionReferenceX (f : NativePacketExpressionOracle) : NativePacketExpressionOracle :=
  nativeExpressionTuple ![nativeExpressionBalancedC f,(fun _ => .literal wordScalarZero),(fun _ => .literal wordScalarZero),nativeExpressionBalancedS f]
def nativeExpressionReferenceY (f : NativePacketExpressionOracle) : NativePacketExpressionOracle :=
  nativeExpressionTuple ![nativeExpressionBalancedC f,(fun _ => .literal wordScalarZero),nativeExpressionBalancedS f,(fun _ => .literal wordScalarZero)]
def nativeExpressionBalancedReference (f : NativePacketExpressionOracle) : NativePacketExpressionOracle :=
  nativeExpressionPacketMul
    (nativeExpressionPacketMul (nativeExpressionPacketMul (nativeExpressionReferenceX f) (nativeExpressionReferenceY f))
      (nativeExpressionPacketInverse (nativeExpressionReferenceX f)))
    (nativeExpressionPacketInverse (nativeExpressionReferenceY f))
def nativeExpressionChartTarget (f : NativePacketExpressionOracle) (j : Fin 4) : NativePacketExpressionOracle :=
  nativeExpressionPacketMul (nativeExpressionPacketMul (nativeExpressionFrame j) f)
    (nativeExpressionPacketInverse (nativeExpressionFrame j))
def nativeExpressionChartMass (f g : NativePacketExpressionOracle) (p : ℕ) (j : Fin 4) : NativeScalarExpression :=
  nativeExpressionDistance f (nativeExpressionPacketInverse (nativeExpressionChartTarget g j)) p
def nativeExpressionRadius (f g : NativePacketExpressionOracle) (j : Fin 4) : NativeScalarExpressionOracle :=
  nativeExpressionSqrt (fun p => nativeExpressionChartMass f g p j)
def nativeExpressionNormalized (f g : NativePacketExpressionOracle) (t : ℕ) (j : Fin 4) : NativePacketExpressionOracle :=
  let radiusInv := nativeExpressionInv (t+1) (nativeExpressionRadius f g j)
  let adjoint := nativeExpressionPacketInverse (nativeExpressionChartTarget g j)
  nativeExpressionTuple (fun i => nativeExpressionMul (t+2)
    (nativeExpressionAdd (nativeExpressionCoordinate f i) (nativeExpressionNeg (nativeExpressionCoordinate adjoint i))) radiusInv)
def nativeExpressionConjugator (f : NativePacketExpressionOracle) (t : ℕ) : NativePacketExpressionOracle :=
  let g := nativeExpressionBalancedReference f
  nativeExpressionSelectMax (nativeExpressionChartMass f g (2*t+2))
    (fun j => nativeExpressionPacketMul (nativeExpressionNormalized f g t j) (nativeExpressionFrame j))
def nativeExpressionConjugate (f g : NativePacketExpressionOracle) : NativePacketExpressionOracle :=
  nativeExpressionPacketMul (nativeExpressionPacketMul f g) (nativeExpressionPacketInverse f)
def nativeExpressionFactorX (f : NativePacketExpressionOracle) (t : ℕ) : NativePacketExpressionOracle :=
  nativeExpressionConjugate (nativeExpressionConjugator f t) (nativeExpressionReferenceX f)
def nativeExpressionFactorY (f : NativePacketExpressionOracle) (t : ℕ) : NativePacketExpressionOracle :=
  nativeExpressionConjugate (nativeExpressionConjugator f t) (nativeExpressionReferenceY f)

@[simp] theorem nativeExpressionBalancedS_eval (f : NativePacketExpressionOracle) :
    evaluateNativeScalarOracle (nativeExpressionBalancedS f)=balancedSOracle (evaluateNativePacketOracle f) := by
  simp only [nativeExpressionBalancedS,nativeExpressionSqrt_eval,nativeExpressionMeanMinus_eval,nativeExpressionCoordinate_eval]
  rfl
@[simp] theorem nativeExpressionBalancedC_eval (f : NativePacketExpressionOracle) :
    evaluateNativeScalarOracle (nativeExpressionBalancedC f)=balancedCOracle (evaluateNativePacketOracle f) := by
  simp only [nativeExpressionBalancedC,nativeExpressionSqrt_eval,nativeExpressionAdd_eval,evaluateNativeScalarOne,
    nativeExpressionNeg_eval,nativeExpressionMul_eval,nativeExpressionBalancedS_eval]
  rfl
@[simp] theorem nativeExpressionReferenceX_eval (f : NativePacketExpressionOracle) :
    evaluateNativePacketOracle (nativeExpressionReferenceX f)=referenceXOracle (evaluateNativePacketOracle f) := by
  simp only [nativeExpressionReferenceX,nativeExpressionTuple_eval]
  funext p
  apply List.Vector.ext
  intro i
  fin_cases i
  · exact congrFun (nativeExpressionBalancedC_eval f) p
  · exact nativeScalarZero_eval
  · exact nativeScalarZero_eval
  · exact congrFun (nativeExpressionBalancedS_eval f) p
@[simp] theorem nativeExpressionReferenceY_eval (f : NativePacketExpressionOracle) :
    evaluateNativePacketOracle (nativeExpressionReferenceY f)=referenceYOracle (evaluateNativePacketOracle f) := by
  simp only [nativeExpressionReferenceY,nativeExpressionTuple_eval]
  funext p
  apply List.Vector.ext
  intro i
  fin_cases i
  · exact congrFun (nativeExpressionBalancedC_eval f) p
  · exact nativeScalarZero_eval
  · exact congrFun (nativeExpressionBalancedS_eval f) p
  · exact nativeScalarZero_eval
@[simp] theorem nativeExpressionBalancedReference_eval (f : NativePacketExpressionOracle) :
    evaluateNativePacketOracle (nativeExpressionBalancedReference f)=balancedReferenceOracle (evaluateNativePacketOracle f) := by
  simp only [nativeExpressionBalancedReference,nativeExpressionPacketMul_eval,nativeExpressionPacketInverse_eval,
    nativeExpressionReferenceX_eval,nativeExpressionReferenceY_eval]
  rfl
@[simp] theorem nativeExpressionChartTarget_eval (f : NativePacketExpressionOracle) (j : Fin 4) :
    evaluateNativePacketOracle (nativeExpressionChartTarget f j)=chartTargetOracle (evaluateNativePacketOracle f) j := by
  simp only [nativeExpressionChartTarget,nativeExpressionPacketMul_eval,nativeExpressionPacketInverse_eval,nativeExpressionFrame_eval]
  rfl
@[simp] theorem nativeExpressionChartMass_eval (f g : NativePacketExpressionOracle) (p : ℕ) (j : Fin 4) :
    (nativeExpressionChartMass f g p j).interpret.eval=chartMassScore (evaluateNativePacketOracle f) (evaluateNativePacketOracle g) p j := by
  simp only [nativeExpressionChartMass,nativeExpressionDistance_eval,nativeExpressionPacketInverse_eval,nativeExpressionChartTarget_eval]
  rfl
@[simp] theorem nativeExpressionRadius_eval (f g : NativePacketExpressionOracle) (j : Fin 4) :
    evaluateNativeScalarOracle (nativeExpressionRadius f g j)=intertwinerRadiusOracle (evaluateNativePacketOracle f) (evaluateNativePacketOracle g) j := by
  have h : evaluateNativeScalarOracle (fun p => nativeExpressionChartMass f g p j)=
      (fun p => chartMassScore (evaluateNativePacketOracle f) (evaluateNativePacketOracle g) p j) :=
    funext (fun p => nativeExpressionChartMass_eval f g p j)
  simp only [nativeExpressionRadius,nativeExpressionSqrt_eval,h]
  rfl
@[simp] theorem nativeExpressionNormalized_eval (f g : NativePacketExpressionOracle) (t : ℕ) (j : Fin 4) :
    evaluateNativePacketOracle (nativeExpressionNormalized f g t j)=
      normalizedIntertwinerOracle (evaluateNativePacketOracle f) (evaluateNativePacketOracle g) t j := by
  simp only [nativeExpressionNormalized,nativeExpressionTuple_eval,nativeExpressionMul_eval,nativeExpressionAdd_eval,
    nativeExpressionCoordinate_eval,nativeExpressionNeg_eval,nativeExpressionInv_eval,nativeExpressionRadius_eval,
    nativeExpressionPacketInverse_eval,nativeExpressionChartTarget_eval]
  rfl
@[simp] theorem nativeExpressionConjugator_eval (f : NativePacketExpressionOracle) (t : ℕ) :
    evaluateNativePacketOracle (nativeExpressionConjugator f t)=conditionedConjugatorOracle (evaluateNativePacketOracle f) t := by
  simp only [nativeExpressionConjugator,nativeExpressionSelectMax_eval,nativeExpressionChartMass_eval,
    nativeExpressionBalancedReference_eval,nativeExpressionPacketMul_eval,nativeExpressionNormalized_eval,nativeExpressionFrame_eval]
  rfl
@[simp] theorem nativeExpressionConjugate_eval (f g : NativePacketExpressionOracle) :
    evaluateNativePacketOracle (nativeExpressionConjugate f g)=quaternionConjugateOracle (evaluateNativePacketOracle f) (evaluateNativePacketOracle g) := by
  simp only [nativeExpressionConjugate,nativeExpressionPacketMul_eval,nativeExpressionPacketInverse_eval]
  rfl
@[simp] theorem nativeExpressionFactorX_eval (f : NativePacketExpressionOracle) (t : ℕ) :
    evaluateNativePacketOracle (nativeExpressionFactorX f t)=conditionedFactorXOracle (evaluateNativePacketOracle f) t := by
  simp only [nativeExpressionFactorX,nativeExpressionConjugate_eval,nativeExpressionConjugator_eval,nativeExpressionReferenceX_eval]
  rfl
@[simp] theorem nativeExpressionFactorY_eval (f : NativePacketExpressionOracle) (t : ℕ) :
    evaluateNativePacketOracle (nativeExpressionFactorY f t)=conditionedFactorYOracle (evaluateNativePacketOracle f) t := by
  simp only [nativeExpressionFactorY,nativeExpressionConjugate_eval,nativeExpressionConjugator_eval,nativeExpressionReferenceY_eval]
  rfl

end CircuitRecursion
