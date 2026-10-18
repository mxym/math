import CircuitRecursion.ArithmeticExpressions

namespace CircuitRecursion

def expressionBalancedS (f : PacketExpressionOracle) : ScalarExpressionOracle :=
  expressionSqrt (expressionSqrt (expressionMeanMinus (expressionCoordinate f 0)))
def expressionBalancedC (f : PacketExpressionOracle) : ScalarExpressionOracle :=
  expressionSqrt (expressionAdd (fun _ => .literal 1)
    (expressionNeg (expressionMul 0 (expressionBalancedS f) (expressionBalancedS f))))
def expressionReferenceX (f : PacketExpressionOracle) : PacketExpressionOracle := fun p =>
  .tuple ![expressionBalancedC f p,.literal 0,.literal 0,expressionBalancedS f p]
def expressionReferenceY (f : PacketExpressionOracle) : PacketExpressionOracle := fun p =>
  .tuple ![expressionBalancedC f p,.literal 0,expressionBalancedS f p,.literal 0]
def expressionBalancedReference (f : PacketExpressionOracle) : PacketExpressionOracle :=
  expressionPacketMul
    (expressionPacketMul (expressionPacketMul (expressionReferenceX f) (expressionReferenceY f))
      (expressionPacketInverse (expressionReferenceX f)))
    (expressionPacketInverse (expressionReferenceY f))
def expressionChartTarget (f : PacketExpressionOracle) (j : Fin 4) : PacketExpressionOracle :=
  expressionPacketMul (expressionPacketMul (expressionFrame j) f)
    (expressionPacketInverse (expressionFrame j))
def expressionChartMass (f g : PacketExpressionOracle) (p : ℕ) (j : Fin 4) : ScalarExpression :=
  expressionDistance f (expressionPacketInverse (expressionChartTarget g j)) p
def expressionRadius (f g : PacketExpressionOracle) (j : Fin 4) : ScalarExpressionOracle :=
  expressionSqrt (fun p => expressionChartMass f g p j)
def expressionNormalized (f g : PacketExpressionOracle) (t : ℕ) (j : Fin 4) : PacketExpressionOracle := fun p =>
  let radiusInv := expressionInv (t+1) (expressionRadius f g j)
  let adjoint := expressionPacketInverse (expressionChartTarget g j)
  .tuple (fun i => expressionMul (t+2)
    (expressionAdd (expressionCoordinate f i) (expressionNeg (expressionCoordinate adjoint i))) radiusInv p)
def expressionConjugator (f : PacketExpressionOracle) (t : ℕ) : PacketExpressionOracle := fun p =>
  let g := expressionBalancedReference f
  .selectMax (expressionChartMass f g (2*t+2))
    (fun j => expressionPacketMul (expressionNormalized f g t j) (expressionFrame j) p)
def expressionConjugate (f g : PacketExpressionOracle) : PacketExpressionOracle :=
  expressionPacketMul (expressionPacketMul f g) (expressionPacketInverse f)
def expressionFactorX (f : PacketExpressionOracle) (t : ℕ) : PacketExpressionOracle :=
  expressionConjugate (expressionConjugator f t) (expressionReferenceX f)
def expressionFactorY (f : PacketExpressionOracle) (t : ℕ) : PacketExpressionOracle :=
  expressionConjugate (expressionConjugator f t) (expressionReferenceY f)

@[simp] theorem expressionBalancedS_eval (f : PacketExpressionOracle) :
    evaluateScalarOracle (expressionBalancedS f)=balancedSOracle (evaluatePacketOracle f) := rfl
@[simp] theorem expressionBalancedC_eval (f : PacketExpressionOracle) :
    evaluateScalarOracle (expressionBalancedC f)=balancedCOracle (evaluatePacketOracle f) := rfl
@[simp] theorem expressionReferenceX_eval (f : PacketExpressionOracle) :
    evaluatePacketOracle (expressionReferenceX f)=referenceXOracle (evaluatePacketOracle f) := rfl
@[simp] theorem expressionReferenceY_eval (f : PacketExpressionOracle) :
    evaluatePacketOracle (expressionReferenceY f)=referenceYOracle (evaluatePacketOracle f) := rfl
@[simp] theorem expressionBalancedReference_eval (f : PacketExpressionOracle) :
    evaluatePacketOracle (expressionBalancedReference f)=balancedReferenceOracle (evaluatePacketOracle f) := rfl
@[simp] theorem expressionChartTarget_eval (f : PacketExpressionOracle) (j : Fin 4) :
    evaluatePacketOracle (expressionChartTarget f j)=chartTargetOracle (evaluatePacketOracle f) j := rfl
@[simp] theorem expressionChartMass_eval (f g : PacketExpressionOracle) (p : ℕ) (j : Fin 4) :
    (expressionChartMass f g p j).eval=chartMassScore (evaluatePacketOracle f) (evaluatePacketOracle g) p j := rfl
@[simp] theorem expressionRadius_eval (f g : PacketExpressionOracle) (j : Fin 4) :
    evaluateScalarOracle (expressionRadius f g j)=intertwinerRadiusOracle (evaluatePacketOracle f) (evaluatePacketOracle g) j := rfl
@[simp] theorem expressionNormalized_eval (f g : PacketExpressionOracle) (t : ℕ) (j : Fin 4) :
    evaluatePacketOracle (expressionNormalized f g t j)=
      normalizedIntertwinerOracle (evaluatePacketOracle f) (evaluatePacketOracle g) t j := rfl
@[simp] theorem expressionConjugator_eval (f : PacketExpressionOracle) (t : ℕ) :
    evaluatePacketOracle (expressionConjugator f t)=conditionedConjugatorOracle (evaluatePacketOracle f) t := rfl
@[simp] theorem expressionConjugate_eval (f g : PacketExpressionOracle) :
    evaluatePacketOracle (expressionConjugate f g)=quaternionConjugateOracle (evaluatePacketOracle f) (evaluatePacketOracle g) := rfl
@[simp] theorem expressionFactorX_eval (f : PacketExpressionOracle) (t : ℕ) :
    evaluatePacketOracle (expressionFactorX f t)=conditionedFactorXOracle (evaluatePacketOracle f) t := rfl
@[simp] theorem expressionFactorY_eval (f : PacketExpressionOracle) (t : ℕ) :
    evaluatePacketOracle (expressionFactorY f t)=conditionedFactorYOracle (evaluatePacketOracle f) t := rfl

end CircuitRecursion
