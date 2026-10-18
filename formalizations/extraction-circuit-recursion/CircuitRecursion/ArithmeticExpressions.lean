import CircuitRecursion.CacheResources

namespace CircuitRecursion

/- The cost semantics counts rational arithmetic, rational comparison,
binary shifts, natural floor and integer square root as primitive operations.
It is deliberately distinct from a Turing bit-cost semantics. Packet product
nodes evaluate each operand once and then use its four stored coordinates. -/
mutual
inductive ScalarExpression where
  | literal : ℚ → ScalarExpression
  | stoppingThreshold : ℕ → ScalarExpression
  | add : ScalarExpression → ScalarExpression → ScalarExpression
  | neg : ScalarExpression → ScalarExpression
  | mul : ScalarExpression → ScalarExpression → ScalarExpression
  | inv : ScalarExpression → ScalarExpression
  | sqrt : ScalarExpression → ℕ → ScalarExpression
  | meanMinus : ScalarExpression → ScalarExpression
  | coordinate : PacketExpression → Fin 4 → ScalarExpression
  | distance : PacketExpression → PacketExpression → ScalarExpression
inductive PacketExpression where
  | literal : List.Vector ℚ 4 → PacketExpression
  | tuple : (Fin 4 → ScalarExpression) → PacketExpression
  | mul : PacketExpression → PacketExpression → PacketExpression
  | inverse : PacketExpression → PacketExpression
  | selectMax : (Fin 4 → ScalarExpression) → (Fin 4 → PacketExpression) → PacketExpression
end

mutual
def ScalarExpression.eval : ScalarExpression → ℚ
  | .literal q => q
  | .stoppingThreshold t => 2*((1/2:ℚ)^t)^2
  | .add a b => a.eval+b.eval
  | .neg a => -a.eval
  | .mul a b => a.eval*b.eval
  | .inv a => a.eval⁻¹
  | .sqrt a p => rationalSqrtApprox (max 0 a.eval) p
  | .meanMinus a => (1-a.eval)/2
  | .coordinate a i => a.eval.get i
  | .distance a b => rationalSquaredDistance a.eval b.eval
def PacketExpression.eval : PacketExpression → List.Vector ℚ 4
  | .literal q => q
  | .tuple a => List.Vector.ofFn (fun i => (a i).eval)
  | .mul a b =>
    let x := a.eval
    let y := b.eval
    List.Vector.ofFn (quaternionProduct x.get y.get)
  | .inverse a =>
    let x := a.eval
    List.Vector.ofFn (fun i => if i=0 then x.get i else -x.get i)
  | .selectMax scores branches =>
    let values := List.Vector.ofFn (fun i => (scores i).eval)
    (branches (rationalMaxIndex 3 values.get)).eval
end

mutual
/-- A conservative operation bound; selective nodes charge all alternatives. -/
def ScalarExpression.operations : ScalarExpression → ℕ
  | .literal _ => 1
  | .stoppingThreshold _ => 4
  | .add a b => a.operations+b.operations+1
  | .neg a => a.operations+1
  | .mul a b => a.operations+b.operations+1
  | .inv a => a.operations+1
  | .sqrt a _ => a.operations+8
  | .meanMinus a => a.operations+2
  | .coordinate a _ => a.operations+1
  | .distance a b => a.operations+b.operations+16
def PacketExpression.operations : PacketExpression → ℕ
  | .literal _ => 1
  | .tuple a => (∑ i : Fin 4,(a i).operations)+4
  | .mul a b => a.operations+b.operations+48
  | .inverse a => a.operations+4
  | .selectMax scores branches =>
      (∑ i : Fin 4,(scores i).operations)+(∑ i : Fin 4,(branches i).operations)+3
end

abbrev ScalarExpressionOracle := ℕ → ScalarExpression
abbrev PacketExpressionOracle := ℕ → PacketExpression

def evaluateScalarOracle (f : ScalarExpressionOracle) : RationalOracle := fun p => (f p).eval
def evaluatePacketOracle (f : PacketExpressionOracle) : QuaternionOracle := fun p => (f p).eval

def expressionAdd (f g : ScalarExpressionOracle) : ScalarExpressionOracle := fun p =>
  .add (f (p+1)) (g (p+1))
def expressionNeg (f : ScalarExpressionOracle) : ScalarExpressionOracle := fun p => .neg (f p)
def expressionMul (b : ℕ) (f g : ScalarExpressionOracle) : ScalarExpressionOracle := fun p =>
  .mul (f (p+b+2)) (g (p+b+2))
def expressionInv (b : ℕ) (f : ScalarExpressionOracle) : ScalarExpressionOracle := fun p =>
  .inv (f (p+2*b+2))
def expressionSqrt (f : ScalarExpressionOracle) : ScalarExpressionOracle := fun p =>
  .sqrt (f (2*p+2)) (p+1)
def expressionMeanMinus (f : ScalarExpressionOracle) : ScalarExpressionOracle := fun p =>
  .meanMinus (f p)
def expressionCoordinate (f : PacketExpressionOracle) (i : Fin 4) : ScalarExpressionOracle := fun p =>
  .coordinate (f p) i
def expressionPacketMul (f g : PacketExpressionOracle) : PacketExpressionOracle := fun p =>
  .mul (f (p+4)) (g (p+4))
def expressionPacketInverse (f : PacketExpressionOracle) : PacketExpressionOracle := fun p =>
  .inverse (f p)
def expressionPacketOne : PacketExpressionOracle := fun _ => .literal (List.Vector.ofFn ![1,0,0,0])
def expressionFrame (j : Fin 4) : PacketExpressionOracle := fun _ =>
  .literal (List.Vector.ofFn (fun i => if i=j then 1 else 0))
def expressionDistance (f g : PacketExpressionOracle) (p : ℕ) : ScalarExpression :=
  .distance (f (p+6)) (g (p+6))

@[simp] theorem expressionAdd_eval (f g : ScalarExpressionOracle) :
    evaluateScalarOracle (expressionAdd f g)=oracleAdd (evaluateScalarOracle f) (evaluateScalarOracle g) := rfl
@[simp] theorem expressionNeg_eval (f : ScalarExpressionOracle) :
    evaluateScalarOracle (expressionNeg f)=oracleNeg (evaluateScalarOracle f) := rfl
@[simp] theorem expressionMul_eval (b : ℕ) (f g : ScalarExpressionOracle) :
    evaluateScalarOracle (expressionMul b f g)=oracleMul b (evaluateScalarOracle f) (evaluateScalarOracle g) := rfl
@[simp] theorem expressionInv_eval (b : ℕ) (f : ScalarExpressionOracle) :
    evaluateScalarOracle (expressionInv b f)=oracleInv b (evaluateScalarOracle f) := rfl
@[simp] theorem expressionSqrt_eval (f : ScalarExpressionOracle) :
    evaluateScalarOracle (expressionSqrt f)=oracleSqrt (evaluateScalarOracle f) := rfl
@[simp] theorem expressionMeanMinus_eval (f : ScalarExpressionOracle) :
    evaluateScalarOracle (expressionMeanMinus f)=oracleMeanMinus (evaluateScalarOracle f) := rfl
@[simp] theorem expressionCoordinate_eval (f : PacketExpressionOracle) (i : Fin 4) :
    evaluateScalarOracle (expressionCoordinate f i)=coordinateOracle (evaluatePacketOracle f) i := rfl
@[simp] theorem expressionPacketMul_eval (f g : PacketExpressionOracle) :
    evaluatePacketOracle (expressionPacketMul f g)=
      quaternionOracleMul (evaluatePacketOracle f) (evaluatePacketOracle g) := rfl
@[simp] theorem expressionPacketInverse_eval (f : PacketExpressionOracle) :
    evaluatePacketOracle (expressionPacketInverse f)=quaternionOracleInverse (evaluatePacketOracle f) := rfl
@[simp] theorem expressionPacketOne_eval : evaluatePacketOracle expressionPacketOne=quaternionOracleOne := rfl
@[simp] theorem expressionFrame_eval (j : Fin 4) : evaluatePacketOracle (expressionFrame j)=frameOracle j := rfl
@[simp] theorem expressionDistance_eval (f g : PacketExpressionOracle) (p : ℕ) :
    (expressionDistance f g p).eval=distanceScore (evaluatePacketOracle f) (evaluatePacketOracle g) p := rfl

end CircuitRecursion
