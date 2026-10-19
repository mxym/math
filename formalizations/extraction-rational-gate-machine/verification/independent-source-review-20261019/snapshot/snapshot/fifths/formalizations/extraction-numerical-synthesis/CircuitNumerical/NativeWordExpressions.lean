import CircuitNumerical.WordSynthesisPolynomial

namespace CircuitRecursion

/- Native literal payloads are actual canonical Boolean input data. No
rational construction or Nat.bits input adapter belongs to these ASTs. -/
mutual
inductive NativeScalarExpression where
  | literal : WordIntegerScalar → NativeScalarExpression
  | stoppingThreshold : ℕ → NativeScalarExpression
  | add : NativeScalarExpression → NativeScalarExpression → NativeScalarExpression
  | neg : NativeScalarExpression → NativeScalarExpression
  | mul : NativeScalarExpression → NativeScalarExpression → NativeScalarExpression
  | inv : NativeScalarExpression → NativeScalarExpression
  | sqrt : NativeScalarExpression → ℕ → NativeScalarExpression
  | meanMinus : NativeScalarExpression → NativeScalarExpression
  | coordinate : NativePacketExpression → Fin 4 → NativeScalarExpression
  | distance : NativePacketExpression → NativePacketExpression → NativeScalarExpression
inductive NativePacketExpression where
  | literal : WordIntegerPacket → NativePacketExpression
  | tuple : (Fin 4 → NativeScalarExpression) → NativePacketExpression
  | mul : NativePacketExpression → NativePacketExpression → NativePacketExpression
  | inverse : NativePacketExpression → NativePacketExpression
  | selectMax : (Fin 4 → NativeScalarExpression) → (Fin 4 → NativePacketExpression) → NativePacketExpression
end

/- Interpretation is semantic only; native value programs do not call it.
Raw literal macros preserve the previously proved 4/20 operation budgets. -/
mutual
def NativeScalarExpression.interpret : NativeScalarExpression → ScalarExpression
  | .literal a => rawScalarExpression a.decode
  | .stoppingThreshold t => .stoppingThreshold t
  | .add a b => .add a.interpret b.interpret
  | .neg a => .neg a.interpret
  | .mul a b => .mul a.interpret b.interpret
  | .inv a => .inv a.interpret
  | .sqrt a p => .sqrt a.interpret p
  | .meanMinus a => .meanMinus a.interpret
  | .coordinate a i => .coordinate a.interpret i
  | .distance a b => .distance a.interpret b.interpret
def NativePacketExpression.interpret : NativePacketExpression → PacketExpression
  | .literal a => rawPacketExpression a.decode
  | .tuple a => .tuple (fun i => (a i).interpret)
  | .mul a b => .mul a.interpret b.interpret
  | .inverse a => .inverse a.interpret
  | .selectMax scores branches => .selectMax (fun i => (scores i).interpret) (fun i => (branches i).interpret)
end

abbrev NativeScalarExpressionOracle := ℕ → NativeScalarExpression
abbrev NativePacketExpressionOracle := ℕ → NativePacketExpression

def interpretNativeScalarOracle (f : NativeScalarExpressionOracle) : ScalarExpressionOracle := fun p => (f p).interpret
def interpretNativePacketOracle (f : NativePacketExpressionOracle) : PacketExpressionOracle := fun p => (f p).interpret

end CircuitRecursion
