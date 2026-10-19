import CircuitNumerical.BinaryIntegerDivision

namespace CircuitRecursion

def IntegerScalar.binaryRoot (a : IntegerScalar) (p : ℕ) : IntegerScalar :=
  ⟨(binaryIntegerSqrt (binaryIntegerDiv (a.numerator.toNat <<< (2*p)) a.denominator):ℤ),expressionPowerTwo p,
    by rw [expressionPowerTwo_eq];positivity⟩

theorem IntegerScalar.binaryRoot_eq (a : IntegerScalar) (p : ℕ) : a.binaryRoot p=a.root p := by
  simp only [binaryRoot,root,binaryIntegerSqrt_eq,binaryIntegerDiv_eq]

theorem IntegerScalar.binaryRoot_operations (a : IntegerScalar) (A p : ℕ)
    (ha : IntegerScalarHeight a A) :
    binarySqrtDigitOperations
      (binaryIntegerSqrtFuel ((a.numerator.toNat <<< (2*p))/a.denominator))≤6*(A+2*p+2) := by
  apply binaryIntegerSqrt_operations
  apply rootOperandTrace_height a A p ha
  simp [rootOperandTrace]

theorem IntegerScalar.binaryRoot_operandTrace_height (a : IntegerScalar) (A p : ℕ)
    (ha : IntegerScalarHeight a A) (x : ℕ)
    (hx : x∈binarySqrtOperandTrace
      (binaryIntegerSqrtFuel ((a.numerator.toNat <<< (2*p))/a.denominator))
      ((a.numerator.toNat <<< (2*p))/a.denominator)) : x≤2^(2*(A+2*p)+2) := by
  apply binaryIntegerSqrt_operandTrace_height _ (A+2*p) _ x hx
  apply rootOperandTrace_height a A p ha
  simp [rootOperandTrace]

/- This evaluator replaces the root primitive's general division and sqrt
by explicit digit algorithms. Its raw integer outputs and selective decisions are exactly
the same as those of the existing evaluator. -/
mutual
def ScalarExpression.binaryRootRun : ScalarExpression → IntegerScalar
  | .literal q => IntegerScalar.ofRat q
  | .stoppingThreshold t => integerStoppingThreshold t
  | .add a b => a.binaryRootRun.add b.binaryRootRun
  | .neg a => a.binaryRootRun.neg
  | .mul a b => a.binaryRootRun.mul b.binaryRootRun
  | .inv a => a.binaryRootRun.inv
  | .sqrt a p => a.binaryRootRun.binaryRoot p
  | .meanMinus a => a.binaryRootRun.meanMinus
  | .coordinate a i => a.binaryRootRun.coordinate i
  | .distance a b => a.binaryRootRun.distanceScalar b.binaryRootRun
def PacketExpression.binaryRootRun : PacketExpression → IntegerPacket
  | .literal q => IntegerPacket.ofVector q
  | .tuple a => IntegerPacket.ofScalars (fun i => (a i).binaryRootRun)
  | .mul a b => a.binaryRootRun.mul b.binaryRootRun
  | .inverse a => a.binaryRootRun.inverse
  | .selectMax scores branches =>
    let values:=List.Vector.ofFn (fun i => (scores i).binaryRootRun.value)
    (branches (rationalMaxIndex 3 values.get)).binaryRootRun
end

mutual
theorem ScalarExpression.binaryRootRun_eq (e : ScalarExpression) : e.binaryRootRun=e.integerRun := by
  cases e with
  | literal q => rfl
  | stoppingThreshold t => rfl
  | add a b => simp only [ScalarExpression.binaryRootRun,ScalarExpression.integerRun,ScalarExpression.binaryRootRun_eq a,ScalarExpression.binaryRootRun_eq b]
  | neg a => simp only [ScalarExpression.binaryRootRun,ScalarExpression.integerRun,ScalarExpression.binaryRootRun_eq a]
  | mul a b => simp only [ScalarExpression.binaryRootRun,ScalarExpression.integerRun,ScalarExpression.binaryRootRun_eq a,ScalarExpression.binaryRootRun_eq b]
  | inv a => simp only [ScalarExpression.binaryRootRun,ScalarExpression.integerRun,ScalarExpression.binaryRootRun_eq a]
  | sqrt a p => simp only [ScalarExpression.binaryRootRun,ScalarExpression.integerRun,ScalarExpression.binaryRootRun_eq a,IntegerScalar.binaryRoot_eq]
  | meanMinus a => simp only [ScalarExpression.binaryRootRun,ScalarExpression.integerRun,ScalarExpression.binaryRootRun_eq a]
  | coordinate a i => simp only [ScalarExpression.binaryRootRun,ScalarExpression.integerRun,PacketExpression.binaryRootRun_eq a]
  | distance a b => simp only [ScalarExpression.binaryRootRun,ScalarExpression.integerRun,PacketExpression.binaryRootRun_eq a,PacketExpression.binaryRootRun_eq b]
theorem PacketExpression.binaryRootRun_eq (e : PacketExpression) : e.binaryRootRun=e.integerRun := by
  cases e with
  | literal q => rfl
  | tuple a =>
    have h : (fun i => (a i).binaryRootRun)=(fun i => (a i).integerRun) :=
      funext (fun i => ScalarExpression.binaryRootRun_eq (a i))
    simp only [PacketExpression.binaryRootRun,PacketExpression.integerRun,h]
  | mul a b => simp only [PacketExpression.binaryRootRun,PacketExpression.integerRun,PacketExpression.binaryRootRun_eq a,PacketExpression.binaryRootRun_eq b]
  | inverse a => simp only [PacketExpression.binaryRootRun,PacketExpression.integerRun,PacketExpression.binaryRootRun_eq a]
  | selectMax scores branches =>
    have h : (fun i => (scores i).binaryRootRun.value)=(fun i => (scores i).integerRun.value) :=
      funext (fun i => congrArg IntegerScalar.value (ScalarExpression.binaryRootRun_eq (scores i)))
    simp only [PacketExpression.binaryRootRun,PacketExpression.integerRun,h]
    exact PacketExpression.binaryRootRun_eq _
end

theorem ScalarExpression.binaryRootRun_correct (e : ScalarExpression) : e.binaryRootRun.value=e.eval := by
  rw [ScalarExpression.binaryRootRun_eq]
  exact ScalarExpression.integerRun_correct e

theorem PacketExpression.binaryRootRun_correct (e : PacketExpression) : e.binaryRootRun.value=e.eval := by
  rw [PacketExpression.binaryRootRun_eq]
  exact PacketExpression.integerRun_correct e

end CircuitRecursion
