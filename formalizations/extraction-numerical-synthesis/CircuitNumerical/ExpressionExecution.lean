import CircuitNumerical.OperationGrowth

namespace CircuitRecursion

/-- Binary shifts are an explicit primitive of the arithmetic model. -/
def expressionPowerTwo (p : ℕ) : ℕ := 1 <<< p

theorem expressionPowerTwo_eq (p : ℕ) : expressionPowerTwo p=2^p := by
  simp [expressionPowerTwo,Nat.shiftLeft_eq]

def executeExpressionRoot (q : ℚ) (p : ℕ) : ℚ :=
  let d : ℚ := expressionPowerTwo p
  (Nat.sqrt ⌊max 0 q*(d*d)⌋₊:ℚ)/d

theorem executeExpressionRoot_correct (q : ℚ) (p : ℕ) :
    executeExpressionRoot q p=rationalSqrtApprox q p := by
  simp only [executeExpressionRoot,expressionPowerTwo_eq,Nat.cast_pow,Nat.cast_ofNat,
    rationalSqrtApprox,pow_two]

def executeStoppingThreshold (t : ℕ) : ℚ := 2/(expressionPowerTwo (2*t):ℚ)

theorem executeStoppingThreshold_correct (t : ℕ) :
    executeStoppingThreshold t=2*((1/2:ℚ)^t)^2 := by
  simp only [executeStoppingThreshold,expressionPowerTwo_eq,Nat.cast_pow,Nat.cast_ofNat,
    one_div,inv_pow,div_eq_mul_inv,← pow_mul]
  rw [Nat.mul_comm 2 t]
  simp only [one_mul,inv_pow]

/- `run` is the executable arithmetic backend. Integer square root, natural
floor, binary shift, rational arithmetic/comparison and cache access are the
listed primitives. In particular, it does not invoke a real square root or
raise a rational to a variable power to construct dyadic constants. -/
mutual
def ScalarExpression.run : ScalarExpression → ℚ
  | .literal q => q
  | .stoppingThreshold t => executeStoppingThreshold t
  | .add a b => a.run+b.run
  | .neg a => -a.run
  | .mul a b => a.run*b.run
  | .inv a => a.run⁻¹
  | .sqrt a p => executeExpressionRoot (max 0 a.run) p
  | .meanMinus a => (1-a.run)/2
  | .coordinate a i => a.run.get i
  | .distance a b => rationalSquaredDistance a.run b.run
def PacketExpression.run : PacketExpression → List.Vector ℚ 4
  | .literal q => q
  | .tuple a => List.Vector.ofFn (fun i => (a i).run)
  | .mul a b =>
    let x := a.run
    let y := b.run
    List.Vector.ofFn (quaternionProduct x.get y.get)
  | .inverse a =>
    let x := a.run
    List.Vector.ofFn (fun i => if i=0 then x.get i else -x.get i)
  | .selectMax scores branches =>
    let values := List.Vector.ofFn (fun i => (scores i).run)
    (branches (rationalMaxIndex 3 values.get)).run
end

mutual
theorem ScalarExpression.run_correct (e : ScalarExpression) : e.run=e.eval := by
  cases e with
  | literal q => rfl
  | stoppingThreshold t => exact executeStoppingThreshold_correct t
  | add a b => simp only [ScalarExpression.run,ScalarExpression.eval,ScalarExpression.run_correct a,ScalarExpression.run_correct b]
  | neg a => simp only [ScalarExpression.run,ScalarExpression.eval,ScalarExpression.run_correct a]
  | mul a b => simp only [ScalarExpression.run,ScalarExpression.eval,ScalarExpression.run_correct a,ScalarExpression.run_correct b]
  | inv a => simp only [ScalarExpression.run,ScalarExpression.eval,ScalarExpression.run_correct a]
  | sqrt a p => simp only [ScalarExpression.run,ScalarExpression.eval,ScalarExpression.run_correct a,executeExpressionRoot_correct]
  | meanMinus a => simp only [ScalarExpression.run,ScalarExpression.eval,ScalarExpression.run_correct a]
  | coordinate a i => simp only [ScalarExpression.run,ScalarExpression.eval,PacketExpression.run_correct a]
  | distance a b => simp only [ScalarExpression.run,ScalarExpression.eval,PacketExpression.run_correct a,PacketExpression.run_correct b]
theorem PacketExpression.run_correct (e : PacketExpression) : e.run=e.eval := by
  cases e with
  | literal q => rfl
  | tuple a =>
    simp only [PacketExpression.run,PacketExpression.eval]
    congr 1
    funext i
    exact ScalarExpression.run_correct (a i)
  | mul a b => simp only [PacketExpression.run,PacketExpression.eval,PacketExpression.run_correct a,PacketExpression.run_correct b]
  | inverse a => simp only [PacketExpression.run,PacketExpression.eval,PacketExpression.run_correct a]
  | selectMax scores branches =>
    have hs : (fun i => (scores i).run)=(fun i => (scores i).eval) :=
      funext (fun i => ScalarExpression.run_correct (scores i))
    simp only [PacketExpression.run,PacketExpression.eval,hs]
    exact PacketExpression.run_correct _
end

end CircuitRecursion
