import CircuitNumerical.IntegerPacketArithmetic

namespace CircuitRecursion

def IntegerScalar.meanMinus (a : IntegerScalar) : IntegerScalar :=
  ((IntegerScalar.ofInt 1).add a.neg).mul (IntegerScalar.ofInt 2).inv

theorem IntegerScalar.meanMinus_value (a : IntegerScalar) : a.meanMinus.value=(1-a.value)/2 := by
  rw [meanMinus,mul_value,add_value,neg_value,inv_value]
  simp only [ofInt,value,Int.cast_one,Int.cast_ofNat,Nat.cast_one,div_one]
  ring

theorem IntegerScalarHeight.mono (a : IntegerScalar) (A B : ℕ)
    (ha : IntegerScalarHeight a A) (hAB : A≤B) : IntegerScalarHeight a B := by
  have h := Nat.pow_le_pow_right (by decide : 1≤2) hAB
  exact ⟨ha.1.trans h,ha.2.trans h⟩

theorem IntegerScalar.meanMinus_height (a : IntegerScalar) (A : ℕ) (ha : IntegerScalarHeight a A) :
    IntegerScalarHeight a.meanMinus (A+2) := by
  have h1 : IntegerScalarHeight (IntegerScalar.ofInt 1) 0 := by constructor <;> decide
  have h2 : IntegerScalarHeight (IntegerScalar.ofInt 2) 1 := by constructor <;> decide
  have h := mul_height _ _ _ _ (add_height _ _ _ _ h1 (neg_height a A ha)) (inv_height _ _ h2)
  convert h using 1 <;> first | rfl | ring

def integerStoppingThreshold (t : ℕ) : IntegerScalar :=
  ⟨2,expressionPowerTwo (2*t),by rw [expressionPowerTwo_eq];positivity⟩

theorem integerStoppingThreshold_value (t : ℕ) :
    (integerStoppingThreshold t).value=2*((1/2:ℚ)^t)^2 :=
  executeStoppingThreshold_correct t

theorem rationalSqrtApprox_max (q : ℚ) (p : ℕ) :
    rationalSqrtApprox (max 0 q) p=rationalSqrtApprox q p := by
  have h : max 0 (max 0 q)=max 0 q := max_eq_right (le_max_left 0 q)
  simp only [rationalSqrtApprox,h]

mutual
def ScalarExpression.integerRun : ScalarExpression → IntegerScalar
  | .literal q => IntegerScalar.ofRat q
  | .stoppingThreshold t => integerStoppingThreshold t
  | .add a b => a.integerRun.add b.integerRun
  | .neg a => a.integerRun.neg
  | .mul a b => a.integerRun.mul b.integerRun
  | .inv a => a.integerRun.inv
  | .sqrt a p => a.integerRun.root p
  | .meanMinus a => a.integerRun.meanMinus
  | .coordinate a i => a.integerRun.coordinate i
  | .distance a b => a.integerRun.distanceScalar b.integerRun
def PacketExpression.integerRun : PacketExpression → IntegerPacket
  | .literal q => IntegerPacket.ofVector q
  | .tuple a => IntegerPacket.ofScalars (fun i => (a i).integerRun)
  | .mul a b => a.integerRun.mul b.integerRun
  | .inverse a => a.integerRun.inverse
  | .selectMax scores branches =>
    let values := List.Vector.ofFn (fun i => (scores i).integerRun.value)
    (branches (rationalMaxIndex 3 values.get)).integerRun
end

mutual
theorem ScalarExpression.integerRun_correct (e : ScalarExpression) : e.integerRun.value=e.eval := by
  cases e with
  | literal q => exact IntegerScalar.ofRat_value q
  | stoppingThreshold t => exact integerStoppingThreshold_value t
  | add a b => simp only [ScalarExpression.integerRun,ScalarExpression.eval,IntegerScalar.add_value,
      ScalarExpression.integerRun_correct a,ScalarExpression.integerRun_correct b]
  | neg a => simp only [ScalarExpression.integerRun,ScalarExpression.eval,IntegerScalar.neg_value,ScalarExpression.integerRun_correct a]
  | mul a b => simp only [ScalarExpression.integerRun,ScalarExpression.eval,IntegerScalar.mul_value,
      ScalarExpression.integerRun_correct a,ScalarExpression.integerRun_correct b]
  | inv a => simp only [ScalarExpression.integerRun,ScalarExpression.eval,IntegerScalar.inv_value,ScalarExpression.integerRun_correct a]
  | sqrt a p => simp only [ScalarExpression.integerRun,ScalarExpression.eval,IntegerScalar.root_value,
      ScalarExpression.integerRun_correct a,rationalSqrtApprox_max]
  | meanMinus a => simp only [ScalarExpression.integerRun,ScalarExpression.eval,IntegerScalar.meanMinus_value,
      ScalarExpression.integerRun_correct a]
  | coordinate a i => simp only [ScalarExpression.integerRun,ScalarExpression.eval,IntegerPacket.coordinate_value,
      PacketExpression.integerRun_correct a]
  | distance a b => simp only [ScalarExpression.integerRun,ScalarExpression.eval,IntegerPacket.distanceScalar_value,
      PacketExpression.integerRun_correct a,PacketExpression.integerRun_correct b]
theorem PacketExpression.integerRun_correct (e : PacketExpression) : e.integerRun.value=e.eval := by
  cases e with
  | literal q => exact IntegerPacket.ofVector_value q
  | tuple a =>
    simp only [PacketExpression.integerRun,PacketExpression.eval,IntegerPacket.ofScalars_value]
    congr 1
    funext i
    exact ScalarExpression.integerRun_correct (a i)
  | mul a b => simp only [PacketExpression.integerRun,PacketExpression.eval,IntegerPacket.mul_value,
      PacketExpression.integerRun_correct a,PacketExpression.integerRun_correct b]
  | inverse a => simp only [PacketExpression.integerRun,PacketExpression.eval,IntegerPacket.inverse_value,
      PacketExpression.integerRun_correct a]
  | selectMax scores branches =>
    have hs : (fun i => (scores i).integerRun.value)=(fun i => (scores i).eval) :=
      funext (fun i => ScalarExpression.integerRun_correct (scores i))
    simp only [PacketExpression.integerRun,PacketExpression.eval,hs]
    exact PacketExpression.integerRun_correct _
end

end CircuitRecursion
