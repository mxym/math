import CircuitNumerical.IntegerExpressionExecution

namespace CircuitRecursion

def rationalBinaryExponent (q : ℚ) : ℕ :=
  max (Nat.clog 2 (q.den+1)) (Nat.clog 2 (q.num.natAbs+1))

theorem rationalBinaryExponent_height (q : ℚ) :
    IntegerScalarHeight (IntegerScalar.ofRat q) (rationalBinaryExponent q) := by
  constructor
  · exact (Nat.le_succ q.den).trans ((Nat.le_pow_clog (by decide) (q.den+1)).trans
      (Nat.pow_le_pow_right (by decide) (le_max_left _ _)))
  · exact (Nat.le_succ q.num.natAbs).trans ((Nat.le_pow_clog (by decide) (q.num.natAbs+1)).trans
      (Nat.pow_le_pow_right (by decide) (le_max_right _ _)))

theorem rationalBinaryExponent_le (a : IntegerScalar) (B : ℕ) (ha : IntegerScalarHeight a B) :
    rationalBinaryExponent a.value≤B+1 := by
  have hc := IntegerScalar.canonical_height a B ha
  apply max_le
  · have h := commonDenominator_binary_bound a.value.den B hc.1
    omega
  · have h := commonDenominator_binary_bound a.value.num.natAbs B hc.2
    omega

mutual
def ScalarExpression.integerBitBudget : ScalarExpression → ℕ
  | .literal q => rationalBinaryExponent q
  | .stoppingThreshold t => 2*t+1
  | .add a b => a.integerBitBudget+b.integerBitBudget+1
  | .neg a => a.integerBitBudget
  | .mul a b => a.integerBitBudget+b.integerBitBudget
  | .inv a => a.integerBitBudget
  | .sqrt a p => a.integerBitBudget+2*p
  | .meanMinus a => a.integerBitBudget+2
  | .coordinate a _ => a.integerBitBudget
  | .distance a b => 2*a.integerBitBudget+2*b.integerBitBudget+4
def PacketExpression.integerBitBudget : PacketExpression → ℕ
  | .literal q => ∑ i : Fin 4,rationalBinaryExponent (q.get i)
  | .tuple a => ∑ i : Fin 4,(a i).integerBitBudget
  | .mul a b => a.integerBitBudget+b.integerBitBudget+2
  | .inverse a => a.integerBitBudget
  | .selectMax scores branches =>
    (∑ i : Fin 4,(scores i).integerBitBudget)+(∑ i : Fin 4,(branches i).integerBitBudget)
end

mutual
theorem ScalarExpression.integerRun_height (e : ScalarExpression) :
    IntegerScalarHeight e.integerRun e.integerBitBudget := by
  cases e with
  | literal q => exact rationalBinaryExponent_height q
  | stoppingThreshold t =>
    change IntegerScalarHeight (integerStoppingThreshold t) (2*t+1)
    constructor
    · change expressionPowerTwo (2*t)≤_
      rw [expressionPowerTwo_eq]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    · change 2≤2^(2*t+1)
      have h := Nat.pow_le_pow_right (n:=2) (by decide) (by omega : 1≤2*t+1)
      simpa only [pow_one] using h
  | add a b =>
    exact IntegerScalar.add_height _ _ _ _
      (ScalarExpression.integerRun_height a) (ScalarExpression.integerRun_height b)
  | neg a => exact IntegerScalar.neg_height _ _ (ScalarExpression.integerRun_height a)
  | mul a b =>
    exact IntegerScalar.mul_height _ _ _ _
      (ScalarExpression.integerRun_height a) (ScalarExpression.integerRun_height b)
  | inv a => exact IntegerScalar.inv_height _ _ (ScalarExpression.integerRun_height a)
  | sqrt a p => exact IntegerScalar.root_height _ _ p (ScalarExpression.integerRun_height a)
  | meanMinus a => exact IntegerScalar.meanMinus_height _ _ (ScalarExpression.integerRun_height a)
  | coordinate a i => exact IntegerPacket.coordinate_height _ _ (PacketExpression.integerRun_height a) i
  | distance a b =>
    exact IntegerPacket.distanceScalar_height _ _ _ _
      (PacketExpression.integerRun_height a) (PacketExpression.integerRun_height b)
theorem PacketExpression.integerRun_height (e : PacketExpression) :
    IntegerPacketHeight e.integerRun e.integerBitBudget := by
  cases e with
  | literal q => exact IntegerPacket.ofScalars_height _ _ (fun i => rationalBinaryExponent_height (q.get i))
  | tuple a => exact IntegerPacket.ofScalars_height _ _ (fun i => ScalarExpression.integerRun_height (a i))
  | mul a b =>
    exact IntegerPacket.mul_height _ _ _ _
      (PacketExpression.integerRun_height a) (PacketExpression.integerRun_height b)
  | inverse a => exact IntegerPacket.inverse_height _ _ (PacketExpression.integerRun_height a)
  | selectMax scores branches =>
    let values := List.Vector.ofFn (fun i => (scores i).integerRun.value)
    let j := rationalMaxIndex 3 values.get
    have h := PacketExpression.integerRun_height (branches j)
    apply IntegerPacketHeight.mono _ _ _ h
    have hs := Finset.single_le_sum (fun i (_ : i∈Finset.univ) => Nat.zero_le ((branches i).integerBitBudget))
      (Finset.mem_univ j)
    change _≤(∑ i : Fin 4,(scores i).integerBitBudget)+(∑ i : Fin 4,(branches i).integerBitBudget)
    omega
end

end CircuitRecursion
