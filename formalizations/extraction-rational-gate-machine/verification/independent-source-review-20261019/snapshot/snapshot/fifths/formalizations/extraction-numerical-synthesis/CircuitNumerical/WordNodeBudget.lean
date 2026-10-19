import CircuitNumerical.WordExpressionTrace

namespace CircuitRecursion

def wordNodeBooleanBudget (B : ℕ) : ℕ := 20000*(2*B+4)^2

theorem wordNodeBooleanBudget_square (B c s : ℕ) (hc : c≤13000) (hs : s≤2*B+4) :
    c*s^2+16≤wordNodeBooleanBudget B := by
  have h:=Nat.mul_le_mul hc (Nat.pow_le_pow_left hs 2)
  have hp : 1≤(2*B+4)^2 := Nat.one_le_pow _ _ (by omega)
  dsimp only [wordNodeBooleanBudget]
  nlinarith

theorem wordNodeBooleanBudget_linear (B c s : ℕ) (hc : c≤13000) (hs : s≤2*B+4) :
    c*s+16≤wordNodeBooleanBudget B := by
  have h:=wordNodeBooleanBudget_square B c s hc hs
  have hp : s≤s^2 := by simpa only [pow_two] using Nat.le_mul_self s
  have hm:=Nat.mul_le_mul_left c hp
  omega

theorem wordNodeBooleanBudget_minimum (B : ℕ) : 16≤wordNodeBooleanBudget B := by
  simpa only [zero_mul,zero_add] using wordNodeBooleanBudget_square B 0 0 (by omega) (by omega)

theorem ScalarExpression.wordRun_height (e : ScalarExpression) (B : ℕ) (h : e.integerBitBudget≤B) :
    IntegerScalarHeight e.wordRun.value.decode B := by
  rw [ScalarExpression.wordRun_decode,ScalarExpression.integerProgramRun_eq]
  exact IntegerScalarHeight.mono _ _ _ (ScalarExpression.integerRun_height e) h

theorem PacketExpression.wordRun_height (e : PacketExpression) (B : ℕ) (h : e.integerBitBudget≤B) :
    IntegerPacketHeight e.wordRun.value.decode B := by
  rw [PacketExpression.wordRun_decode,PacketExpression.integerProgramRun_eq]
  exact IntegerPacketHeight.mono _ _ _ (PacketExpression.integerRun_height e) h

end CircuitRecursion
