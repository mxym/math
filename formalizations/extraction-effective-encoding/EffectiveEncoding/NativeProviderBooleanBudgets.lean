import EffectiveEncoding.NativeProviderRefinement

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

set_option maxRecDepth 4096

/-- Internal represented operand bound for the actual native target program,
including literal fractions before its first root. -/
theorem nativeProviderExpression_bitBudget {k : ℕ} {wire : Fin (originalWireCount k)}
    {u : SingleCode} (hu : GateCode.single wire u∈(preparedNativeDescriptorRun k).word) (p : ℕ) :
    ((prepareNativeSingleInput u).packetExpression p).interpret.integerBitBudget≤
      40000000*(k+3)^7*(p+5) := by
  have h:=(prepareNativeSingleInput_packet_refines u p).budget_le
  rw [preparedNativeDescriptorRun_eq,nativeDescriptorRun_actualWord] at hu
  have hb:=Nat.mul_le_mul_left 20 (extractionCode_rawProviderExpression_budget hu p)
  exact (h.trans hb).trans_eq (by ring)


theorem nativeProviderExpression_operations {k : ℕ} {wire : Fin (originalWireCount k)}
    {u : SingleCode} (hu : GateCode.single wire u∈(preparedNativeDescriptorRun k).word) (p : ℕ) :
    ((prepareNativeSingleInput u).packetExpression p).interpret.operations≤
      20*(100*(halvingBudget k+3)+4) := by
  have h:=(prepareNativeSingleInput_packet_refines u p).operations_le
  rw [preparedNativeDescriptorRun_eq,nativeDescriptorRun_actualWord] at hu
  exact h.trans (Nat.mul_le_mul_left 20 (extractionCode_rawProviderExpression_operations hu p))


def nativeProviderQueryCoefficient (k : ℕ) : ℕ :=
  20000*(2*(40000000*(k+3)^7)+4)^2*(20*(100*(halvingBudget k+3)+4))


theorem nativeProviderQuery_algebra (A F x : ℕ) (hx : 1≤x) :
    20000*(2*(A*x)+4)^2*F≤(20000*(2*A+4)^2*F)*x^2 := by
  have h : 2*(A*x)+4≤(2*A+4)*x := by nlinarith
  have h2:=Nat.pow_le_pow_left h 2
  apply (Nat.mul_le_mul_right F (Nat.mul_le_mul_left 20000 h2)).trans_eq
  ring

/-- Actual stored PacketWordEvaluation trace, not a replayed cost oracle.
Only the Bool/list/record primitives represented by this trace are charged. -/
theorem nativeProviderPacketProgram_booleanActions {k : ℕ} {wire : Fin (originalWireCount k)}
    {u : SingleCode} (hu : GateCode.single wire u∈(preparedNativeDescriptorRun k).word) (p : ℕ) :
    ((prepareNativeSingleInput u).packetProgram p).trace.booleanActions≤
      nativeProviderQueryCoefficient k*(p+5)^2 := by
  have h:=NativePacketExpression.wordRun_booleanActions _ _ (nativeProviderExpression_bitBudget hu p)
  apply h.trans
  apply (Nat.mul_le_mul_left _ (nativeProviderExpression_operations hu p)).trans
  exact nativeProviderQuery_algebra (40000000*(k+3)^7) (20*(100*(halvingBudget k+3)+4))
    (p+5) (by omega)


theorem nativeProviderQueryCoefficient_polynomial (k : ℕ) :
    nativeProviderQueryCoefficient k≤(20000*80000004^2*22080)*(k+3)^15 := by
  have hx : 1≤(k+3)^7 := Nat.one_le_pow _ _ (by omega)
  have h1 : 2*(40000000*(k+3)^7)+4≤80000004*(k+3)^7 := by nlinarith
  have hc : Nat.clog 2 (k+3)≤k+3 := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n:=k+3)).le
  have h2 : 20*(100*(halvingBudget k+3)+4)≤22080*(k+3) := by unfold halvingBudget;omega
  apply (Nat.mul_le_mul (Nat.mul_le_mul_left 20000 (Nat.pow_le_pow_left h1 2)) h2).trans_eq
  ring


theorem nativeProviderPacketProgram_booleanActions_kp {k : ℕ} {wire : Fin (originalWireCount k)}
    {u : SingleCode} (hu : GateCode.single wire u∈(preparedNativeDescriptorRun k).word) (p : ℕ) :
    ((prepareNativeSingleInput u).packetProgram p).trace.booleanActions≤
      (20000*80000004^2*22080)*(k+3)^15*(p+5)^2 :=
  (nativeProviderPacketProgram_booleanActions hu p).trans
    (Nat.mul_le_mul_right _ (nativeProviderQueryCoefficient_polynomial k))

end EffectiveEncoding
