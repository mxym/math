import CircuitNumerical.BinaryRootBackend

namespace CircuitRecursion

/-- The two digit subprograms and the external root scaling operations.
This count treats bounded shifts, arithmetic and comparisons as primitives;
computing the automatic fuel and their bit implementations remain separate. -/
def IntegerScalar.binaryRootPrimitiveOperations (a : IntegerScalar) (p : ℕ) : ℕ :=
  let numerator:=a.numerator.toNat <<< (2*p)
  let quotient:=binaryIntegerDiv numerator a.denominator
  binaryDivDigitOperations (binaryIntegerSqrtFuel numerator)+1+
    binarySqrtDigitOperations (binaryIntegerSqrtFuel quotient)+4

theorem IntegerScalar.binaryRootPrimitiveOperations_bound (a : IntegerScalar) (A p : ℕ)
    (ha : IntegerScalarHeight a A) : a.binaryRootPrimitiveOperations p≤16*(A+2*p+2)+5 := by
  have hn : a.numerator.toNat <<< (2*p)≤2^(A+2*p) :=
    rootOperandTrace_height a A p ha _ (by simp [rootOperandTrace])
  have hq : binaryIntegerDiv (a.numerator.toNat <<< (2*p)) a.denominator≤2^(A+2*p) := by
    rw [binaryIntegerDiv_eq]
    exact (Nat.div_le_self _ _).trans hn
  have hd:=binaryIntegerDiv_operations _ _ hn
  have hs:=binaryIntegerSqrt_operations _ _ hq
  dsimp only [binaryRootPrimitiveOperations]
  omega

def IntegerScalar.binaryRootOperandTrace (a : IntegerScalar) (p : ℕ) : List ℕ :=
  let numerator:=a.numerator.toNat <<< (2*p)
  let quotient:=binaryIntegerDiv numerator a.denominator
  a.rootOperandTrace p++binaryDivOperandTrace a.denominator (binaryIntegerSqrtFuel numerator) numerator++
    binarySqrtOperandTrace (binaryIntegerSqrtFuel quotient) quotient

theorem IntegerScalar.binaryRootOperandTrace_bound (a : IntegerScalar) (A p : ℕ)
    (ha : IntegerScalarHeight a A) (x : ℕ) (hx : x∈a.binaryRootOperandTrace p) : x≤2^(2*(A+2*p)+2) := by
  let N:=a.numerator.toNat <<< (2*p)
  let Q:=binaryIntegerDiv N a.denominator
  have hn : N≤2^(A+2*p) := rootOperandTrace_height a A p ha _ (by simp [N,rootOperandTrace])
  have hden : a.denominator≤2^(A+2*p) :=
    ha.1.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hq : Q≤2^(A+2*p) := by
    dsimp only [Q]
    rw [binaryIntegerDiv_eq]
    exact (Nat.div_le_self _ _).trans hn
  change x∈a.rootOperandTrace p++binaryDivOperandTrace a.denominator (binaryIntegerSqrtFuel N) N++
    binarySqrtOperandTrace (binaryIntegerSqrtFuel Q) Q at hx
  rcases List.mem_append.mp hx with hfirst|hsqrt
  · rcases List.mem_append.mp hfirst with hroot|hdiv
    · exact (rootOperandTrace_height a A p ha x hroot).trans
        (Nat.pow_le_pow_right (by decide) (by omega))
    · exact (binaryDivOperandTrace_height a.denominator _ N (A+2*p) a.denominator_pos
        (binaryIntegerDiv_input_fuel N) hn hden x hdiv).trans
          (Nat.pow_le_pow_right (by decide) (by omega))
  · exact binaryIntegerSqrt_operandTrace_height Q (A+2*p) hq x hsqrt

theorem IntegerScalar.binaryRootOperandTrace_binaryLength (a : IntegerScalar) (A p : ℕ)
    (ha : IntegerScalarHeight a A) (x : ℕ) (hx : x∈a.binaryRootOperandTrace p) :
    Nat.clog 2 (x+1)≤2*(A+2*p)+3 := by
  have h:=commonDenominator_binary_bound x (2*(A+2*p)+2) (binaryRootOperandTrace_bound a A p ha x hx)
  omega

theorem ScalarExpression.binaryRootRun_height (e : ScalarExpression) :
    IntegerScalarHeight e.binaryRootRun e.integerBitBudget := by
  rw [ScalarExpression.binaryRootRun_eq]
  exact ScalarExpression.integerRun_height e

theorem PacketExpression.binaryRootRun_height (e : PacketExpression) :
    IntegerPacketHeight e.binaryRootRun e.integerBitBudget := by
  rw [PacketExpression.binaryRootRun_eq]
  exact PacketExpression.integerRun_height e

end CircuitRecursion
