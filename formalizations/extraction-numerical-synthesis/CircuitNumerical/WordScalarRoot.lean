import CircuitNumerical.WordShifts

namespace CircuitRecursion

structure WordScalarRootResult where
  scalar : WordIntegerScalar
  numeratorShift : BinaryWordShiftResult
  divisionRun : BinaryWordDivisionResult
  rootRun : BinaryWordSqrtResult
  numeratorTrim : BinaryWordTrimResult
  denominatorShift : BinaryWordShiftResult

/-- The entire scalar-root value program operates on Boolean lists: select
the nonnegative numerator, shift by 2p, divide, take restoring square root,
trim, and form the power-two denominator. Every subprogram is stored once.
The semantic decode functions do not compute any of its output bits. -/
def wordScalarRootProgram (a : WordIntegerScalar) (p : ℕ) : WordScalarRootResult :=
  let shifted:=binaryShiftProgram (2*p) a.numerator.positiveBits
  let divided:=binaryWordDivisionProgram shifted.bits a.denominator
  let root:=binaryWordSqrtProgram divided.quotient
  let trimmed:=binaryTrimProgram root.root
  let denominator:=binaryPowerTwoProgram p
  ⟨⟨⟨false,trimmed.bits⟩,denominator.bits,⟨binaryTrimProgram_canonical _,by intro _;rfl⟩,
      binaryPowerTwoProgram_canonical _,by rw [binaryPowerTwoProgram_value];positivity⟩,
    shifted,divided,root,trimmed,denominator⟩

theorem wordScalarRootProgram_decode (a : WordIntegerScalar) (p : ℕ) :
    (wordScalarRootProgram a p).scalar.decode=a.decode.root p := by
  apply integerScalar_eq_components
  · change (binaryWordValue (binaryTrimProgram
        (binaryWordSqrtProgram (binaryWordDivisionProgram
          (binaryShiftProgram (2*p) a.numerator.positiveBits).bits a.denominator).quotient).root).bits:ℤ)=_
    rw [binaryTrimProgram_value,binaryWordSqrtProgram_sqrt,
      (binaryWordDivisionProgram_div_mod _ a.denominator a.denominator_pos).1,
      binaryShiftProgram_value,SignedBinaryWord.positiveBits_value]
    simp only [IntegerScalar.root,WordIntegerScalar.decode,Nat.shiftLeft_eq]
  · change binaryWordValue (binaryPowerTwoProgram p).bits=expressionPowerTwo p
    rw [binaryPowerTwoProgram_value,expressionPowerTwo_eq]

theorem wordScalarRootProgram_value (a : WordIntegerScalar) (p : ℕ) :
    (wordScalarRootProgram a p).scalar.decode.value=rationalSqrtApprox a.decode.value p := by
  rw [wordScalarRootProgram_decode,IntegerScalar.root_value]

theorem wordScalarRootProgram_height_width (a : WordIntegerScalar) (A p : ℕ)
    (ha : IntegerScalarHeight a.decode A) :
    (wordScalarRootProgram a p).scalar.numerator.bits.length≤A+2*p+1 ∧
    (wordScalarRootProgram a p).scalar.denominator.length≤A+2*p+1 := by
  apply WordIntegerScalar.height_width
  rw [wordScalarRootProgram_decode]
  exact IntegerScalar.root_height a.decode A p ha

def WordScalarRootResult.actions (result : WordScalarRootResult) : ℕ :=
  result.numeratorShift.actions+result.divisionRun.trace.actions+result.rootRun.trace.actions+
    result.numeratorTrim.trace.actions+result.denominatorShift.actions+16

theorem wordScalarRootProgram_height_actions (a : WordIntegerScalar) (A p : ℕ)
    (ha : IntegerScalarHeight a.decode A) :
    (wordScalarRootProgram a p).actions≤256*(A+2*p+2)^2 := by
  have hw:=a.height_width A ha
  have hpos:=SignedBinaryWord.positiveBits_length a.numerator
  have hshift:=binaryShiftProgram_length (2*p) a.numerator.positiveBits
  have hshiftCost:=binaryShiftProgram_actions (2*p) a.numerator.positiveBits
  have hdivCost:=binaryWordDivisionProgram_uniform_actions
    (binaryShiftProgram (2*p) a.numerator.positiveBits).bits a.denominator (A+2*p+1) (by omega) (by omega)
  have hdivLen:=binaryWordDivisionProgram_quotient_length
    (binaryShiftProgram (2*p) a.numerator.positiveBits).bits a.denominator
  have hrootCost:=binaryWordSqrtProgram_actions
    (binaryWordDivisionProgram (binaryShiftProgram (2*p) a.numerator.positiveBits).bits a.denominator).quotient
  have hrootLen:=(binaryWordSqrtProgram_lengths
    (binaryWordDivisionProgram (binaryShiftProgram (2*p) a.numerator.positiveBits).bits a.denominator).quotient).1
  have htrimCost:=binaryTrimProgram_actions
    (binaryWordSqrtProgram (binaryWordDivisionProgram
      (binaryShiftProgram (2*p) a.numerator.positiveBits).bits a.denominator).quotient).root
  have hdenCost:=binaryPowerTwoProgram_actions p
  have hrootCost' : (binaryWordSqrtProgram (binaryWordDivisionProgram
      (binaryShiftProgram (2*p) a.numerator.positiveBits).bits a.denominator).quotient).trace.actions≤
        64*(A+2*p+2)^2 := by
    apply hrootCost.trans
    apply Nat.mul_le_mul_left 64
    exact Nat.pow_le_pow_left (by omega) _
  simp only [wordScalarRootProgram,WordScalarRootResult.actions]
  nlinarith

end CircuitRecursion
