import CircuitNumerical.WordInputEncoding

namespace CircuitRecursion

def wordScalarOne : WordIntegerScalar :=
  ⟨⟨false,[true]⟩,[true],⟨.one,by intro _;rfl⟩,.one,by decide⟩

def wordScalarHalf : WordIntegerScalar :=
  ⟨⟨false,[true]⟩,[false,true],⟨.one,by intro _;rfl⟩,.prepend false true [] .one,by decide⟩

theorem wordScalarOne_decode : wordScalarOne.decode=IntegerScalar.ofInt 1 := by rfl

theorem wordScalarHalf_decode : wordScalarHalf.decode=(IntegerScalar.ofInt 2).inv := by
  rfl

structure WordScalarMeanMinusResult where
  scalar : WordIntegerScalar
  negationRun : WordScalarNegationResult
  additionRun : WordScalarAdditionResult
  multiplicationRun : WordScalarMultiplicationResult

def wordScalarMeanMinusProgram (a : WordIntegerScalar) : WordScalarMeanMinusResult :=
  let negated:=wordScalarNegateProgram a
  let added:=wordScalarAddProgram wordScalarOne negated.scalar
  let multiplied:=wordScalarMultiplyProgram added.scalar wordScalarHalf
  ⟨multiplied.scalar,negated,added,multiplied⟩

theorem wordScalarMeanMinusProgram_decode (a : WordIntegerScalar) :
    (wordScalarMeanMinusProgram a).scalar.decode=a.decode.meanMinus := by
  simp only [wordScalarMeanMinusProgram,wordScalarMultiplyProgram_decode,wordScalarAddProgram_decode,
    wordScalarNegateProgram_decode,wordScalarOne_decode,wordScalarHalf_decode,IntegerScalar.meanMinus]

def WordScalarMeanMinusResult.actions (result : WordScalarMeanMinusResult) : ℕ :=
  result.negationRun.normalizationRun.actions+4+result.additionRun.actions+result.multiplicationRun.actions+16

theorem wordScalarMeanMinusProgram_height_actions (a : WordIntegerScalar) (A : ℕ)
    (ha : IntegerScalarHeight a.decode A) :
    (wordScalarMeanMinusProgram a).actions≤1000*(A+3)^2 := by
  have hn:=wordScalarNegateProgram_actions a
  have hw:=(a.height_width A ha).1
  have hneg : IntegerScalarHeight (wordScalarNegateProgram a).scalar.decode A := by
    rw [wordScalarNegateProgram_decode]
    exact IntegerScalar.neg_height a.decode A ha
  have hone0 : IntegerScalarHeight wordScalarOne.decode 0 := by constructor <;> decide
  have hone : IntegerScalarHeight wordScalarOne.decode A := IntegerScalarHeight.mono _ 0 A hone0 (by omega)
  have hadd:=wordScalarAddProgram_height_actions wordScalarOne (wordScalarNegateProgram a).scalar A hone hneg
  have hadh : IntegerScalarHeight
      (wordScalarAddProgram wordScalarOne (wordScalarNegateProgram a).scalar).scalar.decode (A+1) := by
    rw [wordScalarAddProgram_decode]
    simpa only [Nat.zero_add] using IntegerScalar.add_height _ _ 0 A hone0 hneg
  have hhalf0 : IntegerScalarHeight wordScalarHalf.decode 1 := by constructor <;> decide
  have hhalf : IntegerScalarHeight wordScalarHalf.decode (A+1) := IntegerScalarHeight.mono _ 1 (A+1) hhalf0 (by omega)
  have hm:=wordScalarMultiplyProgram_height_actions
    (wordScalarAddProgram wordScalarOne (wordScalarNegateProgram a).scalar).scalar wordScalarHalf (A+1) hadh hhalf
  simp only [Nat.add_assoc] at hm
  norm_num only at hm
  simp only [wordScalarMeanMinusProgram,WordScalarMeanMinusResult.actions]
  nlinarith

structure WordStoppingThresholdResult where
  scalar : WordIntegerScalar
  denominatorRun : BinaryWordShiftResult

def wordStoppingThresholdProgram (t : ℕ) : WordStoppingThresholdResult :=
  let denominator:=binaryPowerTwoProgram (2*t)
  ⟨⟨⟨false,[false,true]⟩,denominator.bits,⟨.prepend false true [] .one,by intro _;rfl⟩,
      binaryPowerTwoProgram_canonical _,by rw [binaryPowerTwoProgram_value];positivity⟩,denominator⟩

theorem wordStoppingThresholdProgram_decode (t : ℕ) :
    (wordStoppingThresholdProgram t).scalar.decode=integerStoppingThreshold t := by
  apply integerScalar_eq_components
  · rfl
  · change binaryWordValue (binaryPowerTwoProgram (2*t)).bits=expressionPowerTwo (2*t)
    rw [binaryPowerTwoProgram_value,expressionPowerTwo_eq]

def WordStoppingThresholdResult.actions (result : WordStoppingThresholdResult) : ℕ :=
  result.denominatorRun.actions+8

theorem wordStoppingThresholdProgram_actions (t : ℕ) :
    (wordStoppingThresholdProgram t).actions≤32*(t+2) := by
  have h:=binaryPowerTwoProgram_actions (2*t)
  simp only [wordStoppingThresholdProgram,WordStoppingThresholdResult.actions]
  omega

end CircuitRecursion
