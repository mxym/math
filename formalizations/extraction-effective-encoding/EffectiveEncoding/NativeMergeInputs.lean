import EffectiveEncoding.UnaryWordEncoding

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

/-- Two actual unary-to-word encodings and one shared denominator add/trim.
Both fraction payloads reuse the same stored denominator word. -/
structure NativeMergeInputResult where
  cosineInput : WordIntegerScalar
  sineInput : WordIntegerScalar
  leftEncoding : UnaryWordEncodingResult
  rightEncoding : UnaryWordEncodingResult
  denominatorAddition : BinaryWordAdditionResult
  denominatorTrim : BinaryWordTrimResult

/-- Construct A/(A+B), B/(A+B) entirely as Boolean fraction payloads.
Only the outer bounded unary recursion is Nat-controlled; no Nat.bits, Rat
constructor, high-level integer conversion or fraction decode is executed. -/
def nativeMergeInputProgram (A B : ℕ) (h : 0<A+B) : NativeMergeInputResult :=
  let left:=unaryWordEncoding A
  let right:=unaryWordEncoding B
  let addition:=binaryAddProgram left.bits right.bits false
  let denominator:=binaryTrimProgram addition.bits
  let hp : 0<binaryWordValue denominator.bits := by
    simp only [denominator,binaryTrimProgram_value,addition,binaryAddProgram_value,
      left,right,unaryWordEncoding_value,binaryBitValue,Nat.add_zero]
    exact h
  let cosine : WordIntegerScalar:=
    ⟨⟨false,left.bits⟩,denominator.bits,⟨unaryWordEncoding_canonical A,by intro _;rfl⟩,
      binaryTrimProgram_canonical _,hp⟩
  let sine : WordIntegerScalar:=
    ⟨⟨false,right.bits⟩,denominator.bits,⟨unaryWordEncoding_canonical B,by intro _;rfl⟩,
      binaryTrimProgram_canonical _,hp⟩
  ⟨cosine,sine,left,right,addition,denominator⟩


theorem nativeMergeInputProgram_cosine_decode (A B : ℕ) (h : 0<A+B) :
    (nativeMergeInputProgram A B h).cosineInput.decode=integerFraction A (A+B) h := by
  apply integerScalar_eq_components
  · simp only [nativeMergeInputProgram,WordIntegerScalar.decode,SignedBinaryWord.value,
      Bool.false_eq_true,ite_false,unaryWordEncoding_value,integerFraction]
  · simp only [nativeMergeInputProgram,WordIntegerScalar.decode,binaryTrimProgram_value,binaryAddProgram_value,
      unaryWordEncoding_value,binaryBitValue,Nat.add_zero,integerFraction]


theorem nativeMergeInputProgram_sine_decode (A B : ℕ) (h : 0<A+B) :
    (nativeMergeInputProgram A B h).sineInput.decode=integerFraction B (A+B) h := by
  apply integerScalar_eq_components
  · simp only [nativeMergeInputProgram,WordIntegerScalar.decode,SignedBinaryWord.value,
      Bool.false_eq_true,ite_false,unaryWordEncoding_value,integerFraction]
  · simp only [nativeMergeInputProgram,WordIntegerScalar.decode,binaryTrimProgram_value,binaryAddProgram_value,
      unaryWordEncoding_value,binaryBitValue,Nat.add_zero,integerFraction]


def NativeMergeInputResult.incrementTrimActions (r : NativeMergeInputResult) : ℕ :=
  r.leftEncoding.trace.incrementTrimActions+r.rightEncoding.trace.incrementTrimActions+
    r.denominatorAddition.trace.actions+r.denominatorTrim.trace.actions


theorem nativeMergeInputProgram_actions (A B M : ℕ) (h : 0<A+B) (hM : A+B≤M) :
    (nativeMergeInputProgram A B h).incrementTrimActions≤100*(M+2)^2 := by
  have ha:=unaryWordEncoding_incrementTrimActions A
  have hb:=unaryWordEncoding_incrementTrimActions B
  have hwa:=unaryWordEncoding_length A
  have hwb:=unaryWordEncoding_length B
  have hadd:=binaryAddProgram_actions (unaryWordEncoding A).bits (unaryWordEncoding B).bits false
  have hlen:=binaryAddProgram_length (unaryWordEncoding A).bits (unaryWordEncoding B).bits false
  have ht:=binaryTrimProgram_actions (binaryAddProgram (unaryWordEncoding A).bits (unaryWordEncoding B).bits false).bits
  have hcA : (unaryWordEncoding A).trace.incrementTrimActions≤32*(M+1)^2 := by
    exact ha.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have hcB : (unaryWordEncoding B).trace.incrementTrimActions≤32*(M+1)^2 := by
    exact hb.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have hcAdd : (binaryAddProgram (unaryWordEncoding A).bits (unaryWordEncoding B).bits false).trace.actions≤12*(M+2) := by omega
  have hcTrim : (binaryTrimProgram (binaryAddProgram (unaryWordEncoding A).bits (unaryWordEncoding B).bits false).bits).trace.actions≤6*(M+3) := by omega
  simp only [NativeMergeInputResult.incrementTrimActions,nativeMergeInputProgram]
  nlinarith


theorem nativeMergeInputProgram_incrementCount (A B : ℕ) (h : 0<A+B) :
    (nativeMergeInputProgram A B h).leftEncoding.trace.incrementCount+
      (nativeMergeInputProgram A B h).rightEncoding.trace.incrementCount=A+B := by
  simp only [nativeMergeInputProgram,unaryWordEncoding_incrementCount]


theorem nativeMergeInputProgram_cosine_height (A B M : ℕ) (h : 0<A+B) (hM : A+B≤M) :
    IntegerScalarHeight (nativeMergeInputProgram A B h).cosineInput.decode (binaryWidth M) := by
  rw [nativeMergeInputProgram_cosine_decode]
  have hp : M≤2^binaryWidth M :=
    (Nat.le_succ M).trans (Nat.le_pow_clog (by decide : 1<2) (M+1))
  constructor
  · exact hM.trans hp
  · simp only [integerFraction,Int.natAbs_natCast]
    omega


theorem nativeMergeInputProgram_sine_height (A B M : ℕ) (h : 0<A+B) (hM : A+B≤M) :
    IntegerScalarHeight (nativeMergeInputProgram A B h).sineInput.decode (binaryWidth M) := by
  rw [nativeMergeInputProgram_sine_decode]
  have hp : M≤2^binaryWidth M :=
    (Nat.le_succ M).trans (Nat.le_pow_clog (by decide : 1<2) (M+1))
  constructor
  · exact hM.trans hp
  · simp only [integerFraction,Int.natAbs_natCast]
    omega

end EffectiveEncoding
