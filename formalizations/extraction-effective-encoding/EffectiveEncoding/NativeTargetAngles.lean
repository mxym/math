import EffectiveEncoding.PreparedNativeInputs
import CircuitNumerical.NativeWordEvaluation

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

/-- Fixed native literal data, with no Int/Rat or Nat.bits constructor. -/
def nativeWordMinusOne : WordIntegerScalar :=
  ⟨⟨true,[true]⟩,[true],⟨.one,by intro h;cases h⟩,.one,by decide⟩


theorem nativeWordMinusOne_decode : nativeWordMinusOne.decode=IntegerScalar.ofInt (-1) := rfl


theorem nativeWordZero_decode : wordScalarZero.decode=IntegerScalar.ofInt 0 := rfl


def NativeAtomInput.cosExpression : NativeAtomInput → NativeScalarExpressionOracle
  | .pi,_ => .literal nativeWordMinusOne
  | .trivial,_ => .literal wordScalarOne
  | .merge r,p => .sqrt (.literal r.cosineInput) (p+1)


def NativeAtomInput.sinExpression : NativeAtomInput → NativeScalarExpressionOracle
  | .pi,_ | .trivial,_ => .literal wordScalarZero
  | .merge r,p => .sqrt (.literal r.sineInput) (p+1)


theorem prepareNativeAtomInput_cos_decode (a : AngleAtom) (p : ℕ) :
    ((prepareNativeAtomInput a).cosExpression p).wordRun.value.decode=rawAtomCos a p := by
  cases a with
  | pi => exact nativeWordMinusOne_decode
  | merge A B j =>
    by_cases hz : j=0 ∨ A+B=0
    · simp only [prepareNativeAtomInput,dite_eq_left hz,NativeAtomInput.cosExpression,
        NativeScalarExpression.wordRun,rawAtomCos,dite_eq_left hz,wordScalarOne_decode]
    · simp only [prepareNativeAtomInput,dite_eq_right hz,NativeAtomInput.cosExpression,
        NativeScalarExpression.wordRun,wordScalarRootProgram_decode,nativeMergeInputProgram_cosine_decode,
        rawAtomCos,dite_eq_right hz,IntegerScalar.binaryRoot_eq]


theorem prepareNativeAtomInput_sin_decode (a : AngleAtom) (p : ℕ) :
    ((prepareNativeAtomInput a).sinExpression p).wordRun.value.decode=rawAtomSin a p := by
  cases a with
  | pi => exact nativeWordZero_decode
  | merge A B j =>
    by_cases hz : j=0 ∨ A+B=0
    · simp only [prepareNativeAtomInput,dite_eq_left hz,NativeAtomInput.sinExpression,
        NativeScalarExpression.wordRun,rawAtomSin,dite_eq_left hz,nativeWordZero_decode]
    · simp only [prepareNativeAtomInput,dite_eq_right hz,NativeAtomInput.sinExpression,
        NativeScalarExpression.wordRun,wordScalarRootProgram_decode,nativeMergeInputProgram_sine_decode,
        rawAtomSin,dite_eq_right hz,IntegerScalar.binaryRoot_eq]


def nativeInputHalfCos : ℕ → NativeScalarExpressionOracle → NativeScalarExpressionOracle
  | 0,f => f
  | n+1,f => fun p => .sqrt
      (.mul (.literal wordScalarHalf) (.add (.literal wordScalarOne) (nativeInputHalfCos n f (2*p+2)))) (p+1)


def nativeInputHalfSin : ℕ → NativeScalarExpressionOracle → NativeScalarExpressionOracle → NativeScalarExpressionOracle
  | 0,_,g => g
  | n+1,f,_ => fun p => .sqrt (.meanMinus (nativeInputHalfCos n f (2*p+2))) (p+1)


theorem nativeInputHalfCos_decode (n : ℕ) (f : NativeScalarExpressionOracle) (g : RawScalarOracle)
    (hf : ∀ p,(f p).wordRun.value.decode=g p) (p : ℕ) :
    (nativeInputHalfCos n f p).wordRun.value.decode=rawHalfCos n g p := by
  induction n generalizing p with
  | zero => exact hf p
  | succ n ih =>
    simp only [nativeInputHalfCos,NativeScalarExpression.wordRun,wordScalarRootProgram_decode,
      wordScalarMultiplyProgram_decode,wordScalarAddProgram_decode,wordScalarOne_decode,
      wordScalarHalf_decode,rawHalfCos,IntegerScalar.binaryRoot_eq,ih]
    rfl


theorem nativeInputHalfSin_decode (n : ℕ) (f g : NativeScalarExpressionOracle) (a b : RawScalarOracle)
    (hf : ∀ p,(f p).wordRun.value.decode=a p) (hg : ∀ p,(g p).wordRun.value.decode=b p) (p : ℕ) :
    (nativeInputHalfSin n f g p).wordRun.value.decode=rawHalfSin n a b p := by
  cases n with
  | zero => exact hg p
  | succ n =>
    simp only [nativeInputHalfSin,NativeScalarExpression.wordRun,wordScalarRootProgram_decode,
      wordScalarMeanMinusProgram_decode,rawHalfSin,IntegerScalar.binaryRoot_eq,nativeInputHalfCos_decode n f a hf]


def NativeAngleInput.cosExpression (a : NativeAngleInput) : NativeScalarExpressionOracle :=
  nativeInputHalfCos a.halvings a.atom.cosExpression


def NativeAngleInput.sinExpression (a : NativeAngleInput) : NativeScalarExpressionOracle := fun p =>
  let s:=nativeInputHalfSin a.halvings a.atom.cosExpression a.atom.sinExpression p
  if a.negative then .neg s else s


theorem prepareNativeAngleInput_cos_decode (a : AngleCode) (p : ℕ) :
    ((prepareNativeAngleInput a).cosExpression p).wordRun.value.decode=a.rawCos p :=
  nativeInputHalfCos_decode a.halvings _ _ (prepareNativeAtomInput_cos_decode a.atom) p


theorem prepareNativeAngleInput_sin_decode (a : AngleCode) (p : ℕ) :
    ((prepareNativeAngleInput a).sinExpression p).wordRun.value.decode=a.rawSin p := by
  have hs:=nativeInputHalfSin_decode a.halvings _ _ _ _
    (prepareNativeAtomInput_cos_decode a.atom) (prepareNativeAtomInput_sin_decode a.atom) p
  cases hn : a.negative <;> simp only [NativeAngleInput.sinExpression,prepareNativeAngleInput,AngleCode.rawSin,
    hn,Bool.false_eq_true,ite_false,ite_true,NativeScalarExpression.wordRun,wordScalarNegateProgram_decode,hs]


def NativeAngleInput.half (a : NativeAngleInput) (n : ℕ) : NativeAngleInput :=
  {a with halvings:=a.halvings+n}


theorem prepareNativeAngleInput_half (a : AngleCode) (n : ℕ) :
    prepareNativeAngleInput (a.half n)=(prepareNativeAngleInput a).half n := rfl

end EffectiveEncoding
