import EffectiveEncoding.NativeTargetPackets
import EffectiveEncoding.RawProviderBudgets
import CircuitNumerical.NativeExpressionRefinement

open CircuitCompletion CircuitRecursion Matrix
namespace EffectiveEncoding

/-- Fixed native data and the old rational literal have matching proof
semantics and a uniform representation bound; the native run uses the data. -/
theorem nativeProviderLiteral_refines (a : WordIntegerScalar) (r : ℚ) (B : ℕ)
    (hv : a.decode.value=r) (hh : IntegerScalarHeight a.decode B)
    (hb : 2*(B+1)≤20*rationalBinaryExponent r) :
    NativeScalarRefines (.literal a) (.literal r) := by
  constructor
  · change (rawScalarExpression a.decode).eval=r
    rw [←ScalarExpression.integerProgramRun_correct,rawScalarExpression_integerProgramRun,hv]
  · exact (rawScalarExpression_integerBitBudget a.decode B hh).trans hb
  · change (rawScalarExpression a.decode).operations≤20*1
    rw [rawScalarExpression_operations]
    decide


theorem nativeProviderHalf_refines : NativeScalarRefines (.literal wordScalarHalf) (.literal (1/2)) := by
  apply nativeProviderLiteral_refines wordScalarHalf (1/2) 1
  · rw [wordScalarHalf_decode]
    norm_num [IntegerScalar.inv,IntegerScalar.ofInt,IntegerScalar.value]
  · constructor <;> decide
  · norm_num [rationalBinaryExponent]


theorem nativeProviderMinusOne_refines : NativeScalarRefines (.literal nativeWordMinusOne) (.literal (-1)) := by
  apply nativeProviderLiteral_refines nativeWordMinusOne (-1) 0
  · rw [nativeWordMinusOne_decode]
    norm_num [IntegerScalar.ofInt,IntegerScalar.value]
  · constructor <;> decide
  · decide


theorem prepareNativeAtomInput_cos_refines (a : AngleAtom) (p : ℕ) :
    NativeScalarRefines ((prepareNativeAtomInput a).cosExpression p) (a.rawCosExpression p) := by
  cases a with
  | pi => exact nativeProviderMinusOne_refines
  | merge A B j =>
    by_cases hz : j=0 ∨ A+B=0
    · simpa only [prepareNativeAtomInput,dite_eq_left hz,NativeAtomInput.cosExpression,
        AngleAtom.rawCosExpression] using nativeScalarOne_refines
    · simp only [prepareNativeAtomInput,dite_eq_right hz,NativeAtomInput.cosExpression,
        AngleAtom.rawCosExpression]
      have h:=NativeScalarRefines.raw (nativeMergeInputProgram A B (by omega)).cosineInput
      rw [nativeMergeInputProgram_cosine_decode] at h
      exact h.sqrt (p+1)


theorem prepareNativeAtomInput_sin_refines (a : AngleAtom) (p : ℕ) :
    NativeScalarRefines ((prepareNativeAtomInput a).sinExpression p) (a.rawSinExpression p) := by
  cases a with
  | pi => exact nativeScalarZero_refines
  | merge A B j =>
    by_cases hz : j=0 ∨ A+B=0
    · simpa only [prepareNativeAtomInput,dite_eq_left hz,NativeAtomInput.sinExpression,
        AngleAtom.rawSinExpression] using nativeScalarZero_refines
    · simp only [prepareNativeAtomInput,dite_eq_right hz,NativeAtomInput.sinExpression,
        AngleAtom.rawSinExpression]
      have h:=NativeScalarRefines.raw (nativeMergeInputProgram A B (by omega)).sineInput
      rw [nativeMergeInputProgram_sine_decode] at h
      exact h.sqrt (p+1)


theorem nativeInputHalfCos_refines (n : ℕ) (f : NativeScalarExpressionOracle)
    (F : ScalarExpressionOracle) (hf : NativeScalarOracleRefines f F) :
    NativeScalarOracleRefines (nativeInputHalfCos n f) (halfCosExpression n F) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    intro p
    exact (nativeProviderHalf_refines.mul (nativeScalarOne_refines.add (ih (2*p+2)))).sqrt (p+1)


theorem nativeInputHalfSin_refines (n : ℕ) (f g : NativeScalarExpressionOracle)
    (F G : ScalarExpressionOracle) (hf : NativeScalarOracleRefines f F)
    (hg : NativeScalarOracleRefines g G) :
    NativeScalarOracleRefines (nativeInputHalfSin n f g) (halfSinExpression n F G) := by
  cases n with
  | zero => exact hg
  | succ n =>
    intro p
    exact ((nativeInputHalfCos_refines n f F hf (2*p+2)).meanMinus).sqrt (p+1)


theorem prepareNativeAngleInput_cos_refines (a : AngleCode) :
    NativeScalarOracleRefines (prepareNativeAngleInput a).cosExpression a.rawCosExpression :=
  nativeInputHalfCos_refines a.halvings _ _ (prepareNativeAtomInput_cos_refines a.atom)


theorem prepareNativeAngleInput_sin_refines (a : AngleCode) :
    NativeScalarOracleRefines (prepareNativeAngleInput a).sinExpression a.rawSinExpression := by
  have h:=nativeInputHalfSin_refines a.halvings _ _ _ _
    (prepareNativeAtomInput_cos_refines a.atom) (prepareNativeAtomInput_sin_refines a.atom)
  intro p
  cases hn : a.negative <;> simp only [prepareNativeAngleInput,NativeAngleInput.sinExpression,
    AngleCode.rawSinExpression,hn,Bool.false_eq_true,ite_false,ite_true]
  · exact h p
  · exact (h p).neg


theorem nativePhaseCosExpression_refines (a b : AngleCode) (p : ℕ) :
    NativeScalarRefines (nativePhaseCosExpression (prepareNativeAngleInput a) (prepareNativeAngleInput b) p)
      (rawPhaseCosExpression a b p) := by
  unfold nativePhaseCosExpression rawPhaseCosExpression
  rw [←prepareNativeAngleInput_half,←prepareNativeAngleInput_half]
  exact ((prepareNativeAngleInput_cos_refines (a.half 1) (p+3)).mul
    (prepareNativeAngleInput_cos_refines (b.half 1) (p+3))).add
      ((prepareNativeAngleInput_sin_refines (a.half 1) (p+3)).mul
        (prepareNativeAngleInput_sin_refines (b.half 1) (p+3)))


theorem nativePhaseSinExpression_refines (a b : AngleCode) (p : ℕ) :
    NativeScalarRefines (nativePhaseSinExpression (prepareNativeAngleInput a) (prepareNativeAngleInput b) p)
      (rawPhaseSinExpression a b p) := by
  unfold nativePhaseSinExpression rawPhaseSinExpression
  rw [←prepareNativeAngleInput_half,←prepareNativeAngleInput_half]
  exact ((prepareNativeAngleInput_sin_refines (a.half 1) (p+3)).mul
    (prepareNativeAngleInput_cos_refines (b.half 1) (p+3))).add
      (((prepareNativeAngleInput_cos_refines (a.half 1) (p+3)).mul
        (prepareNativeAngleInput_sin_refines (b.half 1) (p+3))).neg)

/-- Uniform factor twenty, independent of the number of half-angle levels.
This relates proof representations, not an executed rational shadow program. -/
theorem prepareNativeSingleInput_packet_refines (u : SingleCode) (p : ℕ) :
    NativePacketRefines ((prepareNativeSingleInput u).packetExpression p) (u.rawPacketExpression p) := by
  induction u with
  | hadamard =>
    apply NativePacketRefines.tuple
    intro i
    fin_cases i
    · exact nativeScalarZero_refines
    · exact (nativeProviderHalf_refines.sqrt (p+1)).neg
    · exact nativeScalarZero_refines
    · exact (nativeProviderHalf_refines.sqrt (p+1)).neg
  | yBasis =>
    apply NativePacketRefines.tuple
    intro i
    fin_cases i <;> exact nativeProviderHalf_refines
  | phase a b =>
    apply NativePacketRefines.tuple
    intro i
    fin_cases i
    · exact nativePhaseCosExpression_refines a b p
    · exact nativePhaseSinExpression_refines a b p
    · exact nativeScalarZero_refines
    · exact nativeScalarZero_refines
  | inverse u ih => exact ih.inverse

end EffectiveEncoding
