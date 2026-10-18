import CircuitNumerical.WordScalarComparison

namespace CircuitRecursion

theorem SignedBinaryWord.canonical_nonzero (a : SignedBinaryWord) (h : a.Canonical)
    (hne : a.bits≠[]) : a.value≠0 := by
  intro hv
  have ha : a.value.natAbs=0 := by rw [hv];rfl
  rw [SignedBinaryWord.natAbs_value] at ha
  exact hne ((binaryWordCanonical_zero_iff a.bits h.1).mp ha)

theorem SignedBinaryWord.sign_value (a : SignedBinaryWord) (hne : a.value≠0) :
    a.value.sign=if a.negative then -1 else 1 := by
  have hp : binaryWordValue a.bits≠0 := by
    intro h
    apply hne
    cases hs : a.negative <;> simp [value,hs,h]
  have hpos : (0:ℤ)<(binaryWordValue a.bits:ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hp
  cases hs : a.negative with
  | false =>
    simp only [value,hs,Bool.false_eq_true,ite_false]
    exact Int.sign_eq_one_of_pos hpos
  | true =>
    simp only [value,hs,ite_true]
    exact Int.sign_eq_neg_one_of_neg (by omega)

def wordScalarZero : WordIntegerScalar :=
  ⟨⟨false,[]⟩,[true],⟨.nil,by intro _;rfl⟩,.one,by decide⟩

structure WordScalarNegationResult where
  scalar : WordIntegerScalar
  normalizationRun : SignedBinaryNormalizationResult

def wordScalarNegateProgram (a : WordIntegerScalar) : WordScalarNegationResult :=
  let normalization:=signedBinaryNormalizeProgram a.numerator.negate
  ⟨⟨normalization.word,a.denominator,signedBinaryNormalizeProgram_canonical _,
      a.denominator_canonical,a.denominator_pos⟩,normalization⟩

theorem wordScalarNegateProgram_decode (a : WordIntegerScalar) :
    (wordScalarNegateProgram a).scalar.decode=a.decode.neg := by
  apply integerScalar_eq_components
  · change (signedBinaryNormalizeProgram a.numerator.negate).word.value= -a.numerator.value
    rw [signedBinaryNormalizeProgram_value,SignedBinaryWord.negate_value]
  · rfl

theorem wordScalarNegateProgram_actions (a : WordIntegerScalar) :
    (wordScalarNegateProgram a).normalizationRun.actions+4≤6*(a.numerator.bits.length+1)+8 := by
  have h:=signedBinaryNormalizeProgram_actions a.numerator.negate
  simpa only [wordScalarNegateProgram,SignedBinaryWord.negate] using Nat.add_le_add_right h 4

inductive WordScalarReciprocalDecision where
  | zero | nonzero

structure WordScalarReciprocalResult where
  scalar : WordIntegerScalar
  decision : WordScalarReciprocalDecision

/-- Canonical input makes the zero test an empty-list test. In the nonzero
branch, reciprocal only copies/swaps the magnitude words and retains sign.
No division, rational normalization or integer sign computation is executed. -/
def wordScalarInverseProgram (a : WordIntegerScalar) : WordScalarReciprocalResult :=
  if h : a.numerator.bits=[] then ⟨wordScalarZero,.zero⟩ else
    ⟨⟨⟨a.numerator.negative,a.denominator⟩,a.numerator.bits,by
        constructor
        · exact a.denominator_canonical
        · intro he
          change a.denominator=[] at he
          have hz : binaryWordValue a.denominator=0 := by rw [he];rfl
          exact (by have hp:=a.denominator_pos;omega : False).elim,
      a.numerator_canonical.1,by
        have hn : binaryWordValue a.numerator.bits≠0 := by
          intro hv
          exact h ((binaryWordCanonical_zero_iff _ a.numerator_canonical.1).mp hv)
        exact Nat.pos_of_ne_zero hn⟩,.nonzero⟩

theorem wordScalarInverseProgram_decode (a : WordIntegerScalar) :
    (wordScalarInverseProgram a).scalar.decode=a.decode.inv := by
  by_cases hz : a.numerator.bits=[]
  · have hn : a.decode.numerator=0 := by
      change a.numerator.value=0
      cases hs : a.numerator.negative <;> simp [SignedBinaryWord.value,hs,hz,binaryWordValue]
    simp only [wordScalarInverseProgram,dif_pos hz,IntegerScalar.inv,dif_pos hn]
    rfl
  · have hn:=SignedBinaryWord.canonical_nonzero a.numerator a.numerator_canonical hz
    change a.decode.numerator≠0 at hn
    simp only [wordScalarInverseProgram,dif_neg hz,IntegerScalar.inv,dif_neg hn]
    apply integerScalar_eq_components
    · change (⟨a.numerator.negative,a.denominator⟩ : SignedBinaryWord).value=
        a.numerator.value.sign*(binaryWordValue a.denominator:ℤ)
      rw [SignedBinaryWord.sign_value _ hn]
      cases hs : a.numerator.negative <;> simp [SignedBinaryWord.value,hs]
    · exact (SignedBinaryWord.natAbs_value a.numerator).symm

/-- Twelve local constructor/sign/list-test actions; magnitude words are
shared immutable list values. Copying all their cells would be a different
representation model and is not silently charged as constant. -/
def WordScalarReciprocalResult.actions (_result : WordScalarReciprocalResult) : ℕ := 12

theorem wordScalarInverseProgram_actions (a : WordIntegerScalar) :
    (wordScalarInverseProgram a).actions≤12 := by rfl

end CircuitRecursion
