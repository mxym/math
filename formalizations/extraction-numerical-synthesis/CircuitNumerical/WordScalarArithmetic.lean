import CircuitNumerical.NaturalWordMultiplication

namespace CircuitRecursion

/-- A raw fraction represented entirely by canonical Boolean words. There is
no gcd reduction. The proof fields state the representation invariant only. -/
structure WordIntegerScalar where
  numerator : SignedBinaryWord
  denominator : List Bool
  numerator_canonical : numerator.Canonical
  denominator_canonical : BinaryWordCanonical denominator
  denominator_pos : 0<binaryWordValue denominator

/-- Semantic decoding, not an algorithm called by the word programs. -/
def WordIntegerScalar.decode (a : WordIntegerScalar) : IntegerScalar :=
  ⟨a.numerator.value,binaryWordValue a.denominator,a.denominator_pos⟩

theorem integerScalar_eq_components (a b : IntegerScalar)
    (hn : a.numerator=b.numerator) (hd : a.denominator=b.denominator) : a=b := by
  cases a
  cases b
  cases hn
  cases hd
  rfl

theorem WordIntegerScalar.height_width (a : WordIntegerScalar) (B : ℕ)
    (h : IntegerScalarHeight a.decode B) :
    a.numerator.bits.length≤B+1 ∧ a.denominator.length≤B+1 := by
  constructor
  · exact SignedBinaryWord.canonical_width _ a.numerator_canonical B h.2
  · exact binaryWordCanonical_width _ a.denominator_canonical B h.1

structure WordScalarMultiplicationResult where
  scalar : WordIntegerScalar
  numeratorRun : SignedWordMultiplicationResult
  denominatorRun : NaturalWordMultiplicationResult

def wordScalarMultiplyProgram (a b : WordIntegerScalar) : WordScalarMultiplicationResult :=
  let numerator:=signedMultiplyProgram a.numerator b.numerator
  let denominator:=naturalMultiplyProgram a.denominator b.denominator
  ⟨⟨numerator.word,denominator.bits,signedMultiplyProgram_canonical _ _,
      naturalMultiplyProgram_canonical _ _,by
        rw [naturalMultiplyProgram_value]
        exact Nat.mul_pos a.denominator_pos b.denominator_pos⟩,numerator,denominator⟩

theorem wordScalarMultiplyProgram_decode (a b : WordIntegerScalar) :
    (wordScalarMultiplyProgram a b).scalar.decode=a.decode.mul b.decode := by
  apply integerScalar_eq_components
  · exact signedMultiplyProgram_value a.numerator b.numerator
  · exact naturalMultiplyProgram_value a.denominator b.denominator

def WordScalarMultiplicationResult.actions (result : WordScalarMultiplicationResult) : ℕ :=
  result.numeratorRun.actions+result.denominatorRun.actions+8

theorem wordScalarMultiplyProgram_uniform_actions (a b : WordIntegerScalar) (B : ℕ)
    (ha : a.numerator.bits.length≤B ∧ a.denominator.length≤B)
    (hb : b.numerator.bits.length≤B ∧ b.denominator.length≤B) :
    (wordScalarMultiplyProgram a b).actions≤208*(B+1)^2 := by
  have hn:=signedMultiplyProgram_uniform_actions a.numerator b.numerator B ha.1 hb.1
  have hd:=naturalMultiplyProgram_uniform_actions a.denominator b.denominator B ha.2 hb.2
  simp only [wordScalarMultiplyProgram,WordScalarMultiplicationResult.actions]
  nlinarith

theorem wordScalarMultiplyProgram_height_actions (a b : WordIntegerScalar) (B : ℕ)
    (ha : IntegerScalarHeight a.decode B) (hb : IntegerScalarHeight b.decode B) :
    (wordScalarMultiplyProgram a b).actions≤208*(B+2)^2 := by
  simpa only [Nat.add_assoc] using wordScalarMultiplyProgram_uniform_actions a b (B+1)
    (a.height_width B ha) (b.height_width B hb)

structure WordScalarAdditionResult where
  scalar : WordIntegerScalar
  leftRun : SignedWordMultiplicationResult
  rightRun : SignedWordMultiplicationResult
  additionRun : SignedWordAdditionResult
  denominatorRun : NaturalWordMultiplicationResult

def wordScalarAddProgram (a b : WordIntegerScalar) : WordScalarAdditionResult :=
  let left:=signedMultiplyProgram a.numerator ⟨false,b.denominator⟩
  let right:=signedMultiplyProgram b.numerator ⟨false,a.denominator⟩
  let addition:=signedAddProgram left.word right.word
  let denominator:=naturalMultiplyProgram a.denominator b.denominator
  ⟨⟨addition.word,denominator.bits,signedAddProgram_canonical _ _,
      naturalMultiplyProgram_canonical _ _,by
        rw [naturalMultiplyProgram_value]
        exact Nat.mul_pos a.denominator_pos b.denominator_pos⟩,left,right,addition,denominator⟩

theorem wordScalarAddProgram_decode (a b : WordIntegerScalar) :
    (wordScalarAddProgram a b).scalar.decode=a.decode.add b.decode := by
  apply integerScalar_eq_components
  · change (signedAddProgram
        (signedMultiplyProgram a.numerator ⟨false,b.denominator⟩).word
        (signedMultiplyProgram b.numerator ⟨false,a.denominator⟩).word).word.value=_
    rw [signedAddProgram_value,signedMultiplyProgram_value,signedMultiplyProgram_value]
    rfl
  · exact naturalMultiplyProgram_value a.denominator b.denominator

def WordScalarAdditionResult.actions (result : WordScalarAdditionResult) : ℕ :=
  result.leftRun.actions+result.rightRun.actions+result.additionRun.actions+result.denominatorRun.actions+16

theorem wordScalarAddProgram_uniform_actions (a b : WordIntegerScalar) (B : ℕ)
    (ha : a.numerator.bits.length≤B ∧ a.denominator.length≤B)
    (hb : b.numerator.bits.length≤B ∧ b.denominator.length≤B) :
    (wordScalarAddProgram a b).actions≤500*(B+1)^2 := by
  have hl:=signedMultiplyProgram_uniform_actions a.numerator ⟨false,b.denominator⟩ B ha.1 hb.2
  have hr:=signedMultiplyProgram_uniform_actions b.numerator ⟨false,a.denominator⟩ B hb.1 ha.2
  have hd:=naturalMultiplyProgram_uniform_actions a.denominator b.denominator B ha.2 hb.2
  have hll:=signedMultiplyProgram_length a.numerator ⟨false,b.denominator⟩
  have hrl:=signedMultiplyProgram_length b.numerator ⟨false,a.denominator⟩
  have hadd:=signedAddProgram_actions (signedMultiplyProgram a.numerator ⟨false,b.denominator⟩).word
    (signedMultiplyProgram b.numerator ⟨false,a.denominator⟩).word
  have hm : max (signedMultiplyProgram a.numerator ⟨false,b.denominator⟩).word.bits.length
      (signedMultiplyProgram b.numerator ⟨false,a.denominator⟩).word.bits.length≤3*B := by
    simp only at hll hrl
    omega
  simp only [wordScalarAddProgram,WordScalarAdditionResult.actions]
  nlinarith

theorem wordScalarAddProgram_height_actions (a b : WordIntegerScalar) (B : ℕ)
    (ha : IntegerScalarHeight a.decode B) (hb : IntegerScalarHeight b.decode B) :
    (wordScalarAddProgram a b).actions≤500*(B+2)^2 := by
  simpa only [Nat.add_assoc] using wordScalarAddProgram_uniform_actions a b (B+1)
    (a.height_width B ha) (b.height_width B hb)

end CircuitRecursion
