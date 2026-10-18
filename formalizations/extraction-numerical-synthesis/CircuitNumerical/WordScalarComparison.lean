import CircuitNumerical.WordScalarArithmetic

namespace CircuitRecursion

structure WordScalarComparisonResult where
  le : Bool
  leftRun : SignedWordMultiplicationResult
  rightRun : SignedWordMultiplicationResult
  comparisonRun : SignedWordComparisonResult

/-- Signed cross products are each stored once, followed by the actual signed
word comparison program. No rational or integer comparison chooses the bit. -/
def wordScalarLEProgram (a b : WordIntegerScalar) : WordScalarComparisonResult :=
  let left:=signedMultiplyProgram a.numerator ⟨false,b.denominator⟩
  let right:=signedMultiplyProgram b.numerator ⟨false,a.denominator⟩
  let comparison:=signedLEProgram left.word right.word
  ⟨comparison.le,left,right,comparison⟩

theorem wordScalarLEProgram_correct (a b : WordIntegerScalar) :
    (wordScalarLEProgram a b).le=true ↔ a.decode.crossLE b.decode := by
  change (signedLEProgram
    (signedMultiplyProgram a.numerator ⟨false,b.denominator⟩).word
    (signedMultiplyProgram b.numerator ⟨false,a.denominator⟩).word).le=true ↔ _
  rw [signedLEProgram_correct,signedMultiplyProgram_value,signedMultiplyProgram_value]
  rfl

theorem wordScalarLEProgram_value (a b : WordIntegerScalar) :
    (wordScalarLEProgram a b).le=true ↔ a.decode.value≤b.decode.value := by
  rw [wordScalarLEProgram_correct,IntegerScalar.crossLE_value]

def WordScalarComparisonResult.actions (result : WordScalarComparisonResult) : ℕ :=
  result.leftRun.actions+result.rightRun.actions+result.comparisonRun.actions+16

theorem wordScalarLEProgram_uniform_actions (a b : WordIntegerScalar) (B : ℕ)
    (ha : a.numerator.bits.length≤B ∧ a.denominator.length≤B)
    (hb : b.numerator.bits.length≤B ∧ b.denominator.length≤B) :
    (wordScalarLEProgram a b).actions≤400*(B+1)^2 := by
  have hl:=signedMultiplyProgram_uniform_actions a.numerator ⟨false,b.denominator⟩ B ha.1 hb.2
  have hr:=signedMultiplyProgram_uniform_actions b.numerator ⟨false,a.denominator⟩ B hb.1 ha.2
  have hll:=signedMultiplyProgram_length a.numerator ⟨false,b.denominator⟩
  have hrl:=signedMultiplyProgram_length b.numerator ⟨false,a.denominator⟩
  have hc:=signedLEProgram_actions (signedMultiplyProgram a.numerator ⟨false,b.denominator⟩).word
    (signedMultiplyProgram b.numerator ⟨false,a.denominator⟩).word
  have hm : max (signedMultiplyProgram a.numerator ⟨false,b.denominator⟩).word.bits.length
      (signedMultiplyProgram b.numerator ⟨false,a.denominator⟩).word.bits.length≤3*B := by
    simp only at hll hrl
    omega
  simp only [wordScalarLEProgram,WordScalarComparisonResult.actions]
  nlinarith

theorem wordScalarLEProgram_height_actions (a b : WordIntegerScalar) (B : ℕ)
    (ha : IntegerScalarHeight a.decode B) (hb : IntegerScalarHeight b.decode B) :
    (wordScalarLEProgram a b).actions≤400*(B+2)^2 := by
  simpa only [Nat.add_assoc] using wordScalarLEProgram_uniform_actions a b (B+1)
    (a.height_width B ha) (b.height_width B hb)

end CircuitRecursion
