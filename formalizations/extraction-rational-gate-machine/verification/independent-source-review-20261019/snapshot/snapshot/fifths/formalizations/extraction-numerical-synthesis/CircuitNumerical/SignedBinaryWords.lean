import CircuitNumerical.CanonicalBinaryWords

namespace CircuitRecursion

structure SignedBinaryWord where
  negative : Bool
  bits : List Bool

def SignedBinaryWord.value (a : SignedBinaryWord) : ℤ :=
  if a.negative then -(binaryWordValue a.bits : ℤ) else (binaryWordValue a.bits : ℤ)

def SignedBinaryWord.Canonical (a : SignedBinaryWord) : Prop :=
  BinaryWordCanonical a.bits ∧ (a.bits=[] → a.negative=false)

structure SignedBinaryNormalizationResult where
  word : SignedBinaryWord
  trace : BinaryWordTrimTrace

/-- Actual trimming followed by a list-constructor zero test. Zero has the
empty magnitude and false sign. The trimmed result is stored once. -/
def signedBinaryNormalizeProgram (a : SignedBinaryWord) : SignedBinaryNormalizationResult :=
  let trimmed:=binaryTrimProgram a.bits
  ⟨⟨match trimmed.bits with | [] => false | _::_ => a.negative,trimmed.bits⟩,trimmed.trace⟩

theorem SignedBinaryWord.natAbs_value (a : SignedBinaryWord) :
    a.value.natAbs=binaryWordValue a.bits := by
  cases hs : a.negative <;> simp [SignedBinaryWord.value,hs]

theorem signedBinaryNormalizeProgram_value (a : SignedBinaryWord) :
    (signedBinaryNormalizeProgram a).word.value=a.value := by
  have hv:=binaryTrimProgram_value a.bits
  cases ht : (binaryTrimProgram a.bits).bits with
  | nil =>
    rw [ht] at hv
    cases hs : a.negative <;>
      simp only [signedBinaryNormalizeProgram,ht,SignedBinaryWord.value,hs,binaryWordValue,binaryBitValue,
        Bool.false_eq_true,ite_false,ite_true] <;>
      simp only [binaryWordValue] at hv <;> rw [←hv] <;> rfl
  | cons b bs =>
    simp only [signedBinaryNormalizeProgram,ht,SignedBinaryWord.value]
    rw [←ht,binaryTrimProgram_value]

theorem signedBinaryNormalizeProgram_canonical (a : SignedBinaryWord) :
    (signedBinaryNormalizeProgram a).word.Canonical := by
  have h:=binaryTrimProgram_canonical a.bits
  constructor
  · exact h
  · intro he
    change (binaryTrimProgram a.bits).bits=[] at he
    simp only [signedBinaryNormalizeProgram,he]

theorem signedBinaryNormalizeProgram_length (a : SignedBinaryWord) :
    (signedBinaryNormalizeProgram a).word.bits.length≤a.bits.length :=
  binaryTrimProgram_length a.bits

theorem SignedBinaryWord.canonical_width (a : SignedBinaryWord) (h : a.Canonical)
    (B : ℕ) (hv : a.value.natAbs≤2^B) : a.bits.length≤B+1 := by
  apply binaryWordCanonical_width a.bits h.1 B
  simpa only [SignedBinaryWord.natAbs_value] using hv

theorem signedBinaryNormalizeProgram_width (a : SignedBinaryWord) (B : ℕ)
    (hv : a.value.natAbs≤2^B) : (signedBinaryNormalizeProgram a).word.bits.length≤B+1 := by
  apply SignedBinaryWord.canonical_width _ (signedBinaryNormalizeProgram_canonical a) B
  simpa only [signedBinaryNormalizeProgram_value] using hv

def SignedBinaryNormalizationResult.actions (result : SignedBinaryNormalizationResult) : ℕ :=
  result.trace.actions+4

theorem signedBinaryNormalizeProgram_actions (a : SignedBinaryWord) :
    (signedBinaryNormalizeProgram a).actions≤6*(a.bits.length+1)+4 := by
  have h:=binaryTrimProgram_actions a.bits
  simpa only [signedBinaryNormalizeProgram,SignedBinaryNormalizationResult.actions] using Nat.add_le_add_right h 4

def SignedBinaryWord.negate (a : SignedBinaryWord) : SignedBinaryWord := ⟨!a.negative,a.bits⟩

theorem SignedBinaryWord.negate_value (a : SignedBinaryWord) :
    a.negate.value= -a.value := by
  cases hs : a.negative <;> simp [SignedBinaryWord.negate,SignedBinaryWord.value,hs]

theorem binarySubtractProgram_intValue (as bs : List Bool) (h : binaryWordValue bs≤binaryWordValue as) :
    (binaryWordValue (binarySubtractProgram as bs false).bits : ℤ)=
      (binaryWordValue as : ℤ)-(binaryWordValue bs : ℤ) := by
  have hv:=binarySubtractProgram_nonnegative_value as bs false (by simpa only [binaryBitValue,add_zero] using h)
  simp only [binaryBitValue,Nat.sub_zero] at hv
  rw [hv,Nat.cast_sub h]

end CircuitRecursion
