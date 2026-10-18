import CircuitNumerical.SignedBinaryWords

namespace CircuitRecursion

inductive SignedRawAdditionTrace where
  | same : BinaryWordAdditionTrace → SignedRawAdditionTrace
  | different : BinaryWordComparisonTrace → BinaryWordSubtractionTrace → SignedRawAdditionTrace

structure SignedRawAdditionResult where
  word : SignedBinaryWord
  trace : SignedRawAdditionTrace

/-- Sign/magnitude addition. Opposite signs execute one magnitude comparison
and one subtraction in the direction selected by that returned comparison. -/
def signedRawAddProgram (a b : SignedBinaryWord) : SignedRawAdditionResult :=
  if a.negative=b.negative then
    let addition:=binaryAddProgram a.bits b.bits false
    ⟨⟨a.negative,addition.bits⟩,.same addition.trace⟩
  else
    let comparison:=binaryWordCompareProgram a.bits b.bits
    match comparison.order with
    | .lt =>
      let subtraction:=binarySubtractProgram b.bits a.bits false
      ⟨⟨b.negative,subtraction.bits⟩,.different comparison.trace subtraction.trace⟩
    | _ =>
      let subtraction:=binarySubtractProgram a.bits b.bits false
      ⟨⟨a.negative,subtraction.bits⟩,.different comparison.trace subtraction.trace⟩

theorem signedRawAddProgram_value (a b : SignedBinaryWord) :
    (signedRawAddProgram a b).word.value=a.value+b.value := by
  by_cases hs : a.negative=b.negative
  · simp only [signedRawAddProgram,ite_eq_left hs,SignedBinaryWord.value,binaryAddProgram_value,binaryBitValue,add_zero,
      Nat.cast_add,←hs]
    cases ha : a.negative <;> simp [binaryAddProgram_value,binaryBitValue] <;> ring
  · have hc:=binaryWordCompareProgram_correct a.bits b.bits
    cases he : (binaryWordCompareProgram a.bits b.bits).order with
    | lt =>
      rw [he] at hc
      change binaryWordValue a.bits<binaryWordValue b.bits at hc
      have hv:=binarySubtractProgram_intValue b.bits a.bits (by omega)
      simp only [signedRawAddProgram,ite_eq_right hs,he,SignedBinaryWord.value]
      cases ha : a.negative <;> cases hb : b.negative <;> simp_all [SignedBinaryWord.value] <;> omega
    | eq =>
      rw [he] at hc
      change binaryWordValue a.bits=binaryWordValue b.bits at hc
      have hv:=binarySubtractProgram_intValue a.bits b.bits (by omega)
      simp only [signedRawAddProgram,ite_eq_right hs,he,SignedBinaryWord.value]
      cases ha : a.negative <;> cases hb : b.negative <;> simp_all [SignedBinaryWord.value] <;> omega
    | gt =>
      rw [he] at hc
      change binaryWordValue b.bits<binaryWordValue a.bits at hc
      have hv:=binarySubtractProgram_intValue a.bits b.bits (by omega)
      simp only [signedRawAddProgram,ite_eq_right hs,he,SignedBinaryWord.value]
      cases ha : a.negative <;> cases hb : b.negative <;> simp_all [SignedBinaryWord.value] <;> omega

theorem signedRawAddProgram_length (a b : SignedBinaryWord) :
    (signedRawAddProgram a b).word.bits.length≤max a.bits.length b.bits.length+1 := by
  by_cases hs : a.negative=b.negative
  · simpa only [signedRawAddProgram,ite_eq_left hs] using binaryAddProgram_length a.bits b.bits false
  · cases he : (binaryWordCompareProgram a.bits b.bits).order <;>
      simp only [signedRawAddProgram,ite_eq_right hs,he,binarySubtractProgram_length] <;> omega

def SignedRawAdditionTrace.actions : SignedRawAdditionTrace → ℕ
  | .same addition => addition.actions+4
  | .different comparison subtraction => comparison.actions+subtraction.actions+4

theorem signedRawAddProgram_actions (a b : SignedBinaryWord) :
    (signedRawAddProgram a b).trace.actions≤40*(max a.bits.length b.bits.length+1) := by
  by_cases hs : a.negative=b.negative
  · have h:=binaryAddProgram_actions a.bits b.bits false
    simp only [signedRawAddProgram,ite_eq_left hs,SignedRawAdditionTrace.actions]
    omega
  · have hc:=binaryWordCompareProgram_actions a.bits b.bits
    have hab:=binarySubtractProgram_actions a.bits b.bits false
    have hba:=binarySubtractProgram_actions b.bits a.bits false
    have hm : max a.bits.length b.bits.length=max b.bits.length a.bits.length := Nat.max_comm _ _
    cases he : (binaryWordCompareProgram a.bits b.bits).order <;>
      simp only [signedRawAddProgram,ite_eq_right hs,he,SignedRawAdditionTrace.actions] <;> omega

structure SignedWordAdditionResult where
  word : SignedBinaryWord
  additionTrace : SignedRawAdditionTrace
  trimTrace : BinaryWordTrimTrace

/-- Both the raw arithmetic result and the normalization are evaluated once.
Every output is trimmed and carries the unique false sign for zero. -/
def signedAddProgram (a b : SignedBinaryWord) : SignedWordAdditionResult :=
  let raw:=signedRawAddProgram a b
  let normalized:=signedBinaryNormalizeProgram raw.word
  ⟨normalized.word,raw.trace,normalized.trace⟩

theorem signedAddProgram_value (a b : SignedBinaryWord) :
    (signedAddProgram a b).word.value=a.value+b.value := by
  simp only [signedAddProgram,signedBinaryNormalizeProgram_value,signedRawAddProgram_value]

theorem signedAddProgram_canonical (a b : SignedBinaryWord) :
    (signedAddProgram a b).word.Canonical := signedBinaryNormalizeProgram_canonical _

theorem signedAddProgram_length (a b : SignedBinaryWord) :
    (signedAddProgram a b).word.bits.length≤max a.bits.length b.bits.length+1 :=
  (signedBinaryNormalizeProgram_length _).trans (signedRawAddProgram_length a b)

theorem signedAddProgram_height_width (a b : SignedBinaryWord) (B : ℕ)
    (h : (a.value+b.value).natAbs≤2^B) :
    (signedAddProgram a b).word.bits.length≤B+1 := by
  apply SignedBinaryWord.canonical_width _ (signedAddProgram_canonical a b) B
  simpa only [signedAddProgram_value] using h

def SignedWordAdditionResult.actions (result : SignedWordAdditionResult) : ℕ :=
  result.additionTrace.actions+result.trimTrace.actions+8

theorem signedAddProgram_actions (a b : SignedBinaryWord) :
    (signedAddProgram a b).actions≤48*(max a.bits.length b.bits.length+2) := by
  have hr:=signedRawAddProgram_actions a b
  have hl:=signedRawAddProgram_length a b
  have ht:=binaryTrimProgram_actions (signedRawAddProgram a b).word.bits
  simp only [signedAddProgram,SignedWordAdditionResult.actions,signedBinaryNormalizeProgram]
  omega

end CircuitRecursion
