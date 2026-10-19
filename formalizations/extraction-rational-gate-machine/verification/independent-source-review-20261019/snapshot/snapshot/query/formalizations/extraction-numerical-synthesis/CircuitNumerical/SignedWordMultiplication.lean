import CircuitNumerical.SignedWordAddition

namespace CircuitRecursion

structure SignedWordMultiplicationResult where
  word : SignedBinaryWord
  multiplicationTrace : BinaryWordMultiplicationTrace
  trimTrace : BinaryWordTrimTrace

/-- The Boolean product is evaluated once, its sign is an xor, and the final
normalizer removes padding and the negative-zero representation. -/
def signedMultiplyProgram (a b : SignedBinaryWord) : SignedWordMultiplicationResult :=
  let product:=binaryMultiplyProgram a.bits b.bits
  let normalized:=signedBinaryNormalizeProgram ⟨Bool.xor a.negative b.negative,product.bits⟩
  ⟨normalized.word,product.trace,normalized.trace⟩

theorem signedMultiplyProgram_value (a b : SignedBinaryWord) :
    (signedMultiplyProgram a b).word.value=a.value*b.value := by
  change (signedBinaryNormalizeProgram
    ⟨Bool.xor a.negative b.negative,(binaryMultiplyProgram a.bits b.bits).bits⟩).word.value=a.value*b.value
  rw [signedBinaryNormalizeProgram_value]
  cases ha : a.negative <;> cases hb : b.negative <;>
    simp [SignedBinaryWord.value,ha,hb,binaryMultiplyProgram_value] <;> ring

theorem signedMultiplyProgram_canonical (a b : SignedBinaryWord) :
    (signedMultiplyProgram a b).word.Canonical := signedBinaryNormalizeProgram_canonical _

theorem signedMultiplyProgram_length (a b : SignedBinaryWord) :
    (signedMultiplyProgram a b).word.bits.length≤a.bits.length+2*b.bits.length :=
  (signedBinaryNormalizeProgram_length _).trans (binaryMultiplyProgram_length a.bits b.bits)

theorem signedMultiplyProgram_height_width (a b : SignedBinaryWord) (B : ℕ)
    (h : (a.value*b.value).natAbs≤2^B) :
    (signedMultiplyProgram a b).word.bits.length≤B+1 := by
  apply SignedBinaryWord.canonical_width _ (signedMultiplyProgram_canonical a b) B
  simpa only [signedMultiplyProgram_value] using h

def SignedWordMultiplicationResult.actions (result : SignedWordMultiplicationResult) : ℕ :=
  result.multiplicationTrace.actions+result.trimTrace.actions+8

theorem signedMultiplyProgram_actions (a b : SignedBinaryWord) :
    (signedMultiplyProgram a b).actions≤
      24*(b.bits.length+1)*(a.bits.length+2*b.bits.length+1)+
        6*(a.bits.length+2*b.bits.length+1)+8 := by
  have hp:=binaryMultiplyProgram_actions a.bits b.bits
  have hl:=binaryMultiplyProgram_length a.bits b.bits
  have ht:=binaryTrimProgram_actions (binaryMultiplyProgram a.bits b.bits).bits
  simp only [signedMultiplyProgram,SignedWordMultiplicationResult.actions,signedBinaryNormalizeProgram]
  omega

theorem signedMultiplyProgram_uniform_actions (a b : SignedBinaryWord) (B : ℕ)
    (ha : a.bits.length≤B) (hb : b.bits.length≤B) :
    (signedMultiplyProgram a b).actions≤100*(B+1)^2 := by
  have hp:=binaryMultiplyProgram_uniform_actions a.bits b.bits B ha hb
  have hl:=binaryMultiplyProgram_length a.bits b.bits
  have ht:=binaryTrimProgram_actions (binaryMultiplyProgram a.bits b.bits).bits
  simp only [signedMultiplyProgram,SignedWordMultiplicationResult.actions,signedBinaryNormalizeProgram]
  nlinarith

def signedSubtractProgram (a b : SignedBinaryWord) : SignedWordAdditionResult :=
  signedAddProgram a b.negate

theorem signedSubtractProgram_value (a b : SignedBinaryWord) :
    (signedSubtractProgram a b).word.value=a.value-b.value := by
  simp only [signedSubtractProgram,signedAddProgram_value,SignedBinaryWord.negate_value,sub_eq_add_neg]

theorem signedSubtractProgram_canonical (a b : SignedBinaryWord) :
    (signedSubtractProgram a b).word.Canonical := signedAddProgram_canonical _ _

theorem signedSubtractProgram_actions (a b : SignedBinaryWord) :
    (signedSubtractProgram a b).actions+2≤50*(max a.bits.length b.bits.length+2) := by
  have h:=signedAddProgram_actions a b.negate
  simp only [signedSubtractProgram,SignedBinaryWord.negate] at h ⊢
  omega

end CircuitRecursion
