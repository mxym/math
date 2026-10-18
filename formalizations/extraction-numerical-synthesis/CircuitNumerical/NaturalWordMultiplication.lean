import CircuitNumerical.SignedWordComparison

namespace CircuitRecursion

structure NaturalWordMultiplicationResult where
  bits : List Bool
  multiplicationTrace : BinaryWordMultiplicationTrace
  trimTrace : BinaryWordTrimTrace

def naturalMultiplyProgram (as bs : List Bool) : NaturalWordMultiplicationResult :=
  let product:=binaryMultiplyProgram as bs
  let trimmed:=binaryTrimProgram product.bits
  ⟨trimmed.bits,product.trace,trimmed.trace⟩

theorem naturalMultiplyProgram_value (as bs : List Bool) :
    binaryWordValue (naturalMultiplyProgram as bs).bits=binaryWordValue as*binaryWordValue bs := by
  simp only [naturalMultiplyProgram,binaryTrimProgram_value,binaryMultiplyProgram_value]

theorem naturalMultiplyProgram_canonical (as bs : List Bool) :
    BinaryWordCanonical (naturalMultiplyProgram as bs).bits := binaryTrimProgram_canonical _

theorem naturalMultiplyProgram_length (as bs : List Bool) :
    (naturalMultiplyProgram as bs).bits.length≤as.length+2*bs.length :=
  (binaryTrimProgram_length _).trans (binaryMultiplyProgram_length as bs)

def NaturalWordMultiplicationResult.actions (result : NaturalWordMultiplicationResult) : ℕ :=
  result.multiplicationTrace.actions+result.trimTrace.actions+8

theorem naturalMultiplyProgram_uniform_actions (as bs : List Bool) (B : ℕ)
    (ha : as.length≤B) (hb : bs.length≤B) :
    (naturalMultiplyProgram as bs).actions≤100*(B+1)^2 := by
  have hp:=binaryMultiplyProgram_uniform_actions as bs B ha hb
  have hl:=binaryMultiplyProgram_length as bs
  have ht:=binaryTrimProgram_actions (binaryMultiplyProgram as bs).bits
  simp only [naturalMultiplyProgram,NaturalWordMultiplicationResult.actions]
  nlinarith

end CircuitRecursion
