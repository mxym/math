import CircuitNumerical.WordPacketTuple

namespace CircuitRecursion

structure SignedFourSumResult where
  first : SignedWordAdditionResult
  second : SignedWordAdditionResult
  final : SignedWordAdditionResult

def SignedFourSumResult.word (result : SignedFourSumResult) : SignedBinaryWord := result.final.word

def signedFourSumProgram (as : List.Vector SignedBinaryWord 4) : SignedFourSumResult :=
  let first:=signedAddProgram (as.get 0) (as.get 1)
  let second:=signedAddProgram first.word (as.get 2)
  let final:=signedAddProgram second.word (as.get 3)
  ⟨first,second,final⟩

theorem signedFourSumProgram_value (as : List.Vector SignedBinaryWord 4) :
    (signedFourSumProgram as).word.value=∑ i : Fin 4,(as.get i).value := by
  simp only [signedFourSumProgram,SignedFourSumResult.word,signedAddProgram_value,Fin.sum_univ_four]

theorem signedFourSumProgram_canonical (as : List.Vector SignedBinaryWord 4) :
    (signedFourSumProgram as).word.Canonical := signedAddProgram_canonical _ _

def SignedFourSumResult.actions (result : SignedFourSumResult) : ℕ :=
  result.first.actions+result.second.actions+result.final.actions+12

theorem signedFourSumProgram_uniform_actions (as : List.Vector SignedBinaryWord 4) (B : ℕ)
    (ha : ∀ i,(as.get i).bits.length≤B) :
    (signedFourSumProgram as).actions≤160*(B+4) := by
  let first:=signedAddProgram (as.get 0) (as.get 1)
  let second:=signedAddProgram first.word (as.get 2)
  have h0:=ha 0;have h1:=ha 1;have h2:=ha 2;have h3:=ha 3
  have hf:=signedAddProgram_actions (as.get 0) (as.get 1)
  have hfl:=signedAddProgram_length (as.get 0) (as.get 1)
  have hs:=signedAddProgram_actions first.word (as.get 2)
  have hsl:=signedAddProgram_length first.word (as.get 2)
  have ht:=signedAddProgram_actions second.word (as.get 3)
  have hmax0 : max (as.get 0).bits.length (as.get 1).bits.length≤B := by omega
  have hfirst : first.word.bits.length≤B+1 := by dsimp only [first];omega
  have hmax1 : max first.word.bits.length (as.get 2).bits.length≤B+1 := by omega
  have hsecond : second.word.bits.length≤B+2 := by dsimp only [second];omega
  have hmax2 : max second.word.bits.length (as.get 3).bits.length≤B+2 := by omega
  change first.actions≤_ at hf
  change second.actions≤_ at hs
  change first.actions+second.actions+(signedAddProgram second.word (as.get 3)).actions+12≤_
  omega

end CircuitRecursion
