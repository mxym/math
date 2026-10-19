import CircuitNumerical.SignedWordMultiplication

namespace CircuitRecursion

/-- A constructor/sign test on a canonical signed word. -/
def SignedBinaryWord.nonpositiveTest (a : SignedBinaryWord) : Bool :=
  if a.negative then true else match a.bits with | [] => true | _::_ => false

theorem SignedBinaryWord.nonpositiveTest_correct (a : SignedBinaryWord) (h : a.Canonical) :
    a.nonpositiveTest=true ↔ a.value≤0 := by
  cases hs : a.negative with
  | true => simp [nonpositiveTest,value,hs]
  | false =>
    cases hb : a.bits with
    | nil => simp [nonpositiveTest,value,hs,hb,binaryWordValue]
    | cons b bs =>
      have hz : binaryWordValue a.bits≠0 := by
        intro hv
        have he:=(binaryWordCanonical_zero_iff a.bits h.1).mp hv
        rw [hb] at he
        cases he
      rw [hb] at hz
      have hp : (0:ℤ)<(binaryWordValue (b::bs):ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hz
      simp [nonpositiveTest,value,hs,hb]
      omega

structure SignedWordComparisonResult where
  le : Bool
  difference : SignedWordAdditionResult

/-- Compute one canonical difference, store it once, and inspect its sign and
list constructor. No integer comparison computes the returned Boolean. -/
def signedLEProgram (a b : SignedBinaryWord) : SignedWordComparisonResult :=
  let difference:=signedSubtractProgram a b
  ⟨difference.word.nonpositiveTest,difference⟩

theorem signedLEProgram_correct (a b : SignedBinaryWord) :
    (signedLEProgram a b).le=true ↔ a.value≤b.value := by
  change (signedSubtractProgram a b).word.nonpositiveTest=true ↔ a.value≤b.value
  rw [SignedBinaryWord.nonpositiveTest_correct _ (signedSubtractProgram_canonical a b),signedSubtractProgram_value]
  omega

def SignedWordComparisonResult.actions (result : SignedWordComparisonResult) : ℕ :=
  result.difference.actions+8

theorem signedLEProgram_actions (a b : SignedBinaryWord) :
    (signedLEProgram a b).actions≤56*(max a.bits.length b.bits.length+2) := by
  have h:=signedSubtractProgram_actions a b
  simp only [signedLEProgram,SignedWordComparisonResult.actions]
  omega

end CircuitRecursion
