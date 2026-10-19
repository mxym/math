import CircuitNumerical.WordScalarRoot

namespace CircuitRecursion

/-- The sign table has only sixteen entries. Its comparison is on those
fixed small constants, not on input magnitudes. -/
def quaternionSignedWord (i j : Fin 4) (b : SignedBinaryWord) : SignedBinaryWord :=
  ⟨Bool.xor (decide (quaternionSign i j<0)) b.negative,b.bits⟩

theorem quaternionSignedWord_value (i j : Fin 4) (b : SignedBinaryWord) :
    (quaternionSignedWord i j b).value=quaternionSign i j*b.value := by
  fin_cases i <;> fin_cases j <;> cases hs : b.negative <;>
    norm_num [quaternionSignedWord,SignedBinaryWord.value,quaternionSign,hs]

structure WordQuaternionCoordinateResult where
  terms : List.Vector SignedWordMultiplicationResult 4
  firstSum : SignedWordAdditionResult
  secondSum : SignedWordAdditionResult
  finalSum : SignedWordAdditionResult

def WordQuaternionCoordinateResult.word (result : WordQuaternionCoordinateResult) : SignedBinaryWord :=
  result.finalSum.word

/-- Four stored products and three stored sums. The finite vector stores each
product once before any result fields are read. -/
def wordQuaternionCoordinateProgram (a b : List.Vector SignedBinaryWord 4) (i : Fin 4) :
    WordQuaternionCoordinateResult :=
  let terms:=List.Vector.ofFn (fun j => signedMultiplyProgram (a.get j)
    (quaternionSignedWord i j (b.get (quaternionRight i j))))
  let first:=signedAddProgram (terms.get 0).word (terms.get 1).word
  let second:=signedAddProgram first.word (terms.get 2).word
  let final:=signedAddProgram second.word (terms.get 3).word
  ⟨terms,first,second,final⟩

theorem wordQuaternionCoordinateProgram_value (a b : List.Vector SignedBinaryWord 4) (i : Fin 4) :
    (wordQuaternionCoordinateProgram a b i).word.value=
      quaternionProduct (fun j => (a.get j).value) (fun j => (b.get j).value) i := by
  simp only [wordQuaternionCoordinateProgram,WordQuaternionCoordinateResult.word,signedAddProgram_value,
    List.Vector.get_ofFn,signedMultiplyProgram_value,quaternionSignedWord_value,
    quaternionProduct,Fin.sum_univ_four,Int.cast_id]
  ring

theorem wordQuaternionCoordinateProgram_canonical (a b : List.Vector SignedBinaryWord 4) (i : Fin 4) :
    (wordQuaternionCoordinateProgram a b i).word.Canonical := signedAddProgram_canonical _ _

def WordQuaternionCoordinateResult.actions (result : WordQuaternionCoordinateResult) : ℕ :=
  (∑ j : Fin 4,(result.terms.get j).actions)+result.firstSum.actions+
    result.secondSum.actions+result.finalSum.actions+32

theorem wordQuaternionCoordinateProgram_uniform_actions (a b : List.Vector SignedBinaryWord 4)
    (i : Fin 4) (B : ℕ) (ha : ∀ j,(a.get j).bits.length≤B) (hb : ∀ j,(b.get j).bits.length≤B) :
    (wordQuaternionCoordinateProgram a b i).actions≤1500*(B+1)^2 := by
  let terms:=List.Vector.ofFn (fun j => signedMultiplyProgram (a.get j)
    (quaternionSignedWord i j (b.get (quaternionRight i j))))
  have hlen : ∀ j,(terms.get j).word.bits.length≤3*B := by
    intro j
    have h:=signedMultiplyProgram_length (a.get j) (quaternionSignedWord i j (b.get (quaternionRight i j)))
    simp only [quaternionSignedWord] at h
    simp only [terms,List.Vector.get_ofFn,quaternionSignedWord]
    have ha':=ha j
    have hb':=hb (quaternionRight i j)
    omega
  have hcost : ∀ j,(terms.get j).actions≤100*(B+1)^2 := by
    intro j
    simpa only [terms,List.Vector.get_ofFn] using signedMultiplyProgram_uniform_actions
      (a.get j) (quaternionSignedWord i j (b.get (quaternionRight i j))) B (ha j) (hb _)
  let first:=signedAddProgram (terms.get 0).word (terms.get 1).word
  let second:=signedAddProgram first.word (terms.get 2).word
  have hfl : first.word.bits.length≤3*B+1 := by
    have h:=signedAddProgram_length (terms.get 0).word (terms.get 1).word
    have h0:=hlen 0
    have h1:=hlen 1
    dsimp only [first]
    omega
  have hsl : second.word.bits.length≤3*B+2 := by
    have h:=signedAddProgram_length first.word (terms.get 2).word
    have h2:=hlen 2
    dsimp only [second]
    omega
  have hfc:=signedAddProgram_actions (terms.get 0).word (terms.get 1).word
  have hsc:=signedAddProgram_actions first.word (terms.get 2).word
  have htc:=signedAddProgram_actions second.word (terms.get 3).word
  have hm0 : max (terms.get 0).word.bits.length (terms.get 1).word.bits.length≤3*B := by
    have h0:=hlen 0;have h1:=hlen 1;omega
  have hm1 : max first.word.bits.length (terms.get 2).word.bits.length≤3*B+1 := by
    have h2:=hlen 2;omega
  have hm2 : max second.word.bits.length (terms.get 3).word.bits.length≤3*B+2 := by
    have h3:=hlen 3;omega
  have hsum:=Finset.sum_le_sum (s:=Finset.univ) (fun j (_ : j∈Finset.univ) => hcost j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hsum
  change (∑ j : Fin 4,(terms.get j).actions)+first.actions+second.actions+
      (signedAddProgram second.word (terms.get 3).word).actions+32≤_
  nlinarith

end CircuitRecursion
