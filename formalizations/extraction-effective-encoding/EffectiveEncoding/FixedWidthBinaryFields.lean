import EffectiveEncoding.FullyMaterializedInputExtraction

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding


theorem vectorBool_getD {n : ℕ} (v : List.Vector Bool n) (i : Fin n) :
    v.toList.getD i.val false=v.get i := by
  have hl : v.toList.length=n := v.2
  have hi : i.val<v.toList.length := by rw [hl];exact i.isLt
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
  rfl

/-- Proof-side Nat roundtrip for the actual fixed-width digit program. -/
theorem endpointBitsProgram_value (n : ℕ) (bs : List Bool) (h : binaryWordValue bs<2^n) :
    binaryWordValue (endpointBitsProgram n bs).bits.toList=binaryWordValue bs := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<n
  · rw [binaryWordValue_testBit_getD,binaryWordValue_testBit_getD]
    have hi:=vectorBool_getD (endpointBitsProgram n bs).bits ⟨j,hj⟩
    exact hi.trans (endpointBitsProgram_get n bs ⟨j,hj⟩)
  · have hn : n≤j := by omega
    have hl : (endpointBitsProgram n bs).bits.toList.length=n := (endpointBitsProgram n bs).bits.2
    have ho : binaryWordValue (endpointBitsProgram n bs).bits.toList<2^n := by
      simpa only [hl] using
        binaryWordValue_lt_power_length (endpointBitsProgram n bs).bits.toList
    have hp : 2^n≤2^j := Nat.pow_le_pow_right (by decide) hn
    rw [Nat.testBit_lt_two_pow (ho.trans_le hp),Nat.testBit_lt_two_pow (h.trans_le hp)]

structure BinaryFieldResult (width : ℕ) where
  encoding : UnaryWordEncodingResult
  output : EndpointBitsResult width

/-- Actual count-to-bits execution and one fixed-width output pass. -/
def binaryFieldProgram (width value : ℕ) : BinaryFieldResult width :=
  let encoded:=unaryWordEncoding value
  let output:=endpointBitsProgram width encoded.bits
  ⟨encoded,output⟩


theorem binaryFieldProgram_length (width value : ℕ) :
    (binaryFieldProgram width value).output.bits.toList.length=width :=
  (binaryFieldProgram width value).output.bits.2


theorem binaryFieldProgram_value (width value : ℕ) (h : value<2^width) :
    binaryWordValue (binaryFieldProgram width value).output.bits.toList=value := by
  have hv : binaryWordValue (unaryWordEncoding value).bits<2^width := by rwa [unaryWordEncoding_value]
  exact (endpointBitsProgram_value width (unaryWordEncoding value).bits hv).trans (unaryWordEncoding_value value)


def BinaryFieldResult.actions {width : ℕ} (r : BinaryFieldResult width) : ℕ :=
  r.encoding.trace.incrementTrimActions+r.output.trace.listActions


theorem binaryFieldProgram_actions (width value : ℕ) (h : value<width) :
    (binaryFieldProgram width value).actions≤35*(width+1)^2 := by
  have hi:=(unaryWordEncoding_incrementTrimActions value).trans
    (Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left (show value+1≤width by omega) 2))
  have ho:=endpointBitsProgram_listActions width (unaryWordEncoding value).bits
  have hp : width^2≤(width+1)^2 := Nat.pow_le_pow_left (by omega) 2
  change (unaryWordEncoding value).trace.incrementTrimActions+
    (endpointBitsProgram width (unaryWordEncoding value).bits).trace.listActions≤_
  nlinarith

/-- Concrete prefix reader. Decoder arithmetic/control costs are separate
from the encoder's retained output primitive traces. -/
def takeBoolField : ℕ → List Bool → Option (List Bool×List Bool)
  | 0,bs => some ([],bs)
  | _+1,[] => none
  | n+1,b::bs => do
    let (field,tail)←takeBoolField n bs
    pure (b::field,tail)


theorem takeBoolField_append (field tail : List Bool) :
    takeBoolField field.length (field++tail)=some (field,tail) := by
  induction field with
  | nil => rfl
  | cons b bs ih => simp only [List.length_cons,List.cons_append,takeBoolField,ih];rfl


theorem takeBoolField_binaryField (width value : ℕ) (tail : List Bool) :
    takeBoolField width ((binaryFieldProgram width value).output.bits.toList++tail)=
      some ((binaryFieldProgram width value).output.bits.toList,tail) := by
  have h:=takeBoolField_append (binaryFieldProgram width value).output.bits.toList tail
  have hl : (binaryFieldProgram width value).output.bits.toList.length=width :=
    (binaryFieldProgram width value).output.bits.2
  simpa only [hl] using h

end EffectiveEncoding
