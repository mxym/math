import CircuitNumerical.WordSelection
import Mathlib.Data.Nat.Bits

namespace CircuitRecursion

theorem binaryWordValue_natBits (n : ℕ) : binaryWordValue n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => simp only [Nat.zero_bits,binaryWordValue]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b <;> simp only [binaryWordValue,binaryBitValue,ih,Nat.bit_false_apply,Nat.bit_true_apply] <;> omega

theorem natBits_canonical (n : ℕ) : BinaryWordCanonical n.bits := by
  induction n using Nat.binaryRec' with
  | zero => simpa only [Nat.zero_bits] using BinaryWordCanonical.nil
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    by_cases hz : n=0
    · subst n
      have hb:=hn rfl
      subst b
      simpa only [Nat.zero_bits] using BinaryWordCanonical.one
    · cases he : n.bits with
      | nil =>
        have hv:=binaryWordValue_natBits n
        rw [he] at hv
        exact (hz hv.symm).elim
      | cons c cs =>
        rw [he] at ih
        exact .prepend b c cs ih

theorem natBits_height_width (n B : ℕ) (h : n≤2^B) : n.bits.length≤B+1 :=
  binaryWordCanonical_width _ (natBits_canonical n) B (by simpa only [binaryWordValue_natBits] using h)

/-- Adapter from the host integer input representation. Its binaryRec/bit
access execution cost is explicit remaining input-adapter work; later local
Boolean action models must not silently charge this conversion as constant. -/
def signedWordInput : ℤ → SignedBinaryWord
  | .ofNat n => ⟨false,n.bits⟩
  | .negSucc n => ⟨true,(n+1).bits⟩

theorem signedWordInput_value (n : ℤ) : (signedWordInput n).value=n := by
  cases n <;> simp [signedWordInput,SignedBinaryWord.value,binaryWordValue_natBits,Int.negSucc_eq]

theorem signedWordInput_canonical (n : ℤ) : (signedWordInput n).Canonical := by
  cases n with
  | ofNat n => exact ⟨natBits_canonical n,by intro _;rfl⟩
  | negSucc n =>
    constructor
    · exact natBits_canonical (n+1)
    · intro he
      have hv:=binaryWordValue_natBits (n+1)
      change (n+1).bits=[] at he
      rw [he] at hv
      simp only [binaryWordValue] at hv
      omega

def wordScalarInput (a : IntegerScalar) : WordIntegerScalar :=
  ⟨signedWordInput a.numerator,a.denominator.bits,signedWordInput_canonical _,natBits_canonical _,
    by simpa only [binaryWordValue_natBits] using a.denominator_pos⟩

theorem wordScalarInput_decode (a : IntegerScalar) : (wordScalarInput a).decode=a := by
  apply integerScalar_eq_components
  · exact signedWordInput_value a.numerator
  · exact binaryWordValue_natBits a.denominator

/-- Output bit volume of the adapter, not a bound on executing Nat.bits. -/
def wordScalarInputVolume (a : IntegerScalar) : ℕ :=
  (wordScalarInput a).numerator.bits.length+(wordScalarInput a).denominator.length+1

theorem wordScalarInputVolume_height (a : IntegerScalar) (B : ℕ)
    (ha : IntegerScalarHeight a B) : wordScalarInputVolume a≤2*(B+1)+1 := by
  have h:=(wordScalarInput a).height_width B (by simpa only [wordScalarInput_decode] using ha)
  dsimp only [wordScalarInputVolume]
  omega

def wordScalarLiteralProgram (q : ℚ) : WordIntegerScalar := wordScalarInput (IntegerScalar.ofRat q)

theorem wordScalarLiteralProgram_decode (q : ℚ) :
    (wordScalarLiteralProgram q).decode=IntegerScalar.ofRat q := wordScalarInput_decode _

def wordPacketLiteralProgram (q : List.Vector ℚ 4) : WordPacketTupleResult :=
  let stored:=List.Vector.ofFn (fun i => wordScalarLiteralProgram (q.get i))
  wordPacketTupleProgram stored

theorem wordPacketLiteralProgram_decode (q : List.Vector ℚ 4) :
    (wordPacketLiteralProgram q).packet.decode=IntegerPacket.ofVector q := by
  simp only [wordPacketLiteralProgram,wordPacketTupleProgram_decode,IntegerPacket.ofVector,
    List.Vector.get_ofFn,wordScalarLiteralProgram_decode]

end CircuitRecursion
