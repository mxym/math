import CircuitNumerical.FiniteBinaryLookupTerminal

namespace CircuitRecursion.PacketFraming

inductive Symbol where
  | bit : Bool → Symbol
  | field
  | endPacket
  deriving DecidableEq
instance : Fintype Symbol := ⟨{.bit false,.bit true,.field,.endPacket},by
  intro x;cases x with
  | bit b => cases b <;> simp
  | field => simp
  | endPacket => simp⟩
instance : Inhabited Symbol := ⟨.bit false⟩

/-- Raw decoded fields contain the actual bits, without Nat or Rat decoding.
Typed canonicality/positivity proofs can be supplied as representation invariants. -/
structure RawPacket where
  n0 : SignedBinaryWord
  n1 : SignedBinaryWord
  n2 : SignedBinaryWord
  n3 : SignedBinaryWord
  denominator : List Bool

def rawNumerators (r : RawPacket) : List.Vector SignedBinaryWord 4 :=
  List.Vector.ofFn ![r.n0,r.n1,r.n2,r.n3]

def rawPacket (p : WordIntegerPacket) : RawPacket :=
  ⟨p.numerators.get 0,p.numerators.get 1,p.numerators.get 2,p.numerators.get 3,p.denominator⟩

theorem rawNumerators_rawPacket (p : WordIntegerPacket) : rawNumerators (rawPacket p)=p.numerators := by
  apply List.Vector.ext
  intro i
  fin_cases i <;> rfl

def RawPacket.Valid (r : RawPacket) : Prop :=
  (∀ i,(rawNumerators r).get i |>.Canonical) ∧ BinaryWordCanonical r.denominator ∧ 0<binaryWordValue r.denominator

def RawPacket.toWord (r : RawPacket) (h : r.Valid) : WordIntegerPacket :=
  ⟨rawNumerators r,r.denominator,h.1,h.2.1,h.2.2⟩

theorem rawPacket_valid (p : WordIntegerPacket) : (rawPacket p).Valid := by
  constructor
  · rw [rawNumerators_rawPacket]
    exact p.numerators_canonical
  · exact ⟨p.denominator_canonical,p.denominator_pos⟩

theorem wordPacket_eq_fields (a b : WordIntegerPacket)
    (hn : a.numerators=b.numerators) (hd : a.denominator=b.denominator) : a=b := by
  cases a
  cases b
  cases hn
  cases hd
  rfl

theorem rawPacket_toWord (p : WordIntegerPacket) : (rawPacket p).toWord (rawPacket_valid p)=p := by
  apply wordPacket_eq_fields
  · exact rawNumerators_rawPacket p
  · rfl

/-- Each signed numerator has one sign bit and a field terminator. -/
def signedField (s : SignedBinaryWord) : List Symbol := .bit s.negative::s.bits.map Symbol.bit++[.field]

def payload (r : RawPacket) : List Symbol :=
  signedField r.n0++signedField r.n1++signedField r.n2++signedField r.n3++r.denominator.map Symbol.bit

def encodeRaw (r : RawPacket) : List Symbol := payload r++[.endPacket]
def encodePacket (p : WordIntegerPacket) : List Symbol := encodeRaw (rawPacket p)

def encodeCache : List WordIntegerPacket → List Symbol
  | [] => []
  | p::ps => encodePacket p++encodeCache ps

theorem bitMap_no_end (bs : List Bool) : Symbol.endPacket∉bs.map Symbol.bit := by
  intro h
  rcases List.mem_map.mp h with ⟨b,_,hb⟩
  cases hb

theorem signedField_no_end (s : SignedBinaryWord) : Symbol.endPacket∉signedField s := by
  simp [signedField,bitMap_no_end]

theorem payload_no_end (r : RawPacket) : Symbol.endPacket∉payload r := by
  simp only [payload,List.mem_append]
  exact not_or.mpr ⟨not_or.mpr ⟨not_or.mpr ⟨not_or.mpr ⟨signedField_no_end _,signedField_no_end _⟩,
    signedField_no_end _⟩,signedField_no_end _⟩,bitMap_no_end _⟩

theorem signedField_length (s : SignedBinaryWord) : (signedField s).length=s.bits.length+2 := by
  simp only [signedField,List.length_append,List.length_cons,List.length_map,List.length_nil]

theorem encodeRaw_length (r : RawPacket) : (encodeRaw r).length=
    r.n0.bits.length+r.n1.bits.length+r.n2.bits.length+r.n3.bits.length+r.denominator.length+9 := by
  simp only [encodeRaw,payload,List.length_append,signedField_length,List.length_map,List.length_cons,List.length_nil]
  omega

theorem encodePacket_length_height (p : WordIntegerPacket) (B : ℕ) (h : IntegerPacketHeight p.decode B) :
    (encodePacket p).length≤5*B+14 := by
  have hw:=p.height_width B h
  have h0:=hw.1 0;have h1:=hw.1 1;have h2:=hw.1 2;have h3:=hw.1 3
  simp only [encodePacket,encodeRaw_length,rawPacket]
  omega

theorem encodeCache_length (ps : List WordIntegerPacket) :
    (encodeCache ps).length=(ps.map (fun p => (encodePacket p).length)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [encodeCache,List.length_append,List.map_cons,List.sum_cons,ih]

theorem encodeCache_length_height (ps : List WordIntegerPacket) (B : ℕ)
    (h : ∀ p∈ps,IntegerPacketHeight p.decode B) : (encodeCache ps).length≤(5*B+14)*ps.length := by
  induction ps with
  | nil => simp only [encodeCache,List.length_nil,Nat.mul_zero,le_refl]
  | cons p ps ih =>
    have hp:=encodePacket_length_height p B (h p (List.mem_cons_self))
    have ht:=ih (fun q hq => h q (List.mem_cons_of_mem p hq))
    simp only [encodeCache,List.length_append,List.length_cons]
    nlinarith

theorem symbol_card : Fintype.card Symbol=4 := by decide

end CircuitRecursion.PacketFraming
