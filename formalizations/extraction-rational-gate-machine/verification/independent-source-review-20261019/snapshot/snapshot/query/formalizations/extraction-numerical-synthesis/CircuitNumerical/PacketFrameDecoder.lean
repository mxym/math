import CircuitNumerical.PacketFraming

namespace CircuitRecursion.PacketFraming

/-- Actual finite-symbol field parser. No numeric decoding or padding
normalization occurs: the returned list is exactly the supplied bit data. -/
def readField : List Symbol → Option (List Bool×List Symbol)
  | [] => none
  | .field::rest => some ([],rest)
  | .endPacket::_ => none
  | .bit b::rest => do
      let (bs,tail)←readField rest
      pure (b::bs,tail)

def readSigned : List Symbol → Option (SignedBinaryWord×List Symbol)
  | .bit sign::rest => do
      let (bs,tail)←readField rest
      pure (⟨sign,bs⟩,tail)
  | _ => none

def readDenominator : List Symbol → Option (List Bool×List Symbol)
  | [] => none
  | .endPacket::rest => some ([],rest)
  | .field::_ => none
  | .bit b::rest => do
      let (bs,tail)←readDenominator rest
      pure (b::bs,tail)

/-- Four signed fields and one denominator, with explicit finite sequencing.
Canonicality/positivity are data invariants of the caller's typed packet;
this parser does not assume or execute a Nat/Rat validation procedure. -/
def decodeRaw (input : List Symbol) : Option (RawPacket×List Symbol) := do
  let (n0,r0)←readSigned input
  let (n1,r1)←readSigned r0
  let (n2,r2)←readSigned r1
  let (n3,r3)←readSigned r2
  let (d,rest)←readDenominator r3
  pure (⟨n0,n1,n2,n3,d⟩,rest)

theorem readField_bits_append (bs : List Bool) (rest : List Symbol) :
    readField (bs.map Symbol.bit++Symbol.field::rest)=some (bs,rest) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [List.map_cons,List.cons_append,readField,ih,Option.bind_eq_bind,Option.bind_some];rfl

theorem readSigned_signedField (s : SignedBinaryWord) (rest : List Symbol) :
    readSigned (signedField s++rest)=some (s,rest) := by
  cases s with
  | mk sign bs =>
    simp only [signedField,List.cons_append,List.append_assoc,readSigned,
      readField_bits_append,Option.bind_eq_bind,Option.bind_some]
    rfl

theorem readDenominator_bits_append (bs : List Bool) (rest : List Symbol) :
    readDenominator (bs.map Symbol.bit++Symbol.endPacket::rest)=some (bs,rest) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [List.map_cons,List.cons_append,readDenominator,ih,Option.bind_eq_bind,Option.bind_some];rfl

theorem decodeRaw_encodeRaw (r : RawPacket) (rest : List Symbol) :
    decodeRaw (encodeRaw r++rest)=some (r,rest) := by
  simp only [encodeRaw,payload,List.append_assoc,List.singleton_append,decodeRaw,
    readSigned_signedField,readDenominator_bits_append,Option.bind_eq_bind,Option.bind_some]
  rfl

theorem decodeRaw_encodePacket (p : WordIntegerPacket) (rest : List Symbol) :
    decodeRaw (encodePacket p++rest)=some (rawPacket p,rest) := decodeRaw_encodeRaw _ rest

theorem decodeRaw_cache_head (p : WordIntegerPacket) (ps : List WordIntegerPacket) :
    decodeRaw (encodeCache (p::ps))=some (rawPacket p,encodeCache ps) := decodeRaw_encodePacket p _

theorem encodeRaw_injective : Function.Injective encodeRaw := by
  intro a b h
  have ha:=decodeRaw_encodeRaw a []
  have hb:=decodeRaw_encodeRaw b []
  simp only [List.append_nil] at ha hb
  have he:=congrArg decodeRaw h
  rw [ha,hb] at he
  exact congrArg Prod.fst (Option.some.inj he)

theorem encodePacket_injective : Function.Injective encodePacket := by
  intro a b h
  have hr : rawPacket a=rawPacket b := encodeRaw_injective h
  apply wordPacket_eq_fields
  · rw [←rawNumerators_rawPacket a,←rawNumerators_rawPacket b,hr]
  · exact congrArg RawPacket.denominator hr

/-- The decoded raw data reconstruct exactly the original typed packet.
No normalization or choice of an equivalent rational representative occurs. -/
theorem decoded_typed_roundtrip (p : WordIntegerPacket) :
    decodeRaw (encodePacket p)=some (rawPacket p,[]) ∧ (rawPacket p).toWord (rawPacket_valid p)=p :=
  ⟨by simpa only [List.append_nil] using decodeRaw_encodePacket p [],rawPacket_toWord p⟩

end CircuitRecursion.PacketFraming
