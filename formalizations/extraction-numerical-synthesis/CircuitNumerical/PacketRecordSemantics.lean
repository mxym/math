import CircuitNumerical.PacketRecordRuns

namespace CircuitRecursion.PacketRecordMachine

open Turing ListAssemblyMachine PacketFraming

theorem readField_bits_eof (bs : List Bool) : readField (bs.map Symbol.bit)=none := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [List.map_cons,readField,ih,Option.bind_eq_bind,Option.bind_none]

theorem readSigned_bits_eof (bs : List Bool) : readSigned (bs.map Symbol.bit)=none := by
  cases bs with
  | nil => rfl
  | cons b bs => simp only [List.map_cons,readSigned,readField_bits_eof,Option.bind_eq_bind,Option.bind_none]

theorem decodeRaw_bits_eof (bs : List Bool) : decodeRaw (bs.map Symbol.bit)=none := by
  simp only [decodeRaw,readSigned_bits_eof,Option.bind_eq_bind,Option.bind_none]

/-- Semantic observation of the copied frame. The field parser is an
explicit source program, but its full machine lowering is separate from
this verified whole-frame read/copy machine. -/
def parsedResult (c : Configuration Label) : Option RawPacket := (decodeRaw (c.stk .left)).map Prod.fst

theorem terminal_source_value (ps : List WordIntegerPacket) (i : BinaryIndex) :
    parsedResult (terminal ps i)=(binaryIndexedLookup ps i).value.map rawPacket := by
  induction ps generalizing i with
  | nil => simp only [terminal,parsedResult,configuration,PacketStackPermutation.configuration,stackData_left,
      decodeRaw_bits_eof,binaryIndexedLookup,Option.map_none]
  | cons p ps ih =>
    cases hb : i.bits with
    | nil =>
      have hd:=decodeRaw_encodePacket p []
      simp only [List.append_nil] at hd
      simp only [terminal,hb,parsedResult,configuration,PacketStackPermutation.configuration,stackData_left,
        binaryIndexedLookup,hd,Option.map_some]
    | cons b bs => simpa only [terminal,binaryIndexedLookup,hb] using ih i.predecessor

/-- Unconditional decoded result of the actual terminal frame. The natural
index appears only in this specification, never in the reader transitions. -/
theorem terminal_getElem (ps : List WordIntegerPacket) (i : BinaryIndex) :
    parsedResult (terminal ps i)=(ps[i.value]?).map rawPacket := by
  rw [terminal_source_value,binaryIndexedLookup_getElem]

theorem terminal_encoded_hit (ps : List WordIntegerPacket) (i : BinaryIndex) (p : WordIntegerPacket)
    (hp : (binaryIndexedLookup ps i).value=some p) : (terminal ps i).stk .left=encodePacket p := by
  induction ps generalizing i p with
  | nil => cases hp
  | cons q ps ih =>
    cases hb : i.bits with
    | nil =>
      have hqp : q=p := by
        simpa only [binaryIndexedLookup,hb,Option.some.injEq] using hp
      subst p
      simp only [terminal,hb,configuration,PacketStackPermutation.configuration,stackData_left]
    | cons b bs =>
      simp only [terminal,hb]
      apply ih i.predecessor p
      simpa only [binaryIndexedLookup,hb] using hp

theorem terminal_encoded_getElem (ps : List WordIntegerPacket) (i : BinaryIndex) (p : WordIntegerPacket)
    (hp : ps[i.value]?=some p) : (terminal ps i).stk .left=encodePacket p :=
  terminal_encoded_hit ps i p (by rw [binaryIndexedLookup_getElem];exact hp)

/-- Exact remaining cache, including the out-of-range case. This is a
proof-side List.drop specification, not a runtime Nat traversal. -/
theorem terminal_cache_tail (ps : List WordIntegerPacket) (i : BinaryIndex) :
    (terminal ps i).stk .work=encodeCache (ps.drop (i.value+1)) := by
  induction ps generalizing i with
  | nil => simp only [terminal,configuration,PacketStackPermutation.configuration,stackData_work,List.drop_nil,encodeCache]
  | cons p ps ih =>
    cases hb : i.bits with
    | nil =>
      have hz : i.value=0 := by unfold BinaryIndex.value;rw [hb];rfl
      simp only [terminal,hb,configuration,PacketStackPermutation.configuration,stackData_work,hz]
      rfl
    | cons b bs =>
      have hp:=i.predecessor_progress (by rw [hb];exact List.cons_ne_nil _ _)
      simp only [terminal,hb]
      rw [←hp]
      change (terminal ps i.predecessor).stk .work=encodeCache (ps.drop (i.predecessor.value+1))
      exact ih i.predecessor

/-- Typed packet reconstruction from the copied exact raw fields. The
canonicality/positive denominator proof is the original packet invariant. -/
theorem terminal_typed_hit (ps : List WordIntegerPacket) (i : BinaryIndex) (p : WordIntegerPacket)
    (hp : ps[i.value]?=some p) :
    parsedResult (terminal ps i)=some (rawPacket p) ∧ (rawPacket p).toWord (rawPacket_valid p)=p := by
  constructor
  · rw [terminal_getElem,hp,Option.map_some]
  · exact rawPacket_toWord p

end CircuitRecursion.PacketRecordMachine
