import CircuitNumerical.PacketMasterReader

namespace CircuitRecursion.PacketMasterMachine

open Turing PacketFraming

/-- Every actual prefix in the reader phase preserves every master symbol.
The clone phase itself temporarily drains master and restores it completely. -/
theorem reader_prefix_master (source : PacketRecordMachine.Configuration PacketRecordMachine.Label)
    (master : List Symbol) (n : ℕ) (c : Configuration Label)
    (h : advance^[n] (some (liftConfiguration Sum.inr source master))=some c) :
    c.stk (.inr ())=master := by
  have he:=TM2ConfigurationMap.iterate_map (TM2.step PacketRecordMachine.program) (TM2.step program)
    (fun x => liftConfiguration Sum.inr x master)
    (compiled_step Sum.inr PacketRecordMachine.program program (fun _ => rfl) master) n (some source)
  change advance^[n] (some (liftConfiguration Sum.inr source master))=_ at he
  rw [h] at he
  cases hs : (fun x : Option (PacketRecordMachine.Configuration PacketRecordMachine.Label) =>
      x.bind (TM2.step PacketRecordMachine.program))^[n] (some source) with
  | none => rw [hs] at he;cases he
  | some d =>
    rw [hs,Option.map_some] at he
    cases Option.some.inj he
    rfl

theorem terminal_master (ps : List WordIntegerPacket) (i : BinaryIndex) :
    (terminal ps i).stk (.inr ())=encodeCache ps := rfl

theorem terminal_master_unchanged (ps : List WordIntegerPacket) (i : BinaryIndex) :
    (terminal ps i).stk (.inr ())=
      (configuration (some (.inl .move)) none (i.bits.map Symbol.bit) [] [] (encodeCache ps) : Configuration Label).stk (.inr ()) := rfl

theorem source_terminal_scratch (ps : List WordIntegerPacket) (i : BinaryIndex) :
    (PacketRecordMachine.terminal ps i).stk .right=[] := by
  induction ps generalizing i with
  | nil => rfl
  | cons p ps ih =>
    cases hb : i.bits with
    | nil => simp only [PacketRecordMachine.terminal,hb,PacketRecordMachine.configuration,
        PacketStackPermutation.configuration,ListAssemblyMachine.stackData_right]
    | cons b bs => simpa only [PacketRecordMachine.terminal,hb] using ih i.predecessor

theorem terminal_scratch (ps : List WordIntegerPacket) (i : BinaryIndex) :
    (terminal ps i).stk (.inl .right)=[] := source_terminal_scratch ps i

theorem terminal_cache_tail (ps : List WordIntegerPacket) (i : BinaryIndex) :
    (terminal ps i).stk (.inl .work)=encodeCache (ps.drop (i.value+1)) :=
  PacketRecordMachine.terminal_cache_tail ps i

theorem terminal_encoded_getElem (ps : List WordIntegerPacket) (i : BinaryIndex) (p : WordIntegerPacket)
    (hp : ps[i.value]?=some p) : (terminal ps i).stk (.inl .left)=encodePacket p :=
  PacketRecordMachine.terminal_encoded_getElem ps i p hp

/-- A semantic observation of the exact output frame. This source parser
is not treated as a primitive of the finite copy/read machine. -/
def parsedResult (c : Configuration Label) : Option RawPacket :=
  (decodeRaw (c.stk (.inl .left))).map Prod.fst

theorem terminal_getElem (ps : List WordIntegerPacket) (i : BinaryIndex) :
    parsedResult (terminal ps i)=(ps[i.value]?).map rawPacket :=
  PacketRecordMachine.terminal_getElem ps i

theorem terminal_typed_hit (ps : List WordIntegerPacket) (i : BinaryIndex) (p : WordIntegerPacket)
    (hp : ps[i.value]?=some p) :
    parsedResult (terminal ps i)=some (rawPacket p) ∧ (rawPacket p).toWord (rawPacket_valid p)=p :=
  PacketRecordMachine.terminal_typed_hit ps i p hp

/-- The actual machine result simultaneously has the original immutable
master, exact selected frame on a hit, and the exact consumed-copy suffix. -/
theorem terminal_frame_contract (ps : List WordIntegerPacket) (i : BinaryIndex) :
    (terminal ps i).stk (.inr ())=encodeCache ps ∧
    (terminal ps i).stk (.inl .right)=[] ∧
    (terminal ps i).stk (.inl .work)=encodeCache (ps.drop (i.value+1)) ∧
    parsedResult (terminal ps i)=(ps[i.value]?).map rawPacket :=
  ⟨terminal_master ps i,terminal_scratch ps i,terminal_cache_tail ps i,terminal_getElem ps i⟩

end CircuitRecursion.PacketMasterMachine
