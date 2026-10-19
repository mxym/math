import CircuitNumerical.PacketQueryRuns

namespace CircuitRecursion.PacketQueryMachine

open Turing PacketFraming

theorem terminal_master (ps : List WordIntegerPacket) (i : BinaryIndex) (rest : List Symbol) :
    (terminal ps i rest).stk (.inl (.inr ()))=encodeCache ps := rfl

theorem terminal_queries (ps : List WordIntegerPacket) (i : BinaryIndex) (rest : List Symbol) :
    (terminal ps i rest).stk (.inr ())=rest := rfl

theorem terminal_scratch (ps : List WordIntegerPacket) (i : BinaryIndex) (rest : List Symbol) :
    (terminal ps i rest).stk (.inl (.inl .right))=[] := PacketMasterMachine.terminal_scratch ps i

theorem terminal_cache_tail (ps : List WordIntegerPacket) (i : BinaryIndex) (rest : List Symbol) :
    (terminal ps i rest).stk (.inl (.inl .work))=encodeCache (ps.drop (i.value+1)) :=
  PacketMasterMachine.terminal_cache_tail ps i

theorem terminal_encoded_getElem (ps : List WordIntegerPacket) (i : BinaryIndex) (rest : List Symbol)
    (p : WordIntegerPacket) (hp : ps[i.value]?=some p) :
    (terminal ps i rest).stk (.inl (.inl .left))=encodePacket p :=
  PacketMasterMachine.terminal_encoded_getElem ps i p hp

def parsedResult (c : Configuration Label) : Option RawPacket :=
  (decodeRaw (c.stk (.inl (.inl .left)))).map Prod.fst

theorem terminal_getElem (ps : List WordIntegerPacket) (i : BinaryIndex) (rest : List Symbol) :
    parsedResult (terminal ps i rest)=(ps[i.value]?).map rawPacket :=
  PacketMasterMachine.terminal_getElem ps i

theorem terminal_typed_hit (ps : List WordIntegerPacket) (i : BinaryIndex) (rest : List Symbol)
    (p : WordIntegerPacket) (hp : ps[i.value]?=some p) :
    parsedResult (terminal ps i rest)=some (rawPacket p) ∧ (rawPacket p).toWord (rawPacket_valid p)=p :=
  PacketMasterMachine.terminal_typed_hit ps i p hp

/-- Actual remaining working data, including out-of-range indices. This
bound is proved from the terminal recursion; old data are not released free. -/
theorem record_terminal_volume (ps : List WordIntegerPacket) (i : BinaryIndex) :
    ((PacketRecordMachine.terminal ps i).stk .left).length +
      ((PacketRecordMachine.terminal ps i).stk .right).length +
      ((PacketRecordMachine.terminal ps i).stk .work).length≤ i.bits.length+(encodeCache ps).length := by
  induction ps generalizing i with
  | nil =>
    simp only [PacketRecordMachine.terminal,PacketRecordMachine.configuration,
      PacketStackPermutation.configuration,ListAssemblyMachine.stackData_left,ListAssemblyMachine.stackData_right,
      ListAssemblyMachine.stackData_work,List.length_map,List.length_nil,encodeCache,Nat.add_zero]
    exact le_rfl
  | cons p ps ih =>
    cases hb : i.bits with
    | nil =>
      simp only [PacketRecordMachine.terminal,hb,PacketRecordMachine.configuration,
        PacketStackPermutation.configuration,ListAssemblyMachine.stackData_left,ListAssemblyMachine.stackData_right,
        ListAssemblyMachine.stackData_work,List.length_nil,encodeCache,List.length_append,Nat.add_zero,Nat.zero_add]
      exact le_rfl
    | cons b bs =>
      have ht:=ih i.predecessor
      have hw:=i.predecessor_width
      rw [hb] at hw
      simp only [PacketRecordMachine.terminal,hb,encodeCache,List.length_append]
      omega

theorem terminal_working_volume (ps : List WordIntegerPacket) (i : BinaryIndex) (rest : List Symbol) :
    ((terminal ps i rest).stk (.inl (.inl .left))).length+
      ((terminal ps i rest).stk (.inl (.inl .right))).length+
      ((terminal ps i rest).stk (.inl (.inl .work))).length≤ i.bits.length+(encodeCache ps).length :=
  record_terminal_volume ps i

/-- Re-entry data of the just-completed call. Changing its control label is
performed by the proved CPS return compiler, not an assumed free reset. -/
def reentry (ps : List WordIntegerPacket) (previous : BinaryIndex) (queries : List Symbol) : Configuration Label :=
  configuration (some (.inl .clearIndex)) (terminal ps previous queries).var
    ((terminal ps previous queries).stk (.inl (.inl .left)))
    ((terminal ps previous queries).stk (.inl (.inl .right)))
    ((terminal ps previous queries).stk (.inl (.inl .work))) (encodeCache ps) queries

theorem reentry_stacks (ps : List WordIntegerPacket) (previous : BinaryIndex) (queries : List Symbol) :
    (reentry ps previous queries).stk=(terminal ps previous queries).stk := by
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k;exact (terminal_master ps previous queries).symm
  | inr k => cases k;rfl

/-- Fully charged next call from the concrete previous output and suffix. -/
def reuseRun (ps : List WordIntegerPacket) (previous next : BinaryIndex) (rest : List Symbol) :
    StateTransition.EvalsToInTime (TM2.step program)
      (reentry ps previous (queryCode next.bits++rest)) (some (terminal ps next rest))
      (previous.bits.length+2*next.bits.length+(2*next.bits.length+3)*ps.length+5*(encodeCache ps).length+10) :=
  ⟨⟨queryTime ps next
      ((terminal ps previous (queryCode next.bits++rest)).stk (.inl (.inl .left)))
      ((terminal ps previous (queryCode next.bits++rest)).stk (.inl (.inl .right)))
      ((terminal ps previous (queryCode next.bits++rest)).stk (.inl (.inl .work))),by
    exact query_iterate ps next _ _ _ _ rest⟩,by
    change queryTime ps next _ _ _≤_
    have ht:=queryTime_bound ps next
      ((terminal ps previous (queryCode next.bits++rest)).stk (.inl (.inl .left)))
      ((terminal ps previous (queryCode next.bits++rest)).stk (.inl (.inl .right)))
      ((terminal ps previous (queryCode next.bits++rest)).stk (.inl (.inl .work)))
    have hv:=terminal_working_volume ps previous (queryCode next.bits++rest)
    omega⟩

theorem reuseRun_steps_height (ps : List WordIntegerPacket) (previous next : BinaryIndex) (rest : List Symbol)
    (B : ℕ) (h : ∀ p∈ps,IntegerPacketHeight p.decode B) :
    (reuseRun ps previous next rest).steps≤previous.bits.length+2*next.bits.length+
      (2*next.bits.length+25*B+73)*ps.length+10 := by
  have hs:=(reuseRun ps previous next rest).steps_le_m
  have hc:=encodeCache_length_height ps B h
  nlinarith

/-- A literal call/return insertion into any specified finite caller. The
source call already includes all old-data cleanup and request installation. -/
def queryCall {Δ : Type*} (ret : Option Symbol → Δ)
    (outer : Δ → TM2.Stmt (fun _ : Stack => Symbol) (Label⊕Δ) (Option Symbol))
    (ps : List WordIntegerPacket) (i : BinaryIndex) (v : Option Symbol)
    (oldIndex oldScratch oldCache rest : List Symbol) :
    StateTransition.EvalsToInTime (TM2.step (TM2Subroutine.splice program ret outer))
      (TM2Subroutine.liftConfiguration Sum.inl (fun v => Sum.inr (ret v))
        (configuration (some (.inl .clearIndex)) v oldIndex oldScratch oldCache (encodeCache ps) (queryCode i.bits++rest)))
      (some (TM2Subroutine.liftConfiguration Sum.inl (fun v => Sum.inr (ret v)) (terminal ps i rest)))
      (oldIndex.length+oldScratch.length+oldCache.length+2*i.bits.length+
        (2*i.bits.length+3)*ps.length+4*(encodeCache ps).length+10) :=
  TM2Subroutine.spliceRun program ret outer (nextQueryRun ps i v oldIndex oldScratch oldCache rest)

end CircuitRecursion.PacketQueryMachine
