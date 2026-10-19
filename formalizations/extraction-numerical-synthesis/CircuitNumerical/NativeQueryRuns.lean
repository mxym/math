import CircuitNumerical.NativeQueryClearRuns

namespace CircuitRecursion.NativeQueryMachine

open Turing PacketFraming

set_option maxHeartbeats 1500000

def sourceInitial (ps : List WordIntegerPacket) (i : BinaryIndex)
    (oldIndex oldScratch oldCache rest : List Symbol) : PacketQueryMachine.Configuration PacketQueryMachine.Label :=
  PacketQueryMachine.configuration (some (.inl .clearIndex)) none oldIndex oldScratch oldCache (encodeCache ps)
    (PacketQueryMachine.queryCode i.bits++rest)

def initial (ps : List WordIntegerPacket) (i : BinaryIndex) (m : Memory)
    (oldIndex oldScratch oldCache rest : List Symbol) (words : WordStack → List Bool) : Configuration :=
  configuration (some (.inl .scratch)) m (sourceInitial ps i oldIndex oldScratch oldCache rest).stk words

def readerCall (ps : List WordIntegerPacket) (i : BinaryIndex)
    (oldIndex oldScratch oldCache rest : List Symbol) :
    StateTransition.EvalsToInTime (TM2.step program)
      (TM2Subroutine.liftConfiguration readerEmbed readerReturn
        (readerConfiguration (sourceInitial ps i oldIndex oldScratch oldCache rest) emptyWords))
      (some (TM2Subroutine.liftConfiguration readerEmbed readerReturn
        (readerConfiguration (PacketQueryMachine.terminal ps i rest) emptyWords)))
      (oldIndex.length+oldScratch.length+oldCache.length+2*i.bits.length+(2*i.bits.length+3)*ps.length+
        4*(encodeCache ps).length+10) :=
  TM2Subroutine.redirectedRun readerEmbed readerReturn readerProgram program (fun _ => rfl)
    (readerRun ps i none oldIndex oldScratch oldCache rest emptyWords)

theorem clear_to_reader (ps : List WordIntegerPacket) (i : BinaryIndex)
    (oldIndex oldScratch oldCache rest : List Symbol) :
    configuration (some (readerEmbed (.inl .clearIndex))) resetMemory
      (sourceInitial ps i oldIndex oldScratch oldCache rest).stk emptyWords=
    TM2Subroutine.liftConfiguration readerEmbed readerReturn
      (readerConfiguration (sourceInitial ps i oldIndex oldScratch oldCache rest) emptyWords) := rfl

theorem record_terminal_memory (ps : List WordIntegerPacket) (i : BinaryIndex) :
    (PacketRecordMachine.terminal ps i).var=none := by
  induction ps generalizing i with
  | nil => rfl
  | cons p ps ih =>
    cases hb : i.bits with
    | nil => simp only [PacketRecordMachine.terminal,hb,PacketRecordMachine.configuration,PacketStackPermutation.configuration]
    | cons b bs => simpa only [PacketRecordMachine.terminal,hb] using ih i.predecessor

theorem query_terminal_memory (ps : List WordIntegerPacket) (i : BinaryIndex) (rest : List Symbol) :
    (PacketQueryMachine.terminal ps i rest).var=none := record_terminal_memory ps i

theorem reader_to_parser (ps : List WordIntegerPacket) (i : BinaryIndex) (rest : List Symbol)
    (p : WordIntegerPacket) (hp : ps[i.value]?=some p) :
    TM2Subroutine.liftConfiguration readerEmbed readerReturn
      (readerConfiguration (PacketQueryMachine.terminal ps i rest) emptyWords)=
    parserConfiguration parserEmbed
      (PacketFieldMachine.configuration (some (.sign .n0)) PacketFieldMachine.emptyFlags none false
        (encodePacket p++[]) [] PacketFieldMachine.emptyFields []) (PacketQueryMachine.terminal ps i rest).stk := by
  simp only [TM2Subroutine.liftConfiguration,readerConfiguration,PacketQueryMachine.terminal_label,query_terminal_memory]
  change TM2.Cfg.mk (some (parserEmbed (.sign .n0))) resetMemory
      (readerStacks (PacketQueryMachine.terminal ps i rest).stk emptyWords)=
    TM2.Cfg.mk (some (parserEmbed (.sign .n0))) resetMemory
      (parserStacks (PacketFieldMachine.stackData (encodePacket p++[]) [] PacketFieldMachine.emptyFields [])
        (PacketQueryMachine.terminal ps i rest).stk)
  congr 1
  funext k
  cases k with
  | inl k =>
    by_cases hk : k=inputStack
    · subst k
      simp only [readerStacks,parserStacks,ite_true,PacketFieldMachine.stackData,List.append_nil]
      exact PacketQueryMachine.terminal_encoded_getElem ps i rest p hp
    · simp only [readerStacks,parserStacks,hk,ite_false]
  | inr k => cases k with
    | scratch | denominator => rfl
    | numerator q => rfl

def terminal (ps : List WordIntegerPacket) (i : BinaryIndex) (rest : List Symbol) (p : WordIntegerPacket) : Configuration :=
  parserConfiguration parserEmbed (PacketFieldMachine.terminal (rawPacket p) []) (PacketQueryMachine.terminal ps i rest).stk

def selectedParserCall (ps : List WordIntegerPacket) (i : BinaryIndex) (rest : List Symbol) (p : WordIntegerPacket) :
    StateTransition.EvalsToInTime (TM2.step program)
      (parserConfiguration parserEmbed
        (PacketFieldMachine.configuration (some (.sign .n0)) PacketFieldMachine.emptyFlags none false
          (encodePacket p++[]) [] PacketFieldMachine.emptyFields []) (PacketQueryMachine.terminal ps i rest).stk)
      (some (terminal ps i rest p)) (PacketFieldMachine.parseTime (rawPacket p)) :=
  parserRun parserEmbed program (fun _ => rfl) (PacketQueryMachine.terminal ps i rest).stk p []

/-- One actual finite heterogeneous-stack program: clears all prior native
outputs, clears prior Symbol working data, consumes and installs the next
binary query, physically clones/reads immutable master, then parses the exact
selected frame into native Bool words. hp is input address validity. -/
def nativeQueryRun (ps : List WordIntegerPacket) (i : BinaryIndex) (m : Memory)
    (oldIndex oldScratch oldCache rest : List Symbol) (words : WordStack → List Bool)
    (p : WordIntegerPacket) (hp : ps[i.value]?=some p) :
    StateTransition.EvalsToInTime (TM2.step program) (initial ps i m oldIndex oldScratch oldCache rest words)
      (some (terminal ps i rest p)) (wordVolume words+oldIndex.length+oldScratch.length+oldCache.length+
        2*i.bits.length+(2*i.bits.length+3)*ps.length+4*(encodeCache ps).length+
        PacketFieldMachine.parseTime (rawPacket p)+16) :=
  let hc:=clearRun m (sourceInitial ps i oldIndex oldScratch oldCache rest).stk words
  let hr:=readerCall ps i oldIndex oldScratch oldCache rest
  let ht:=selectedParserCall ps i rest p
  ⟨⟨ht.steps+(hr.steps+hc.steps),by
    have hcombined : advance^[hr.steps+hc.steps] (some (initial ps i m oldIndex oldScratch oldCache rest words))=
        some (parserConfiguration parserEmbed
          (PacketFieldMachine.configuration (some (.sign .n0)) PacketFieldMachine.emptyFlags none false
            (encodePacket p++[]) [] PacketFieldMachine.emptyFields []) (PacketQueryMachine.terminal ps i rest).stk) := by
      rw [Function.iterate_add_apply]
      have hxc : advance^[hc.steps] (some (initial ps i m oldIndex oldScratch oldCache rest words))=
        some (configuration (some (readerEmbed (.inl .clearIndex))) resetMemory
          (sourceInitial ps i oldIndex oldScratch oldCache rest).stk emptyWords) := hc.evals_in_steps
      rw [hxc,clear_to_reader]
      have hxr : advance^[hr.steps] _=some (TM2Subroutine.liftConfiguration readerEmbed readerReturn
        (readerConfiguration (PacketQueryMachine.terminal ps i rest) emptyWords)) := hr.evals_in_steps
      rw [hxr,reader_to_parser ps i rest p hp]
    change advance^[ht.steps+(hr.steps+hc.steps)] _=_
    rw [Function.iterate_add_apply,hcombined]
    exact ht.evals_in_steps⟩,by
    change ht.steps+(hr.steps+hc.steps)≤_
    have htc:=hc.steps_le_m
    have htr:=hr.steps_le_m
    have htt:=ht.steps_le_m
    omega⟩

theorem nativeQueryRun_steps (ps : List WordIntegerPacket) (i : BinaryIndex) (m : Memory)
    (oldIndex oldScratch oldCache rest : List Symbol) (words : WordStack → List Bool)
    (p : WordIntegerPacket) (hp : ps[i.value]?=some p) :
    (nativeQueryRun ps i m oldIndex oldScratch oldCache rest words p hp).steps=
      PacketFieldMachine.parseTime (rawPacket p)+
        (PacketQueryMachine.queryTime ps i oldIndex oldScratch oldCache+(wordVolume words+6)) := rfl

theorem addressed_mem {α : Type*} (xs : List α) (n : ℕ) (p : α) (hp : xs[n]?=some p) : p∈xs := by
  induction xs generalizing n with
  | nil => cases hp
  | cons a xs ih =>
    cases n with
    | zero =>
      change some a=some p at hp
      cases Option.some.inj hp
      exact List.mem_cons_self
    | succ n =>
      change xs[n]?=some p at hp
      exact List.mem_cons_of_mem a (ih n hp)

theorem nativeQueryRun_steps_height (ps : List WordIntegerPacket) (i : BinaryIndex) (m : Memory)
    (oldIndex oldScratch oldCache rest : List Symbol) (words : WordStack → List Bool)
    (p : WordIntegerPacket) (hp : ps[i.value]?=some p) (B : ℕ) (h : ∀ p∈ps,IntegerPacketHeight p.decode B) :
    (nativeQueryRun ps i m oldIndex oldScratch oldCache rest words p hp).steps≤
      wordVolume words+oldIndex.length+oldScratch.length+oldCache.length+2*i.bits.length+
        (2*i.bits.length+20*B+59)*ps.length+10*B+40 := by
  have hs:=(nativeQueryRun ps i m oldIndex oldScratch oldCache rest words p hp).steps_le_m
  have hc:=encodeCache_length_height ps B h
  have ht:=PacketFieldMachine.parsePacketRun_steps_height p [] B (h p (addressed_mem ps i.value p hp))
  change PacketFieldMachine.parseTime (rawPacket p)≤_ at ht
  nlinarith

end CircuitRecursion.NativeQueryMachine
