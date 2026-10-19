import CircuitNumerical.PacketQuerySetupRuns

namespace CircuitRecursion.PacketQueryMachine

open Turing PacketFraming

set_option maxHeartbeats 1500000

theorem lift_masterConfiguration {Λ Δ : Type*} (embed : Λ → Δ) (l : Option Λ) (v : Option Symbol)
    (i s c m q : List Symbol) :
    TM2ExtraStack.liftConfiguration embed (PacketMasterMachine.configuration l v i s c m) q=
      configuration (l.map embed) v i s c m q := by
  change TM2.Cfg.mk (l.map embed) v (TM2ExtraStack.extendStacks (PacketMasterMachine.stackData i s c m) q)=
    TM2.Cfg.mk (l.map embed) v (stackData i s c m q)
  congr 1
  funext k
  cases k <;> rfl

def terminal (ps : List WordIntegerPacket) (i : BinaryIndex) (rest : List Symbol) : Configuration Label :=
  TM2ExtraStack.liftConfiguration Sum.inr (PacketMasterMachine.terminal ps i) rest

def readerCall (ps : List WordIntegerPacket) (i : BinaryIndex) (rest : List Symbol) :
    StateTransition.EvalsToInTime (TM2.step program)
      (TM2ExtraStack.liftConfiguration Sum.inr
        (PacketMasterMachine.configuration (some (.inl .move)) none (i.bits.map Symbol.bit) [] [] (encodeCache ps)) rest)
      (some (terminal ps i rest)) ((2*i.bits.length+3)*ps.length+4*(encodeCache ps).length+5) :=
  TM2ExtraStack.compiledRun Sum.inr PacketMasterMachine.program program (fun _ => rfl) rest
    (PacketMasterMachine.readRun ps i)

theorem readerCall_steps (ps : List WordIntegerPacket) (i : BinaryIndex) (rest : List Symbol) :
    (readerCall ps i rest).steps=2*(encodeCache ps).length+2+PacketRecordMachine.readTime ps i := rfl

theorem readerCall_iterate (ps : List WordIntegerPacket) (i : BinaryIndex) (rest : List Symbol) :
    advance^[2*(encodeCache ps).length+2+PacketRecordMachine.readTime ps i]
      (some (configuration (some (.inr (.inl .move))) none (i.bits.map Symbol.bit) [] [] (encodeCache ps) rest))=
      some (terminal ps i rest) := by
  have hx:=(readerCall ps i rest).evals_in_steps
  change advance^[2*(encodeCache ps).length+2+PacketRecordMachine.readTime ps i]
    (some (TM2ExtraStack.liftConfiguration Sum.inr
      (PacketMasterMachine.configuration (some (.inl .move)) none (i.bits.map Symbol.bit) [] [] (encodeCache ps)) rest))=_ at hx
  simpa only [lift_masterConfiguration,Option.map_some] using hx

/-- Exact external time indexing, not a machine Nat/fuel register. -/
def queryTime (ps : List WordIntegerPacket) (i : BinaryIndex) (oldIndex oldScratch oldCache : List Symbol) : ℕ :=
  (oldIndex.length+oldScratch.length+oldCache.length+2*i.bits.length+5)+
    (2*(encodeCache ps).length+2+PacketRecordMachine.readTime ps i)

theorem query_iterate (ps : List WordIntegerPacket) (i : BinaryIndex) (v : Option Symbol)
    (oldIndex oldScratch oldCache rest : List Symbol) :
    advance^[queryTime ps i oldIndex oldScratch oldCache]
      (some (configuration (some (.inl .clearIndex)) v oldIndex oldScratch oldCache (encodeCache ps) (queryCode i.bits++rest)))=
      some (terminal ps i rest) := by
  unfold queryTime
  rw [Nat.add_comm,Function.iterate_add_apply,setup_iterate,readerCall_iterate]

theorem queryTime_bound (ps : List WordIntegerPacket) (i : BinaryIndex)
    (oldIndex oldScratch oldCache : List Symbol) :
    queryTime ps i oldIndex oldScratch oldCache≤oldIndex.length+oldScratch.length+oldCache.length+
      2*i.bits.length+(2*i.bits.length+3)*ps.length+4*(encodeCache ps).length+10 := by
  unfold queryTime
  have ht:=PacketRecordMachine.readTime_bound ps i
  omega

/-- One complete repeatable cache query from arbitrary previous working
contents. Old payload/suffix cleanup and real input-stream consumption,
reversal and installation are all included in official machine time. -/
def nextQueryRun (ps : List WordIntegerPacket) (i : BinaryIndex) (v : Option Symbol)
    (oldIndex oldScratch oldCache rest : List Symbol) :
    StateTransition.EvalsToInTime (TM2.step program)
      (configuration (some (.inl .clearIndex)) v oldIndex oldScratch oldCache (encodeCache ps) (queryCode i.bits++rest))
      (some (terminal ps i rest)) (oldIndex.length+oldScratch.length+oldCache.length+
        2*i.bits.length+(2*i.bits.length+3)*ps.length+4*(encodeCache ps).length+10) :=
  ⟨⟨queryTime ps i oldIndex oldScratch oldCache,query_iterate ps i v oldIndex oldScratch oldCache rest⟩,
    queryTime_bound ps i oldIndex oldScratch oldCache⟩

theorem nextQueryRun_steps (ps : List WordIntegerPacket) (i : BinaryIndex) (v : Option Symbol)
    (oldIndex oldScratch oldCache rest : List Symbol) :
    (nextQueryRun ps i v oldIndex oldScratch oldCache rest).steps=queryTime ps i oldIndex oldScratch oldCache := rfl

theorem terminal_label (ps : List WordIntegerPacket) (i : BinaryIndex) (rest : List Symbol) :
    (terminal ps i rest).l=none := by
  simp only [terminal,TM2ExtraStack.liftConfiguration,PacketMasterMachine.terminal_label,Option.map_none]

theorem terminal_halts (ps : List WordIntegerPacket) (i : BinaryIndex) (rest : List Symbol) :
    TM2.step program (terminal ps i rest)=none := by
  have hl:=terminal_label ps i rest
  cases ht : terminal ps i rest with
  | mk l v S =>
    rw [ht] at hl
    change l=none at hl
    subst l
    rfl

theorem query_mem_eval (ps : List WordIntegerPacket) (i : BinaryIndex) (v : Option Symbol)
    (oldIndex oldScratch oldCache rest : List Symbol) :
    terminal ps i rest∈StateTransition.eval (TM2.step program)
      (configuration (some (.inl .clearIndex)) v oldIndex oldScratch oldCache (encodeCache ps) (queryCode i.bits++rest)) :=
  ListAssemblyMachine.evalsTo_terminal_mem_eval (nextQueryRun ps i v oldIndex oldScratch oldCache rest).toEvalsTo
    (terminal_halts ps i rest)

theorem nextQueryRun_steps_height (ps : List WordIntegerPacket) (i : BinaryIndex) (v : Option Symbol)
    (oldIndex oldScratch oldCache rest : List Symbol) (B : ℕ) (h : ∀ p∈ps,IntegerPacketHeight p.decode B) :
    (nextQueryRun ps i v oldIndex oldScratch oldCache rest).steps≤
      oldIndex.length+oldScratch.length+oldCache.length+2*i.bits.length+(2*i.bits.length+20*B+59)*ps.length+10 := by
  have hs:=(nextQueryRun ps i v oldIndex oldScratch oldCache rest).steps_le_m
  have hc:=encodeCache_length_height ps B h
  nlinarith

theorem program_supports : TM2.Supports program Finset.univ :=
  ⟨Finset.mem_univ _,fun _ _ => TM2Subroutine.supportsStmt_univ _⟩

theorem running_control_card : Fintype.card (Label×Option Symbol)=80 := by decide

theorem statement_depth (q : Label) : ListAssemblyMachine.statementDepth (program q)≤7 := by
  cases q with
  | inl q => cases q <;> simp only [program,ListAssemblyMachine.statementDepth] <;> omega
  | inr q =>
    rw [program,TM2ExtraStack.compile_statementDepth]
    exact PacketMasterMachine.statement_depth q

end CircuitRecursion.PacketQueryMachine
