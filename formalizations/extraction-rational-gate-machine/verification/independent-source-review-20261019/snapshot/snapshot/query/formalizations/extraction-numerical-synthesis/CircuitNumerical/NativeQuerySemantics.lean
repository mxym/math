import CircuitNumerical.NativeQueryRuns

namespace CircuitRecursion.NativeQueryMachine

open Turing PacketFraming

theorem parserStacks_other (S : ∀ k,List (PacketFieldMachine.Alphabet k))
    (old : PacketQueryMachine.Stack → List Symbol) (k : PacketQueryMachine.Stack) (hk : k≠inputStack) :
    parserStacks S old (.inl k)=old k := by simp only [parserStacks,hk,ite_false]

def resultRaw (c : Configuration) : RawPacket :=
  ⟨⟨c.var.1.1,c.stk (.inr (.numerator .n0))⟩,⟨c.var.1.2.1,c.stk (.inr (.numerator .n1))⟩,
    ⟨c.var.1.2.2.1,c.stk (.inr (.numerator .n2))⟩,⟨c.var.1.2.2.2,c.stk (.inr (.numerator .n3))⟩,
    c.stk (.inr .denominator)⟩

def nativeWords (c : Configuration) : WordStack → List Bool := fun k => c.stk (.inr k)

theorem resultRaw_terminal (ps : List WordIntegerPacket) (i : BinaryIndex) (rest : List Symbol) (p : WordIntegerPacket) :
    resultRaw (terminal ps i rest p)=rawPacket p := rfl

theorem typed_result (ps : List WordIntegerPacket) (i : BinaryIndex) (rest : List Symbol) (p : WordIntegerPacket) :
    (resultRaw (terminal ps i rest p)).toWord (rawPacket_valid p)=p := rawPacket_toWord p

theorem terminal_master (ps : List WordIntegerPacket) (i : BinaryIndex) (rest : List Symbol) (p : WordIntegerPacket) :
    (terminal ps i rest p).stk (.inl (.inl (.inr ())))=encodeCache ps := by
  unfold terminal parserConfiguration
  dsimp only
  rw [parserStacks_other _ _ _ (by decide)]
  exact PacketQueryMachine.terminal_master ps i rest

theorem terminal_queries (ps : List WordIntegerPacket) (i : BinaryIndex) (rest : List Symbol) (p : WordIntegerPacket) :
    (terminal ps i rest p).stk (.inl (.inr ()))=rest := by
  unfold terminal parserConfiguration
  dsimp only
  rw [parserStacks_other _ _ _ (by decide)]
  exact PacketQueryMachine.terminal_queries ps i rest

theorem terminal_cache_tail (ps : List WordIntegerPacket) (i : BinaryIndex) (rest : List Symbol) (p : WordIntegerPacket) :
    (terminal ps i rest p).stk (.inl (.inl (.inl .work)))=encodeCache (ps.drop (i.value+1)) := by
  unfold terminal parserConfiguration
  dsimp only
  rw [parserStacks_other _ _ _ (by decide)]
  exact PacketQueryMachine.terminal_cache_tail ps i rest

theorem terminal_symbol_scratch (ps : List WordIntegerPacket) (i : BinaryIndex) (rest : List Symbol) (p : WordIntegerPacket) :
    (terminal ps i rest p).stk (.inl (.inl (.inl .right)))=[] := by
  unfold terminal parserConfiguration
  dsimp only
  rw [parserStacks_other _ _ _ (by decide)]
  exact PacketQueryMachine.terminal_scratch ps i rest

theorem terminal_symbol_payload_consumed (ps : List WordIntegerPacket) (i : BinaryIndex) (rest : List Symbol) (p : WordIntegerPacket) :
    (terminal ps i rest p).stk (.inl inputStack)=[] := by
  unfold terminal parserConfiguration
  dsimp only
  rw [parserStacks_input]
  rfl

theorem terminal_native_scratch (ps : List WordIntegerPacket) (i : BinaryIndex) (rest : List Symbol) (p : WordIntegerPacket) :
    (terminal ps i rest p).stk (.inr .scratch)=[] := rfl

theorem terminal_accepted (ps : List WordIntegerPacket) (i : BinaryIndex) (rest : List Symbol) (p : WordIntegerPacket) :
    (terminal ps i rest p).var.2.2=true := rfl

theorem terminal_halts (ps : List WordIntegerPacket) (i : BinaryIndex) (rest : List Symbol) (p : WordIntegerPacket) :
    TM2.step program (terminal ps i rest p)=none := rfl

theorem nativeQuery_mem_eval (ps : List WordIntegerPacket) (i : BinaryIndex) (m : Memory)
    (oldIndex oldScratch oldCache rest : List Symbol) (words : WordStack → List Bool)
    (p : WordIntegerPacket) (hp : ps[i.value]?=some p) :
    terminal ps i rest p∈StateTransition.eval (TM2.step program) (initial ps i m oldIndex oldScratch oldCache rest words) :=
  ListAssemblyMachine.evalsTo_terminal_mem_eval (nativeQueryRun ps i m oldIndex oldScratch oldCache rest words p hp).toEvalsTo
    (terminal_halts ps i rest p)

theorem terminal_wordVolume (ps : List WordIntegerPacket) (i : BinaryIndex) (rest : List Symbol) (p : WordIntegerPacket) :
    wordVolume (nativeWords (terminal ps i rest p))=
      (rawPacket p).n0.bits.length+(rawPacket p).n1.bits.length+(rawPacket p).n2.bits.length+
        (rawPacket p).n3.bits.length+p.denominator.length := by
  simp only [wordVolume,nativeWords,terminal,parserConfiguration,parserStacks,PacketFieldMachine.terminal,
    PacketFieldMachine.configuration,PacketFieldMachine.stackData,PacketFieldMachine.outputFields,List.length_nil,Nat.zero_add]
  rfl

theorem terminal_wordVolume_height (ps : List WordIntegerPacket) (i : BinaryIndex) (rest : List Symbol) (p : WordIntegerPacket)
    (B : ℕ) (h : IntegerPacketHeight p.decode B) : wordVolume (nativeWords (terminal ps i rest p))≤5*B+5 := by
  rw [terminal_wordVolume]
  have hw:=p.height_width B h
  have h0:=hw.1 0;have h1:=hw.1 1;have h2:=hw.1 2;have h3:=hw.1 3
  simp only [rawPacket]
  omega

/-- Actual return compiler interface for a specified caller. Native data
remain on physical Bool stacks; all six old native stacks will be cleared on
re-entry by the very same program, rather than assumed empty by the caller. -/
def nativeQueryCall {Δ : Type*} (ret : Memory → Δ)
    (outer : Δ → TM2.Stmt Alphabet (Label⊕Δ) Memory)
    (ps : List WordIntegerPacket) (i : BinaryIndex) (m : Memory)
    (oldIndex oldScratch oldCache rest : List Symbol) (words : WordStack → List Bool)
    (p : WordIntegerPacket) (hp : ps[i.value]?=some p) :
    StateTransition.EvalsToInTime (TM2.step (TM2Subroutine.splice program ret outer))
      (TM2Subroutine.liftConfiguration Sum.inl (fun m => Sum.inr (ret m))
        (initial ps i m oldIndex oldScratch oldCache rest words))
      (some (TM2Subroutine.liftConfiguration Sum.inl (fun m => Sum.inr (ret m)) (terminal ps i rest p)))
      (wordVolume words+oldIndex.length+oldScratch.length+oldCache.length+2*i.bits.length+
        (2*i.bits.length+3)*ps.length+4*(encodeCache ps).length+PacketFieldMachine.parseTime (rawPacket p)+16) :=
  TM2Subroutine.spliceRun program ret outer (nativeQueryRun ps i m oldIndex oldScratch oldCache rest words p hp)

theorem program_supports : TM2.Supports program Finset.univ :=
  ⟨Finset.mem_univ _,fun _ _ => TM2Subroutine.supportsStmt_univ _⟩

theorem stack_card : Fintype.card Stack=11 := by decide

theorem running_control_card : Fintype.card (Label×Memory)=5760 := by
  rw [Fintype.card_prod,Fintype.card_sum,Fintype.card_sum,PacketFieldMachine.memory_card]
  have hw : Fintype.card WordStack=6 := by decide
  have hp : Fintype.card PacketFieldMachine.Label=14 := by decide
  have hq : Fintype.card PacketQueryMachine.Label=16 := by
    have h:=PacketQueryMachine.running_control_card
    have hs : Fintype.card (Option Symbol)=5 := by decide
    rw [Fintype.card_prod,hs] at h
    omega
  rw [hw,hq,hp]

theorem statement_depth (q : Label) : ListAssemblyMachine.statementDepth (program q)≤7 := by
  cases q with
  | inl w => simp only [program,ListAssemblyMachine.statementDepth];omega
  | inr q => cases q with
    | inl q =>
      rw [program,TM2Subroutine.redirect_statementDepth,readerProgram,compileReader_statementDepth]
      exact PacketQueryMachine.statement_depth q
    | inr q =>
      rw [program,compileParser_statementDepth]
      exact (PacketFieldMachine.statement_depth q).trans (by decide)

end CircuitRecursion.NativeQueryMachine
