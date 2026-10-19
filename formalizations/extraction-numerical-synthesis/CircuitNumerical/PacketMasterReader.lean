import CircuitNumerical.PacketMasterEmbedding

namespace CircuitRecursion.PacketMasterMachine

open Turing PacketFraming

abbrev Label := CloneLabel ⊕ PacketRecordMachine.Label

/-- A single finite program: physical master clone followed by the complete
binary-indexed frame reader. Calls are syntactic goto labels, not host calls. -/
def program : Label → TM2.Stmt (fun _ : Stack => Symbol) Label (Option Symbol) :=
  TM2Subroutine.splice cloneProgram (fun _ => PacketRecordMachine.Label.check)
    (fun q => compile Sum.inr (PacketRecordMachine.program q))

def advance : Option (Configuration Label) → Option (Configuration Label) :=
  fun c => c.bind (TM2.step program)

def terminal (ps : List WordIntegerPacket) (i : BinaryIndex) : Configuration Label :=
  liftConfiguration Sum.inr (PacketRecordMachine.terminal ps i) (encodeCache ps)

/-- The master is restored and the working copy exists after both real passes. -/
def cloneCall (index master : List Symbol) :
    StateTransition.EvalsToInTime (TM2.step program)
      (configuration (some (.inl .move)) none index [] [] master)
      (some (configuration (some (.inr .check)) none index [] master master)) (2*master.length+2) :=
  TM2Subroutine.spliceRun cloneProgram (fun _ => PacketRecordMachine.Label.check)
    (fun q => compile Sum.inr (PacketRecordMachine.program q)) (cloneRun index master)

theorem cloneCall_steps (index master : List Symbol) : (cloneCall index master).steps=2*master.length+2 := rfl

def readerCall (ps : List WordIntegerPacket) (i : BinaryIndex) :
    StateTransition.EvalsToInTime (TM2.step program)
      (liftConfiguration Sum.inr
        (PacketRecordMachine.configuration (some .check) none (i.bits.map Symbol.bit) [] (encodeCache ps))
        (encodeCache ps))
      (some (terminal ps i)) ((2*i.bits.length+3)*ps.length+2*(encodeCache ps).length+3) :=
  compiledRun Sum.inr PacketRecordMachine.program program (fun _ => rfl) (encodeCache ps)
    (PacketRecordMachine.readRun ps i)

theorem readerCall_steps (ps : List WordIntegerPacket) (i : BinaryIndex) :
    (readerCall ps i).steps=PacketRecordMachine.readTime ps i := rfl

theorem cloneCall_iterate (index master : List Symbol) :
    advance^[2*master.length+2] (some (configuration (some (.inl .move)) none index [] [] master))=
      some (configuration (some (.inr .check)) none index [] master master) :=
  (cloneCall index master).evals_in_steps

theorem readerCall_iterate (ps : List WordIntegerPacket) (i : BinaryIndex) :
    advance^[PacketRecordMachine.readTime ps i]
      (some (configuration (some (.inr .check)) none (i.bits.map Symbol.bit) [] (encodeCache ps) (encodeCache ps)))=
      some (terminal ps i) := by
  have hx:=(readerCall ps i).evals_in_steps
  change advance^[PacketRecordMachine.readTime ps i]
    (some (liftConfiguration Sum.inr
      (PacketRecordMachine.configuration (some .check) none (i.bits.map Symbol.bit) [] (encodeCache ps))
      (encodeCache ps)))=_ at hx
  simpa only [lift_recordConfiguration,Option.map_some] using hx

theorem read_iterate (ps : List WordIntegerPacket) (i : BinaryIndex) :
    advance^[2*(encodeCache ps).length+2+PacketRecordMachine.readTime ps i]
      (some (configuration (some (.inl .move)) none (i.bits.map Symbol.bit) [] [] (encodeCache ps)))=
      some (terminal ps i) := by
  rw [show 2*(encodeCache ps).length+2+PacketRecordMachine.readTime ps i=
    PacketRecordMachine.readTime ps i+(2*(encodeCache ps).length+2) by omega,
    Function.iterate_add_apply,cloneCall_iterate,readerCall_iterate]

/-- Actual immutable-master packet read, including the full physical working
copy. Neither final correctness nor the desired budget is a caller premise. -/
def readRun (ps : List WordIntegerPacket) (i : BinaryIndex) :
    StateTransition.EvalsToInTime (TM2.step program)
      (configuration (some (.inl .move)) none (i.bits.map Symbol.bit) [] [] (encodeCache ps))
      (some (terminal ps i)) ((2*i.bits.length+3)*ps.length+4*(encodeCache ps).length+5) :=
  ⟨⟨2*(encodeCache ps).length+2+PacketRecordMachine.readTime ps i,read_iterate ps i⟩,by
    change 2*(encodeCache ps).length+2+PacketRecordMachine.readTime ps i≤
      (2*i.bits.length+3)*ps.length+4*(encodeCache ps).length+5
    have ht:=PacketRecordMachine.readTime_bound ps i
    omega⟩

theorem readRun_steps (ps : List WordIntegerPacket) (i : BinaryIndex) :
    (readRun ps i).steps=2*(encodeCache ps).length+2+PacketRecordMachine.readTime ps i := rfl

theorem terminal_label (ps : List WordIntegerPacket) (i : BinaryIndex) : (terminal ps i).l=none := by
  simp only [terminal,liftConfiguration,PacketRecordMachine.terminal_label,Option.map_none]

theorem terminal_halts (ps : List WordIntegerPacket) (i : BinaryIndex) :
    TM2.step program (terminal ps i)=none := by
  have hl:=terminal_label ps i
  cases ht : terminal ps i with
  | mk l v S =>
    rw [ht] at hl
    change l=none at hl
    subst l
    rfl

theorem read_mem_eval (ps : List WordIntegerPacket) (i : BinaryIndex) :
    terminal ps i∈StateTransition.eval (TM2.step program)
      (configuration (some (.inl .move)) none (i.bits.map Symbol.bit) [] [] (encodeCache ps)) :=
  ListAssemblyMachine.evalsTo_terminal_mem_eval (readRun ps i).toEvalsTo (terminal_halts ps i)

theorem program_supports : TM2.Supports program Finset.univ :=
  ⟨Finset.mem_univ _,fun _ _ => TM2Subroutine.supportsStmt_univ _⟩

theorem running_control_card : Fintype.card (Label×Option Symbol)=55 := by decide

theorem statement_depth (q : Label) : ListAssemblyMachine.statementDepth (program q)≤7 := by
  cases q with
  | inl q =>
    rw [program,TM2Subroutine.splice_local_statementDepth]
    exact (clone_statement_depth q).trans (by decide)
  | inr q =>
    rw [program,TM2Subroutine.splice_outer,compile_statementDepth]
    exact PacketRecordMachine.statement_depth q

theorem readRun_steps_height (ps : List WordIntegerPacket) (i : BinaryIndex) (B : ℕ)
    (h : ∀ p∈ps,IntegerPacketHeight p.decode B) :
    (readRun ps i).steps≤(2*i.bits.length+20*B+59)*ps.length+5 := by
  have hs:=(readRun ps i).steps_le_m
  have hc:=encodeCache_length_height ps B h
  nlinarith

end CircuitRecursion.PacketMasterMachine
