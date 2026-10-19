import CircuitNumerical.TM2ConfigurationMap

namespace CircuitRecursion.PacketCounterLift

open Turing ListAssemblyMachine PacketFraming

abbrev Configuration := TM2.Cfg (fun _ : Stack => Symbol) BinaryCounterMachine.Label (Option Symbol)

def program (q : BinaryCounterMachine.Label) : TM2.Stmt (fun _ : Stack => Symbol) BinaryCounterMachine.Label (Option Symbol) :=
  compile (BinaryCounterMachine.program q)

theorem source_workFree (q : BinaryCounterMachine.Label) : WorkFree (BinaryCounterMachine.program q) := by
  cases q <;> simp [WorkFree,BinaryCounterMachine.program]

theorem program_step (c : BinaryCounterMachine.Configuration) (frame : List Symbol) :
    TM2.step program (liftConfiguration c frame)=
      (TM2.step BinaryCounterMachine.program c).map (fun d => liftConfiguration d frame) := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => rfl
  | some l => simp only [liftConfiguration,TM2.step,program,compile_stepAux _ (source_workFree l),Option.map_some]

def configuration (l : Option BinaryCounterMachine.Label) (v : Option Symbol)
    (as bs frame : List Symbol) : Configuration := ⟨l,v,stackData as bs frame⟩

theorem lift_source_configuration (l : Option BinaryCounterMachine.Label) (v : Option Bool)
    (as bs ws : List Bool) (frame : List Symbol) :
    liftConfiguration (BinaryCounterMachine.configuration l v as bs ws) frame=
      configuration l (liftMemory v) (as.map Symbol.bit) (bs.map Symbol.bit) frame := rfl

/-- The exact old finite counter run compiled to the packet alphabet, with
an arbitrary separated packet stream preserved on work. -/
def counterRun (as : List Bool) (h : BinaryWordCanonical as) (frame : List Symbol) :
    StateTransition.EvalsToInTime (TM2.step program)
      (configuration (some .borrow) none (as.map Symbol.bit) [] frame)
      (some (configuration none none ((binaryPredecessorBits as).map Symbol.bit) [] frame)) (2*as.length+2) :=
  TM2ConfigurationMap.mapRun (TM2.step BinaryCounterMachine.program) (TM2.step program)
    (fun c => liftConfiguration c frame) (fun c => program_step c frame) (BinaryCounterMachine.counterRun as h [])

theorem counterRun_steps (as : List Bool) (h : BinaryWordCanonical as) (frame : List Symbol) :
    (counterRun as h frame).steps=BinaryCounterMachine.borrowTime as 0 := rfl

theorem counter_mem_eval (as : List Bool) (h : BinaryWordCanonical as) (frame : List Symbol) :
    configuration none none ((binaryPredecessorBits as).map Symbol.bit) [] frame∈
      StateTransition.eval (TM2.step program) (configuration (some .borrow) none (as.map Symbol.bit) [] frame) :=
  evalsTo_terminal_mem_eval (counterRun as h frame).toEvalsTo rfl

theorem program_supports : TM2.Supports program Finset.univ :=
  ⟨Finset.mem_univ _,fun _ _ => TM2Subroutine.supportsStmt_univ _⟩

theorem running_control_card : Fintype.card (BinaryCounterMachine.Label×Option Symbol)=20 := by decide

theorem statement_depth (q : BinaryCounterMachine.Label) : statementDepth (program q)≤7 := by
  rw [program,compile_statementDepth]
  exact BinaryCounterMachine.statement_depth q

end CircuitRecursion.PacketCounterLift
