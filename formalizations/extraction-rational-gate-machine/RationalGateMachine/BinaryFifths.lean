import RationalGateMachine.StateLift

namespace RationalGateMachine.BinaryFifths

open Turing RationalGateProvider CircuitRecursion
open ListAssemblyMachine

inductive OuterLabel where
  | init | loop
  deriving DecidableEq
instance : Fintype OuterLabel := ⟨{.init,.loop},by intro q;cases q <;> simp⟩
instance : Inhabited OuterLabel := ⟨.init⟩

abbrev Label := BinaryClock.Label ⊕ OuterLabel
abbrev Variable := Remainder × Option Bool
abbrev Configuration := TM2.Cfg (fun _ : Stack => Bool) Label Variable

def configuration (l : Option Label) (r : Remainder) (v : Option Bool)
    (left right work : List Bool) : Configuration :=
  ⟨l,(r,v),ListAssemblyMachine.stackData left right work⟩

def clockProgram : BinaryClock.Label → TM2.Stmt (fun _ : Stack => Bool) BinaryClock.Label Variable :=
  fun q => StateLift.compile (BinaryClock.program q)

/-- The binary clock returns to init; the same finite program then consumes
that actual unary clock while emitting numerator and denominator digits. -/
def outer : OuterLabel → TM2.Stmt (fun _ : Stack => Bool) Label Variable
  | .init => .push .right (fun _ => true)
      (.load (fun v => (v.1,none)) (.goto (fun _ => .inr .loop)))
  | .loop => .pop .work (fun v b => (v.1,b))
      (.branch (fun v => v.2.isSome)
        (.push .left (fun v => (transition v.1).1)
          (.push .right (fun _ => false)
            (.load (fun v => ((transition v.1).2,none)) (.goto (fun _ => .inr .loop)))))
        .halt)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Variable :=
  TM2Subroutine.splice clockProgram (fun _ => .init) outer

def advance : Option Configuration → Option Configuration :=
  fun c => c.bind (TM2.step program)

def terminal (initial : Remainder) (q : ℕ) : Configuration :=
  configuration none (RationalGateProvider.run initial q).remainder none
    (RationalGateProvider.run initial q).bits (denominatorBits q) []

def clockCall (initial : Remainder) (i : BinaryIndex) :
    StateTransition.EvalsToInTime (TM2.step program)
      (configuration (some (.inl (.inr .loop))) initial none i.bits [] [])
      (some (configuration (some (.inr .init)) initial none [] [] (List.replicate i.value false)))
      ((2*i.bits.length+4)*i.value+1) := by
  let h:=TM2Subroutine.spliceRun clockProgram (fun _ => OuterLabel.init) outer
    (StateLift.run initial BinaryClock.program (BinaryClock.clockRun i []))
  refine ⟨⟨BinaryClock.clockTime i.value i,?_⟩,BinaryClock.clock_time_bound i.value i⟩
  have hs : h.steps=BinaryClock.clockTime i.value i := rfl
  have he:=h.evals_in_steps
  rw [hs] at he
  simpa only [TM2Subroutine.liftConfiguration,StateLift.configuration,
    BinaryClock.configuration,configuration,List.append_nil,program] using he

theorem clockCall_steps (initial : Remainder) (i : BinaryIndex) :
    (clockCall initial i).steps=BinaryClock.clockTime i.value i := rfl

theorem clockCall_iterate (initial : Remainder) (i : BinaryIndex) :
    advance^[BinaryClock.clockTime i.value i]
      (some (configuration (some (.inl (.inr .loop))) initial none i.bits [] []))=
      some (configuration (some (.inr .init)) initial none [] [] (List.replicate i.value false)) :=
  (clockCall initial i).evals_in_steps

theorem step_init (initial : Remainder) (clock : List Bool) :
    TM2.step program (configuration (some (.inr .init)) initial none [] [] clock)=
      some (configuration (some (.inr .loop)) initial none [] [true] clock) := by
  simp only [program,TM2Subroutine.splice,outer,configuration,TM2.step,TM2.stepAux,
    stackData_right,update_stackData_right]

theorem step_empty (initial : Remainder) (numerator denominator : List Bool) :
    TM2.step program (configuration (some (.inr .loop)) initial none numerator denominator [])=
      some (configuration none initial none numerator denominator []) := by
  simp only [program,TM2Subroutine.splice,outer,configuration,TM2.step,TM2.stepAux,
    stackData_work,List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false,
    update_stackData_work]

theorem step_cons (initial : Remainder) (b : Bool) (clock numerator denominator : List Bool) :
    TM2.step program (configuration (some (.inr .loop)) initial none numerator denominator (b::clock))=
      some (configuration (some (.inr .loop)) (transition initial).2 none
        ((transition initial).1::numerator) (false::denominator) clock) := by
  simp only [program,TM2Subroutine.splice,outer,configuration,TM2.step,TM2.stepAux,
    stackData_work,List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true,
    update_stackData_work,stackData_left,update_stackData_left,stackData_right,update_stackData_right]

theorem generation_steps (clock : List Bool) (s : Output) (denominator : List Bool) :
    advance^[clock.length+1]
      (some (configuration (some (.inr .loop)) s.remainder none s.bits denominator clock))=
      some (configuration none (RationalGateMachine.advance s clock).remainder none
        (RationalGateMachine.advance s clock).bits (List.replicate clock.length false ++ denominator) []) := by
  induction clock generalizing s denominator with
  | nil => simp [advance,step_empty,RationalGateMachine.advance]
  | cons b clock ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      change advance^[clock.length+1] (TM2.step program
        (configuration (some (.inr .loop)) s.remainder none s.bits denominator (b::clock)))=_
      rw [step_cons]
      have h:=ih (next s) (false::denominator)
      change advance^[clock.length+1]
        (some (configuration (some (.inr .loop)) (next s).remainder none (next s).bits
          (false::denominator) clock))=_
      rw [h]
      simp only [RationalGateMachine.advance]
      congr 2
      rw [List.replicate_add]
      simp [List.append_assoc]

theorem unary_generation_steps (initial : Remainder) (q : ℕ) :
    advance^[q+1]
      (some (configuration (some (.inr .loop)) initial none [] [true] (List.replicate q false)))=
      some (terminal initial q) := by
  have h:=generation_steps (List.replicate q false) ⟨[],initial⟩ [true]
  rw [RationalGateMachine.advance_seed] at h
  simpa only [List.length_replicate,terminal,denominatorBits] using h

theorem binary_generation_steps (initial : Remainder) (i : BinaryIndex) :
    advance^[BinaryClock.clockTime i.value i+i.value+2]
      (some (configuration (some (.inl (.inr .loop))) initial none i.bits [] []))=
      some (terminal initial i.value) := by
  rw [show BinaryClock.clockTime i.value i+i.value+2=
      (i.value+1)+1+BinaryClock.clockTime i.value i by omega,
    Function.iterate_add_apply,clockCall_iterate,Function.iterate_succ_apply]
  change advance^[i.value+1]
    (TM2.step program (configuration (some (.inr .init)) initial none [] [] (List.replicate i.value false)))=_
  rw [step_init,unary_generation_steps]

/-- Genuine binary precision input to the exact fifths output, in one finite
TM2 program including clock construction, denominator initialization and
generation. No caller-supplied correctness or runtime certificate occurs. -/
def binaryFifthsRun (initial : Remainder) (i : BinaryIndex) :
    StateTransition.EvalsToInTime (TM2.step program)
      (configuration (some (.inl (.inr .loop))) initial none i.bits [] [])
      (some (terminal initial i.value)) ((2*i.bits.length+5)*i.value+3) :=
  ⟨⟨BinaryClock.clockTime i.value i+i.value+2,binary_generation_steps initial i⟩,by
    have h:=BinaryClock.clock_time_bound i.value i
    nlinarith⟩

theorem binaryFifthsRun_steps (initial : Remainder) (i : BinaryIndex) :
    (binaryFifthsRun initial i).steps=BinaryClock.clockTime i.value i+i.value+2 := rfl

theorem binaryFifthsRun_steps_logarithmic (initial : Remainder) (i : BinaryIndex) :
    (binaryFifthsRun initial i).steps ≤ (2*Nat.clog 2 (i.value+1)+7)*i.value+3 := by
  have h:=BinaryClock.clockRun_steps_logarithmic i []
  rw [BinaryClock.clockRun_steps] at h
  rw [binaryFifthsRun_steps]
  nlinarith

theorem terminal_halts (initial : Remainder) (q : ℕ) :
    TM2.step program (terminal initial q)=none := rfl

theorem binaryFifths_mem_eval (initial : Remainder) (i : BinaryIndex) :
    terminal initial i.value ∈ StateTransition.eval (TM2.step program)
      (configuration (some (.inl (.inr .loop))) initial none i.bits [] []) :=
  evalsTo_terminal_mem_eval (binaryFifthsRun initial i).toEvalsTo (terminal_halts _ _)

theorem terminal_numerator (initial : Remainder) (q : ℕ) :
    (terminal initial q).stk .left=(RationalGateProvider.run initial q).bits := rfl

theorem terminal_denominator (initial : Remainder) (q : ℕ) :
    (terminal initial q).stk .right=denominatorBits q := rfl

theorem terminal_clock_empty (initial : Remainder) (q : ℕ) :
    (terminal initial q).stk .work=[] := rfl

theorem terminal_dyadic_error (initial : Remainder) (q : ℕ) :
    0 ≤ (initial.value : ℚ)/5 - (bitValue ((terminal initial q).stk .left) : ℚ)/2^q ∧
      (initial.value : ℚ)/5 - (bitValue ((terminal initial q).stk .left) : ℚ)/2^q < 1/(2:ℚ)^q :=
  run_dyadic_error initial q

theorem program_supports : TM2.Supports program Finset.univ :=
  TM2Subroutine.splice_supports _ _ _

theorem finite_running_control_card : Fintype.card (Label × Variable)=120 := by decide

theorem label_card : Fintype.card Label=8 := by decide

theorem stack_card : Fintype.card Stack=3 := by decide

theorem statement_depth (q : Label) : ListAssemblyMachine.statementDepth (program q)≤7 := by
  cases q with
  | inl q =>
      rw [program,TM2Subroutine.splice_local_statementDepth,clockProgram,StateLift.statement_depth]
      cases q with
      | inl q =>
          rw [BinaryClock.program,TM2Subroutine.splice_local_statementDepth]
          exact BinaryCounterMachine.statement_depth q
      | inr q =>
          rw [BinaryClock.program,TM2Subroutine.splice_outer]
          exact (BinaryClock.outer_statement_depth q).trans (by decide)
  | inr q =>
      cases q <;> simp [program,TM2Subroutine.splice,outer,ListAssemblyMachine.statementDepth]

end RationalGateMachine.BinaryFifths
