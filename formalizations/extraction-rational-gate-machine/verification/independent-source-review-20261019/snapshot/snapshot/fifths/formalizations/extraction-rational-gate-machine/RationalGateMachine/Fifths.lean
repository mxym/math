import RationalGateProvider.SignedFifths
import CircuitNumerical.FiniteStackOperationalBridge

open Turing RationalGateProvider

namespace RationalGateMachine

/-- Exactly three Boolean stacks: unary precision clock, numerator digits,
and denominator digits. The local state has only five remainders and a flag. -/
abbrev Configuration := TM2.Cfg (fun _ : Fin 3 => Bool) Unit (Remainder × Bool)

instance : Fintype Remainder := ⟨{.r0,.r1,.r2,.r3,.r4}, by intro r; cases r <;> simp⟩

def stackData (clock numerator denominator : List Bool) : Fin 3 → List Bool :=
  ![clock, numerator, denominator]

@[simp] theorem stackData_zero (a b c : List Bool) : stackData a b c 0 = a := rfl
@[simp] theorem stackData_one (a b c : List Bool) : stackData a b c 1 = b := rfl
@[simp] theorem stackData_two (a b c : List Bool) : stackData a b c 2 = c := rfl

@[simp] theorem update_zero (a b c x : List Bool) :
    Function.update (stackData a b c) 0 x = stackData x b c := by
  funext i; fin_cases i <;> rfl
@[simp] theorem update_one (a b c x : List Bool) :
    Function.update (stackData a b c) 1 x = stackData a x c := by
  funext i; fin_cases i <;> rfl
@[simp] theorem update_two (a b c x : List Bool) :
    Function.update (stackData a b c) 2 x = stackData a b x := by
  funext i; fin_cases i <;> rfl

def program : Unit → TM2.Stmt (fun _ : Fin 3 => Bool) Unit (Remainder × Bool) :=
  fun _ => .pop 0 (fun s b => (s.1, b.isSome))
    (.branch Prod.snd
      (.push 1 (fun s => (transition s.1).1)
        (.push 2 (fun _ => false)
          (.load (fun s => ((transition s.1).2, false)) (.goto (fun _ => ())))))
      .halt)

def active (clock numerator denominator : List Bool) (r : Remainder) : Configuration :=
  ⟨some (), (r, false), stackData clock numerator denominator⟩

def terminal (numerator denominator : List Bool) (r : Remainder) : Configuration :=
  ⟨none, (r, false), stackData [] numerator denominator⟩

theorem step_empty (numerator denominator : List Bool) (r : Remainder) :
    TM2.step program (active [] numerator denominator r) =
      some (terminal numerator denominator r) := by
  simp only [active, terminal, TM2.step, program, TM2.stepAux, stackData_zero,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, update_zero]

theorem step_cons (b : Bool) (clock numerator denominator : List Bool) (r : Remainder) :
    TM2.step program (active (b::clock) numerator denominator r) =
      some (active clock ((transition r).1::numerator) (false::denominator) (transition r).2) := by
  simp only [active, TM2.step, program, TM2.stepAux, stackData_zero,
    List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true,
    update_zero, update_one, update_two, stackData_one, stackData_two]

theorem terminal_stops (numerator denominator : List Bool) (r : Remainder) :
    TM2.step program (terminal numerator denominator r) = none := rfl

theorem program_supports : TM2.Supports program Finset.univ := by
  simp [TM2.Supports, TM2.SupportsStmt, program]

theorem program_statement_depth :
    CircuitRecursion.ListAssemblyMachine.statementDepth (program ()) = 6 := rfl

/-- Proof-side description of consuming the clock. The actual machine
program above branches on stack constructors and never stores a Nat. -/
def advance (s : Output) : List Bool → Output
  | [] => s
  | _::clock => advance (next s) clock

theorem advance_iterate (s : Output) (clock : List Bool) :
    advance s clock = next^[clock.length] s := by
  induction clock generalizing s with
  | nil => rfl
  | cons b clock ih =>
      simpa only [advance, List.length_cons, Function.iterate_succ_apply] using ih (next s)

theorem iterate_seed (initial : Remainder) (p : ℕ) :
    next^[p] ⟨[], initial⟩ = RationalGateProvider.run initial p := by
  induction p with
  | zero => rfl
  | succ p ih =>
      rw [Function.iterate_succ_apply', ih]
      rfl

theorem advance_seed (initial : Remainder) (clock : List Bool) :
    advance ⟨[], initial⟩ clock = RationalGateProvider.run initial clock.length := by
  rw [advance_iterate, iterate_seed]

theorem machine_steps (clock : List Bool) (s : Output) (denominator : List Bool) :
    (fun c : Option Configuration => c.bind (TM2.step program))^[clock.length+1]
      (some (active clock s.bits denominator s.remainder)) =
      some (terminal (advance s clock).bits
        (List.replicate clock.length false ++ denominator) (advance s clock).remainder) := by
  induction clock generalizing s denominator with
  | nil => simp [step_empty, advance]
  | cons b clock ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, step_cons]
      have h := ih (next s) (false::denominator)
      change (fun c : Option Configuration => c.bind (TM2.step program))^[clock.length+1]
        (some (active clock (next s).bits (false::denominator) (next s).remainder)) = _
      rw [h]
      simp only [advance]
      congr 2
      rw [List.replicate_add]
      simp [List.append_assoc]

/-- Real official TM2 transition certificate, with unary clock as input.
The time index is proof-side; there is no machine Nat/fuel register. -/
def fifthsRun (initial : Remainder) (clock : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program) (active clock [] [true] initial)
      (some (terminal (RationalGateProvider.run initial clock.length).bits
        (denominatorBits clock.length) (RationalGateProvider.run initial clock.length).remainder))
      (clock.length+1) := by
  refine ⟨⟨clock.length+1, ?_⟩, le_refl _⟩
  change (fun c : Option Configuration => c.bind (TM2.step program))^[clock.length+1]
    (some (active clock [] [true] initial)) = _
  have h := machine_steps clock ⟨[],initial⟩ [true]
  rw [advance_seed] at h
  exact h

theorem finite_state_card : Fintype.card (Remainder × Bool) = 10 := by decide

theorem stack_card : Fintype.card (Fin 3) = 3 := by decide

theorem label_card : Fintype.card Unit = 1 := by decide

theorem fifthsRun_steps (initial : Remainder) (clock : List Bool) :
    (fifthsRun initial clock).steps = clock.length + 1 := rfl

theorem fifths_terminal_numerator (initial : Remainder) (clock : List Bool) :
    (terminal (RationalGateProvider.run initial clock.length).bits
      (denominatorBits clock.length) (RationalGateProvider.run initial clock.length).remainder).stk 1 =
        (RationalGateProvider.run initial clock.length).bits := rfl

theorem fifths_terminal_denominator (initial : Remainder) (clock : List Bool) :
    (terminal (RationalGateProvider.run initial clock.length).bits
      (denominatorBits clock.length) (RationalGateProvider.run initial clock.length).remainder).stk 2 =
        denominatorBits clock.length := rfl

theorem fifths_terminal_dyadic_error (initial : Remainder) (clock : List Bool) :
    0 ≤ (initial.value : ℚ)/5 -
        (bitValue ((terminal (RationalGateProvider.run initial clock.length).bits
          (denominatorBits clock.length) (RationalGateProvider.run initial clock.length).remainder).stk 1) : ℚ) /
            2^clock.length ∧
      (initial.value : ℚ)/5 -
        (bitValue ((terminal (RationalGateProvider.run initial clock.length).bits
          (denominatorBits clock.length) (RationalGateProvider.run initial clock.length).remainder).stk 1) : ℚ) /
            2^clock.length < 1/(2 : ℚ)^clock.length := by
  exact run_dyadic_error initial clock.length

theorem fifths_terminal_mem_eval (initial : Remainder) (clock : List Bool) :
    terminal (RationalGateProvider.run initial clock.length).bits
      (denominatorBits clock.length) (RationalGateProvider.run initial clock.length).remainder ∈
        StateTransition.eval (TM2.step program) (active clock [] [true] initial) :=
  CircuitRecursion.ListAssemblyMachine.evalsTo_terminal_mem_eval
    (fifthsRun initial clock).toEvalsTo (terminal_stops _ _ _)

end RationalGateMachine
